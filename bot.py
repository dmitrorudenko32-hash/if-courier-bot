"""Personal courier address bot, Render webhook, Python 3.12+."""
import asyncio
import io
import json
import logging
import math
import os
import re
import secrets
import sqlite3
import time
import uuid
import psycopg
from psycopg.rows import dict_row
from pathlib import Path

import aiohttp
from aiohttp import web
from aiogram import Bot, Dispatcher, F
from aiogram.filters import CommandStart, Command
from aiogram.types import BufferedInputFile, InlineKeyboardButton, InlineKeyboardMarkup, ReplyKeyboardMarkup, KeyboardButton
from aiogram.webhook.aiohttp_server import SimpleRequestHandler, setup_application
from PIL import Image, ImageDraw, ImageFont

VERSION = '1.5-personal'
ROOT = Path(__file__).parent
NOMINATIM = os.getenv('NOMINATIM_URL', 'https://nominatim.openstreetmap.org').rstrip('/')
OVERPASS = os.getenv('OVERPASS_URL', 'https://overpass.private.coffee/api/interpreter')
# Bounding box restricts searches to Ivano-Frankivsk and immediate surroundings.
BOX = '24.62,49.00,24.80,48.85'
lock = asyncio.Lock()
last_request = 0.0
session = None
cache = None
choices = {}
drafts = {}
DATABASE_URL = os.getenv("DATABASE_URL", "")
menu = ReplyKeyboardMarkup(keyboard=[[KeyboardButton(text="➕ Додати під’їзд / корпус")],[KeyboardButton(text="📒 Мої позначки"),KeyboardButton(text="Скасувати")]],resize_keyboard=True)
allowed = {int(x) for x in os.getenv('ALLOWED_USER_IDS', '').split(',') if x.strip()}
dp = Dispatcher()


def normalize_house(value):
    value=value.casefold().strip()
    value=re.sub(r'(?:корпус|корп\.?|к\.)\s*', 'к', value)
    return re.sub(r'\s+', '', value)


def parse_address(text):
    text = text.strip().replace('’', "'").replace('ʼ', "'")
    m = re.search(r"(?:під['’]?їзд|під[.]?|парадне)\s*№?\s*([\w-]+)", text, re.I)
    entrance = m.group(1) if m else None
    if m:
        text = text[:m.start()] + text[m.end():]
    text = re.sub(r'[,;\s]+$', '', text)
    # Corpus is separate from an entrance and from letter suffixes (18А).
    corpus = re.search(r'(?:[,;\s]+)(?:корпус|корп\.?|к\.?)\s*№?\s*(\d+[а-яіїєґa-z]?)\s*$',text,re.I)
    if not corpus:
        corpus=re.search(r'(?<=\d)к\.?\s*(\d+[а-яіїєґa-z]?)\s*$',text,re.I)
    unit=corpus.group(1) if corpus else None
    if corpus:
        text=text[:corpus.start()].rstrip(' ,;')
    house=re.search(r'(\d+[а-яіїєґa-z]?(?:\s*[/\-]\s*\d+[а-яіїєґa-z]?)?)\s*$',text,re.I)
    if not house:
        raise ValueError('Напиши адресу: Височана 18, корпус 2, під’їзд 1. Також можна: Височана 18 к2 або Пулюя 15.')
    number=house.group(1).replace(' ','')
    if unit:
        number+=' к'+unit
        text=text[:house.start()]+number
    return text,entrance,normalize_house(number)


def permitted(event):
    return not allowed or event.from_user.id in allowed


async def fetch_json(url, *, params=None, data=None, ttl=86400, geocode=False):
    global last_request
    key = json.dumps([url, params, data], sort_keys=True, ensure_ascii=False)
    row = cache.execute('SELECT body, expires FROM cache WHERE key=?', (key,)).fetchone()
    if row and row[1] > time.time():
        return json.loads(row[0])
    async def request():
        method = 'POST' if data is not None else 'GET'
        async with session.request(method, url, params=params, data=data) as response:
            response.raise_for_status()
            body = await response.json()
        if isinstance(body, dict) and body.get('remark'):
            raise ValueError('Сервіс карти тимчасово перевантажений. Спробуй ще раз за хвилину.')
        cache.execute('INSERT OR REPLACE INTO cache VALUES (?,?,?)', (key, json.dumps(body), time.time()+(300 if body == [] else ttl)))
        cache.commit()
        return body
    if geocode:
        async with lock:
            await asyncio.sleep(max(0, 1.1 - (time.monotonic()-last_request)))
            last_request = time.monotonic()
            return await request()
    return await request()


async def search(text, house):
    rows = await fetch_json(NOMINATIM + '/search', params={
        'q': text + ', Івано-Франківськ, Україна', 'format': 'jsonv2',
        'addressdetails': 1, 'limit': 8, 'countrycodes': 'ua',
        'viewbox': BOX, 'bounded': 1, 'accept-language': 'uk'}, geocode=True)
    # Never present a street centre or another house number as the requested house.
    exact = [r for r in rows if normalize_house(r.get('address', {}).get('house_number', '')) == house]
    if not exact and 'к' not in house:
        exact=[r for r in rows if normalize_house(r.get('address',{}).get('house_number','')).startswith(house+'к')]
    buildings = [r for r in exact if r.get('category', r.get('class')) == 'building']
    addresses = [r for r in exact if r.get('category', r.get('class')) in ('place', 'boundary') and r.get('type') in ('house', 'address', 'yes')]
    candidates = buildings or addresses
    if not candidates:
        return []  # Do not substitute a shop/ATM for a residential building.
    unique = {}
    for r in candidates:
        unique[(r.get('osm_type'), r.get('osm_id'))] = r
    return list(unique.values())


def contains_point(ring, lat, lon):
    inside = False
    for a, b in zip(ring, ring[1:] + ring[:1]):
        if (a['lat'] > lat) != (b['lat'] > lat):
            cross = (b['lon']-a['lon'])*(lat-a['lat'])/(b['lat']-a['lat']) + a['lon']
            if lon < cross:
                inside = not inside
    return inside


def boundary_distance(point, element):
    lat,lon=point['lat'],point['lon']
    c=math.cos(math.radians(lat))
    def xy(p): return ((p['lon']-lon)*111320*c,(p['lat']-lat)*111320)
    distances=[]
    for ring in shape(element):
        for a,b in zip(ring,ring[1:]+ring[:1]):
            ax,ay=xy(a); bx,by=xy(b); dx,dy=bx-ax,by-ay
            den=dx*dx+dy*dy
            u=max(0,min(1,-(ax*dx+ay*dy)/den)) if den else 0
            distances.append(math.hypot(ax+u*dx,ay+u*dy))
    return min(distances,default=float('inf'))


def entrance_label(e):
    tags=e.get('tags',{})
    ref=tags.get('ref')
    flats=tags.get('addr:flats')
    title=('Під’їзд '+ref) if ref else 'Вхід'
    return title+(' • кв. '+flats if flats else '')


def associate(item, elements):
    typ, oid = item.get('osm_type'), item.get('osm_id')
    target = next((e for e in elements if e['type']==typ and e['id']==oid and e.get('tags',{}).get('building')), None)
    if target is None:
        number = normalize_house(item.get('address', {}).get('house_number', ''))
        street = item.get('address', {}).get('road', '').casefold()
        candidates = []
        for e in elements:
            tags = e.get('tags', {})
            if not tags.get('building') or not shape(e):
                continue
            # An address point inside a building establishes a geometric link.
            contains = any(contains_point(ring,float(item['lat']),float(item['lon'])) for ring in shape(e))
            address_match = bool(number and street and normalize_house(tags.get('addr:housenumber',''))==number and tags.get('addr:street','').casefold()==street)
            if contains or address_match:
                candidates.append(e)
        if len(candidates)==1:
            target=candidates[0]
    ids = set(target.get('nodes', [])) if target else set()
    if target and target['type']=='relation':
        for member in target.get('members', []):
            if member.get('type')=='way':
                way=next((e for e in elements if e['type']=='way' and e['id']==member['ref']),None)
                if way: ids.update(way.get('nodes', []))
    entrances=[]
    buildings=[e for e in elements if e.get('tags',{}).get('building') and shape(e)]
    for e in elements:
        if e['type']!='node' or e.get('tags',{}).get('entrance') in (None,'no','exit','emergency'):
            continue
        if e['id'] in ids:
            entrances.append(e)
        elif target and boundary_distance(e,target)<=1.5:
            # Some OSM entrances lie on a separate residential outline instead of
            # sharing the building's nodes. Accept only an unambiguous close wall.
            others=[w for w in buildings if w['id']!=target['id'] and boundary_distance(e,w)<=1.5]
            if not others:
                entrances.append(e)
    return elements,target,entrances


async def direct_building(item):
    # Read only the exact object and its constituent nodes, cached for one day.
    typ=item.get('osm_type')
    if typ not in ('way','relation'):
        raise ValueError('Контур адресної точки не отримано')
    result=await fetch_json(f"https://www.openstreetmap.org/api/0.6/{typ}/{int(item['osm_id'])}/full.json",ttl=86400)
    return unpack_osm(item,result)


def unpack_osm(item,result):
    elements=result.get('elements',[])
    nodes={e['id']:e for e in elements if e['type']=='node'}
    ways={}
    for e in elements:
        if e['type']=='way':
            e['geometry']=[{'lat':nodes[n]['lat'],'lon':nodes[n]['lon']} for n in e.get('nodes',[]) if n in nodes]
            ways[e['id']]=e
    for e in elements:
        if e['type']=='relation':
            for member in e.get('members',[]):
                if member.get('type')=='way' and member['ref'] in ways:
                    member['geometry']=ways[member['ref']].get('geometry',[])
    return associate(item,elements)


async def geometry(item):
    lat,lon=float(item['lat']),float(item['lon'])
    typ=item.get('osm_type')
    selector=f"{typ}({int(item['osm_id'])});" if typ in ('way','relation') else ''
    # Recurse to obtain all outline nodes, including entrances outside the viewport.
    query=f"""[out:json][timeout:18];({selector}
way(around:180,{lat},{lon})[building];
relation(around:180,{lat},{lon})[building];
way(around:180,{lat},{lon})[highway];
node(around:180,{lat},{lon})[entrance];);(._;>;);out body geom;"""
    try:
        result=await fetch_json(OVERPASS,data={'data':query},ttl=86400)
        resolved=associate(item,result.get('elements',[]))
        if resolved[1] is not None:
            return resolved
    except (aiohttp.ClientError,asyncio.TimeoutError,ValueError) as exc:
        # Logs show status/type but do not include submitted addresses or tokens.
        logging.warning('Geometry provider failed: %s status=%s',type(exc).__name__,getattr(exc,'status','n/a'))
    basic=await direct_building(item)
    if basic[2]:
        return basic
    # Fetch a single small, requested viewport; cached, never scan the city.
    try:
        dlat=0.0014; dlon=0.0021
        bbox=f'{lon-dlon},{lat-dlat},{lon+dlon},{lat+dlat}'
        result=await fetch_json('https://www.openstreetmap.org/api/0.6/map.json',params={'bbox':bbox},ttl=86400)
        detailed=unpack_osm(item,result)
        if detailed[1]: return detailed
    except (aiohttp.ClientError,asyncio.TimeoutError,ValueError):
        pass
    return basic


def shape(element):
    if not element:
        return []
    if element['type'] == 'relation':
        return [m['geometry'] for m in element.get('members', []) if m.get('role') == 'outer' and m.get('geometry')]
    return [element['geometry']] if element.get('geometry') else []


def draw_map(item, elements, target, entrances, selected):
    lat, lon = float(item['lat']), float(item['lon'])
    rings = shape(target)
    meters = [( (p['lon']-lon)*111320*math.cos(math.radians(lat)), (p['lat']-lat)*111320) for ring in rings for p in ring]
    extent = max([abs(v) for p in meters for v in p] + [55]) + 35
    scale = 700/(2*extent)
    def xy(p):
        return (450+(p['lon']-lon)*111320*math.cos(math.radians(lat))*scale,
                470-(p['lat']-lat)*111320*scale)
    img = Image.new('RGB', (900, 900), '#f3f1e9')
    d = ImageDraw.Draw(img)
    font = ImageFont.truetype(str(ROOT/'DejaVuSans.ttf'), 19)
    small = ImageFont.truetype(str(ROOT/'DejaVuSans.ttf'), 15)
    for e in elements:
        if e.get('tags', {}).get('highway'):
            for ring in shape(e):
                pts = [xy(p) for p in ring]
                if len(pts)>1:
                    d.line(pts, fill='#ffffff', width=12)
                    name = e.get('tags', {}).get('name')
                    if name:
                        p = pts[len(pts)//2]
                        if 30<p[0]<760 and 100<p[1]<820:
                            d.text(p, name, font=small, fill='#505050')
    for e in elements:
        if e.get('tags', {}).get('building'):
            for ring in shape(e):
                pts = [xy(p) for p in ring]
                if len(pts)>2:
                    d.polygon(pts, fill='#d6d1ca', outline='#9a948c')
                    number = e.get('tags', {}).get('addr:housenumber')
                    if number:
                        mid = (sum(p[0] for p in pts)/len(pts), sum(p[1] for p in pts)/len(pts))
                        d.text(mid, number, font=small, fill='#444444')
    for ring in rings:
        pts = [xy(p) for p in ring]
        if len(pts)>2:
            d.polygon(pts, fill='#ffd4b8', outline='#d35400', width=4)
    if rings:
        pts = [xy(p) for ring in rings for p in ring]
        center = (sum(p[0] for p in pts)/len(pts), sum(p[1] for p in pts)/len(pts))
        number = target.get('tags', {}).get('addr:housenumber') or item.get('address', {}).get('house_number', '')
        d.text(center, number, font=font, fill='#713500')
    if not rings:
        x,y=xy({'lat':lat,'lon':lon})
        d.ellipse((x-10,y-10,x+10,y+10), fill='#d35400')
    for e in entrances:
        x,y=xy(e)
        ref=e.get('tags',{}).get('ref')
        color='#db2626' if selected and ref and ref.casefold()==selected.casefold() else '#1268c4'
        d.ellipse((x-9,y-9,x+9,y+9), fill=color, outline='white', width=2)
        label=(ref or '?') + (' • кв. '+e['tags']['addr:flats'] if e.get('tags',{}).get('addr:flats') else '')
        d.text((x+12,y-22), label, font=small, fill=color, stroke_width=2, stroke_fill='white')
    d.rectangle((0,0,900,80), fill='white')
    d.text((20,15), 'Будинок і під’їзди • Івано-Франківськ', font=font, fill='#222222')
    d.text((20,45), 'Північ ↑  |  сині точки — входи; ? — номер відсутній', font=small, fill='#555555')
    d.rectangle((0,840,900,900), fill='white')
    d.text((18,850), 'Схема за даними OSM • © OpenStreetMap contributors', font=small, fill='#444444')
    d.text((18,875), 'openstreetmap.org/copyright • не фото фасаду', font=small, fill='#444444')
    out=io.BytesIO(); img.save(out, format='PNG'); return out.getvalue()


async def deliver(message, item, selected):
    warning = ''
    try:
        elements, target, entrances = await geometry(item)
    except (aiohttp.ClientError, asyncio.TimeoutError, ValueError):
        elements, target, entrances = [], None, []
        warning = '\n⚠️ Дані контуру й під’їздів зараз недоступні. Показую адресну точку.'
    matching = [e for e in entrances if selected and e.get('tags',{}).get('ref','').casefold()==selected.casefold()]
    point = matching[0] if len(matching)==1 else item
    lat,lon=float(point['lat']),float(point['lon'])
    refs = [entrance_label(e) for e in entrances]
    info = 'Входи в OSM:\n' + '\n'.join(refs) if refs else 'Під’їзди для цього будинку не підтверджені в OSM.'
    if selected:
        info += f'\nПід’їзд {selected}: ' + ('знайдено, геолокація входу.' if len(matching)==1 else 'не визначено однозначно; геолокація будинку.')
    house_label=item.get('address',{}).get('house_number','')
    corpus_info=''
    corpus_match=re.search(r'к(\d+[а-яіїєґa-z]?)$',normalize_house(house_label))
    if corpus_match: corpus_info='\n🏢 Корпус '+corpus_match.group(1)
    text = f"📍 {item['display_name']}{corpus_info}\n\n{lat:.7f}, {lon:.7f}\n{info}{warning}\n\n© OpenStreetMap contributors"
    buttons=InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text='🗺 OpenStreetMap', url=f'https://www.openstreetmap.org/?mlat={lat}&mlon={lon}#map=19/{lat}/{lon}'),
        InlineKeyboardButton(text='🧭 Маршрут', url=f'https://www.google.com/maps/dir/?api=1&destination={lat},{lon}&travelmode=walking')]])
    await message.answer(text, reply_markup=buttons)
    await message.answer_location(latitude=lat, longitude=lon)
    if not target or not shape(target):
        await message.answer('Не вдалося завантажити контур будинку. Карту-зображення зараз не формую; відкрий OpenStreetMap за кнопкою вище.')
        return
    picture=await asyncio.to_thread(draw_map,item,elements,target,entrances,selected)
    await message.answer_photo(BufferedInputFile(picture, filename='building.png'), caption='Схема будинку з даних OpenStreetMap. Номери під’їздів показані лише там, де внесені в карту.')


def address_key(text):
    text=text.casefold().replace('’', "'").replace('ʼ', "'")
    text=re.sub(r'\b(?:вулиця|вул\.?|івано-франківськ|україна)\b','',text)
    return re.sub(r'[\s,.;]+','',text)


def database(action, owner, payload=None):
    if not DATABASE_URL:
        raise ValueError('Для власних позначок додай DATABASE_URL у Render. Збереження поки не підключене.')
    # Separate table; direct Postgres only. No Telegram/customer data sent to OSM.
    with psycopg.connect(DATABASE_URL,connect_timeout=10,sslmode='require',prepare_threshold=None,row_factory=dict_row) as conn:
        conn.execute("""CREATE TABLE IF NOT EXISTS courier_personal_v1 (
            id UUID PRIMARY KEY, owner BIGINT NOT NULL, address_key TEXT NOT NULL,
            address_text TEXT NOT NULL, entrance TEXT NOT NULL DEFAULT '',
            flats TEXT NOT NULL DEFAULT '', lat DOUBLE PRECISION NOT NULL,
            lon DOUBLE PRECISION NOT NULL, updated_at TIMESTAMPTZ NOT NULL DEFAULT now(),
            UNIQUE(owner,address_key,entrance))""")
        # Keep table inaccessible through Supabase's public REST roles.
        conn.execute('ALTER TABLE courier_personal_v1 ENABLE ROW LEVEL SECURITY')
        if action=='save':
            d=payload
            conn.execute("""INSERT INTO courier_personal_v1
              (id,owner,address_key,address_text,entrance,flats,lat,lon)
              VALUES (%s,%s,%s,%s,%s,%s,%s,%s)
              ON CONFLICT(owner,address_key,entrance) DO UPDATE SET
              address_text=EXCLUDED.address_text,flats=EXCLUDED.flats,
              lat=EXCLUDED.lat,lon=EXCLUDED.lon,updated_at=now()""",
              (uuid.uuid4(),owner,address_key(d['address']),d['address'],d.get('entrance') or '',d.get('flats',''),d['lat'],d['lon']))
            return []
        if action=='find':
            return conn.execute('SELECT * FROM courier_personal_v1 WHERE owner=%s AND address_key=%s ORDER BY entrance',(owner,address_key(payload))).fetchall()
        if action=='list':
            return conn.execute('SELECT * FROM courier_personal_v1 WHERE owner=%s ORDER BY updated_at DESC LIMIT 50',(owner,)).fetchall()
        if action=='delete':
            return conn.execute('DELETE FROM courier_personal_v1 WHERE owner=%s AND id=%s RETURNING id',(owner,uuid.UUID(payload))).fetchall()
        return []


async def db(action,owner,payload=None):
    try:
        return await asyncio.to_thread(database,action,owner,payload)
    except ValueError:
        raise
    except Exception as exc:
        logging.error('Personal storage error: %s',type(exc).__name__)
        raise ValueError('База позначок недоступна. Перевір DATABASE_URL у Render або спробуй пізніше. Дані не збережено.') from None


def draft_for(message):
    key=(message.chat.id,message.from_user.id)
    d=drafts.get(key)
    if d and d['expires']<time.time():
        drafts.pop(key,None);return None
    return d


@dp.message(Command('cancel'))
@dp.message(F.text=='Скасувати')
async def cancel(message):
    if not permitted(message):return
    drafts.pop((message.chat.id,message.from_user.id),None)
    await message.answer('Додавання скасовано. Можеш шукати адресу.',reply_markup=menu)


@dp.message(Command('add'))
@dp.message(F.text=='➕ Додати під’їзд / корпус')
async def add(message):
    if not permitted(message):return
    if message.chat.type!='private':
        await message.answer('Додавай власні позначки в особистому чаті з ботом.');return
    if not DATABASE_URL:
        await message.answer('Спочатку додай DATABASE_URL у налаштування Render — це постійна база для твоїх позначок.');return
    drafts[(message.chat.id,message.from_user.id)]={'stage':'address','expires':time.time()+1800,'nonce':secrets.token_hex(6)}
    await message.answer('Напиши адресу з номером під’їзду або корпусу:\nПулюя 15, під’їзд 1\nВисочана 18, корпус 30\n\nЗбереження позначки замінить твою попередню точку для тієї самої адреси й під’їзду. Скасувати: /cancel',reply_markup=menu)


@dp.message(F.location)
async def saved_location(message):
    if not permitted(message):return
    d=draft_for(message)
    if not d or d['stage']!='location':
        await message.answer('Щоб зберегти точку, спочатку натисни «Додати під’їзд / корпус».');return
    loc=message.location
    if loc.live_period:
        await message.answer('Надішли звичайну точку, а не трансляцію геопозиції.');return
    if not (48.85<=loc.latitude<=49.00 and 24.62<=loc.longitude<=24.80):
        await message.answer('Точка поза Івано-Франківськом і найближчими околицями. Перевір її.');return
    d.update(lat=loc.latitude,lon=loc.longitude,stage='flats')
    await message.answer('Напиши діапазон квартир, наприклад 1–37. Якщо він невідомий або додаєш корпус — надішли «-».')


async def process_draft(message,d):
    if d['stage']=='address':
        try:
            text,entrance,house=parse_address(message.text)
        except ValueError as exc:
            await message.answer(str(exc));return
        if not entrance and not re.search(r'к\d',house):
            await message.answer('Укажи під’їзд або корпус, наприклад: Пулюя 15, під’їзд 1.');return
        d.update(address=text,entrance=entrance,stage='location')
        await message.answer('Надішли точну точку входу або корпусу: 📎 → Геопозиція → вибери місце на карті. Поточну геопозицію надсилай лише якщо стоїш біля потрібного входу.');return
    if d['stage']=='location':
        await message.answer('Очікую точку через 📎 → Геопозиція. Скасувати: /cancel');return
    if d['stage']=='flats':
        value=message.text.strip()
        if value!='-' and not re.fullmatch(r'\d+(?:\s*[-–—]\s*\d+)?',value):
            await message.answer('Укажи номер або діапазон квартир, наприклад 1–37, або «-».');return
        if '-' in value.replace('–','-').replace('—','-') and value!='-':
            a,z=map(int,re.split(r'[-–—]',value));
            if a>z:
                await message.answer('Початок діапазону має бути не більшим за кінець.');return
        d.update(flats='' if value=='-' else value,stage='confirm')
        label=d['address']+(f", під’їзд {d['entrance']}" if d['entrance'] else '')
        await message.answer_location(latitude=d['lat'],longitude=d['lon'])
        await message.answer(f"Зберегти?\n{label}\nКвартири: {d['flats'] or 'не вказані'}\n{d['lat']:.7f}, {d['lon']:.7f}",reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text='✅ Зберегти',callback_data='save:'+d['nonce'])]]));return
    await message.answer('Натисни «Зберегти» під перевіреною точкою або /cancel.')


@dp.callback_query(F.data.startswith('save:'))
async def save_point(callback):
    if not permitted(callback):await callback.answer();return
    key=(callback.message.chat.id,callback.from_user.id);d=drafts.get(key)
    if not d or d['stage']!='confirm' or d['nonce']!=callback.data.split(':')[1] or d['expires']<time.time():
        await callback.answer('Цей запис застарів. Почни /add знову.',show_alert=True);return
    await callback.answer('Зберігаю…')
    try:
        await db('save',callback.from_user.id,d)
    except ValueError as exc:
        await callback.message.answer(str(exc));return
    drafts.pop(key,None)
    await callback.message.edit_reply_markup(reply_markup=None)
    await callback.message.answer('✅ Позначку збережено. Під час пошуку цієї адреси покажу твою точку. Перегляд і видалення: /mine',reply_markup=menu)


@dp.message(Command('mine'))
@dp.message(F.text=='📒 Мої позначки')
async def mine(message):
    if not permitted(message):return
    try:rows=await db('list',message.from_user.id)
    except ValueError as exc:await message.answer(str(exc));return
    if not rows:await message.answer('У тебе ще немає позначок. Додати: /add');return
    await message.answer('Твої останні 50 позначок. Видалення потребує підтвердження.')
    for r in rows:
        label=r['address_text']+(f", під’їзд {r['entrance']}" if r['entrance'] else '')
        await message.answer(label+(f"\nКвартири: {r['flats']}" if r['flats'] else ''),reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text='🗺 Точка',url=f"https://www.openstreetmap.org/?mlat={r['lat']}&mlon={r['lon']}#map=19/{r['lat']}/{r['lon']}"),InlineKeyboardButton(text='Видалити',callback_data='delask:'+str(r['id']))]]))


@dp.callback_query(F.data.startswith('delask:'))
async def delete_ask(callback):
    if not permitted(callback):await callback.answer();return
    await callback.answer()
    await callback.message.answer('Видалити цю позначку?',reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text='Так, видалити',callback_data='delete:'+callback.data.split(':')[1])]]))


@dp.callback_query(F.data.startswith('delete:'))
async def delete_point(callback):
    if not permitted(callback):await callback.answer();return
    await callback.answer()
    try:rows=await db('delete',callback.from_user.id,callback.data.split(':')[1])
    except ValueError as exc:await callback.message.answer(str(exc));return
    await callback.message.edit_text('Позначку видалено.' if rows else 'Позначка вже видалена або не належить тобі.')


async def deliver_personal(message,rows,entrance):
    matches=[r for r in rows if (r['entrance'] or None)==entrance]
    if entrance and not matches:
        return False  # Other saved entrances cannot substitute the requested one.
    if not entrance and len(rows)>1:
        token=secrets.token_hex(6)
        choices[token]=(message.from_user.id,time.time()+600,[{'_personal_row':r} for r in rows],None)
        keyboard=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text=r['address_text']+(f" • під’їзд {r['entrance']}" if r['entrance'] else ' • корпус'),callback_data=f'pick:{token}:{i}')] for i,r in enumerate(rows[:20])])
        await message.answer('Є твої збережені точки. Обери потрібну:',reply_markup=keyboard);return True
    r=(matches or rows)[0]
    lat,lon=r['lat'],r['lon']
    await message.answer('📌 Твоя позначка: '+r['address_text']+(f", під’їзд {r['entrance']}" if r['entrance'] else '')+(f"\nКвартири: {r['flats']}" if r['flats'] else '')+f"\n{lat:.7f}, {lon:.7f}",reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text='🗺 OpenStreetMap',url=f'https://www.openstreetmap.org/?mlat={lat}&mlon={lon}#map=19/{lat}/{lon}'),InlineKeyboardButton(text='🧭 Маршрут',url=f'https://www.google.com/maps/dir/?api=1&destination={lat},{lon}&travelmode=walking')]]))
    await message.answer_location(latitude=lat,longitude=lon)
    # Only geographic coordinates are sent to OSM; private notes stay in database.
    try:
        bbox=f'{lon-0.0021},{lat-0.0014},{lon+0.0021},{lat+0.0014}'
        result=await fetch_json('https://www.openstreetmap.org/api/0.6/map.json',params={'bbox':bbox},ttl=86400)
        item={'lat':str(lat),'lon':str(lon),'osm_type':'custom','osm_id':0}
        elements,target,_=unpack_osm(item,result)
        mark={'type':'node','id':-1,'lat':lat,'lon':lon,'tags':{'ref':r['entrance'] or 'Точка','addr:flats':r['flats']}}
        picture=await asyncio.to_thread(draw_map,item,elements,target,[mark],mark['tags']['ref'])
        await message.answer_photo(BufferedInputFile(picture,filename='personal.png'),caption='Червона точка — твоя позначка. Підкладка: © OpenStreetMap contributors.')
    except (aiohttp.ClientError,asyncio.TimeoutError,ValueError):
        await message.answer('Карта-зображення зараз недоступна; твоя точка збережена й доступна за посиланням.')
    return True


@dp.message(CommandStart())
async def start(message):
    if not permitted(message):
        return
    drafts.pop((message.chat.id,message.from_user.id),None)
    await message.answer('Версія '+VERSION+'\nПривіт! Напиши адресу в Івано-Франківську:\nМазепи 42\nМазепи 42, під’їзд 3\nВисочана 18, корпус 2\nВисочана 18 к2, під’їзд 1\n\nЯ надішлю координати, карту й позначені входи. Невідомі під’їзди не вгадую.\nТвій Telegram ID: '+str(message.from_user.id)+'\nДодати свою точку: /add\nМої позначки: /mine',reply_markup=menu)


@dp.message(Command('version'))
async def version(message):
    if permitted(message):
        await message.answer('Версія '+VERSION)


@dp.message(F.text)
async def address(message):
    if not permitted(message):
        return
    d=draft_for(message)
    if d:
        await process_draft(message,d);return
    try:
        text, entrance, house = parse_address(message.text)
        if DATABASE_URL:
            try:
                personal=await db('find',message.from_user.id,text)
                if personal and await deliver_personal(message,personal,entrance):return
            except ValueError as exc:
                await message.answer(str(exc)+' Продовжую пошук у OSM.')
        status = await message.answer('🔎 Шукаю будинок…')
        rows = await search(text, house)
        if not rows:
            await status.edit_text(f'Точного будинку в OSM не знайдено. Запит: {text}.\nПеревір номер і назву вулиці.\nВерсія {VERSION}')
            return
        if len(rows)==1:
            await status.delete()
            await deliver(message,rows[0],entrance)
        else:
            nonce=secrets.token_hex(6)
            choices[nonce]=(message.from_user.id,time.time()+600,rows,entrance)
            # Bound short-lived in-memory choices.
            for k,v in list(choices.items()):
                if v[1]<time.time(): choices.pop(k,None)
            keyboard=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text=r['display_name'][:90],callback_data=f'pick:{nonce}:{i}')] for i,r in enumerate(rows)])
            await status.edit_text('Знайшов кілька варіантів. Обери потрібний:',reply_markup=keyboard)
    except ValueError as exc:
        await message.answer(str(exc))
    except (aiohttp.ClientError, asyncio.TimeoutError):
        await message.answer('Сервіс карти зараз недоступний. Спробуй ще раз за хвилину.')
    except Exception as exc:
        logging.error('Address processing failed: %s', type(exc).__name__)
        await message.answer('Не вдалося обробити адресу. Спробуй ще раз.')


@dp.callback_query(F.data.startswith('pick:'))
async def pick(callback):
    if not permitted(callback):
        await callback.answer(); return
    _,nonce,index=callback.data.split(':')
    record=choices.get(nonce)
    if not record or record[0]!=callback.from_user.id or record[1]<time.time():
        await callback.answer('Вибір застарів. Надішли адресу ще раз.',show_alert=True); return
    await callback.answer('Готую карту…')
    try:
        item=record[2][int(index)]
        if '_personal_row' in item:
            await deliver_personal(callback.message,[item['_personal_row']],item['_personal_row']['entrance'] or None)
        else:
            await deliver(callback.message,item,record[3])
    except Exception as exc:
        logging.error('Selection failed: %s',type(exc).__name__)
        await callback.message.answer('Не вдалося отримати карту. Надішли адресу ще раз.')


async def main():
    global session, cache
    token=os.environ['BOT_TOKEN']
    base=os.getenv('WEBHOOK_URL') or os.getenv('RENDER_EXTERNAL_URL')
    if not base or not base.startswith('https://'):
        raise RuntimeError('Set WEBHOOK_URL to your HTTPS Render service URL')
    secret=os.environ['WEBHOOK_SECRET']
    if not re.fullmatch(r'[A-Za-z0-9_-]{24,256}',secret):
        raise RuntimeError('WEBHOOK_SECRET must contain 24-256 letters, digits, underscores or hyphens')
    contact=os.getenv('OSM_CONTACT',base)
    data_dir=Path(os.getenv('DATA_DIR','./data')); data_dir.mkdir(parents=True,exist_ok=True)
    cache=sqlite3.connect(data_dir/'cache.db')
    cache.execute('CREATE TABLE IF NOT EXISTS cache (key TEXT PRIMARY KEY, body TEXT, expires REAL)')
    cache.execute('DELETE FROM cache WHERE expires < ?', (time.time(),)); cache.commit()
    session=aiohttp.ClientSession(headers={'User-Agent':f'IFCourierMapBot/1.0 ({contact})'},timeout=aiohttp.ClientTimeout(total=40))
    bot=Bot(token)
    app=web.Application()
    async def health(request): return web.Response(text='Courier bot OK')
    app.router.add_get('/',health)
    SimpleRequestHandler(dp,bot,secret_token=secret).register(app,path='/webhook')
    setup_application(app,dp,bot=bot)
    runner=web.AppRunner(app)
    try:
        await runner.setup()
        await web.TCPSite(runner,'0.0.0.0',int(os.getenv('PORT','10000'))).start()
        await bot.set_webhook(base.rstrip('/')+'/webhook',secret_token=secret,allowed_updates=dp.resolve_used_update_types())
        logging.info('Courier bot started: %s', VERSION)
        await asyncio.Event().wait()
    finally:
        await runner.cleanup()
        await session.close()
        await bot.session.close()
        cache.close()


if __name__=='__main__':
    logging.basicConfig(level=logging.INFO)
    asyncio.run(main())
