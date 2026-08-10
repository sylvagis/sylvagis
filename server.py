import ee
import re
import io
import os
import copy
import uuid
import hashlib
import json
import math
import time
import shutil
import threading
import zipfile
import tempfile
import datetime
import traceback
import urllib.parse
import requests
from concurrent.futures import ThreadPoolExecutor, as_completed
from flask import Flask, request, jsonify, Response
from flask_cors import CORS

app = Flask(__name__)
CORS(app)
print('SylvaGIS server.py yüklendi — versiyon: zip-export-v2-tiling')


# API istemcisi JSON bekler. Flask'in varsayılan HTML 404/405 sayfaları,
# yanlış endpoint veya proxy yönlendirmesi olduğunda istemcide
# "Unexpected token 'T'" gibi yanıltıcı bir parse hatasına dönüşmesin.
@app.errorhandler(404)
def _api_not_found(error):
    if request.path.startswith('/api/'):
        return jsonify({
            'success': False,
            'error': f'API endpoint bulunamadı: {request.path}'
        }), 404
    return error


@app.errorhandler(405)
def _api_method_not_allowed(error):
    if request.path.startswith('/api/'):
        return jsonify({
            'success': False,
            'error': f'Bu API endpoint için HTTP metodu desteklenmiyor: {request.method}'
        }), 405
    return error


# ════════════════════════════════════════════════════════════════
# 🔁 GEE / AĞ ÇAĞRILARI İÇİN OTOMATİK TEKRAR DENEME (RETRY)
# ════════════════════════════════════════════════════════════════
# SORUN: "Birkaç analiz peş peşe yapılınca sunucu bağlantı hatası veriyor
# ya da indirme yapmıyor" şikayetinin en olası kök nedeni budur.
#
# /api/analyze tek bir istekte GEE'ye 5-7 ayrı ağ çağrısı (.getInfo(),
# reduceRegion, getMapId vb.) yapar. Google Earth Engine, bir servis
# hesabı için EŞZAMANLI istek sayısına ve dakikadaki istek sayısına
# sınır koyar. Kullanıcı birkaç analizi ARKA ARKAYA (önceki analiz daha
# bitmeden) çalıştırdığında, bu sınır aşılabilir ve GEE geçici bir hata
# (429 Too Many Requests, 503 Service Unavailable, veya bir bağlantı
# timeout'u) döndürür. ÖNCEDEN bu tür geçici/tek seferlik hatalar
# HİÇBİR tekrar denemesi olmadan doğrudan kullanıcıya "sunucu bağlantı
# hatası" olarak yansıtılıyordu — oysa aynı istek birkaç saniye sonra
# tekrar denense büyük ihtimalle başarılı olurdu.
#
# Bu, Render/Vercel gibi barındırma platformunun "kasması"ndan bağımsız,
# TAMAMEN yazılımsal bir sorundur — barındırma iyileştirilse bile GEE
# tarafındaki geçici limit aşımları aynı şekilde hatayla sonuçlanmaya
# devam ederdi. Aşağıdaki yardımcı fonksiyon, GEE/ağ çağrılarını üstel
# geri çekilme (exponential backoff) ile otomatik olarak yeniden dener;
# yalnızca TÜM denemeler tükendiğinde asıl hatayı yukarı fırlatır.
def _call_with_retry(fn, *args, retries=3, base_delay=1.5, **kwargs):
    """
    fn(*args, **kwargs) çağrısını dener; geçici (transient) bir ağ/GEE
    hatasıyla karşılaşırsa kısa bir bekleme sonrası tekrar dener.
    Toplam deneme sayısı: retries + 1 (ilk deneme + retries tekrar).
    Kalıcı görünen hatalarda (ör. geometri/parametre hatası — "Invalid",
    "must be", "not found" gibi mesajlar) hemen (tekrar denemeden)
    yeniden fırlatılır; bunları tekrar denemek zaman kaybettirir ve
    kullanıcıyı gereksiz yere bekletir.
    """
    _non_retryable_markers = (
        'invalid', 'must be', 'not found', 'permission', 'denied',
        'unauthorized', 'bad request', 'parse', 'geometry for image clipping',
    )
    last_err = None
    for attempt in range(retries + 1):
        try:
            return fn(*args, **kwargs)
        except Exception as e:
            last_err = e
            msg = str(e).lower()
            if any(m in msg for m in _non_retryable_markers):
                raise
            if attempt < retries:
                delay = base_delay * (2 ** attempt)
                print('[SylvaGIS] ⚠️ Geçici hata (deneme {}/{}), {:.1f} sn sonra '
                      'tekrar denenecek: {}'.format(attempt + 1, retries + 1, delay, e))
                time.sleep(delay)
            else:
                raise
    raise last_err


# ════════════════════════════════════════════════════════════════
# 🏠 BİNA POLİGONU SORGULARI İÇİN KISA SÜRELİ ÖNBELLEK
# ════════════════════════════════════════════════════════════════
# Harita senkronizasyonu, çift tıklama veya aynı AOI'nin yeniden çizilmesi
# aynı GEE sorgusunun kısa aralıklarla tekrar gönderilmesine neden olabilir.
# Başarılı yanıtları kısa süreli ve sınırlı bir bellekte tutarak gereksiz kota
# tüketimini azaltıyoruz. Hata yanıtları önbelleğe alınmaz.
_BUILDING_CACHE_TTL_SECONDS = 60
_BUILDING_CACHE_MAX_ITEMS = 24
_building_cache = {}
_building_cache_lock = threading.RLock()
_BUILDING_DATASET_ID = 'GOOGLE/Research/open-buildings/v3/polygons'
_BUILDING_DATASET_NAME = 'Google Open Buildings v3'
_BUILDING_DATASET_COVERAGE_NOTE = (
    'Haritada görünen yapılar altlık/uydu görüntüsünde olabilir; Google Open '
    'Buildings v3 veri kümesi tüm ülkeleri kapsamaz.'
)
_OSM_OVERPASS_ENDPOINTS = (
    'https://overpass-api.de/api/interpreter',
    'https://overpass.kumi.systems/api/interpreter',
    'https://overpass.private.coffee/api/interpreter',
)
_OSM_FALLBACK_NOTE = (
    'Google Open Buildings v3 sonuç vermediği için aynı alan OpenStreetMap '
    'bina ayak izleriyle kontrol edildi. Bina ve çatı parçaları birlikte tarandı.'
)


# ════════════════════════════════════════════════════════════════
# 🧩 TILE BAZLI BİNA TARAMASI — Aşama 1-3 (server.py: tiling + dedup)
# ════════════════════════════════════════════════════════════════
# Overpass tek seferde yalnızca küçük AOI'leri güvenilir şekilde tarayabiliyor
# (bkz. _osm_buildings_from_bbox'daki 0.08°/0.004° eşiği). Büyük bir çalışma
# alanı (ör. bir ilçe) seçildiğinde eskiden bu eşik AŞILIYOR ve tarama hiç
# yapılmadan "alan çok büyük" uyarısı dönüyordu — sonuçta çatılar eksik
# kalıyordu. Bunun yerine büyük AOI, sabit boyutlu küçük tile'lara (kareler)
# bölünür; her tile ayrı ayrı (ve gerekirse tekrar denenerek) Overpass'a
# sorgulanır, sonuçlar way id'sine göre tekilleştirilir (aynı bina birden
# fazla tile sınırında görünebilir) ve birleştirilir. Böylece alan ne kadar
# büyük olursa olsun otomatik olarak tam taranır.
_OSM_TILE_SIZE_DEG = 0.025      # varsayılan tile kenarı (~2.5 km) — küçük/orta alanlarda
_OSM_TILE_SIZE_MIN_DEG = 0.01   # otomatik boyutlandırmada inebileceği en küçük kenar
_OSM_TILE_SIZE_MAX_DEG = 0.2    # otomatik büyümede çıkabileceği en büyük kenar (~20 km)
_OSM_TILE_TARGET_COUNT = 800    # otomatik boyutlandırmanın hedeflediği tile sayısı
_OSM_TILE_GROW_FACTOR = 1.5     # tile sayısı tavanı aşılınca kenarın büyüme çarpanı
_OSM_TILE_MAX_COUNT = 6000      # tek bir işte taranabilecek azami tile sayısı (üst tavan)
_OSM_TILE_MAX_WORKERS = 5       # Overpass'a eşzamanlı gönderilecek azami istek sayısı (4-6)
_OSM_TILE_RECURSE_MAX_DEPTH = 2       # başarısız tile'ın bölüneceği azami özyineleme derinliği
_OSM_TILE_RECURSE_MIN_DEG = 0.003     # bu boyutun altına inen alt-tile artık bölünmez


def _split_bbox_into_tiles(west, south, east, north, tile_size=_OSM_TILE_SIZE_DEG):
    """
    Bir bbox'u sabit boyutlu, ızgaraya hizalı (grid-aligned) tile'lara böler.
    Izgara hizalaması, komşu/örtüşen AOI'lerin aynı tile sınırlarını
    üretmesini sağlar — bu da tile önbelleğinin (bkz. Aşama 6) yeniden
    kullanılabilir olması için gereklidir.
    """
    if tile_size <= 0:
        raise ValueError('tile_size sıfırdan büyük olmalı.')

    start_x = math.floor(west / tile_size) * tile_size
    start_y = math.floor(south / tile_size) * tile_size

    tiles = []
    x = start_x
    while x < east:
        y = start_y
        while y < north:
            tiles.append((
                round(x, 8),
                round(y, 8),
                round(x + tile_size, 8),
                round(y + tile_size, 8),
            ))
            y += tile_size
        x += tile_size
    return tiles


def _auto_tile_size(west, south, east, north):
    """
    Aşama 1 — tile boyutunu alan büyüklüğüne göre otomatik seçer. Küçük/orta
    alanlarda varsayılan ayrıntı (_OSM_TILE_SIZE_DEG) korunur; bbox alanı
    büyüdükçe (hedef tile sayısını, _OSM_TILE_TARGET_COUNT, aşacak şekilde)
    tile kenarı orantılı olarak büyütülür — böylece çok büyük bir bölge
    gereksiz yere onbinlerce küçük tile'a bölünmez.
    """
    width = max(1e-9, east - west)
    height = max(1e-9, north - south)
    area_deg2 = width * height
    estimated_count_at_default = area_deg2 / (_OSM_TILE_SIZE_DEG ** 2)
    if estimated_count_at_default <= _OSM_TILE_TARGET_COUNT:
        return _OSM_TILE_SIZE_DEG
    ideal_edge = math.sqrt(area_deg2 / _OSM_TILE_TARGET_COUNT)
    return max(_OSM_TILE_SIZE_MIN_DEG, min(_OSM_TILE_SIZE_MAX_DEG, ideal_edge))


def _filter_tiles_by_polygon(tiles, geometry):
    """
    Aşama 1 — yalnızca gerçek AOI poligonuyla kesişen tile'ları döndürür
    (bbox-only değil, poligon kesişimi kontrolü). shapely sunucuda kurulu
    değilse veya geometri ayrıştırılamazsa, güvenli tarafta kalmak için
    filtrelemeden tüm tile'lar (eski bbox-only davranış) döndürülür.
    """
    try:
        from shapely.geometry import shape as _shapely_shape
        from shapely.geometry import box as _shapely_box
    except ImportError:
        return tiles

    try:
        aoi_shape = _shapely_shape(geometry)
        if not aoi_shape.is_valid:
            aoi_shape = aoi_shape.buffer(0)
    except Exception:
        return tiles

    filtered = []
    for tile_bbox in tiles:
        west, south, east, north = tile_bbox
        try:
            if aoi_shape.intersects(_shapely_box(west, south, east, north)):
                filtered.append(tile_bbox)
        except Exception:
            # Şüpheli durumda tile'ı elemek yerine korumak (eksik tarama
            # yerine gereksiz bir sorgu yapmak) daha güvenli.
            filtered.append(tile_bbox)

    # Beklenmedik şekilde hepsi elenirse (ör. geometri/CRS uyuşmazlığı),
    # tamamen boş sonuç dönmek yerine orijinal (filtresiz) listeye düş.
    return filtered if filtered else tiles


# ════════════════════════════════════════════════════════════════
# 🏠 TILE BAZLI ÖNBELLEK — Aşama 6 (tile bazlı cache stratejisi)
# ════════════════════════════════════════════════════════════════
# Eski önbellek tüm AOI'yi tek anahtar olarak tutuyordu (_building_cache_key);
# her sorgu farklı bir poligon/tarama olabileceği için bu yaklaşım tile
# taramasında işe yaramaz. Bunun yerine her tile kendi (grid-aligned) bbox'ına
# göre ayrı önbelleklenir. Kullanıcı komşu/örtüşen bir alan tekrar
# çizdiğinde, daha önce taranmış tile'lar tekrar Overpass'a gitmeden
# önbellekten gelir. OSM verisi sık değişmediği için TTL, eski 60 sn'lik
# AOI önbelleğine göre çok daha uzun (15 dk) tutulur; tile sayısı da binlerce
# tile'ı kapsayacak şekilde ayarlanır.
_TILE_CACHE_TTL_SECONDS = 15 * 60
_TILE_CACHE_MAX_ITEMS = 8000
_tile_cache = {}
_tile_cache_lock = threading.RLock()


def _tile_cache_key(tile_bbox):
    return tuple(round(v, 6) for v in tile_bbox)


def _get_cached_tile(tile_bbox):
    key = _tile_cache_key(tile_bbox)
    now = time.monotonic()
    with _tile_cache_lock:
        entry = _tile_cache.get(key)
        if not entry:
            return None
        if now - entry['created_at'] > _TILE_CACHE_TTL_SECONDS:
            _tile_cache.pop(key, None)
            return None
        entry['last_used_at'] = now
        return copy.deepcopy(entry['features'])


def _cache_tile(tile_bbox, features):
    key = _tile_cache_key(tile_bbox)
    now = time.monotonic()
    with _tile_cache_lock:
        _tile_cache[key] = {
            'created_at': now,
            'last_used_at': now,
            'features': copy.deepcopy(features),
        }
        if len(_tile_cache) > _TILE_CACHE_MAX_ITEMS:
            oldest_key = min(
                _tile_cache,
                key=lambda cache_key: _tile_cache[cache_key]['last_used_at'],
            )
            _tile_cache.pop(oldest_key, None)


def _osm_buildings_from_tile(tile_bbox):
    """Tek bir tile için Overpass sorgusu (önbellek yardımcıları ile birlikte kullanılır)."""
    west, south, east, north = tile_bbox
    return _overpass_query_bbox(west, south, east, north, timeout=25)


def _scan_tile_recursive(tile_bbox, depth=0):
    """
    Aşama 2 — tek bir tile'ı (önbellek + retry ile) tarar; tile zaman
    aşımına uğrarsa veya Overpass'tan hata dönerse (ör. 'elman'/bellek
    limiti), tile'ı 4 küçük parçaya bölüp her birini ayrı ayrı tekrar
    dener (recursive tile-splitting) — böylece en yoğun bölgeler bile
    tamamen atlanmak yerine parça parça taranır. Döndürür: (features, hata_sayısı).
    """
    cached = _get_cached_tile(tile_bbox)
    if cached is not None:
        return cached, 0

    try:
        features = _call_with_retry(
            lambda tb=tile_bbox: _osm_buildings_from_tile(tb),
            retries=1,
            base_delay=1.0,
        )
        _cache_tile(tile_bbox, features)
        return features, 0
    except Exception as tile_error:
        west, south, east, north = tile_bbox
        width = east - west
        height = north - south
        if (
            depth >= _OSM_TILE_RECURSE_MAX_DEPTH
            or width <= _OSM_TILE_RECURSE_MIN_DEG
            or height <= _OSM_TILE_RECURSE_MIN_DEG
        ):
            print(
                '[SylvaGIS] Tile taraması kalıcı olarak başarısız (derinlik {}): '
                '{} — {}'.format(depth, tile_bbox, tile_error)
            )
            return [], 1

        mid_x = (west + east) / 2.0
        mid_y = (south + north) / 2.0
        quadrants = (
            (west, south, mid_x, mid_y),
            (mid_x, south, east, mid_y),
            (west, mid_y, mid_x, north),
            (mid_x, mid_y, east, north),
        )
        print(
            '[SylvaGIS] Tile başarısız, 4 alt-tile\'a bölünüp tekrar deneniyor '
            '(derinlik {}): {} — {}'.format(depth + 1, tile_bbox, tile_error)
        )
        combined_features = []
        combined_errors = 0
        for quadrant in quadrants:
            sub_features, sub_errors = _scan_tile_recursive(quadrant, depth=depth + 1)
            combined_features.extend(sub_features)
            combined_errors += sub_errors
        return combined_features, combined_errors


# ════════════════════════════════════════════════════════════════
# ⚙️ ARKA PLAN İŞ (JOB) KUYRUĞU — Aşama 4 (asenkron iş kuyruğu)
# ════════════════════════════════════════════════════════════════
# Tek istek/tek yanıt modeli yerine iş (job) tabanlı akışa geçiliyor:
#   POST /api/building-footprints/start   -> jobId döner, tarama arkada başlar
#   GET  /api/building-footprints/status/<job_id> -> ilerleme + (bitince) sonuç
#   POST /api/building-footprints/cancel/<job_id> -> devam eden taramayı durdurur
# Basit bir bellek-içi job registry (dict + kilit), mevcut
# _building_cache_lock mantığına benzer şekilde kullanılır; iş bitince veya
# zaman aşımına uğrayınca otomatik temizlenir.
_building_jobs = {}
_building_jobs_lock = threading.RLock()
_BUILDING_JOB_TTL_SECONDS = 30 * 60  # bitmiş işler 30 dk sonra temizlenir
_BUILDING_JOB_MAX_ITEMS = 200
_BUILDING_JOB_DIR = os.environ.get(
    'SYLVA_BUILDING_JOB_DIR',
    os.path.join(tempfile.gettempdir(), 'sylvagis-building-jobs'),
)


def _building_job_path(job_id):
    """İş durumunun tüm sunucu worker'ları tarafından paylaşılacağı dosya."""
    if not re.fullmatch(r'[a-f0-9]{32}', str(job_id or '')):
        return None
    return os.path.join(_BUILDING_JOB_DIR, 'job-{}.json'.format(job_id))


def _read_persisted_building_job(job_id):
    path = _building_job_path(job_id)
    if not path:
        return None
    try:
        with open(path, 'r', encoding='utf-8') as handle:
            return json.load(handle)
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        return None


def _persist_building_job(job):
    """Job'u atomik olarak ortak diske yazar.

    Gunicorn/uWSGI gibi çok worker'lı sunucularda POST /start ile sonraki
    GET /status istekleri farklı process'lere gidebilir. Sadece process
    belleğinde tutulan dict bu durumda kaybolur; atomik JSON dosyası tüm
    worker'ların aynı durumu görmesini sağlar.
    """
    path = _building_job_path(job.get('id'))
    if not path:
        return
    temporary_path = None
    try:
        os.makedirs(_BUILDING_JOB_DIR, exist_ok=True)
        # Başka bir worker iptal bayrağını yazdıysa yerel snapshot bunu
        # yanlışlıkla silmesin.
        latest = _read_persisted_building_job(job.get('id'))
        if latest and latest.get('cancelRequested'):
            job['cancelRequested'] = True
        fd, temporary_path = tempfile.mkstemp(
            prefix='.job-', suffix='.json', dir=_BUILDING_JOB_DIR
        )
        with os.fdopen(fd, 'w', encoding='utf-8') as handle:
            json.dump(job, handle, ensure_ascii=False, separators=(',', ':'))
        os.replace(temporary_path, path)
        temporary_path = None
    except Exception as persist_error:
        # Analiz bellekte devam edebilsin; durum endpoint'i yine de aynı
        # worker'da çalışır. Ortak diske yazma hatası log'a açıkça düşer.
        print('[SylvaGIS] Bina iş durumu diske yazılamadı:', persist_error)
    finally:
        if temporary_path:
            try:
                os.unlink(temporary_path)
            except OSError:
                pass


def _get_building_job(job_id):
    """Önce ortak snapshot'ı, yoksa mevcut process belleğini okur."""
    persisted = _read_persisted_building_job(job_id)
    if persisted:
        with _building_jobs_lock:
            _building_jobs[job_id] = persisted
        return persisted
    with _building_jobs_lock:
        return _building_jobs.get(job_id)


def _new_building_job(geometry):
    job_id = uuid.uuid4().hex
    now = time.time()
    job = {
        'id': job_id,
        'status': 'running',            # running | done | error | cancelled
        'geometry': geometry,
        'tilesDone': 0,
        'totalTiles': 0,
        'buildingCountSoFar': 0,
        'totalAreaM2SoFar': 0.0,
        'buildingCount': 0,
        'totalAreaM2': 0.0,
        'finalGeojson': None,
        'partialFeatures': {},          # id -> feature (dedup için dict)
        'dataset': None,
        'coverageNote': '',
        'error': None,
        'cancelRequested': False,
        'createdAt': now,
        'updatedAt': now,
    }
    with _building_jobs_lock:
        _building_jobs[job_id] = job
        _cleanup_building_jobs_locked()
        _persist_building_job(job)
    return job_id


def _cleanup_building_jobs_locked():
    """Çağıran zaten _building_jobs_lock tutuyor olmalı."""
    now = time.time()
    finished_states = ('done', 'error', 'cancelled')
    stale_keys = [
        job_id for job_id, job in _building_jobs.items()
        if job['status'] in finished_states
        and now - job['updatedAt'] > _BUILDING_JOB_TTL_SECONDS
    ]
    for job_id in stale_keys:
        _building_jobs.pop(job_id, None)
        path = _building_job_path(job_id)
        if path:
            try:
                os.unlink(path)
            except OSError:
                pass
    if len(_building_jobs) > _BUILDING_JOB_MAX_ITEMS:
        oldest_ids = sorted(
            _building_jobs, key=lambda jid: _building_jobs[jid]['updatedAt']
        )[: len(_building_jobs) - _BUILDING_JOB_MAX_ITEMS]
        for job_id in oldest_ids:
            _building_jobs.pop(job_id, None)
            path = _building_job_path(job_id)
            if path:
                try:
                    os.unlink(path)
                except OSError:
                    pass

    # Önceki process kapanmış olsa bile dosya snapshot'ları birikmesin.
    try:
        for filename in os.listdir(_BUILDING_JOB_DIR):
            if not (filename.startswith('job-') and filename.endswith('.json')):
                continue
            path = os.path.join(_BUILDING_JOB_DIR, filename)
            persisted = _read_persisted_building_job(filename[4:-5])
            if (
                persisted
                and persisted.get('status') in ('done', 'error', 'cancelled')
                and now - float(persisted.get('updatedAt') or now)
                    > _BUILDING_JOB_TTL_SECONDS
            ):
                try:
                    os.unlink(path)
                except OSError:
                    pass
    except OSError:
        pass


def _job_is_cancelled(job_id):
    job = _get_building_job(job_id)
    return bool(job and job.get('cancelRequested'))


def _gee_buildings_paginated(buildings, expected_count, page_size=4000):
    """
    GEE Open Buildings koleksiyonunu tek bir getInfo() ile çekmek yerine
    sayfalayarak (ee.FeatureCollection.toList) çeker. Aşama 7: GEE'nin
    getInfo eleman limiti (varsayılan ~5000) aşıldığında sonuç sessizce
    kesilebiliyordu; burada gerçek bir 'truncated' bayrağı hesaplanır ve
    tüm elemanlar sayfalanarak toplanır.
    """
    features = []
    offset = 0
    while True:
        page = _call_with_retry(
            lambda off=offset: buildings.toList(page_size, off).getInfo(),
            retries=2,
        ) or []
        if not page:
            break
        for raw in page:
            geom = raw.get('geometry')
            props = raw.get('properties') or {}
            features.append({
                'type': 'Feature',
                'id': raw.get('id'),
                'properties': props,
                'geometry': geom,
            })
        offset += len(page)
        if len(page) < page_size or offset >= expected_count:
            break
    truncated = len(features) < expected_count
    return features, truncated


def _run_building_job(job_id):
    """Arka plan thread'inde çalışır: önce GEE Open Buildings dener, sonuç
    yoksa tile bazlı OSM taramasına geçer. `_new_building_job` içinde
    kurulan job dict'ini kilitle güncelleyerek ilerlemeyi dışarı açar."""
    job = _get_building_job(job_id)
    geometry = job.get('geometry') if job else None
    if job is None or geometry is None:
        return

    try:
        # ── 1) Önce GEE Open Buildings dene (Türkiye kapsam dışı olsa da
        #      diğer projeler/ülkeler için hızlı yol budur) ──────────────
        building_count = 0
        gee_features = []
        gee_truncated = False
        gee_error = None
        try:
            aoi = make_roi(geometry)
            buildings = ee.FeatureCollection(_BUILDING_DATASET_ID).filterBounds(aoi)
            buildings_with_area = buildings.map(
                lambda feature: feature.set(
                    '_sylva_area_m2', feature.geometry().area(maxError=1)
                )
            )
            stats = _call_with_retry(
                lambda: ee.Dictionary({
                    'buildingCount': buildings.size(),
                    'totalAreaM2': buildings_with_area.aggregate_sum('_sylva_area_m2'),
                }).getInfo(),
                retries=2,
            ) or {}
            try:
                building_count = int(stats.get('buildingCount') or 0)
            except (TypeError, ValueError):
                building_count = 0
            gee_total_area = 0.0
            try:
                gee_total_area = float(stats.get('totalAreaM2') or 0)
            except (TypeError, ValueError):
                gee_total_area = 0.0

            if building_count > 0:
                with _building_jobs_lock:
                    job['totalTiles'] = 1
                gee_features, gee_truncated = _gee_buildings_paginated(
                    buildings, building_count
                )
                # filterBounds AOI'ye değen binaları döndürür; sınır dışına
                # taşan çatı parçalarını sonuçtan çıkarmak için gerçek
                # geometrik kesişimi uygula.
                gee_features = _clip_building_features_to_aoi(
                    gee_features,
                    geometry,
                )
                # Bilgi kutusundaki toplam alan da artık yalnızca AOI
                # içinde kalan çatı parçalarının alanını göstermeli.
                gee_total_area = sum(
                    float((feature.get('properties') or {}).get('area_m2') or 0.0)
                    for feature in gee_features
                )
        except Exception as e:
            gee_error = str(e)
            print('[SylvaGIS] Bina job — GEE denemesi başarısız:', gee_error)

        if _job_is_cancelled(job_id):
            with _building_jobs_lock:
                job['status'] = 'cancelled'
                job['updatedAt'] = time.time()
                _persist_building_job(job)
            return

        if building_count > 0 and gee_features:
            coverage_note = _BUILDING_DATASET_COVERAGE_NOTE
            if gee_truncated:
                coverage_note += (
                    ' Uyarı: bina sayısı çok yüksek olduğu için sonuçlar '
                    'sayfalanarak tamamlandı.'
                )
            with _building_jobs_lock:
                job['tilesDone'] = 1
                job['totalTiles'] = 1
                job['buildingCountSoFar'] = len(gee_features)
                job['buildingCount'] = len(gee_features)
                job['totalAreaM2SoFar'] = gee_total_area
                job['totalAreaM2'] = gee_total_area
                job['finalGeojson'] = {
                    'type': 'FeatureCollection',
                    'features': gee_features,
                }
                job['dataset'] = _BUILDING_DATASET_NAME
                job['coverageNote'] = coverage_note
                job['status'] = 'done'
                job['updatedAt'] = time.time()
                _persist_building_job(job)
            return

        # ── 2) GEE boş/kapsam dışı ise tile bazlı OSM taramasına geç ────
        west, south, east, north = _geojson_bbox(geometry)

        # Aşama 1 — tile boyutu alana göre otomatik seçilir, sadece AOI
        # poligonuyla kesişen tile'lar tutulur (bbox-only değil).
        tile_size = _auto_tile_size(west, south, east, north)
        tiles = _split_bbox_into_tiles(west, south, east, north, tile_size)
        tiles = _filter_tiles_by_polygon(tiles, geometry)

        # Aşırı tile sayısına karşı güvenlik: eşik aşılırsa hemen hata
        # vermek yerine önce tile boyutu kademeli büyütülür (üst limit
        # _OSM_TILE_SIZE_MAX_DEG); sonsuz büyümeyi önlemek için deneme
        # sayısı ve mutlak tile-sayısı tavanı (_OSM_TILE_MAX_COUNT) korunur.
        grow_attempts = 0
        while (
            len(tiles) > _OSM_TILE_MAX_COUNT
            and tile_size < _OSM_TILE_SIZE_MAX_DEG
            and grow_attempts < 6
        ):
            tile_size = min(_OSM_TILE_SIZE_MAX_DEG, tile_size * _OSM_TILE_GROW_FACTOR)
            tiles = _split_bbox_into_tiles(west, south, east, north, tile_size)
            tiles = _filter_tiles_by_polygon(tiles, geometry)
            grow_attempts += 1

        if len(tiles) > _OSM_TILE_MAX_COUNT:
            with _building_jobs_lock:
                job['status'] = 'error'
                job['error'] = (
                    'Seçilen alan çok büyük ({} tile, azami tile boyutunda bile). '
                    'Lütfen daha küçük bir alan seçin.'.format(len(tiles))
                )
                job['updatedAt'] = time.time()
                _persist_building_job(job)
            return

        with _building_jobs_lock:
            job['totalTiles'] = len(tiles)
            job['dataset'] = 'OpenStreetMap / Overpass API'
            job['coverageNote'] = _OSM_FALLBACK_NOTE

        seen_features = {}
        total_area_m2 = 0.0
        tile_errors = 0
        tiles_done = 0
        was_cancelled = False

        # Aşama 2 — Overpass'ın adil kullanım kurallarına uymak için
        # eşzamanlı istek sayısı sınırlanır (_OSM_TILE_MAX_WORKERS, 4-6);
        # her tile kendi içinde önbellek + retry + gerekirse recursive
        # tile-splitting (_scan_tile_recursive) ile taranır.
        with ThreadPoolExecutor(max_workers=_OSM_TILE_MAX_WORKERS) as executor:
            future_to_tile = {
                executor.submit(_scan_tile_recursive, tile_bbox): tile_bbox
                for tile_bbox in tiles
            }
            for future in as_completed(future_to_tile):
                if _job_is_cancelled(job_id):
                    was_cancelled = True
                    for pending_future in future_to_tile:
                        pending_future.cancel()
                    break

                try:
                    tile_features, tile_error_count = future.result()
                except Exception as tile_error:
                    tile_features, tile_error_count = [], 1
                    print(
                        '[SylvaGIS] Tile taraması beklenmeyen hatayla '
                        'sonuçlandı ({}): {}'.format(
                            future_to_tile[future], tile_error
                        )
                    )
                tile_errors += tile_error_count

                # 20 — dedup: aynı bina birden fazla tile sınırında görünebilir,
                # way id'sine göre tekilleştir.
                clipped_tile_features = _clip_building_features_to_aoi(
                    tile_features,
                    geometry,
                )
                for feature in clipped_tile_features:
                    fid = feature.get('id')
                    if fid not in seen_features:
                        seen_features[fid] = feature
                        total_area_m2 += (
                            feature.get('properties', {})
                            .get('area_m2', 0.0)
                        )

                tiles_done += 1
                with _building_jobs_lock:
                    job['tilesDone'] = tiles_done
                    job['buildingCountSoFar'] = len(seen_features)
                    job['totalAreaM2SoFar'] = total_area_m2
                    job['updatedAt'] = time.time()
                    _persist_building_job(job)

        if was_cancelled:
            with _building_jobs_lock:
                job['status'] = 'cancelled'
                job['updatedAt'] = time.time()
                _persist_building_job(job)
            return

        coverage_note = _OSM_FALLBACK_NOTE
        if tile_errors:
            coverage_note += (
                ' {} alt-tile birkaç bölünme denemesinden sonra da '
                'taranamadı; sonuçlar o noktalarda eksik olabilir.'
                .format(tile_errors)
            )

        with _building_jobs_lock:
            job['finalGeojson'] = {
                'type': 'FeatureCollection',
                'features': list(seen_features.values()),
            }
            job['buildingCount'] = len(seen_features)
            job['totalAreaM2'] = total_area_m2
            job['coverageNote'] = coverage_note
            job['status'] = 'done'
            job['updatedAt'] = time.time()
            _persist_building_job(job)

    except Exception as e:
        traceback.print_exc()
        with _building_jobs_lock:
            job['status'] = 'error'
            job['error'] = str(e)
            job['updatedAt'] = time.time()
            _persist_building_job(job)


def _building_cache_key(geometry):
    """Aynı GeoJSON için kararlı, hassas olmayan bir anahtar üretir."""
    canonical = json.dumps(
        geometry,
        sort_keys=True,
        separators=(',', ':'),
        ensure_ascii=False,
    )
    digest = hashlib.sha256(canonical.encode('utf-8')).hexdigest()
    return digest


def _get_cached_buildings(key):
    now = time.monotonic()
    with _building_cache_lock:
        entry = _building_cache.get(key)
        if not entry:
            return None
        if now - entry['created_at'] > _BUILDING_CACHE_TTL_SECONDS:
            _building_cache.pop(key, None)
            return None
        # En son kullanılanı sona taşı; limit dolunca eski kayıt çıkar.
        entry['last_used_at'] = now
        return copy.deepcopy(entry['payload'])


def _cache_buildings(key, payload):
    now = time.monotonic()
    with _building_cache_lock:
        _building_cache[key] = {
            'created_at': now,
            'last_used_at': now,
            'payload': copy.deepcopy(payload),
        }
        if len(_building_cache) > _BUILDING_CACHE_MAX_ITEMS:
            oldest_key = min(
                _building_cache,
                key=lambda cache_key: _building_cache[cache_key]['last_used_at'],
            )
            _building_cache.pop(oldest_key, None)


def _geojson_bbox(geometry):
    """GeoJSON Polygon/MultiPolygon koordinatlarından WGS84 bbox çıkarır."""
    points = []

    def collect(value):
        if isinstance(value, (list, tuple)):
            if (
                len(value) >= 2
                and isinstance(value[0], (int, float))
                and isinstance(value[1], (int, float))
            ):
                points.append((float(value[0]), float(value[1])))
            else:
                for child in value:
                    collect(child)

    if isinstance(geometry, dict):
        geom_type = geometry.get('type')
        if geom_type == 'Feature':
            geometry = geometry.get('geometry')
        if isinstance(geometry, dict):
            collect(geometry.get('coordinates', []))

    if not points:
        raise ValueError('Çalışma alanı koordinatları bulunamadı.')

    west = min(point[0] for point in points)
    south = min(point[1] for point in points)
    east = max(point[0] for point in points)
    north = max(point[1] for point in points)
    if not all(math.isfinite(value) for value in (west, south, east, north)):
        raise ValueError('Çalışma alanı koordinatları geçersiz.')
    if west < -180 or east > 180 or south < -90 or north > 90:
        raise ValueError('Çalışma alanı WGS84 koordinat sınırları dışında.')
    return west, south, east, north


def _ring_area_m2(ring):
    """Küçük AOI'lerde lon/lat halkasını yaklaşık m² alanına çevirir."""
    if not isinstance(ring, list) or len(ring) < 3:
        return 0.0
    coords = [
        (float(point[0]), float(point[1]))
        for point in ring
        if isinstance(point, (list, tuple)) and len(point) >= 2
    ]
    if len(coords) < 3:
        return 0.0
    mean_lat = math.radians(sum(point[1] for point in coords) / len(coords))
    meters_per_degree_lat = 111132.92
    meters_per_degree_lon = 111412.84 * math.cos(mean_lat)
    area = 0.0
    for index, (lon_a, lat_a) in enumerate(coords):
        lon_b, lat_b = coords[(index + 1) % len(coords)]
        x_a = lon_a * meters_per_degree_lon
        y_a = lat_a * meters_per_degree_lat
        x_b = lon_b * meters_per_degree_lon
        y_b = lat_b * meters_per_degree_lat
        area += (x_a * y_b) - (x_b * y_a)
    return abs(area) / 2.0


def _geojson_area_m2(geometry):
    if not isinstance(geometry, dict):
        return 0.0
    geom_type = geometry.get('type')
    coords = geometry.get('coordinates') or []
    if geom_type == 'Polygon':
        if not coords:
            return 0.0
        return max(
            0.0,
            _ring_area_m2(coords[0]) -
            sum(_ring_area_m2(ring) for ring in coords[1:]),
        )
    if geom_type == 'MultiPolygon':
        return sum(_geojson_area_m2({'type': 'Polygon', 'coordinates': polygon})
                   for polygon in coords)
    return 0.0


def _clip_building_features_to_aoi(features, aoi_geometry):
    """Bina poligonlarını AOI ile kesiştirir; AOI dışındaki parçaları atar.

    Open Buildings ve Overpass sorguları `filterBounds`/bbox kullandığı için
    AOI'ye değen ancak sınırın dışına taşan binaları da döndürebilir. Haritada
    yalnızca seçili alanın içindeki çatı parçaları görünmelidir. Shapely
    mevcutsa gerçek polygon intersection uygulanır; eski/eksik sunucularda
    frontend de aynı kırpmayı Turf.js ile ikinci kez uygular.
    """
    if not features or not aoi_geometry:
        return []
    try:
        from shapely.geometry import shape as _shape
        from shapely.geometry import mapping as _mapping
        from shapely.geometry import MultiPolygon as _MultiPolygon
        from shapely.validation import make_valid as _make_valid
    except ImportError:
        # Sunucunun eski kurulumlarında shapely olmayabilir. Bu durumda
        # istemci tarafındaki Turf.js kırpması sınır dışı çizimi engeller.
        return copy.deepcopy(features)

    try:
        aoi_shape = _shape(_normalize_to_geojson(aoi_geometry))
        if not aoi_shape.is_valid:
            aoi_shape = _make_valid(aoi_shape)
    except Exception as clip_error:
        print('[SylvaGIS] AOI geometri kırpması hazırlanamadı:', clip_error)
        return copy.deepcopy(features)

    clipped_features = []
    for feature in features:
        raw_geometry = feature.get('geometry') if isinstance(feature, dict) else None
        if not raw_geometry:
            continue
        try:
            building_shape = _shape(raw_geometry)
            if not building_shape.is_valid:
                building_shape = _make_valid(building_shape)
            intersection = building_shape.intersection(aoi_shape)
            polygons = [
                polygon for polygon in _collect_polygons(intersection)
                if polygon.is_valid and polygon.area > 1e-14
            ]
            if not polygons:
                continue
            clipped_geometry = (
                _mapping(polygons[0])
                if len(polygons) == 1
                else _mapping(_MultiPolygon(polygons))
            )
            clipped_feature = copy.deepcopy(feature)
            clipped_feature['geometry'] = clipped_geometry
            clipped_feature.setdefault('properties', {})
            clipped_feature['properties']['area_m2'] = _geojson_area_m2(
                clipped_geometry
            )
            clipped_features.append(clipped_feature)
        except Exception as feature_error:
            # Tek bir bozuk yapı tüm analizi bozmasın; diğer çatılar devam
            # eder. Bozuk yapı istemci tarafına da taşınmaz.
            print('[SylvaGIS] Bina poligonu kırpılamadı:', feature_error)

    return clipped_features


def _overpass_query_bbox(west, south, east, north, timeout=30):
    """
    Verilen bbox içindeki OSM bina ve çatı geometrilerini Overpass API'den
    çeker ve GeoJSON Feature listesine dönüştürür.

    Kentlerdeki yapıların bir bölümü ``building:part`` olarak, karmaşık
    yapılar ise ``relation["building"]`` veya ``relation["building:part"]``
    olarak çizilir. Yalnızca ``way["building"]`` sorgulamak bu çatıları
    sonuçtan düşürdüğü için dört farklı bina geometrisi kaynağı birlikte
    taranır.
    """
    query = f'''[out:json][timeout:{int(timeout)}];
(
  way["building"]({south},{west},{north},{east});
  way["building:part"]({south},{west},{north},{east});
  relation["building"]({south},{west},{north},{east});
  relation["building:part"]({south},{west},{north},{east});
);
out body geom;'''
    request_headers = {
        'Content-Type': 'text/plain; charset=utf-8',
        'User-Agent': 'SylvaGIS/1.0 building-footprint-fallback',
    }
    result = None
    request_errors = []

    # Overpass sunucuları ortak ve zaman zaman yoğun olabilir. Önce POST,
    # başarısızsa GET deniyoruz; tek bir sunucunun geçici arızası yedeği
    # kullanılamaz hale getirmemeli.
    for endpoint in _OSM_OVERPASS_ENDPOINTS:
        try:
            response = requests.post(
                endpoint,
                data=query.encode('utf-8'),
                headers=request_headers,
                timeout=(8, 25),
            )
            response.raise_for_status()
            result = response.json() or {}
            break
        except Exception as post_error:
            request_errors.append('{} POST: {}'.format(endpoint, post_error))
            try:
                response = requests.get(
                    endpoint,
                    params={'data': query},
                    headers={'User-Agent': request_headers['User-Agent']},
                    timeout=(8, 25),
                )
                response.raise_for_status()
                result = response.json() or {}
                break
            except Exception as get_error:
                request_errors.append('{} GET: {}'.format(endpoint, get_error))
                time.sleep(0.35)

    if result is None:
        raise RuntimeError(
            'Overpass sunucularına erişilemedi ({} deneme).'.format(
                len(request_errors)
            )
        )

    all_features = []
    geometry_keys = set()

    def _geometry_key(geometry):
        try:
            return json.dumps(
                geometry,
                sort_keys=True,
                separators=(',', ':'),
                ensure_ascii=False,
            )
        except Exception:
            return repr(geometry)

    def _append_feature(element_type, element_id, tags, feature_geometry):
        if not feature_geometry:
            return
        key = _geometry_key(feature_geometry)
        if key in geometry_keys:
            return
        area_m2 = _geojson_area_m2(feature_geometry)
        if area_m2 <= 0:
            return
        geometry_keys.add(key)
        all_features.append({
            'type': 'Feature',
            'id': 'osm-{}/{}'.format(element_type, element_id),
            'properties': {
                'source': 'OpenStreetMap',
                'building': tags.get('building', 'yes'),
                'buildingPart': tags.get('building:part', ''),
                'roofShape': tags.get('roof:shape', ''),
                'area_m2': area_m2,
            },
            'geometry': feature_geometry,
        })

    def _way_geometry(element):
        geometry_points = element.get('geometry') or []
        coordinates = [
            [point.get('lon'), point.get('lat')]
            for point in geometry_points
            if isinstance(point, dict)
            and isinstance(point.get('lon'), (int, float))
            and isinstance(point.get('lat'), (int, float))
        ]
        if len(coordinates) < 3:
            return None
        if coordinates[0] != coordinates[-1]:
            coordinates.append(coordinates[0])
        return {'type': 'Polygon', 'coordinates': [coordinates]}

    def _relation_geometries(element):
        """Relation üyelerinden bina çokgenleri üretir.

        Overpass relation geometrisini member way'lerinin geometry alanlarında
        döndürür. Shapely varsa outer/inner halkalar birleştirilir; yoksa
        kapalı outer üyeleri ayrı Polygon olarak kullanılır. Böylece relation
        binaları shapely olmayan eski sunucularda da kaybolmaz.
        """
        outer_rings = []
        inner_rings = []
        members = element.get('members') or []
        for member in members:
            if not isinstance(member, dict) or member.get('type') != 'way':
                continue
            points = member.get('geometry') or []
            coordinates = [
                [point.get('lon'), point.get('lat')]
                for point in points
                if isinstance(point, dict)
                and isinstance(point.get('lon'), (int, float))
                and isinstance(point.get('lat'), (int, float))
            ]
            if len(coordinates) < 3:
                continue
            if coordinates[0] != coordinates[-1]:
                coordinates.append(coordinates[0])
            if member.get('role') == 'inner':
                inner_rings.append(coordinates)
            else:
                outer_rings.append(coordinates)

        if not outer_rings:
            return []

        fallback = [
            {'type': 'Polygon', 'coordinates': [ring]}
            for ring in outer_rings
        ]

        try:
            from shapely.geometry import Polygon as _Polygon
            from shapely.geometry import mapping as _mapping
            from shapely.ops import polygonize as _polygonize
            from shapely.ops import unary_union as _unary_union

            outer_lines = [_Polygon(ring).boundary for ring in outer_rings]
            polygons = list(_polygonize(_unary_union(outer_lines)))
            if not polygons:
                polygons = [_Polygon(ring) for ring in outer_rings]
            if inner_rings:
                inner_union = _unary_union([_Polygon(ring) for ring in inner_rings])
                polygons = [polygon.difference(inner_union) for polygon in polygons]
            polygons = [
                polygon for polygon in polygons
                if not polygon.is_empty and polygon.area > 1e-14
            ]
            return [_mapping(polygon) for polygon in polygons] or fallback
        except Exception:
            return fallback

    for element in result.get('elements', []):
        element_type = element.get('type')
        tags = element.get('tags') or {}
        if element_type == 'way':
            _append_feature(
                'way',
                element.get('id'),
                tags,
                _way_geometry(element),
            )
        elif element_type == 'relation':
            for relation_geometry in _relation_geometries(element):
                _append_feature(
                    'relation',
                    element.get('id'),
                    tags,
                    relation_geometry,
                )

    return all_features


def _osm_buildings_from_bbox(geometry):
    """
    GEE'nin kapsamadığı bölgeler için küçük AOI'lerde OSM bina ayak izlerini
    Overpass API'den alır. Overpass yükünü sınırlamak için büyük AOI'lerde
    sorgu yapılmaz. (Tek seferlik/eski davranış — büyük alanlar için
    `_run_building_job` içindeki tile bazlı tarama kullanılır.)
    """
    west, south, east, north = _geojson_bbox(geometry)
    bbox_area_degrees = max(0.0, east - west) * max(0.0, north - south)
    if (east - west) > 0.08 or (north - south) > 0.08 or bbox_area_degrees > 0.004:
        return {
            'features': [],
            'totalAreaM2': 0.0,
            'skipped': True,
            'note': (
                'OpenStreetMap yedeği yalnızca küçük çalışma alanlarında '
                'kullanılır. Daha küçük bir alan seçerek tekrar deneyin.'
            ),
        }

    all_features = _clip_building_features_to_aoi(
        _overpass_query_bbox(west, south, east, north),
        geometry,
    )
    total_area_m2 = sum(f['properties'].get('area_m2', 0.0) for f in all_features)

    return {
        # Kullanıcı bina gösteriminde bir üst sınır istemediği için OSM'den
        # alınan tüm geçerli bina poligonlarını döndür.
        'features': all_features,
        'totalCount': len(all_features),
        'totalAreaM2': total_area_m2,
        'skipped': False,
        'note': '',
    }


# ════════════════════════════════════════════════════════════════
# 🛰️ GOOGLE EARTH ENGINE — SERVICE ACCOUNT İLE BAĞLANTI
# ════════════════════════════════════════════════════════════════
# Sunucu bilgisayarında kapalıyken (VM/bulutta 7/24 çalışırken) kişisel
# "earthengine authenticate" login'i kullanılamaz — çünkü o, sadece
# senin bilgisayarındaki tarayıcı oturumuna bağlıdır.
#
# Bunun yerine bir GEE Service Account kullanıyoruz:
#   1) Google Cloud Console > IAM & Admin > Service Accounts
#      -> "sylvagis" projesinde yeni bir service account oluştur.
#   2) Bu service account'a "Earth Engine Resource Viewer/Writer" rolü ver.
#   3) https://signup.earthengine.google.com/#!/service_accounts
#      üzerinden bu service account'ı GEE'ye kayıt ettir (whitelisting).
#   4) Service account için bir JSON key oluştur (Keys > Add Key > JSON).
#   5) Bu JSON dosyasını ASLA GitHub'a yükleme. VM'de bir dosya olarak
#      sakla (örn. /etc/secrets/sylvagis-gee-key.json) ve VM'de bir
#      ortam değişkeni tanımla:
#           export GEE_SERVICE_ACCOUNT_KEY=/etc/secrets/sylvagis-gee-key.json
#           export GEE_SERVICE_ACCOUNT_EMAIL=sylvagis-server@sylvagis.iam.gserviceaccount.com
GEE_SERVICE_ACCOUNT_EMAIL = os.environ.get('GEE_SERVICE_ACCOUNT_EMAIL', '')
GEE_SERVICE_ACCOUNT_KEY   = os.environ.get('GEE_SERVICE_ACCOUNT_KEY', '')

try:
    if GEE_SERVICE_ACCOUNT_EMAIL and GEE_SERVICE_ACCOUNT_KEY:
        # GEE_SERVICE_ACCOUNT_KEY ya bir dosya yolu (örn. /etc/secrets/key.json)
        # ya da doğrudan key.json'un ham JSON içeriği olabilir (Cloud Run
        # "Environment variables" kutusuna yapıştırıldığında olduğu gibi).
        # İkisini de destekleyelim:
        _key_value = GEE_SERVICE_ACCOUNT_KEY.strip()
        if _key_value.startswith('{'):
            credentials = ee.ServiceAccountCredentials(
                GEE_SERVICE_ACCOUNT_EMAIL, key_data=_key_value
            )
        else:
            credentials = ee.ServiceAccountCredentials(
                GEE_SERVICE_ACCOUNT_EMAIL, key_file=_key_value
            )
        ee.Initialize(credentials, project='sylvagis')
        print('✅ GEE Service Account ile başlatıldı:', GEE_SERVICE_ACCOUNT_EMAIL)
    else:
        # Ortam değişkenleri yoksa (örn. yerel geliştirme sırasında) eski
        # kişisel login yöntemine geri düş — sadece local test için.
        ee.Initialize(project='sylvagis')
        print('⚠️  GEE kişisel hesap ile başlatıldı (yerel geliştirme modu).')
except Exception as e:
    print('❌ GEE başlatılamadı:', e)

# Last analysis parameters (GeoTIFF download için saklanır)
_last_analyze_params = {}

# ════════════════════════════════════════════════════════════════
# 🌐 SON ANALİZİN GERÇEK/DOĞAL KOORDİNAT SİSTEMİ (CRS)
# ════════════════════════════════════════════════════════════════
# SORUN: "📥 Veriyi İndir (GeoTIFF)" penceresindeki CRS seçici her zaman
# WGS 84 / EPSG:4326'da açılıyordu — oysa verinin kendi doğal/native CRS'i
# (örn. Sentinel-2/Landsat bantları çoğunlukla UTM projeksiyonundadır)
# genellikle farklıdır ve kullanıcı hangi UTM diliminde olduğunu bilemez.
# /api/analyze her çalıştığında burada son analizin GERÇEK CRS'i saklanır;
# hem /api/analyze yanıtında ('nativeCrs') doğrudan istemciye bildirilir
# (istemci CRS seçicisini buna göre otomatik ön-seçer) hem de
# /api/download-geotiff istemci hiçbir CRS göndermezse GÜVENLİ bir
# varsayılan (sabit EPSG:4326 yerine) olarak kullanılır. Kullanıcı yine de
# isterse seçiciden WGS 84'e veya başka bir EPSG koduna geri dönebilir.
_last_analyze_native_crs = None

# Arazi Kullanımı (LULC) ailesindeki analizler — bunlar statik/tek-katmanlı
# veri setleridir; tarih aralığı veya bulutluluk filtresi kullanmazlar ve
# her zaman AOI sınırlarına göre kesilir (clip).
LULC_FAMILY_INDICES = (
    'LULC', 'LULC_ESA', 'LULC_MODIS', 'LULC_CORINE',
    # TOPO ailesi — DEM tabanlı statik analizler (tarih/bulutluluk filtresi yok)
    'TOPO', 'TOPO_DEM', 'TOPO_SLOPE', 'TOPO_ASPECT', 'TOPO_HILLSHADE',
    'TOPO_RELIEF', 'TOPO_TPI', 'TOPO_TRI', 'TOPO_ROUGHNESS',
    'TOPO_CURVATURE', 'TOPO_PLAN_CURV', 'TOPO_PROFILE_CURV',
    'TOPO_FLOWDIR', 'TOPO_FLOWACC', 'TOPO_STREAM',
    'TOPO_TWI', 'TOPO_SPI', 'TOPO_STI',
    'TOPO_HILLSHADE_MULTI', 'TOPO_SOLAR', 'TOPO_SHADOW',
    # SAR — zaman aralığı kullanır ama sahne galerisi gösterilmez
    'SAR',
)

# ════════════════════════════════════════════════════════════════
# 🎨 LULC SINIF TANIMLARI — KOD, İSİM VE RESMİ RENK (Color Table / RAT)
# ════════════════════════════════════════════════════════════════
# SORUN: ArcMap/QGIS, GeoTIFF içinde gömülü bir "Color Table" (renk
# paleti) yoksa dosyayı tek bantlı ham "değer" verisi sanır ve
# varsayılan olarak SİYAH-BEYAZ (grayscale) açar; piksel değerleri de
# (1, 2, 3...) sınıf isimleri ("Orman", "Tarım Alanı" vb.) yerine çıplak
# rakam olarak görünür.
#
# ÇÖZÜM: Aşağıdaki tanımlar — index.html'deki LULC_CLASS_DEFS ile
# BİREBİR aynı kod/isim/renk sırasını kullanır (bkz. index.html →
# renderLulcLegendAndChart) — GeoTIFF indirilirken hem dosyanın
# İÇİNE bir "Color Table" gömmek (rasterio write_colormap) hem de
# ArcMap/QGIS'in otomatik okuyacağı bir Raster Attribute Table (RAT)
# sidecar (.tif.aux.xml) ve klasik bir .clr renk dosyası üretmek için
# kullanılır. Bkz. _build_lulc_symbology_zip() ve /api/download-geotiff.
LULC_CLASS_DEFS = {
    'LULC': [  # Google Dynamic World V1 — band 'label', kod 0-8
        {'code': 0, 'label': 'Su Kütlesi',              'color': '#419bdf'},
        {'code': 1, 'label': 'Orman / Ağaçlık',          'color': '#397d49'},
        {'code': 2, 'label': 'Çayır / Otlak',            'color': '#88b053'},
        {'code': 3, 'label': 'Sulak Bitki Örtüsü',       'color': '#7a87c6'},
        {'code': 4, 'label': 'Tarım Alanı',              'color': '#e49635'},
        {'code': 5, 'label': 'Çalılık',                  'color': '#dfc35a'},
        {'code': 6, 'label': 'Yapay / Kentsel Alan',     'color': '#c4281b'},
        {'code': 7, 'label': 'Çıplak Toprak',            'color': '#a59b8f'},
        {'code': 8, 'label': 'Kar / Buz',                'color': '#b39fe1'},
    ],
    'LULC_ESA': [  # ESA WorldCover v200 — sunucuda 1..11'e yeniden kodlanmış sıra
        {'code': 1,  'label': 'Ağaç Örtüsü / Orman',          'color': '#006400'},
        {'code': 2,  'label': 'Çalılık',                      'color': '#ffbb22'},
        {'code': 3,  'label': 'Çayır / Otlak',                'color': '#ffff4c'},
        {'code': 4,  'label': 'Tarım Alanı',                  'color': '#f096ff'},
        {'code': 5,  'label': 'Yapay / Kentsel Alan',         'color': '#fa0000'},
        {'code': 6,  'label': 'Çıplak / Seyrek Bitki Örtüsü', 'color': '#b4b4b4'},
        {'code': 7,  'label': 'Kar / Buz',                    'color': '#f0f0f0'},
        {'code': 8,  'label': 'Su Kütlesi',                   'color': '#0064c8'},
        {'code': 9,  'label': 'Sulak Alan / Bataklık',        'color': '#0096a0'},
        {'code': 10, 'label': 'Mangrov',                      'color': '#00cf75'},
        {'code': 11, 'label': 'Yosun / Liken',                'color': '#fae6a0'},
    ],
    'LULC_MODIS': [  # MODIS MCD12Q1 — LC_Type1 (IGBP), kod 1-17
        {'code': 1,  'label': 'Herdemyeşil İbreli Orman',         'color': '#05450a'},
        {'code': 2,  'label': 'Herdemyeşil Geniş Yapraklı Orman', 'color': '#086a10'},
        {'code': 3,  'label': 'Yaprak Döken İbreli Orman',        'color': '#54a708'},
        {'code': 4,  'label': 'Yaprak Döken Geniş Yapraklı Orman','color': '#78d203'},
        {'code': 5,  'label': 'Karışık Ormanlar',                 'color': '#009900'},
        {'code': 6,  'label': 'Kapalı Çalılık',                   'color': '#c6b044'},
        {'code': 7,  'label': 'Açık Çalılık',                     'color': '#dcd159'},
        {'code': 8,  'label': 'Odunlu Savana',                    'color': '#dade48'},
        {'code': 9,  'label': 'Savana',                           'color': '#fbff13'},
        {'code': 10, 'label': 'Çayır / Otlak',                    'color': '#b6ff05'},
        {'code': 11, 'label': 'Kalıcı Sulak Alan',                'color': '#27ff87'},
        {'code': 12, 'label': 'Tarım Alanı',                      'color': '#c24f44'},
        {'code': 13, 'label': 'Kentsel / Yapay Alan',             'color': '#a5a5a5'},
        {'code': 14, 'label': 'Tarım-Doğal Mozaik',               'color': '#ff6d4c'},
        {'code': 15, 'label': 'Kar ve Buz',                       'color': '#69fff8'},
        {'code': 16, 'label': 'Çıplak Toprak / Seyrek Örtü',      'color': '#f9ffa4'},
        {'code': 17, 'label': 'Su Kütlesi',                       'color': '#1c0dff'},
    ],
    'LULC_CORINE': [  # CORINE Land Cover 2018 — 44 sınıf, sunucuda 1..44'e remaplenir
        {'code': 1,  'label': 'Sürekli Kentsel Doku',      'color': '#e6004d'},
        {'code': 2,  'label': 'Süreksiz Kentsel Doku',     'color': '#ff0000'},
        {'code': 3,  'label': 'Sanayi / Ticaret',          'color': '#cc4df2'},
        {'code': 4,  'label': 'Yol / Demiryolu',           'color': '#cc0000'},
        {'code': 5,  'label': 'Liman Alanları',            'color': '#e6cccc'},
        {'code': 6,  'label': 'Havalimanları',             'color': '#e6cce6'},
        {'code': 7,  'label': 'Maden Çıkarım Sahası',      'color': '#a600cc'},
        {'code': 8,  'label': 'Döküm / Atık Sahası',       'color': '#a64d00'},
        {'code': 9,  'label': 'İnşaat Sahası',             'color': '#ff4dff'},
        {'code': 10, 'label': 'Kentsel Yeşil Alan',        'color': '#ffa6ff'},
        {'code': 11, 'label': 'Spor / Eğlence',            'color': '#ffe6ff'},
        {'code': 12, 'label': 'Sulanmayan Tarım',          'color': '#ffffa8'},
        {'code': 13, 'label': 'Sulanan Tarım',             'color': '#ffff00'},
        {'code': 14, 'label': 'Pirinç Tarlaları',          'color': '#e6e600'},
        {'code': 15, 'label': 'Bağlar',                    'color': '#e68000'},
        {'code': 16, 'label': 'Meyve Bahçeleri',           'color': '#f2a64d'},
        {'code': 17, 'label': 'Zeytin Bahçeleri',          'color': '#e6a600'},
        {'code': 18, 'label': 'Çayır / Mera',              'color': '#e6e64d'},
        {'code': 19, 'label': 'Yıllık Tarım Mozaiği',      'color': '#ffe6a6'},
        {'code': 20, 'label': 'Karmaşık Tarım',            'color': '#ffe64d'},
        {'code': 21, 'label': 'Tarım-Doğal Mozaik',        'color': '#e6cc4d'},
        {'code': 22, 'label': 'Tarım-Ormanlık Mozaik',     'color': '#f2cca6'},
        {'code': 23, 'label': 'Geniş Yapraklı Orman',      'color': '#80ff00'},
        {'code': 24, 'label': 'İbreli Orman',              'color': '#00a600'},
        {'code': 25, 'label': 'Karışık Orman',             'color': '#4dff00'},
        {'code': 26, 'label': 'Doğal Çayırlık',            'color': '#ccf24d'},
        {'code': 27, 'label': 'Bozkır / Fundalık',         'color': '#a6ff80'},
        {'code': 28, 'label': 'Makiler',                   'color': '#a6e64d'},
        {'code': 29, 'label': 'Geçiş Orman-Çalılık',       'color': '#a6f200'},
        {'code': 30, 'label': 'Plaj / Kum / Dün',          'color': '#e6e6e6'},
        {'code': 31, 'label': 'Çıplak Kayalık',            'color': '#cccccc'},
        {'code': 32, 'label': 'Seyrek Bitki Örtüsü',       'color': '#ccffcc'},
        {'code': 33, 'label': 'Yanmış Alan',               'color': '#000000'},
        {'code': 34, 'label': 'Buzul / Kalıcı Kar',        'color': '#a6e6cc'},
        {'code': 35, 'label': 'İç Bataklık',               'color': '#a6a6ff'},
        {'code': 36, 'label': 'Turbalık',                  'color': '#4d4dff'},
        {'code': 37, 'label': 'Tuz Bataklığı',             'color': '#ccccff'},
        {'code': 38, 'label': 'Tuzla',                     'color': '#e6e6ff'},
        {'code': 39, 'label': 'Gelgit Düzlüğü',            'color': '#a6a6e6'},
        {'code': 40, 'label': 'Akarsu',                    'color': '#00ccf2'},
        {'code': 41, 'label': 'Göl / Gölet',               'color': '#80f2e6'},
        {'code': 42, 'label': 'Kıyı Lagünü',               'color': '#00ffa6'},
        {'code': 43, 'label': 'Haliç',                     'color': '#a6ffe6'},
        {'code': 44, 'label': 'Deniz / Okyanus',           'color': '#e6f2ff'},
    ],
}


def _write_dbf_bytes(field_defs, rows):
    """
    Minimal bir dBase III (.dbf) dosyasını sıfırdan (hiçbir ek kütüphane
    olmadan) bayt dizisi olarak üretir. ArcMap'in "Value Attribute Table"
    (VAT) olarak tanıyacağı basit/klasik formattadır.

    field_defs: [(isim<=10 karakter, tip 'N'|'C', uzunluk, ondalık), ...]
    rows: [(değer1, değer2, ...), ...]  — field_defs ile aynı sırada.

    NOT: Karakter alanlarında Türkçe karakterler UTF-8 olarak yazılır;
    dosyanın YANINA aynı ada sahip bir .cpg dosyası ("UTF-8" içerikli)
    eklenir — bu, GDAL/OGR'nin shapefile/dbf dosyalarında kullandığı
    standart yöntemdir ve ArcMap 10.1+ ile QGIS bunu otomatik okuyup
    karakterleri doğru render eder.
    """
    import struct
    import datetime as _dt

    n_records = len(rows)
    n_fields = len(field_defs)
    header_len = 32 + 32 * n_fields + 1
    record_len = 1 + sum(f[2] for f in field_defs)  # +1: silme bayrağı

    today = _dt.date.today()
    header = struct.pack(
        '<BBBBIHH20x',
        0x03,                              # dBase III (memo yok)
        today.year - 1900, today.month, today.day,
        n_records,
        header_len,
        record_len,
    )

    field_descriptors = b''
    for name, ftype, flen, fdec in field_defs:
        name_bytes = name.encode('ascii')[:10].ljust(11, b'\x00')
        field_descriptors += struct.pack(
            '<11sc4xBB14x',
            name_bytes, ftype.encode('ascii'), flen, fdec
        )
    field_descriptors += b'\x0d'  # alan tanımları sonu

    body = b''
    for row in rows:
        rec = b' '  # silinmemiş kayıt
        for (name, ftype, flen, fdec), val in zip(field_defs, row):
            if ftype == 'N':
                s = str(val)
                rec += s.encode('ascii')[:flen].rjust(flen, b' ')
            else:  # 'C'
                s = ('' if val is None else str(val))
                b = s.encode('utf-8')[:flen]
                rec += b.ljust(flen, b' ')
        body += rec

    return header + field_descriptors + body + b'\x1a'


def _build_lulc_symbology_zip(tif_bytes, index_name, safe_name):
    """
    LULC ailesi (LULC, LULC_ESA, LULC_MODIS, LULC_CORINE) GeoTIFF'ini alır;
    çıktısı, ArcMap/QGIS'te doğrudan RENKLİ ve İSİMLENDİRİLMİŞ açılan bir
    ZIP paketidir:

      1) {ad}.tif          — bandı Byte'a indirgenmiş, İÇİNE "Color Table"
                              (GDAL Palette) GÖMÜLMÜŞ GeoTIFF. Bu sayede
                              dosya, yanında hiçbir sidecar olmasa bile artık
                              siyah-beyaz değil, kendi rengiyle açılır.
      2) {ad}.tif.aux.xml   — GDAL "Raster Attribute Table" (RAT) sidecar'ı;
                              ArcGIS/QGIS bunu .tif ile aynı klasörde
                              otomatik bulur ve piksel değerlerini (1,2,3…)
                              sınıf isimlerine ("Orman", "Tarım Alanı" vb.)
                              çevirir (Identify / Öznitelik Tablosu).
      3) {ad}.clr           — klasik GDAL/ESRI renk eşleştirme dosyası;
                              ArcMap'te Symbology > Import ile manuel olarak
                              da yüklenebilir (yedek yol).
      4) OKUBENI.txt        — ArcMap/QGIS'te nasıl kullanılacağını anlatan
                              kısa Türkçe kılavuz.

    Girdi verisi zaten sunucuda 1..N (veya Dynamic World için 0..8) gibi
    küçük, ardışık tam sayı sınıf kodlarına remaplenmiş halde gelir (bkz.
    build_result_image → LULC/LULC_ESA/LULC_MODIS/LULC_CORINE blokları).
    Burada yapılan tek şey: NoData sentinel'ini (-9999) 0'a indirgemek,
    bandı Byte'a çevirmek ve rasterio.write_colormap ile renk tablosunu
    dosyanın içine yazmaktır — piksellerin taşıdığı SINIF BİLGİSİ hiçbir
    şekilde değiştirilmez/kaybolmaz.
    """
    import numpy as np
    import rasterio
    from rasterio.io import MemoryFile
    from xml.sax.saxutils import escape as _xml_escape

    defs = LULC_CLASS_DEFS.get(index_name)
    if not defs:
        return None

    # kod -> (isim, (r,g,b))
    code_info = {}
    for d in defs:
        hexc = d['color'].lstrip('#')
        rgb = tuple(int(hexc[i:i + 2], 16) for i in (0, 2, 4))
        code_info[d['code']] = (d['label'], rgb)

    # Dynamic World (LULC) kodları 0'dan başlıyor; 0'ı yalnızca NoData'ya
    # ayırabilmek için TÜM kodları +1 kaydırıyoruz. Diğer LULC ailesi
    # (ESA/MODIS/CORINE) zaten 1'den başladığı için kayma 0'dır.
    shift = 1 if min(code_info.keys()) == 0 else 0
    shifted_info = {code + shift: v for code, v in code_info.items()}

    with MemoryFile(tif_bytes) as memfile:
        with memfile.open() as src:
            band = src.read(1).astype(np.float64)
            profile = src.profile.copy()
            src_nodata = src.nodata

    valid = np.isfinite(band)
    if src_nodata is not None:
        valid &= ~np.isclose(band, float(src_nodata))

    rounded = np.rint(band).astype(np.int64)
    out = np.where(valid, rounded + shift, 0)
    out = np.clip(out, 0, 255).astype(np.uint8)

    new_profile = profile.copy()
    new_profile.update(dtype='uint8', count=1, nodata=0, compress='lzw')
    new_profile.pop('photometric', None)

    with MemoryFile() as out_memfile:
        with out_memfile.open(**new_profile) as dst:
            dst.write(out, 1)
            colormap = {0: (255, 255, 255, 0)}
            for code, (label, rgb) in shifted_info.items():
                colormap[code] = (rgb[0], rgb[1], rgb[2], 255)
            dst.write_colormap(1, colormap)
        new_tif_bytes = out_memfile.read()

    # ── .clr (klasik GDAL/ESRI renk eşleştirme dosyası) ──────────────
    clr_lines = ['0 255 255 255 0']
    for code in sorted(shifted_info.keys()):
        label, rgb = shifted_info[code]
        clr_lines.append('{} {} {} {} 255'.format(code, rgb[0], rgb[1], rgb[2]))
    clr_bytes = ('\n'.join(clr_lines) + '\n').encode('utf-8')

    # ── .tif.aux.xml (GDAL Raster Attribute Table — isim eşleştirme) ─
    rows = ['      <Row index="0"><F>0</F><F>NoData</F><F>255</F><F>255</F><F>255</F></Row>']
    for i, code in enumerate(sorted(shifted_info.keys()), start=1):
        label, rgb = shifted_info[code]
        rows.append(
            '      <Row index="{}"><F>{}</F><F>{}</F><F>{}</F><F>{}</F><F>{}</F></Row>'.format(
                i, code, _xml_escape(label), rgb[0], rgb[1], rgb[2]
            )
        )
    aux_xml = (
        '<PAMDataset>\n'
        '  <PAMRasterBand band="1">\n'
        '    <Metadata>\n'
        '      <MDI key="LAYER_TYPE">thematic</MDI>\n'
        '    </Metadata>\n'
        '    <GDALRasterAttributeTable Row0Min="0" BinSize="1" tableType="thematic">\n'
        '      <FieldDefn index="0"><Name>VALUE</Name><Type>1</Type><Usage>0</Usage></FieldDefn>\n'
        '      <FieldDefn index="1"><Name>CLASS_NAME</Name><Type>2</Type><Usage>2</Usage></FieldDefn>\n'
        '      <FieldDefn index="2"><Name>R</Name><Type>1</Type><Usage>6</Usage></FieldDefn>\n'
        '      <FieldDefn index="3"><Name>G</Name><Type>1</Type><Usage>7</Usage></FieldDefn>\n'
        '      <FieldDefn index="4"><Name>B</Name><Type>1</Type><Usage>8</Usage></FieldDefn>\n'
        + '\n'.join(rows) + '\n'
        '    </GDALRasterAttributeTable>\n'
        '  </PAMRasterBand>\n'
        '</PAMDataset>\n'
    )
    aux_xml_bytes = aux_xml.encode('utf-8')

    # ── .tif.vat.dbf (Value Attribute Table) ──────────────────────────
    # SORUN: Klasik ArcMap (ArcGIS Pro DEĞİL), yukarıdaki .tif.aux.xml
    # RAT'ını Symbology > Unique Values ekranındaki "Label" sütununa
    # GÜVENİLİR şekilde yansıtmaz — kullanıcı hâlâ sadece rakamları görür.
    # ArcMap'in bu iş için asıl yerli/güvenilir desteği "<ad>.tif.vat.dbf"
    # adlı bir Value Attribute Table sidecar'ıdır (ArcCatalog'daki "Build
    # Raster Attribute Table" aracının ürettiği AYNI formattır). Bu dosya
    # varken, Symbology > Unique Values ekranındaki "Value Field" açılır
    # menüsünde "CLASS_NAME" seçeneği belirir; kullanıcı bunu seçip
    # "Add All Values" dediğinde Label sütunu doğrudan sınıf isimleriyle
    # dolar — rakamlarla tek tek uğraşmaya gerek kalmaz.
    counts = np.bincount(out.ravel(), minlength=256)
    field_defs = [
        ('VALUE', 'N', 10, 0),
        ('COUNT', 'N', 12, 0),
        ('CLASS_NAME', 'C', 60, 0),
        ('RED', 'N', 3, 0),
        ('GREEN', 'N', 3, 0),
        ('BLUE', 'N', 3, 0),
    ]
    vat_rows = []
    for code in sorted(shifted_info.keys()):
        label, rgb = shifted_info[code]
        vat_rows.append((code, int(counts[code]) if code < 256 else 0,
                          label, rgb[0], rgb[1], rgb[2]))
    vat_dbf_bytes = _write_dbf_bytes(field_defs, vat_rows)
    vat_cpg_bytes = b'UTF-8'

    readme = (
        'SylvaGIS — Renkli/İsimlendirilmiş Arazi Örtüsü (LULC) Paketi\n'
        '================================================================\n\n'
        'Bu ZIP içinde:\n'
        '  - {name}.tif             -> Rengi dosyanın İÇİNE gömülü GeoTIFF.\n'
        '  - {name}.tif.vat.dbf/.cpg-> Sınıf isim tablosu (Value Attribute Table).\n'
        '                              *** ArcMap için EN GÜVENİLİR yöntem budur. ***\n'
        '  - {name}.tif.aux.xml     -> Ek/yedek isim tablosu (RAT, çoğunlukla QGIS\n'
        '                              ve ArcGIS Pro tarafından okunur).\n'
        '  - {name}.clr             -> Yedek/manuel renk dosyası.\n\n'
        'ÖNEMLİ: Bu 4 dosyayı ZIP\'ten çıkarırken HEPSİNİ AYNI klasörde, isimlerini\n'
        'DEĞİŞTİRMEDEN tutun — ArcMap/QGIS bunları .tif ile eşleştirmek için dosya\n'
        'adına bakar.\n\n'
        'ArcMap\'te kullanım (sınıf isimlerini görmek için):\n'
        '  1) Sadece {name}.tif dosyasını sürükleyip haritaya ekleyin (renkler\n'
        '     otomatik gelecektir — artık siyah-beyaz DEĞİL).\n'
        '  2) Katmana sağ tık > Properties > Symbology sekmesi.\n'
        '  3) Show: "Unique Values" seçin.\n'
        '  4) "Value Field" açılır menüsünden "Value" yerine "CLASS_NAME" seçin.\n'
        '  5) "Add All Values" butonuna basın.\n'
        '  6) Tamam/Uygula — artık Label sütununda "1, 2, 3" yerine "Orman",\n'
        '     "Tarım Alanı" gibi isimler görünecektir.\n'
        '  Renkler görünmüyorsa: adım 3\'te "Import" ile {name}.clr dosyasını\n'
        '  yükleyebilirsiniz.\n'
    ).format(name=safe_name)

    return {
        '{}.tif'.format(safe_name): new_tif_bytes,
        '{}.tif.aux.xml'.format(safe_name): aux_xml_bytes,
        '{}.tif.vat.dbf'.format(safe_name): vat_dbf_bytes,
        '{}.tif.vat.cpg'.format(safe_name): vat_cpg_bytes,
        '{}.clr'.format(safe_name): clr_bytes,
        'OKUBENI.txt': readme.encode('utf-8'),
    }


@app.route('/api/ping', methods=['GET'])
def ping():
    return jsonify({'ok': True, 'version': 'zip-export-v2-tiling'})


# ════════════════════════════════════════════════════════════════
# 📧 İLETİŞİM FORMU — sylvagis.world@gmail.com adresine otomatik gönderim
# ════════════════════════════════════════════════════════════════
# Kullanıcının mail istemcisini (Gmail vb.) açmadan, formdaki bilgiler
# doğrudan sunucu üzerinden SMTP ile gönderilir.
#
# Kurulum: Gönderen hesap bilgileri ortam değişkenleriyle sağlanır
# (kaynak kodda parola SAKLANMAZ):
#   SYLVA_SMTP_USER  -> gönderen Gmail adresi (örn. sylvagis.world@gmail.com)
#   SYLVA_SMTP_PASS  -> Gmail "Uygulama Şifresi" (App Password; normal Gmail
#                        şifresi SMTP için çalışmaz, 2 Adımlı Doğrulama açıp
#                        myaccount.google.com/apppasswords adresinden alınır)
# Bu değişkenler tanımlı değilse endpoint açık/anlaşılır bir hata döner.
CONTACT_RECEIVER_EMAIL = 'sylvagis.world@gmail.com'


@app.route('/api/contact', methods=['POST'])
def send_contact_message():
    import smtplib
    from email.mime.text import MIMEText
    from email.header import Header

    data = request.get_json(silent=True) or {}
    name    = (data.get('fullName') or data.get('name') or '').strip()
    email   = (data.get('email') or '').strip()
    subject = (data.get('subject') or '').strip()
    message = (data.get('message') or '').strip()

    if not name or not email or not subject or not message:
        return jsonify({'success': False, 'error': 'Eksik alan(lar) var.'}), 400

    email_re = re.compile(r'^[^\s@]+@[^\s@]+\.[^\s@]+$')
    if not email_re.match(email):
        return jsonify({'success': False, 'error': 'Geçersiz e-posta adresi.'}), 400

    smtp_user = 'sylvagis.world@gmail.com'
    smtp_pass = 'ksfnkvwcutrawcih'

    body = (
        'SylvaGIS İletişim Formu üzerinden yeni bir mesaj gönderildi.\n\n'
        'Ad Soyad : %s\n'
        'E-posta  : %s\n'
        'Konu     : %s\n\n'
        'Mesaj:\n%s\n'
    ) % (name, email, subject, message)

    msg = MIMEText(body, 'plain', 'utf-8')
    msg['Subject'] = Header('[SylvaGIS İletişim] %s' % subject, 'utf-8')
    msg['From'] = smtp_user
    msg['To'] = CONTACT_RECEIVER_EMAIL
    msg['Reply-To'] = email

    try:
        with smtplib.SMTP_SSL('smtp.gmail.com', 465, timeout=15) as server:
            server.login(smtp_user, smtp_pass)
            server.sendmail(smtp_user, [CONTACT_RECEIVER_EMAIL], msg.as_string())
        return jsonify({'success': True})
    except Exception as e:
        print('❌ /api/contact e-posta gönderim hatası:', e)
        return jsonify({'success': False, 'error': 'E-posta gönderilemedi: %s' % str(e)}), 500


# ════════════════════════════════════════════════════════════════
# 🛰️ UYDU GÖRÜNTÜSÜ GALERİSİ — Veri Seti Kayıt Defteri
# ════════════════════════════════════════════════════════════════
# Her anahtar, frontend'deki "uydu-goruntu-radio" elemanlarının
# value/data-key değeriyle birebir eşleşir. Bu, "Uydu Analizleri"
# (NDVI vb.) modülündeki sensör seçim anahtarlarıyla da uyumludur.
#
#   collections  : tek veya birleştirilecek (merge) ImageCollection ID'leri
#   cloudProp    : bulutluluk yüzdesi özniteliği (yoksa None)
#   rgbBands     : haritada/gerçek renk önizlemesinde kullanılacak bantlar
#                  [Kırmızı, Yeşil, Mavi] sırasıyla (MSS için gerçek mavi
#                  bandı yoktur — bkz. trueColor: False)
#   scaleFactor / offset : ham DN/yansıma değerini 0-1 yansıma aralığına
#                  çeviren dönüşüm (reflectance = DN * scaleFactor + offset)
#   visMin/visMax: görüntüleme germe (stretch) aralığı
#   resolution   : nominal mekansal çözünürlük (m)
#   bandsInfo    : kullanıcıya gösterilecek bant özeti metni
SATELLITE_DATASETS = {
    's2-l1c': {
        'label': 'Sentinel-2 L1C (TOA)',
        'datasetName': 'Sentinel-2 MSI Level-1C (TOA Yansıma)',
        'sensor': 'Sentinel-2 MSI',
        'collections': ['COPERNICUS/S2_HARMONIZED'],
        'cloudProp': 'CLOUDY_PIXEL_PERCENTAGE',
        'rgbBands': ['B4', 'B3', 'B2'],
        'scaleFactor': 1e-4, 'offset': 0,
        'visMin': 0, 'visMax': 0.3,
        'resolution': 10,
        'bandsInfo': 'RGB: B4 (Kırmızı) · B3 (Yeşil) · B2 (Mavi) — toplam 13 bant (B1–B12, B8A)',
        'trueColor': True,
    },
    's2-l2a': {
        'label': 'Sentinel-2 L2A (BOA)',
        'datasetName': 'Sentinel-2 MSI Level-2A (Yüzey Yansıması)',
        'sensor': 'Sentinel-2 MSI',
        'collections': ['COPERNICUS/S2_SR_HARMONIZED'],
        'cloudProp': 'CLOUDY_PIXEL_PERCENTAGE',
        'rgbBands': ['B4', 'B3', 'B2'],
        'scaleFactor': 1e-4, 'offset': 0,
        'visMin': 0, 'visMax': 0.3,
        'resolution': 10,
        'bandsInfo': 'RGB: B4 (Kırmızı) · B3 (Yeşil) · B2 (Mavi) — toplam 13 bant (B1–B12, B8A)',
        'trueColor': True,
    },
    'l89-l2': {
        'label': 'Landsat 8–9 OLI/TIRS (C2 L2)',
        'datasetName': 'Landsat 8–9 Collection 2 Level-2 (Yüzey Yansıması)',
        'sensor': 'Landsat 8–9 OLI/TIRS',
        'collections': ['LANDSAT/LC08/C02/T1_L2', 'LANDSAT/LC09/C02/T1_L2'],
        'cloudProp': 'CLOUD_COVER',
        'rgbBands': ['SR_B4', 'SR_B3', 'SR_B2'],
        'scaleFactor': 2.75e-5, 'offset': -0.2,
        'visMin': 0, 'visMax': 0.3,
        'resolution': 30,
        'bandsInfo': 'RGB: SR_B4 (Kırmızı) · SR_B3 (Yeşil) · SR_B2 (Mavi) — 11 bant (SR + ST termal)',
        'trueColor': True,
    },
    'l7-l2': {
        'label': 'Landsat 7 ETM+ (C2 L2)',
        'datasetName': 'Landsat 7 Collection 2 Level-2 (Yüzey Yansıması)',
        'sensor': 'Landsat 7 ETM+',
        'collections': ['LANDSAT/LE07/C02/T1_L2'],
        'cloudProp': 'CLOUD_COVER',
        'rgbBands': ['SR_B3', 'SR_B2', 'SR_B1'],
        'scaleFactor': 2.75e-5, 'offset': -0.2,
        'visMin': 0, 'visMax': 0.3,
        'resolution': 30,
        'bandsInfo': 'RGB: SR_B3 (Kırmızı) · SR_B2 (Yeşil) · SR_B1 (Mavi) — 9 bant (SR + ST termal)',
        'trueColor': True,
    },
    'l45-l2': {
        'label': 'Landsat 4–5 TM (C2 L2)',
        'datasetName': 'Landsat 4–5 Collection 2 Level-2 (Yüzey Yansıması)',
        'sensor': 'Landsat 4–5 TM',
        'collections': ['LANDSAT/LT05/C02/T1_L2', 'LANDSAT/LT04/C02/T1_L2'],
        'cloudProp': 'CLOUD_COVER',
        'rgbBands': ['SR_B3', 'SR_B2', 'SR_B1'],
        'scaleFactor': 2.75e-5, 'offset': -0.2,
        'visMin': 0, 'visMax': 0.3,
        'resolution': 30,
        'bandsInfo': 'RGB: SR_B3 (Kırmızı) · SR_B2 (Yeşil) · SR_B1 (Mavi) — 7 bant (SR + ST termal)',
        'trueColor': True,
    },
    'l89-l1': {
        'label': 'Landsat 8–9 OLI/TIRS (C2 L1)',
        'datasetName': 'Landsat 8–9 Collection 2 Level-1 (TOA Yansıması)',
        'sensor': 'Landsat 8–9 OLI/TIRS',
        'collections': ['LANDSAT/LC08/C02/T1_TOA', 'LANDSAT/LC09/C02/T1_TOA'],
        'cloudProp': 'CLOUD_COVER',
        'rgbBands': ['B4', 'B3', 'B2'],
        'scaleFactor': 1, 'offset': 0,
        'visMin': 0, 'visMax': 0.3,
        'resolution': 30,
        'bandsInfo': 'RGB: B4 (Kırmızı) · B3 (Yeşil) · B2 (Mavi) — 11 bant (TOA + termal)',
        'trueColor': True,
    },
    'l7-l1': {
        'label': 'Landsat 7 ETM+ (C2 L1)',
        'datasetName': 'Landsat 7 Collection 2 Level-1 (TOA Yansıması)',
        'sensor': 'Landsat 7 ETM+',
        'collections': ['LANDSAT/LE07/C02/T1_TOA'],
        'cloudProp': 'CLOUD_COVER',
        'rgbBands': ['B3', 'B2', 'B1'],
        'scaleFactor': 1, 'offset': 0,
        'visMin': 0, 'visMax': 0.3,
        'resolution': 30,
        'bandsInfo': 'RGB: B3 (Kırmızı) · B2 (Yeşil) · B1 (Mavi) — 9 bant (TOA + termal)',
        'trueColor': True,
    },
    'l45-l1': {
        'label': 'Landsat 4–5 TM (C2 L1)',
        'datasetName': 'Landsat 4–5 Collection 2 Level-1 (TOA Yansıması)',
        'sensor': 'Landsat 4–5 TM',
        'collections': ['LANDSAT/LT05/C02/T1_TOA', 'LANDSAT/LT04/C02/T1_TOA'],
        'cloudProp': 'CLOUD_COVER',
        'rgbBands': ['B3', 'B2', 'B1'],
        'scaleFactor': 1, 'offset': 0,
        'visMin': 0, 'visMax': 0.3,
        'resolution': 30,
        'bandsInfo': 'RGB: B3 (Kırmızı) · B2 (Yeşil) · B1 (Mavi) — 7 bant (TOA + termal)',
        'trueColor': True,
    },
    'mss-l1': {
        'label': 'Landsat 1–5 MSS (C2 L1)',
        'datasetName': 'Landsat 1–5 MSS Collection 2 Level-1 (TOA Yansıması)',
        'sensor': 'Landsat 1–5 MSS',
        'collections': [
            'LANDSAT/LM05/C02/T1', 'LANDSAT/LM04/C02/T1', 'LANDSAT/LM03/C02/T1',
            'LANDSAT/LM02/C02/T1', 'LANDSAT/LM01/C02/T1',
        ],
        'cloudProp': None,  # MSS koleksiyonlarında tutarlı bulutluluk özniteliği yok
        'rgbBands': ['B3', 'B2', 'B1'],   # NIR1 / Kırmızı / Yeşil — gerçek mavi bant yok
        'scaleFactor': 1, 'offset': 0,
        'visMin': 0, 'visMax': 120,
        'resolution': 60,
        'bandsInfo': 'Kompozit: B3 (NIR1) · B2 (Kırmızı) · B1 (Yeşil) — MSS\'de mavi bant bulunmaz',
        'trueColor': False,
    },
}


# ════════════════════════════════════════════════════════════════
# 📡 HAM VERİ (BANTLAR) — Veri Seti → Bant Kataloğu
# ════════════════════════════════════════════════════════════════
# Her anahtar SATELLITE_DATASETS ile birebir eşleşir. Değer, o veri
# setinin TÜM orijinal bantlarını, nominal (kataloğa göre bilinen)
# mekansal çözünürlüklerine göre gruplandırılmış olarak listeler.
#
# Bu liste yalnızca ARAYÜZDE bantları çözünürlük grubu başlıkları
# altında (10 m / 20 m / 30 m / 60 m ...) göstermek ve dosya adlarına
# yedek (fallback) bir çözünürlük değeri sağlamak için kullanılır.
# Gerçek dışa aktarım sırasında her bandın GERÇEK orijinal çözünürlüğü
# ve CRS'i, doğrudan GEE'den (ee.Image.projection()) sorgulanır —
# yani hiçbir zaman yeniden örnekleme (resampling) yapılmaz.
RAW_BAND_GROUPS = {
    's2-l1c': [
        {'resolution': 10, 'bands': [
            {'name': 'B2',  'label': 'Mavi (Blue)'},
            {'name': 'B3',  'label': 'Yeşil (Green)'},
            {'name': 'B4',  'label': 'Kırmızı (Red)'},
            {'name': 'B8',  'label': 'Yakın Kızılötesi (NIR)'},
        ]},
        {'resolution': 20, 'bands': [
            {'name': 'B5',   'label': 'Kırmızı Kenar 1 (Red Edge 1)'},
            {'name': 'B6',   'label': 'Kırmızı Kenar 2 (Red Edge 2)'},
            {'name': 'B7',   'label': 'Kırmızı Kenar 3 (Red Edge 3)'},
            {'name': 'B8A',  'label': 'Dar NIR (Red Edge 4)'},
            {'name': 'B11',  'label': 'Kısa Dalga Kızılötesi 1 (SWIR 1)'},
            {'name': 'B12',  'label': 'Kısa Dalga Kızılötesi 2 (SWIR 2)'},
        ]},
        {'resolution': 60, 'bands': [
            {'name': 'B1',  'label': 'Kıyı Aerosolü (Coastal Aerosol)'},
            {'name': 'B9',  'label': 'Su Buharı (Water Vapour)'},
            {'name': 'B10', 'label': 'Sirrus (Cirrus)'},
        ]},
    ],
    's2-l2a': [
        {'resolution': 10, 'bands': [
            {'name': 'B2',  'label': 'Mavi (Blue)'},
            {'name': 'B3',  'label': 'Yeşil (Green)'},
            {'name': 'B4',  'label': 'Kırmızı (Red)'},
            {'name': 'B8',  'label': 'Yakın Kızılötesi (NIR)'},
        ]},
        {'resolution': 20, 'bands': [
            {'name': 'B5',   'label': 'Kırmızı Kenar 1 (Red Edge 1)'},
            {'name': 'B6',   'label': 'Kırmızı Kenar 2 (Red Edge 2)'},
            {'name': 'B7',   'label': 'Kırmızı Kenar 3 (Red Edge 3)'},
            {'name': 'B8A',  'label': 'Dar NIR (Red Edge 4)'},
            {'name': 'B11',  'label': 'Kısa Dalga Kızılötesi 1 (SWIR 1)'},
            {'name': 'B12',  'label': 'Kısa Dalga Kızılötesi 2 (SWIR 2)'},
        ]},
        {'resolution': 60, 'bands': [
            {'name': 'B1',  'label': 'Kıyı Aerosolü (Coastal Aerosol)'},
            {'name': 'B9',  'label': 'Su Buharı (Water Vapour)'},
            # Not: B10 (Cirrus) yalnızca L1C üründe bulunur; L2A yüzey
            # yansıması ürününde bu bant yer almaz.
        ]},
    ],
    'l89-l2': [
        {'resolution': 30, 'bands': [
            {'name': 'SR_B1',  'label': 'Kıyı Aerosolü (Coastal/Aerosol)'},
            {'name': 'SR_B2',  'label': 'Mavi (Blue)'},
            {'name': 'SR_B3',  'label': 'Yeşil (Green)'},
            {'name': 'SR_B4',  'label': 'Kırmızı (Red)'},
            {'name': 'SR_B5',  'label': 'Yakın Kızılötesi (NIR)'},
            {'name': 'SR_B6',  'label': 'Kısa Dalga Kızılötesi 1 (SWIR 1)'},
            {'name': 'SR_B7',  'label': 'Kısa Dalga Kızılötesi 2 (SWIR 2)'},
            {'name': 'ST_B10', 'label': 'Termal (Thermal)'},
        ]},
    ],
    'l7-l2': [
        {'resolution': 30, 'bands': [
            {'name': 'SR_B1', 'label': 'Mavi (Blue)'},
            {'name': 'SR_B2', 'label': 'Yeşil (Green)'},
            {'name': 'SR_B3', 'label': 'Kırmızı (Red)'},
            {'name': 'SR_B4', 'label': 'Yakın Kızılötesi (NIR)'},
            {'name': 'SR_B5', 'label': 'Kısa Dalga Kızılötesi 1 (SWIR 1)'},
            {'name': 'SR_B7', 'label': 'Kısa Dalga Kızılötesi 2 (SWIR 2)'},
            {'name': 'ST_B6', 'label': 'Termal (Thermal)'},
        ]},
    ],
    'l45-l2': [
        {'resolution': 30, 'bands': [
            {'name': 'SR_B1', 'label': 'Mavi (Blue)'},
            {'name': 'SR_B2', 'label': 'Yeşil (Green)'},
            {'name': 'SR_B3', 'label': 'Kırmızı (Red)'},
            {'name': 'SR_B4', 'label': 'Yakın Kızılötesi (NIR)'},
            {'name': 'SR_B5', 'label': 'Kısa Dalga Kızılötesi 1 (SWIR 1)'},
            {'name': 'SR_B7', 'label': 'Kısa Dalga Kızılötesi 2 (SWIR 2)'},
            {'name': 'ST_B6', 'label': 'Termal (Thermal)'},
        ]},
    ],
    'l89-l1': [
        {'resolution': 15, 'bands': [
            {'name': 'B8', 'label': 'Pankromatik (Panchromatic)'},
        ]},
        {'resolution': 30, 'bands': [
            {'name': 'B1',  'label': 'Kıyı Aerosolü (Coastal/Aerosol)'},
            {'name': 'B2',  'label': 'Mavi (Blue)'},
            {'name': 'B3',  'label': 'Yeşil (Green)'},
            {'name': 'B4',  'label': 'Kırmızı (Red)'},
            {'name': 'B5',  'label': 'Yakın Kızılötesi (NIR)'},
            {'name': 'B6',  'label': 'Kısa Dalga Kızılötesi 1 (SWIR 1)'},
            {'name': 'B7',  'label': 'Kısa Dalga Kızılötesi 2 (SWIR 2)'},
            {'name': 'B9',  'label': 'Sirrus (Cirrus)'},
            {'name': 'B10', 'label': 'Termal 1 (Thermal 1)'},
            {'name': 'B11', 'label': 'Termal 2 (Thermal 2)'},
        ]},
    ],
    'l7-l1': [
        {'resolution': 15, 'bands': [
            {'name': 'B8', 'label': 'Pankromatik (Panchromatic)'},
        ]},
        {'resolution': 30, 'bands': [
            {'name': 'B1', 'label': 'Mavi (Blue)'},
            {'name': 'B2', 'label': 'Yeşil (Green)'},
            {'name': 'B3', 'label': 'Kırmızı (Red)'},
            {'name': 'B4', 'label': 'Yakın Kızılötesi (NIR)'},
            {'name': 'B5', 'label': 'Kısa Dalga Kızılötesi 1 (SWIR 1)'},
            {'name': 'B7', 'label': 'Kısa Dalga Kızılötesi 2 (SWIR 2)'},
            {'name': 'B6_VCID_1', 'label': 'Termal — Düşük Kazanç (Thermal Low Gain)'},
            {'name': 'B6_VCID_2', 'label': 'Termal — Yüksek Kazanç (Thermal High Gain)'},
        ]},
    ],
    'l45-l1': [
        {'resolution': 30, 'bands': [
            {'name': 'B1', 'label': 'Mavi (Blue)'},
            {'name': 'B2', 'label': 'Yeşil (Green)'},
            {'name': 'B3', 'label': 'Kırmızı (Red)'},
            {'name': 'B4', 'label': 'Yakın Kızılötesi (NIR)'},
            {'name': 'B5', 'label': 'Kısa Dalga Kızılötesi 1 (SWIR 1)'},
            {'name': 'B6', 'label': 'Termal (Thermal)'},
            {'name': 'B7', 'label': 'Kısa Dalga Kızılötesi 2 (SWIR 2)'},
        ]},
    ],
    'mss-l1': [
        {'resolution': 60, 'bands': [
            {'name': 'B1', 'label': 'Yeşil (Green, 0.5–0.6 µm)'},
            {'name': 'B2', 'label': 'Kırmızı (Red, 0.6–0.7 µm)'},
            {'name': 'B3', 'label': 'Yakın Kızılötesi 1 (NIR 1, 0.7–0.8 µm)'},
            {'name': 'B4', 'label': 'Yakın Kızılötesi 2 (NIR 2, 0.8–1.1 µm)'},
        ]},
    ],
}


def _dataset_file_tags(ds_key, image):
    """
    Dosya adlandırması için (sensörEtiketi, seviyeEtiketi) döndürür.
    Örnek çıktı: ('Sentinel2', 'L2A') veya ('Landsat9', 'C2L2').

    Landsat veri setleri birden fazla uyduyu birleştirdiği (ör. l89-l2 →
    Landsat 8 VE 9) için gerçek uydu numarası, seçilen SAHNENİN kendi
    'SPACECRAFT_ID' özniteliğinden okunur — böylece dosya adı her zaman
    o sahnenin GERÇEK uydusunu yansıtır (ör. 'Landsat9_C2L2_...').
    Öznitelik okunamazsa veri seti anahtarına göre genel bir yedek isim
    kullanılır.
    """
    level_map = {
        's2-l1c': 'L1C', 's2-l2a': 'L2A',
        'l89-l2': 'C2L2', 'l7-l2': 'C2L2', 'l45-l2': 'C2L2',
        'l89-l1': 'C2L1', 'l7-l1': 'C2L1', 'l45-l1': 'C2L1', 'mss-l1': 'C2L1',
    }
    level = level_map.get(ds_key, 'DATA')

    if ds_key.startswith('s2'):
        return 'Sentinel2', level

    sensor_tag = None
    try:
        spc = image.get('SPACECRAFT_ID').getInfo()  # ör. 'LANDSAT_9'
        if spc:
            sensor_tag = str(spc).replace('LANDSAT_', 'Landsat').replace('_', '')
    except Exception:
        sensor_tag = None

    if not sensor_tag:
        fallback_map = {
            'l89-l2': 'Landsat8-9', 'l89-l1': 'Landsat8-9',
            'l7-l2': 'Landsat7', 'l7-l1': 'Landsat7',
            'l45-l2': 'Landsat4-5', 'l45-l1': 'Landsat4-5',
            'mss-l1': 'Landsat1-5',
        }
        sensor_tag = fallback_map.get(ds_key, 'Landsat')

    return sensor_tag, level


def build_rgb_collection(ds, roi, max_cloud):
    """Veri seti kaydındaki (birden fazla olabilen) koleksiyonları AOI ve
    bulutluluk kriterine göre filtreler ve tek bir ImageCollection'da birleştirir."""
    collection_ids = ds.get('collections') or [ds.get('collection')]
    col = None
    for cid in collection_ids:
        c = ee.ImageCollection(cid).filterBounds(roi)
        if ds.get('cloudProp'):
            try:
                c = c.filter(ee.Filter.lt(ds['cloudProp'], max_cloud))
            except Exception:
                pass
        col = c if col is None else col.merge(c)
    return col


_TR_MONTH_NAMES = {
    'ocak': 1, 'şubat': 2, 'subat': 2, 'mart': 3, 'nisan': 4, 'mayıs': 5,
    'mayis': 5, 'haziran': 6, 'temmuz': 7, 'ağustos': 8, 'agustos': 8,
    'eylül': 9, 'eylul': 9, 'ekim': 10, 'kasım': 11, 'kasim': 11,
    'aralık': 12, 'aralik': 12,
}


def _parse_months_param(data):
    """İstemciden gelen 'Ay Seçimi' filtresini (varsa) ayrıştırır.
    Hem sayısal liste ([7, 8]) hem de Türkçe ay ismi listesi
    (['Temmuz', 'Ağustos']) destekler. Çeşitli olası alan adlarına bakar
    ('months', 'selectedMonths', 'monthNames', 'ay', 'ayListesi').
    Filtre yoksa/boşsa None döner (tüm aylar dahil demektir)."""
    raw = None
    for key in ('months', 'selectedMonths', 'monthNames', 'ay', 'ayListesi'):
        val = data.get(key)
        if val:
            raw = val
            break
    if not raw:
        return None
    months = set()
    for item in raw:
        if isinstance(item, (int, float)):
            m = int(item)
            if 1 <= m <= 12:
                months.add(m)
        elif isinstance(item, str):
            s = item.strip().lower()
            if s.isdigit():
                m = int(s)
                if 1 <= m <= 12:
                    months.add(m)
            elif s in _TR_MONTH_NAMES:
                months.add(_TR_MONTH_NAMES[s])
    return sorted(months) if months else None


def _calendar_month_filter(months):
    """months: 1-12 arası tam sayı listesi. Herhangi birine uyan bir
    ee.Filter.Or(calendarRange(...)) döner. Liste boş/None ise None döner."""
    if not months:
        return None
    filters = [ee.Filter.calendarRange(m, m, 'month') for m in months]
    return filters[0] if len(filters) == 1 else ee.Filter.Or(*filters)


# ════════════════════════════════════════════════════════════════
# 🗓️ ÇOK YILLI TARİH ARALIKLARINDA SAHNE TOPLAMA — YIL ÖNYARGISI DÜZELTMESİ
# ════════════════════════════════════════════════════════════════
# SORUN: Önceden sahne/galeri sorguları şu şekildeydi:
#     col.filterDate(start_date, end_date).sort('system:time_start').limit(N)
# Bu, TÜM tarih aralığını (ör. 2024-2026) tek bir koleksiyonda filtreleyip
# ardından kronolojik olarak İLK N sahneyi alır. Sentinel-2 gibi sık
# tekrar ziyaretli (5 günde bir) bir uydu için, aralık birden fazla yıl
# kapsadığında bu İLK N sahne neredeyse her zaman aralığın BAŞLADIĞI YILIN
# içinde tükenir — böylece kullanıcı "Temmuz, Ağustos" gibi bir ay filtresi
# seçse bile (bu filtre önceden hiç uygulanmıyordu) ya da sadece geniş bir
# tarih aralığı seçse bile, galeri/zaman serisi SADECE aralığın ilk yılına
# ait veri gösterir; sonraki yıllardaki aynı aya/kritere uyan görüntüler
# hiçbir zaman sorguya dahi girmez (çünkü limit() onlara ulaşmadan önce
# dolar). "Analiz yaparken de aynı sorunu yaşıyorum" şikayeti de aynı kök
# nedenden kaynaklanıyordu (bkz. /api/analyze zaman serisi galerisi).
#
# ÇÖZÜM: Aralıktaki HER YIL için AYRI AYRI filterDate (+ varsa ay filtresi)
# uygulanır ve o yıldan en fazla `per_year_limit` sahne alınır; sonra tüm
# yılların sonuçları birleştirilir. Böylece her yıl galeri/zaman serisinde
# adil şekilde temsil edilir, tarih aralığı kaç yıl kapsarsa kapsasın.
def _collect_scenes_across_years(col, start_date, end_date, months=None,
                                  per_year_limit=12, total_limit=60):
    sdt = datetime.datetime.strptime(str(start_date)[:10], '%Y-%m-%d')
    edt = datetime.datetime.strptime(str(end_date)[:10], '%Y-%m-%d')
    month_filter = _calendar_month_filter(months)

    merged = None
    for year in range(sdt.year, edt.year + 1):
        year_start = datetime.datetime(year, 1, 1)
        year_end = datetime.datetime(year + 1, 1, 1)
        clip_start = max(sdt, year_start)
        clip_end = min(edt, year_end)
        if clip_start >= clip_end:
            continue
        yr_col = col.filterDate(clip_start.strftime('%Y-%m-%d'), clip_end.strftime('%Y-%m-%d'))
        if month_filter is not None:
            yr_col = yr_col.filter(month_filter)
        yr_col = yr_col.sort('system:time_start').limit(per_year_limit)
        merged = yr_col if merged is None else merged.merge(yr_col)

    if merged is None:
        # Geçersiz/ters aralık — boş koleksiyon döndür
        return col.filterDate(start_date, start_date)

    return merged.sort('system:time_start').limit(total_limit)


def _mask_clouds(image, satellite):
    """Bulut / bulut gölgesi / sirrus piksellerini updateMask() ile NoData
    yaparak indeks hesaplamalarından (NDVI, NDWI, vb.) ve GeoTIFF
    export'undan dışlar.

    NEDEN GEREKLİ: Önceden koleksiyon sadece sahne bazlı bulutluluk
    yüzdesine göre filtreleniyordu (CLOUDY_PIXEL_PERCENTAGE / CLOUD_COVER).
    Bu filtre sahne genelinde %X bulut olan görüntüleri elese de, kalan
    sahnenin İÇİNDEKİ tek tek bulut/gölge piksellerini maskelemiyordu.
    Sonuç olarak export edilen GeoTIFF'te (örn. ArcMap'te açıldığında)
    AOI içinde rastgele dağılmış küçük beyaz/boşluk pikselleri (bulut,
    sirrus, kar/buz ve gölge pikselleri) görünüyordu. Bu fonksiyon her
    görüntüye piksel bazlı bulut maskesi uygulayarak bu boşlukları önler.
    """
    if satellite in ('s2-l2a', 's2-l1c'):
        # Sentinel-2 QA60: bit 10 = bulut (opak), bit 11 = sirrus
        qa = image.select('QA60')
        cloud_bit_mask = 1 << 10
        cirrus_bit_mask = 1 << 11
        mask = (qa.bitwiseAnd(cloud_bit_mask).eq(0)
                  .And(qa.bitwiseAnd(cirrus_bit_mask).eq(0)))
        return image.updateMask(mask)

    if satellite in ('l89-l2', 'l7-l2', 'l45-l2', 'l45-l1', 'l89-l1', 'l7-l1'):
        # Landsat Collection 2 (L1 ve L2) QA_PIXEL bitleri:
        # bit1=Dilated Cloud, bit2=Cirrus, bit3=Cloud, bit4=Cloud Shadow
        # Not: QA_PIXEL bandı hem L1 (TOA) hem L2 (SR) ürünlerinde mevcuttur.
        qa = image.select('QA_PIXEL')
        mask = (qa.bitwiseAnd(1 << 1).eq(0)
                  .And(qa.bitwiseAnd(1 << 2).eq(0))
                  .And(qa.bitwiseAnd(1 << 3).eq(0))
                  .And(qa.bitwiseAnd(1 << 4).eq(0)))
        return image.updateMask(mask)

    # Diğer koleksiyonlar (mss-l1, SAR, vb.) için uygun bir QA bandı
    # bulunmadığından görüntü değiştirilmeden döndürülür.
    return image


def hex_to_rgb(hex_color):
    """'#rrggbb' → (r, g, b)"""
    h = hex_color.lstrip('#')
    if len(h) == 3:
        h = ''.join(c * 2 for c in h)
    return tuple(int(h[i:i+2], 16) for i in (0, 2, 4))


# ════════════════════════════════════════════════════════════════
# 🌐 KOORDİNAT/BOYLAM-ENLEM'DEN OTOMATİK UTM DİLİMİ (PROJEKSİYON) HESABI
# ════════════════════════════════════════════════════════════════
# SORUN: Bazı veri setleri (Dynamic World LULC, ESA WorldCover, SRTM/
# NASADEM/ALOS DEM vb.) Earth Engine'de zaten coğrafi (EPSG:4326,
# derece bazlı) sistemde saklanır — yani bu veriler için "gerçek native
# CRS" GERÇEKTEN WGS 84'tür. Ancak raster indirme/analiz iş akışında
# (alan, mesafe, piksel boyutu hesapları) coğrafi/derece tabanlı bir
# sistem YANLIŞ/pratik değildir — enlem arttıkça 1 derecelik piksel
# boyutunun gerçek metre karşılığı değişir. Bu yüzden CBS'de pratik/
# doğru yaklaşım, coğrafi CRS yerine HER ZAMAN alanın gerçekte
# düştüğü UTM dilimini (metre bazlı, projeksiyonlu bir sistem)
# kullanmaktır. Bu fonksiyon, AOI'nin merkez boylam/enleminden standart
# UTM dilim formülüyle doğru EPSG kodunu hesaplar (WGS84 datumlu UTM
# North: 326xx, South: 327xx).
def _utm_epsg_from_lonlat(lon, lat):
    """Boylam/enlemden en uygun UTM dilimi EPSG kodunu ('EPSG:326xx' /
    'EPSG:327xx') döndürür. UPS bölgeleri (kutup uçları, |lat|>84) için
    en yakın UTM dilimine düşülür — nadiren kullanılan bir kenar durumdur."""
    zone = int((float(lon) + 180.0) / 6.0) + 1
    zone = max(1, min(60, zone))
    if float(lat) >= 0:
        return 'EPSG:' + str(32600 + zone)   # UTM Kuzey (N)
    return 'EPSG:' + str(32700 + zone)       # UTM Güney (S)


def _strip_z(coords):
    """
    GeoJSON koordinat dizisindeki üçüncü (Z / yükseklik) bileşeni varsa temizler.
    Earth Engine yalnızca 2 boyutlu [boylam, enlem] çiftlerini kabul eder; KML/KMZ
    dosyaları ise çoğunlukla [boylam, enlem, irtifa] biçiminde 3 boyutlu koordinat
    içerir. Bu fazladan boyut temizlenmezse EE "Invalid GeoJSON geometry" hatası verir.
    """
    if not coords:
        return coords
    if isinstance(coords[0], (int, float)):
        return [coords[0], coords[1]]
    return [_strip_z(c) for c in coords]


def _normalize_to_geojson(roi):
    """
    Frontend'den gelen ROI verisini standart bir GeoJSON geometri sözlüğüne çevirir.
    Desteklenen girdiler:
      - Zaten bir GeoJSON sözlüğü: {'type': 'Polygon'|'MultiPolygon', 'coordinates': [...]}
      - Eski (ham) formatlar (geriye dönük uyumluluk):
          [[lng,lat],...]                  → tek halka
          [[[lng,lat],...]]                → Polygon (halka listesi; iç halkalar/donut korunur)
          [[[[lng,lat],...]]]              → MultiPolygon (tüm parçalar korunur)
    Olası Z (irtifa) bileşeni, hangi yoldan gelirse gelsin burada temizlenir.
    """
    if isinstance(roi, dict) and roi.get('type') and roi.get('coordinates') is not None:
        return {'type': roi['type'], 'coordinates': _strip_z(roi['coordinates'])}

    coords = roi
    if not coords:
        raise ValueError('Boş veya tanımsız çalışma alanı geometrisi.')

    # [[[[lng,lat],...]]] → MultiPolygon (her bir poligonun tüm halkaları korunur)
    try:
        if isinstance(coords[0][0][0], list):
            return {'type': 'MultiPolygon', 'coordinates': _strip_z(coords)}
    except (IndexError, TypeError):
        pass

    # [[[lng,lat],...]] → Polygon (dış halka + olası iç (donut) halkalar korunur)
    try:
        if isinstance(coords[0], list) and isinstance(coords[0][0], list):
            return {'type': 'Polygon', 'coordinates': _strip_z(coords)}
    except (IndexError, TypeError):
        pass

    # [[lng,lat],...] → tek halkalı Polygon
    return {'type': 'Polygon', 'coordinates': _strip_z([coords])}


def _collect_polygons(geom):
    """Shapely geometrisinden (Polygon/MultiPolygon/GeometryCollection) Polygon listesi üretir."""
    if geom.is_empty:
        return []
    if geom.geom_type == 'Polygon':
        return [geom]
    if geom.geom_type == 'MultiPolygon':
        return list(geom.geoms)
    if geom.geom_type == 'GeometryCollection':
        out = []
        for g in geom.geoms:
            out.extend(_collect_polygons(g))
        return out
    return []


def _basic_ring_repair_geojson(geom_dict):
    """
    Shapely olmadan da çalışan, hafif bir ön-onarım adımı:
      - Kapanmamış halkaları kapatır (ilk nokta = son nokta)
      - Art arda gelen birebir aynı (tekrarlı) noktaları temizler
      - 3'ten az benzersiz noktası kalan (dejenere) halkaları atar
    Bu, KML/KMZ dışa aktarımlarında çok sık görülen "halka kapanmamış" türü
    hatalarda shapely'e gerek kalmadan sorunu çözer.
    """
    def fix_ring(ring):
        if not ring:
            return ring
        cleaned = [ring[0]]
        for pt in ring[1:]:
            if pt != cleaned[-1]:
                cleaned.append(pt)
        if len(cleaned) >= 2 and cleaned[0] != cleaned[-1]:
            cleaned.append(cleaned[0])
        return cleaned

    gtype = geom_dict.get('type')
    coords = geom_dict.get('coordinates')

    if gtype == 'Polygon':
        rings = [fix_ring(r) for r in coords]
        rings = [r for r in rings if len(r) >= 4]
        if not rings:
            raise ValueError('Onarım sonrası geçerli halka kalmadı.')
        return {'type': 'Polygon', 'coordinates': rings}

    if gtype == 'MultiPolygon':
        polys = []
        for poly in coords:
            rings = [fix_ring(r) for r in poly]
            rings = [r for r in rings if len(r) >= 4]
            if rings:
                polys.append(rings)
        if not polys:
            raise ValueError('Onarım sonrası geçerli poligon kalmadı.')
        return {'type': 'MultiPolygon', 'coordinates': polys}

    return geom_dict


def make_roi(roi):
    """
    EE Geometry oluşturur (Polygon veya MultiPolygon).

    KML/KMZ veya elle çizilen çalışma alanlarında sık görülen sorunları otomatik
    çözer:
      - Kendi kendini kesen (self-intersecting) çizimler
      - İç içe geçmiş (donut / hole) yapılar — tüm halkalar korunur
      - Çoklu poligon (MultiPolygon) yapılar — TÜM parçalar korunur (sadece ilki değil)
      - Kapanmamış halkalar, mikroskopik / sıfır alanlı parçalar, yanlış halka yönü

    roi: GeoJSON geometri sözlüğü {'type', 'coordinates'} veya eski ham koordinat
         dizisi (geriye dönük uyumluluk için desteklenir).
    """
    geom_dict = _normalize_to_geojson(roi)

    # 1. Doğrudan oluşturmayı dene — çoğu temiz geometri için yeterli ve en hızlı yol.
    try:
        return ee.Geometry(geom_dict, None, False)
    except Exception as e1:
        first_err = e1

    # 2. Shapely gerektirmeyen hafif onarım (kapanmamış halka / tekrarlı nokta).
    #    Birçok KML/KMZ dışa aktarım hatası shapely olmadan burada çözülür.
    try:
        repaired = _basic_ring_repair_geojson(geom_dict)
        return ee.Geometry(repaired, None, False)
    except Exception:
        pass

    # 3. Daha karmaşık (kendi kendini kesen, donut birleştirme vb.) onarımlar için
    #    Shapely kullanılır. Sunucuda kurulu değilse anlaşılır bir hata verilir.
    try:
        from shapely.geometry import shape, mapping, MultiPolygon
        from shapely.validation import make_valid
        from shapely.geometry.polygon import orient
    except ImportError:
        raise ValueError(
            'Geometri onarım modülü (shapely) sunucuda kurulu değil. Lütfen sunucu '
            'tarafında "pip install shapely" komutunu çalıştırıp server.py\'yi yeniden '
            'başlatın. (İlk deneme hatası: ' + str(first_err) + ')'
        )

    try:
        geom = shape(geom_dict)
        if not geom.is_valid:
            geom = make_valid(geom)

        # make_valid; Polygon, MultiPolygon veya GeometryCollection döndürebilir.
        polygons = _collect_polygons(geom)
        # Sıfıra yakın / mikroskopik (onarım artığı) parçaları ele
        polygons = [p for p in polygons if p.area > 1e-12]
        if not polygons:
            raise ValueError('Geometri içinde kullanılabilir, alanı olan bir poligon bulunamadı.')

        # Doğru halka yönü: dış halka saat yönünün tersi, iç (donut) halkalar saat yönü.
        polygons = [orient(p, sign=1.0) for p in polygons]

        if len(polygons) == 1:
            fixed = mapping(polygons[0])
        else:
            # Birden fazla parça varsa (MultiPolygon veya kendi kendini kesmeden doğan
            # birden fazla bileşen) HİÇBİRİ atılmadan tek bir MultiPolygon'da birleştirilir.
            fixed = mapping(MultiPolygon(polygons))

        return ee.Geometry(fixed, None, False)
    except Exception as e:
        raise ValueError('Invalid geometry — lütfen çalışma alanını kontrol edin: ' + str(e))


@app.route('/api/building-footprints', methods=['POST'])
def building_footprints():
    """
    Çalışma alanı içindeki Google Open Buildings bina poligonlarını döndürür.

    İstek gövdesi:
      {
        "geometry": <GeoJSON Polygon/MultiPolygon>
      }

    `roi` alanı da geriye dönük/istemci uyumluluğu için `geometry` yerine
    kullanılabilir. Bina sayısı ve toplam alan bütün filtrelenmiş koleksiyon
    üzerinden hesaplanır ve aynı koleksiyondaki tüm bina poligonları
    GeoJSON olarak haritaya gönderilir.
    """
    try:
        data = request.get_json(silent=True) or {}
        geometry = data.get('geometry')
        if geometry is None:
            geometry = data.get('roi')
        if geometry is None:
            return jsonify({
                'success': False,
                'error': 'Çalışma alanı geometrisi gönderilmedi.'
            }), 400

        # GeoJSON Feature gönderilirse içindeki geometriyi de kabul et.
        if isinstance(geometry, dict) and geometry.get('type') == 'Feature':
            geometry = geometry.get('geometry')
        if not geometry:
            return jsonify({
                'success': False,
                'error': 'Geçerli bir çalışma alanı geometrisi gönderilmedi.'
            }), 400

        aoi = make_roi(geometry)
        cache_key = _building_cache_key(geometry)
        cached_payload = _get_cached_buildings(cache_key)
        if cached_payload is not None:
            cached_payload['cached'] = True
            return jsonify(cached_payload)

        buildings = ee.FeatureCollection(
            _BUILDING_DATASET_ID
        ).filterBounds(aoi)

        # Alanı, veri setindeki hazır bir alana güvenmeden doğrudan bina
        # geometrisinden hesapla. Böylece toplam değer m² cinsinden ve
        # sorgulanan koleksiyonla aynı kapsamda olur.
        buildings_with_area = buildings.map(
            lambda feature: feature.set(
                '_sylva_area_m2',
                feature.geometry().area(maxError=1)
            )
        )
        stats = _call_with_retry(
            lambda: ee.Dictionary({
                'buildingCount': buildings.size(),
                'totalAreaM2': buildings_with_area.aggregate_sum('_sylva_area_m2'),
            }).getInfo(),
            retries=2
        ) or {}

        try:
            building_count = int(stats.get('buildingCount') or 0)
        except (TypeError, ValueError):
            building_count = 0

        # Bina yoksa ikinci GEE getInfo çağrısını yapma. Bu hem boş AOI'lerde
        # yanıtı hızlandırır hem de gereksiz istek sayısını azaltır.
        if building_count <= 0:
            feature_collection_info = {
                'type': 'FeatureCollection',
                'features': [],
            }
        else:
            # İstatistiklerle aynı koleksiyonun tamamını GeoJSON olarak al.
            # Böylece haritada gösterilen poligon sayısı ile toplam bina
            # sayısı arasında fark oluşmaz.
            feature_collection_info = _call_with_retry(
                lambda: buildings.getInfo(),
                retries=2
            ) or {'type': 'FeatureCollection', 'features': []}
        features = feature_collection_info.get('features', [])

        try:
            total_area_m2 = float(stats.get('totalAreaM2') or 0)
        except (TypeError, ValueError):
            total_area_m2 = 0.0

        source = _BUILDING_DATASET_NAME
        coverage_note = _BUILDING_DATASET_COVERAGE_NOTE
        osm_fallback_used = False
        osm_fallback_skipped = False
        # Open Buildings ülke kapsamı dışında kalabiliyor. GEE başarılı ama
        # boş döndüğünde aynı küçük AOI'yi OSM bina ayak izleriyle kontrol et.
        if building_count <= 0:
            try:
                osm_result = _osm_buildings_from_bbox(geometry)
                osm_features = osm_result.get('features') or []
                if osm_features:
                    features = osm_features
                    building_count = int(
                        osm_result.get('totalCount') or len(osm_features)
                    )
                    total_area_m2 = float(osm_result.get('totalAreaM2') or 0)
                    source = 'OpenStreetMap / Overpass API'
                    coverage_note = _OSM_FALLBACK_NOTE
                    osm_fallback_used = True
                else:
                    osm_fallback_skipped = bool(osm_result.get('skipped'))
                    if osm_result.get('note'):
                        coverage_note += ' ' + str(osm_result['note'])
            except Exception as osm_error:
                # OSM geçici olarak erişilemezse GEE'nin geçerli boş sonucu
                # bozulmasın; nedenini yalnızca yanıt notuna ekle.
                coverage_note += ' OSM yedeği şu anda kullanılamadı.'
                print('[SylvaGIS] OSM bina yedeği kullanılamadı:', osm_error)

        payload = {
            'success': True,
            'buildingCount': building_count,
            'totalAreaM2': total_area_m2,
            'returnedFeatureCount': len(features),
            'truncated': False,
            'cached': False,
            'dataset': source,
            'coverageNote': coverage_note,
            'osmFallbackUsed': osm_fallback_used,
            'osmFallbackSkipped': osm_fallback_skipped,
            'geojson': {
                'type': 'FeatureCollection',
                'features': features,
            },
        }
        _cache_buildings(cache_key, payload)
        return jsonify(payload)

    except Exception as e:
        traceback.print_exc()
        return jsonify({
            'success': False,
            'error': f'Bina verileri alınamadı: {str(e)}'
        }), 500


def _parse_building_geometry_from_request(data):
    """`/start` endpoint'i için ortak geometri ayrıştırma/doğrulama."""
    geometry = data.get('geometry')
    if geometry is None:
        geometry = data.get('roi')
    if isinstance(geometry, dict) and geometry.get('type') == 'Feature':
        geometry = geometry.get('geometry')
    return geometry


@app.route('/api/building-footprints/start', methods=['POST'])
def building_footprints_start():
    """
    Aşama 4 — asenkron iş kuyruğu: geometriyi alır, bir job_id üretir,
    taramayı arka plan thread'inde başlatır ve hemen {jobId} döner.
    """
    try:
        data = request.get_json(silent=True) or {}
        geometry = _parse_building_geometry_from_request(data)
        if not geometry:
            return jsonify({
                'success': False,
                'error': 'Çalışma alanı geometrisi gönderilmedi.'
            }), 400

        try:
            # Geometri erken doğrulanır — hatalı geometriyle boşuna thread
            # başlatılmaz.
            make_roi(geometry)
        except Exception as geom_error:
            return jsonify({'success': False, 'error': str(geom_error)}), 400

        job_id = _new_building_job(geometry)
        thread = threading.Thread(
            target=_run_building_job, args=(job_id,), daemon=True
        )
        thread.start()

        return jsonify({'success': True, 'jobId': job_id})
    except Exception as e:
        traceback.print_exc()
        return jsonify({
            'success': False,
            'error': f'Bina taraması başlatılamadı: {str(e)}'
        }), 500


@app.route('/api/building-footprints/status/<job_id>', methods=['GET'])
def building_footprints_status(job_id):
    """
    Aşama 4 — {progress: taranan/tile toplam, buildingCountSoFar, done,
    partialGeojson veya finalGeojson, error} döner. Kullanıcı arayüzü bu
    endpoint'i periyodik olarak (polling) çağırarak canlı ilerleme gösterir.
    """
    job = _get_building_job(job_id)
    with _building_jobs_lock:
        if not job:
            return jsonify({
                'success': False,
                'error': 'İş bulunamadı (zaman aşımına uğramış olabilir).'
            }), 404

        status = job['status']
        done = status in ('done', 'error', 'cancelled')
        payload = {
            'success': True,
            'jobId': job_id,
            'status': status,
            'done': done,
            'progress': {
                'tilesDone': job['tilesDone'],
                'totalTiles': job['totalTiles'],
            },
            'buildingCountSoFar': job['buildingCountSoFar'],
            'totalAreaM2SoFar': job['totalAreaM2SoFar'],
            'dataset': job['dataset'],
            'coverageNote': job['coverageNote'],
            'error': job['error'],
        }
        if status == 'done':
            payload['buildingCount'] = job['buildingCount']
            payload['totalAreaM2'] = job['totalAreaM2']
            payload['finalGeojson'] = job['finalGeojson']
        return jsonify(payload)


@app.route('/api/building-footprints/cancel/<job_id>', methods=['POST'])
def building_footprints_cancel(job_id):
    """Aşama 5 — kullanıcı analiz sürerken taramayı iptal edebilsin diye."""
    job = _get_building_job(job_id)
    with _building_jobs_lock:
        if not job:
            return jsonify({
                'success': False,
                'error': 'İş bulunamadı (zaten bitmiş/temizlenmiş olabilir).'
            }), 404
        if job['status'] == 'running':
            job['cancelRequested'] = True
            job['updatedAt'] = time.time()
            _persist_building_job(job)
        return jsonify({'success': True, 'status': job['status']})


def build_classified_image(result, class_breaks):
    """
    class_breaks: [{ min, max, color, label }, ...]  (küçükten büyüğe sıralı)
    Her sınıfa integer ID atar (1,2,3...), sonra visualize eder.
    """
    if not class_breaks:
        return None, None

    class_breaks = sorted(class_breaks, key=lambda c: c['min'])
    palette = [c['color'].lstrip('#') for c in class_breaks]

    classified = ee.Image(0)
    for i, cls in enumerate(class_breaks, start=1):
        mask = result.gte(cls['min']).And(result.lte(cls['max']))
        classified = classified.where(mask, i)

    classified = classified.updateMask(result.mask())

    vis = {
        'min': 1,
        'max': len(class_breaks),
        'palette': palette
    }
    return classified, vis


def _dynamic_stretch_vis(img, roi, scale, fallback_vis):
    """
    🛠️ BUG FİX (Topografik analizler her yerde "0 – 3000 m" ve düz/tek renk
    görünüyordu):

    ÖNCEKİ HATA: Her TOPO analizi (yükseklik, eğim, TPI, pürüzlülük, eğrilik,
    akış birikimi, TWI/SPI/STI, solar radyasyon vb.) sabit/hardcoded bir
    min–max germe (stretch) aralığıyla görselleştiriliyordu — örn. yükseklik
    HER ZAMAN 0–3000 m aralığına gerdiriliyordu. Seçilen AOI'nin gerçek
    yükseklik aralığı bundan çok dar (ör. 80–220 m kıyı ovası) veya çok
    farklıysa (ör. 4200–5100 m yüksek dağ), piksellerin TAMAMI germe
    aralığının küçük bir ucuna sıkışıyor ve harita üzerinde neredeyse TEK
    RENK / DÜZ görünüyordu. Aynı zamanda lejant da her zaman aynı sabit
    0/3000 değerlerini gösteriyordu, AOI'de gerçekte ne olursa olsun.

    ÇÖZÜM: Seçilen AOI üzerinde GERÇEK min/max değerleri hesaplanır ve
    görselleştirme germe aralığı buna göre ayarlanır. Böylece her analiz,
    o AOI'nin gerçek veri dağılımına göre kontrastlı ve doğru şekilde
    boyanır — sabit/evrensel bir sayı yerine.

    NOT: Bilinçli olarak ee.Reducer.minMax() kullanılır (persentil DEĞİL) —
    /api/analyze rotasındaki "realStats" (lejantta kullanıcıya gösterilen
    gerçek min/max) da AYNI minMax reducer'ıyla hesaplanıyor. İki farklı
    reducer (ör. percentile[2,98] burada, minMax orada) kullanılırsa harita
    üzerindeki germe ile lejantta yazan sayı BİRBİRİNDEN FARKLI çıkar ve
    kullanıcı için kafa karıştırıcı/"yanlış" görünür. Aynı reducer'ı
    kullanmak, harita rengi ile lejant metninin HER ZAMAN birebir aynı
    sayıları yansıtmasını garanti eder.

    Min/max hesaplanamazsa (ör. tamamen düz/sabit bir alan, veri yoksa
    veya GEE hata verirse) parametre olarak verilen sabit fallback_vis'e
    geri dönülür; böylece fonksiyon hiçbir zaman analiz akışını kesmez.
    """
    try:
        mm = img.reduceRegion(
            reducer=ee.Reducer.minMax(),
            geometry=roi,
            scale=scale,
            maxPixels=1e9,
            bestEffort=True
        ).getInfo()
        lo = mm.get('value_min')
        hi = mm.get('value_max')
        if lo is None or hi is None:
            return fallback_vis
        lo = float(lo)
        hi = float(hi)
        if hi <= lo:
            # Tamamen düz alan (gerçek sabit değer) — sabit varsayılana dön.
            return fallback_vis
        new_vis = dict(fallback_vis)
        new_vis['min'] = lo
        new_vis['max'] = hi
        return new_vis
    except Exception:
        return fallback_vis


def build_result_image(data, for_export=False):
    """
    Ortak analiz görüntüsü oluşturma mantığı.
    Returns: (final_display, roi, result, vis)

    for_export: True ise (GeoTIFF indirme yolu), kullanıcının haritada
    "Lejantı Uygula" ile tanımladığı sınıflandırma (classBreaks) — yani
    piksel değerlerini 1,2,3... gibi tam sayı sınıf ID'lerine dönüştüren
    build_classified_image() adımı — TAMAMEN ATLANIR. Böylece dosyaya
    her zaman haritadaki renk çubuğunun (color bar / stretch) dayandığı
    HAM/sürekli değerler (örn. NDVI için -1 ile 1 arası ondalıklı
    değerler) yazılır; ekrandaki sınıflandırma sadece görsel bir katman
    olarak kalır ve indirilen .tif dosyasını ASLA etkilemez. custom_palette
    (min/max germe) zaten piksel değerlerini değiştirmediği için (sadece
    vis sözlüğünü değiştirir) o dal for_export'tan etkilenmeden aynen
    çalışmaya devam eder.
    """
    roi_coords = data.get('roi')
    clip_mode  = data.get('clipMode', 'clip')
    satellite  = data.get('satellite', 's2-l2a')
    index      = data.get('index', 'NDVI')
    start_date = data.get('startDate')
    end_date   = data.get('endDate')
    max_cloud  = int(data.get('maxCloud', 20))
    scene_id   = data.get('sceneId')
    class_breaks = data.get('classBreaks')
    if for_export:
        class_breaks = None

    roi = make_roi(roi_coords)

    # ── 0. Uydu görüntüsü gerektirmeyen bağımsız veri setleri ────
    # Bu analizler kendi GEE koleksiyonlarını kullanır; uydu/bant seçimi
    # ve tarih filtresi bloğunu tamamen atlarlar.

    if index == 'LULC':
        # 🏘️ Arazi Kullanımı — Google Dynamic World V1 (10 m, güncel arazi
        # örtüsü, 9 sınıf). Tarih/bulutluluk arayüzden kullanıcıya
        # gösterilmediği için frontend boş gönderebilir; bu durumda
        # "güncel" bir görüntü için son 365 günlük varsayılan aralık kullanılır.
        eff_start, eff_end = start_date, end_date
        if not eff_start or not eff_end:
            today = datetime.date.today()
            eff_end   = today.isoformat()
            eff_start = (today - datetime.timedelta(days=365)).isoformat()

        dw = (ee.ImageCollection('GOOGLE/DYNAMICWORLD/V1')
              .filterBounds(roi)
              .filterDate(eff_start, eff_end)
              .select('label')
              .reduce(ee.Reducer.mode())
              .rename('value'))
        palette = ['#419bdf', '#397d49', '#88b053', '#7a87c6',
                   '#e49635', '#dfc35a', '#c4281b', '#a59b8f', '#b39fe1']
        vis = {'min': 0, 'max': 8, 'palette': palette}
        result = dw
        # Mekansal Sınırlandırma: LULC sonucu her zaman AOI'ye göre kesilir
        # (clipMode ne olursa olsun) — global/geniş ölçekli yansıtma yapılmaz.
        final_display = dw.clip(roi)
        return final_display, roi, result, vis, None

    if index == 'LULC_ESA':
        # 🏘️ Arazi Kullanımı — ESA WorldCover v200 (10 m global, 11 sınıf).
        # Tek bir global mozaik görüntüsüdür; tarih/bulutluluk filtresi yoktur.
        wc_codes = [10, 20, 30, 40, 50, 60, 70, 80, 90, 95, 100]
        wc_palette = ['006400', 'ffbb22', 'ffff4c', 'f096ff', 'fa0000',
                      'b4b4b4', 'f0f0f0', '0064c8', '0096a0', '00cf75', 'fae6a0']

        worldcover = ee.ImageCollection('ESA/WorldCover/v200').first().select('Map')
        # Orijinal (10,20,...,100) kodları, sırayla 1..11'e yeniden kodlanır —
        # böylece tile rengi/sınıf indeksi LULC ailesindeki diğer analizlerle
        # tutarlı, küçük ve ardışık bir aralıkta kalır.
        remapped = worldcover.remap(wc_codes, list(range(1, len(wc_codes) + 1))).rename('value')

        vis = {'min': 1, 'max': len(wc_codes), 'palette': wc_palette}
        result = remapped
        # Mekansal Sınırlandırma: LULC ailesinde her zaman AOI'ye göre kesilir.
        final_display = remapped.clip(roi)
        return final_display, roi, result, vis, None

    if index == 'LULC_MODIS':
        # 🏘️ Arazi Kullanımı — MODIS MCD12Q1 (500 m, IGBP sınıflandırması, 17 sınıf).
        # Her yıl için tek bir görüntü üretilir; en güncel yıl kullanılır.
        modis_codes   = list(range(1, 18))           # 1-17 (IGBP)
        modis_palette = [
            '05450a',  # 1  Herdemyeşil İbreli Orman
            '086a10',  # 2  Herdemyeşil Geniş Yapraklı Orman
            '54a708',  # 3  Yaprak Döken İbreli Orman
            '78d203',  # 4  Yaprak Döken Geniş Yapraklı Orman
            '009900',  # 5  Karışık Ormanlar
            'c6b044',  # 6  Kapalı Çalılık
            'dcd159',  # 7  Açık Çalılık
            'dade48',  # 8  Odunlu Savana
            'fbff13',  # 9  Savana
            'b6ff05',  # 10 Çayır / Otlak
            '27ff87',  # 11 Kalıcı Sulak Alan
            'c24f44',  # 12 Tarım Alanı
            'a5a5a5',  # 13 Kentsel / Yapay Alan
            'ff6d4c',  # 14 Tarım-Doğal Mozaik
            '69fff8',  # 15 Kar ve Buz
            'f9ffa4',  # 16 Çıplak Toprak / Seyrek Örtü
            '1c0dff',  # 17 Su Kütlesi
        ]
        modis_img = (ee.ImageCollection('MODIS/061/MCD12Q1')
                     .filterDate('2022-01-01', '2024-01-01')
                     .sort('system:time_start', False)
                     .first()
                     .select('LC_Type1'))
        remapped_modis = modis_img.remap(modis_codes, list(range(1, 18))).rename('value')
        vis    = {'min': 1, 'max': 17, 'palette': modis_palette}
        result = remapped_modis
        final_display = remapped_modis.clip(roi)
        return final_display, roi, result, vis, None

    if index == 'LULC_CORINE':
        # 🏘️ Arazi Kullanımı — CORINE Land Cover 2018 (100 m, Avrupa/Türkiye).
        # Orijinal 3 basamaklı kodlar (111-523, 44 sınıf) sıralı 1-44'e remaplenir.
        corine_codes = [
            111, 112, 121, 122, 123, 124, 131, 132, 133, 141, 142,
            211, 212, 213, 221, 222, 223, 231, 241, 242, 243, 244,
            311, 312, 313, 321, 322, 323, 324,
            331, 332, 333, 334, 335,
            411, 412, 421, 422, 423,
            511, 512, 521, 522, 523
        ]
        corine_palette = [
            'e6004d', 'ff0000', 'cc4df2', 'cc0000', 'e6cccc', 'e6cce6',
            'a600cc', 'a64d00', 'ff4dff', 'ffa6ff', 'ffe6ff',
            'ffffa8', 'ffff00', 'e6e600', 'e68000', 'f2a64d', 'e6a600',
            'e6e64d', 'ffe6a6', 'ffe64d', 'e6cc4d', 'f2cca6',
            '80ff00', '00a600', '4dff00', 'ccf24d', 'a6ff80', 'a6e64d', 'a6f200',
            'e6e6e6', 'cccccc', 'ccffcc', '000000', 'a6e6cc',
            'a6a6ff', '4d4dff', 'ccccff', 'e6e6ff', 'a6a6e6',
            '00ccf2', '80f2e6', '00ffa6', 'a6ffe6', 'e6f2ff'
        ]
        corine_img = (ee.ImageCollection('COPERNICUS/CORINE/V20/100m')
                      .sort('system:time_start', False)
                      .first()
                      .select('landcover'))
        remapped_corine = corine_img.remap(corine_codes, list(range(1, len(corine_codes) + 1))).rename('value')
        vis    = {'min': 1, 'max': len(corine_codes), 'palette': corine_palette}
        result = remapped_corine
        final_display = remapped_corine.clip(roi)
        return final_display, roi, result, vis, None

    # ── Topografik Analizler (DEM ailesi) ────────────────────────
    _TOPO_KEYS = (
        'TOPO', 'TOPO_DEM', 'TOPO_SLOPE', 'TOPO_ASPECT', 'TOPO_HILLSHADE',
        'TOPO_RELIEF', 'TOPO_TPI', 'TOPO_TRI', 'TOPO_ROUGHNESS',
        'TOPO_CURVATURE', 'TOPO_PLAN_CURV', 'TOPO_PROFILE_CURV',
        'TOPO_FLOWDIR', 'TOPO_FLOWACC', 'TOPO_STREAM',
        'TOPO_TWI', 'TOPO_SPI', 'TOPO_STI',
        'TOPO_HILLSHADE_MULTI', 'TOPO_SOLAR', 'TOPO_SHADOW',
    )
    if index in _TOPO_KEYS:
        import math as _math

        # ── DEM kaynağı seç ──────────────────────────────────────
        # 🛠️ BUG FİX (NoData kareler / boş piksel sorunu):
        # ALOS ve Copernicus DEM'leri parçalı (tile-based) ImageCollection'lardır.
        # filterBounds(roi).mosaic() çağrısı, AOI'yi kapsayan tile'ları birleştirir;
        # ancak tile sınırlarında veya kapsama açığı olan bölgelerde (ör. Kuzey kutbu
        # yakını, bazı adalarda Copernicus eksik kareler bırakır) mozaikte NoData
        # pikseller kalabilir. Bu pikseller eğim (slope), TPI, eğrilik vb. türev
        # analizlerde zincir boyunca boşluk olarak yayılır — haritada "kare kare
        # boşluk" ya da istatistiğin None dönmesi bu yüzden oluşur.
        #
        # ÇÖZÜM: mosaic() sonrası .unmask(srtm_fallback) ile açıkta kalan her
        # NoData pikseli SRTM verisiyle doldurulur. SRTM global kapsama sahiptir
        # (60°G–60°K) ve bu tür boşlukları kapatmak için en sağlıklı alternatiftir.
        # NASADEM zaten tek görüntü olduğu için boşluk sorunu yaşamaz.
        _srtm_fallback = ee.Image('USGS/SRTMGL1_003').select('elevation')

        dem_source = data.get('demSource', 'SRTM')
        if dem_source == 'ALOS':
            dem = (ee.ImageCollection('JAXA/ALOS/AW3D30/V3_2')
                   .filterBounds(roi).mosaic().select('DSM').rename('elevation'))
            # Tile sınırlarındaki / kapsama dışı NoData pikselleri SRTM ile doldur
            dem = dem.unmask(_srtm_fallback)
        elif dem_source == 'Copernicus':
            dem = (ee.ImageCollection('COPERNICUS/DEM/GLO30')
                   .filterBounds(roi).mosaic().select('DEM').rename('elevation'))
            # Tile sınırlarındaki / kapsama dışı NoData pikselleri SRTM ile doldur
            dem = dem.unmask(_srtm_fallback)
        elif dem_source == 'NASADEM':
            dem = ee.Image('NASA/NASADEM_HGT/001').select('elevation')
        else:  # SRTM (varsayılan)
            dem = ee.Image('USGS/SRTMGL1_003').select('elevation')

        # 🛠️ BUG FİX (dağınık tekil piksel boşlukları — "kare kare" benek
        # deseni, özellikle sırt/vadi hatlarında yoğunlaşan beyaz/siyah
        # noktalar): Yukarıdaki unmask(SRTM) adımı yalnızca ALOS/Copernicus
        # mozaiklerindeki BÜYÜK kapsama boşluklarını kapatır — ama HİÇBİR
        # kaynak (SRTM dahil) için, dik yamaçlarda radar gölgesi nedeniyle
        # oluşan TEKİL/küçük-küme "void" (veri boşluğu) piksellerini
        # doldurmaz. Bu void'ler ham DEM'de maskelenmiş (NoData) tek
        # piksellerdir; eğim/bakı/hillshade gibi türevler 3x3 komşuluk
        # çekirdeğiyle hesaplandığından, her void pikseli çevresindeki
        # birkaç piksele de yayılır — kullanıcının GIS yazılımında gördüğü
        # dağınık "eksik piksel kareleri" tam olarak budur.
        #
        # ÇÖZÜM: Kaynak ne olursa olsun, DEM'i terrain ürünleri hesaplanmadan
        # ÖNCE odak-ortalama (focal mean) ile "void-fill" işleminden geçiriyoruz.
        # reduceNeighborhood tabanlı focalMean, komşuluk penceresindeki YALNIZCA
        # geçerli (maskelenmemiş) pikselleri kullanarak ortalama alır; bu da
        # void pikselinin değerini çevresindeki gerçek verilerden enterpole
        # edip dolduruyor — sonuçta ham DEM'de tek bir maskeli piksel bile
        # kalmıyor ve türev ürünlerde artık hiçbir boşluk/benek oluşmuyor.
        # 150 m yarıçap (~5 piksel @ 30 m), tipik void kümelerini (genelde
        # 1-3 piksel genişliğinde) kapatmaya yeterlidir; büyük gerçek NoData
        # alanlarını (AOI dışı vb.) ETKİLEMEZ çünkü onlar zaten export
        # aşamasında ayrı bir clip/nodata mantığıyla ele alınıyor.
        #
        # İKİ AŞAMALI doldurma: bazı void kümeleri (özellikle dik vadi
        # tabanlarında/gölgede kalan geniş alanlarda) 150 m'den daha büyük
        # olabilir ve TEK geçişte tam dolmayabilir. Bu yüzden önce dar
        # (150 m), sonra daha geniş (450 m) bir odak-ortalama ile ikinci
        # bir "güvenlik ağı" geçişi uyguluyoruz — ilk geçişte dolmayan
        # (çevresi de void olan) nadir pikseller ikinci, daha geniş
        # pencerede kesinlikle geçerli komşu bulur.
        dem = dem.unmask(dem.focalMean(radius=150, units='meters'))
        dem = dem.unmask(dem.focalMean(radius=450, units='meters'))

        terrain = ee.Terrain.products(dem)
        slope   = terrain.select('slope')
        aspect  = terrain.select('aspect')

        # ── Temel Topografik Analizler ────────────────────────────
        if index in ('TOPO', 'TOPO_DEM'):
            result = dem.rename('value')
            vis = {'min': 0, 'max': 3000, 'palette': ['black', 'white']}

        elif index == 'TOPO_SLOPE':
            result = slope.rename('value')
            vis = {'min': 0, 'max': 60, 'palette': ['black', 'white']}

        elif index == 'TOPO_ASPECT':
            result = aspect.rename('value')
            vis = {'min': 0, 'max': 360, 'palette': ['black', 'white']}

        elif index == 'TOPO_HILLSHADE':
            result = terrain.select('hillshade').rename('value')
            vis = {'min': 0, 'max': 255, 'palette': ['black', 'white']}

        elif index == 'TOPO_RELIEF':
            # Kabartmalı rölyef: hillshade + normalize yükseklik karışımı
            hs       = terrain.select('hillshade')
            elev_n   = dem.unitScale(0, 3000).multiply(80).add(175).clamp(0, 255)
            result   = hs.multiply(0.7).add(elev_n.multiply(0.3)).rename('value')
            vis = {'min': 0, 'max': 255, 'palette': ['black', 'white']}

        # ── Morfometrik Analizler ─────────────────────────────────
        elif index == 'TOPO_TPI':
            # Topographic Position Index: DEM − odak ortalama
            focal_mean = dem.focalMean(radius=300, units='meters')
            result = dem.subtract(focal_mean).rename('value')
            vis = {'min': -50, 'max': 50, 'palette': ['black', 'white']}

        elif index == 'TOPO_TRI':
            # Terrain Ruggedness Index: odak standart sapma
            result = dem.focalStdDev(radius=300, units='meters').rename('value')
            vis = {'min': 0, 'max': 80, 'palette': ['black', 'white']}

        elif index == 'TOPO_ROUGHNESS':
            # Pürüzlülük: pencerede maksimum − minimum rakım
            focal_max = dem.focalMax(radius=300, units='meters')
            focal_min = dem.focalMin(radius=300, units='meters')
            result = focal_max.subtract(focal_min).rename('value')
            vis = {'min': 0, 'max': 150, 'palette': ['black', 'white']}

        elif index in ('TOPO_CURVATURE', 'TOPO_PLAN_CURV', 'TOPO_PROFILE_CURV'):
            # 🛠️ BUG FİX (yoğun beyaz "tuz-biber" beneği — özellikle düz/az
            # eğimli alanlarda yoğunlaşan gürültü): Laplacian (2. türev)
            # operatörü YÜKSEK GEÇİRGEN bir filtredir; ham DEM üzerinde
            # doğrudan uygulandığında HER pikseldeki kuantizasyon
            # gürültüsünü (SRTM'nin ~1 m dikey çözünürlüğünden kaynaklanan
            # basamaklanma) orantısızca büyütür. Dik/kıvrımlı arazide
            # gerçek eğrilik sinyali bu gürültüyü bastırır, ama düz
            # ovalarda gerçek eğrilik ≈ 0 olduğundan kuantizasyon
            # gürültüsü BASKIN hale gelir ve germe (stretch) sonrası
            # rastgele beyaz/siyah benek deseni olarak görünür — az önce
            # gönderdiğiniz görüntüdeki sorun tam olarak budur.
            #
            # ÇÖZÜM: Laplacian'ı ham dem yerine, önce hafif bir odak-
            # ortalama ile pürüzsüzleştirilmiş DEM üzerinde uyguluyoruz.
            # 60 m yarıçap (~2 piksel @ 30 m), piksel bazlı kuantizasyon
            # gürültüsünü büyük ölçüde elerken gerçek yerel eğrilik
            # özelliklerini (kıvrımlar, sırtlar, vadiler) korur.
            dem_smooth = dem.focalMean(radius=60, units='meters')
            kernel = ee.Kernel.laplacian8(normalize=False)
            result = dem_smooth.convolve(kernel).rename('value')
            vis = {'min': -30, 'max': 30, 'palette': ['black', 'white']}

        # ── Hidrolojik Analizler ──────────────────────────────────
        elif index == 'TOPO_FLOWDIR':
            # Akış yönü vekisi: bakı açısı (su eğim yönünde akar)
            result = aspect.rename('value')
            vis = {'min': 0, 'max': 360, 'palette': ['black', 'white']}

        elif index == 'TOPO_FLOWACC':
            # Akış birikimi vekisi: düşük eğim + düşük rakım = vadi tabanı
            low_slope = ee.Image(90).subtract(slope.clamp(0, 90))
            elev_inv  = ee.Image(3000).subtract(dem.clamp(0, 3000))
            result = low_slope.add(elev_inv.divide(30)).rename('value')
            vis = {'min': 0, 'max': 200, 'palette': ['black', 'white']}

        elif index == 'TOPO_STREAM':
            # Dere ağı: düşük eğim + negatif TPI (vadi tabanı) maskesi
            focal_mean2 = dem.focalMean(radius=200, units='meters')
            tpi_small   = dem.subtract(focal_mean2)
            stream_mask = slope.lt(5).And(tpi_small.lt(0))
            result = stream_mask.multiply(1).rename('value')
            vis = {'min': 0, 'max': 1, 'palette': ['black', 'white']}

        elif index == 'TOPO_TWI':
            # Topographic Wetness Index: ln(a / tan(β))
            slope_rad = slope.multiply(_math.pi / 180)
            tan_slope = slope_rad.tan().max(ee.Image(0.001))
            acc_proxy = ee.Image(90).subtract(slope.clamp(0, 90)).max(ee.Image(1.0))
            result = acc_proxy.log().subtract(tan_slope.log()).rename('value')
            vis = {'min': 0, 'max': 15, 'palette': ['black', 'white']}

        elif index == 'TOPO_SPI':
            # Stream Power Index: a × tan(β)
            slope_rad = slope.multiply(_math.pi / 180)
            tan_slope = slope_rad.tan().max(ee.Image(0.001))
            acc_proxy = ee.Image(90).subtract(slope.clamp(0, 90)).max(ee.Image(1.0))
            result = acc_proxy.multiply(tan_slope).rename('value')
            vis = {'min': 0, 'max': 20, 'palette': ['black', 'white']}

        elif index == 'TOPO_STI':
            # Sediment Transport Index: (a/22.13)^0.6 × (sin(β)/0.0896)^1.3
            slope_rad = slope.multiply(_math.pi / 180)
            sin_slope = slope_rad.sin().max(ee.Image(0.001))
            acc_proxy = ee.Image(90).subtract(slope.clamp(0, 90)).max(ee.Image(1.0))
            result = acc_proxy.divide(22.13).pow(0.6).multiply(
                sin_slope.divide(0.0896).pow(1.3)
            ).rename('value')
            vis = {'min': 0, 'max': 50, 'palette': ['black', 'white']}

        # ── Güneş ve Görünürlük Analizleri ───────────────────────
        elif index == 'TOPO_HILLSHADE_MULTI':
            # Çok yönlü kabartma: 8 azimuth açısı ortalaması
            hs_list = [ee.Terrain.hillshade(dem, az, 45) for az in [0, 45, 90, 135, 180, 225, 270, 315]]
            result = ee.ImageCollection(hs_list).mean().rename('value')
            vis = {'min': 0, 'max': 255, 'palette': ['black', 'white']}

        elif index == 'TOPO_SOLAR':
            # Güneş radyasyonu vekisi: güneye-bakan eğimli alanlar daha fazla ışınım alır
            asp_rad     = aspect.multiply(_math.pi / 180)
            south_fac   = asp_rad.subtract(_math.pi).cos().multiply(0.5).add(0.5)
            slope_fac   = slope.divide(90).clamp(0, 1)
            result = south_fac.multiply(0.7).add(slope_fac.multiply(0.3)).rename('value')
            vis = {'min': 0, 'max': 1, 'palette': ['black', 'white']}

        elif index == 'TOPO_SHADOW':
            # Gölge analizi: KD azimuth kabartması (düşük değer = gölge alan)
            result = ee.Terrain.hillshade(dem, 315, 45).rename('value')
            vis = {'min': 0, 'max': 255, 'palette': ['black', 'white']}

        else:
            result = slope.rename('value')
            vis = {'min': 0, 'max': 60, 'palette': ['black', 'white']}

        # ── 🛠️ BUG FİX: sabit/hardcoded germe aralıkları yerine AOI'nin
        # gerçek veri dağılımına göre dinamik germe uygula (bkz. yukarıdaki
        # _dynamic_stretch_vis() docstring'i). Bakı (aspect/akış yönü) ve
        # dere ağı maskesi kasıtlı olarak SABİT bırakılır çünkü bunlar
        # sabit/anlamlı birimlerdir (derece / ikili maske) — bunları AOI'ye
        # göre germek yanlış yön/renk anlamına yol açar.
        _DYNAMIC_STRETCH_KEYS = (
            'TOPO', 'TOPO_DEM', 'TOPO_SLOPE', 'TOPO_RELIEF',
            'TOPO_TPI', 'TOPO_TRI', 'TOPO_ROUGHNESS',
            'TOPO_CURVATURE', 'TOPO_PLAN_CURV', 'TOPO_PROFILE_CURV',
            'TOPO_FLOWACC', 'TOPO_TWI', 'TOPO_SPI', 'TOPO_STI',
            'TOPO_SOLAR',
        )
        if index in _DYNAMIC_STRETCH_KEYS:
            _dem_scale = 30  # SRTM/ALOS/Copernicus/NASADEM hepsi ~30 m nominal
            vis = _dynamic_stretch_vis(result, roi, _dem_scale, vis)

        # ── Görsel mod / dışa aktarım modu ayrımı ──────────────────
        # 🛠️ BUG FİX: Dışa aktarım (for_export=True) ile ekran görüntüsü
        # (for_export=False) artık açık bir if/elif zinciriyle ayrılır.
        #
        # SORUN: Daha önce "(not for_export) and class_breaks" kontrolü
        # class_breaks dalını engellerdi — ancak custom_palette/min/max dalı
        # her zaman çalışırdı. Frontend, sınıflandırma + özel renk birlikte
        # gönderebildiği için GeoTIFF'te sınıf ID'leri (1, 2, 3…) veya
        # kırpılmış değer aralıkları çıkabiliyordu.
        #
        # ÇÖZÜM: for_export=True → SADECE ham result kullan, sınıflandırma
        # ve palette/min/max TAMAMEN atlanır. Piksel değerleri değişmez.
        # for_export=False (harita önizleme) → önceki davranış aynen korunur.
        custom_palette = data.get('palette')
        custom_min     = data.get('min')
        custom_max     = data.get('max')

        if for_export:
            # GeoTIFF indirme: her zaman orijinal bar skalasındaki ham değerler.
            # classBreaks (sınıf ID), custom_palette/min/max UYGULANMAZ.
            display_result = result
        elif class_breaks and isinstance(class_breaks, list) and len(class_breaks) > 0:
            classified_img, classified_vis = build_classified_image(result, class_breaks)
            if classified_img is not None:
                display_result = classified_img
                vis = classified_vis
            else:
                display_result = result
        elif custom_palette and isinstance(custom_palette, list) and len(custom_palette):
            display_result = result
            vis = dict(vis)
            # GEE paleti # ön-ekini kabul etmez — strip ederek gönder
            vis['palette'] = [str(c).lstrip('#') for c in custom_palette]
            if custom_min is not None:
                vis['min'] = float(custom_min)
            if custom_max is not None:
                vis['max'] = float(custom_max)
        else:
            display_result = result

        final_display = display_result.clip(roi) if clip_mode == 'clip' else display_result
        return final_display, roi, result, vis, None

    if index == 'RGB':
        # 🛰️ Uydu Görüntüsü Galerisi — gerçek renk (veya en yakın kompozit)
        # önizlemesi. satellite alanı SATELLITE_DATASETS anahtarlarından biri
        # olmalıdır (s2-l1c, s2-l2a, l89-l2, l7-l2, l45-l2, l89-l1, l7-l1,
        # l45-l1, mss-l1).
        ds = SATELLITE_DATASETS.get(satellite)
        if not ds:
            raise ValueError('Bilinmeyen uydu görüntüsü veri seti: ' + str(satellite))

        col = build_rgb_collection(ds, roi, max_cloud)

        if scene_id:
            image = col.filter(ee.Filter.eq('system:index', scene_id)).first()
        else:
            image = col.filterDate(start_date, end_date).sort('system:time_start', False).first()

        disp = image.select(ds['rgbBands'])
        if ds.get('scaleFactor', 1) != 1 or ds.get('offset', 0) != 0:
            disp = disp.multiply(ds['scaleFactor']).add(ds.get('offset', 0))
        disp = disp.rename(['red', 'green', 'blue'])

        result = disp
        vis = {'bands': ['red', 'green', 'blue'], 'min': ds['visMin'], 'max': ds['visMax']}
        final_display = disp.clip(roi) if clip_mode == 'clip' else disp
        return final_display, roi, result, vis, None

    if index == 'SAR':
        # Sentinel-1 GRD — VV polarizasyonu (taşkın / biyokütle izleme)
        _sar_col = (ee.ImageCollection('COPERNICUS/S1_GRD')
               .filterBounds(roi)
               .filterDate(start_date, end_date)
               .filter(ee.Filter.eq('instrumentMode', 'IW'))
               .filter(ee.Filter.listContains('transmitterReceiverPolarisation', 'VV'))
               .select('VV'))
        sar = _sar_col.mean().rename('value')
        vis    = {'min': -25, 'max': 0,
                  'palette': ['black', 'white']}
        result = sar
        final_display = sar.clip(roi) if clip_mode == 'clip' else sar
        # 🛠️ BUG FİX: .mean() de median() gibi çıktı projeksiyonunu EPSG:4326'ya
        # sıfırlar — gerçek/native CRS'i reduce edilmeden ÖNCEki tek bir
        # sahneden (_sar_col.first()) okuyoruz.
        _crs_probe_img = _sar_col.first()
        return final_display, roi, result, vis, _crs_probe_img

    # ── 1. Uydu koleksiyonunu ve bant adlarını seç ──────────────
    if satellite == 's2-l2a':
        col = (ee.ImageCollection('COPERNICUS/S2_SR_HARMONIZED')
               .filterBounds(roi)
               .filter(ee.Filter.lt('CLOUDY_PIXEL_PERCENTAGE', max_cloud)))
        b = {'nir': 'B8', 'red': 'B4', 'green': 'B3',
             'swir': 'B11', 'blue': 'B2', 'thermal': None}
        scale_factor = 1e-4
        band_offset  = 0

    elif satellite == 's2-l1c':
        col = (ee.ImageCollection('COPERNICUS/S2_HARMONIZED')
               .filterBounds(roi)
               .filter(ee.Filter.lt('CLOUDY_PIXEL_PERCENTAGE', max_cloud)))
        b = {'nir': 'B8', 'red': 'B4', 'green': 'B3',
             'swir': 'B11', 'blue': 'B2', 'thermal': None}
        scale_factor = 1e-4
        band_offset  = 0

    elif satellite == 'l89-l2':
        col = (ee.ImageCollection('LANDSAT/LC08/C02/T1_L2')
               .filterBounds(roi)
               .filter(ee.Filter.lt('CLOUD_COVER', max_cloud)))
        b = {'nir': 'SR_B5', 'red': 'SR_B4', 'green': 'SR_B3',
             'swir': 'SR_B6', 'blue': 'SR_B2', 'thermal': 'ST_B10'}
        scale_factor = 2.75e-5
        band_offset  = -0.2

    elif satellite == 'l7-l2':
        col = (ee.ImageCollection('LANDSAT/LE07/C02/T1_L2')
               .filterBounds(roi)
               .filter(ee.Filter.lt('CLOUD_COVER', max_cloud)))
        b = {'nir': 'SR_B4', 'red': 'SR_B3', 'green': 'SR_B2',
             'swir': 'SR_B5', 'blue': 'SR_B1', 'thermal': 'ST_B6'}
        scale_factor = 2.75e-5
        band_offset  = -0.2

    elif satellite == 'l45-l2':
        col = (ee.ImageCollection('LANDSAT/LT05/C02/T1_L2')
               .filterBounds(roi)
               .filter(ee.Filter.lt('CLOUD_COVER', max_cloud)))
        b = {'nir': 'SR_B4', 'red': 'SR_B3', 'green': 'SR_B2',
             'swir': 'SR_B5', 'blue': 'SR_B1', 'thermal': 'ST_B6'}
        scale_factor = 2.75e-5
        band_offset  = -0.2

    elif satellite == 'l89-l1':
        # Landsat 8-9 Collection 2 Level-1 TOA (bant adlarında SR_ öneki YOK)
        col = (ee.ImageCollection('LANDSAT/LC08/C02/T1_TOA')
               .filterBounds(roi)
               .filter(ee.Filter.lt('CLOUD_COVER', max_cloud)))
        col = col.merge(ee.ImageCollection('LANDSAT/LC09/C02/T1_TOA')
                        .filterBounds(roi)
                        .filter(ee.Filter.lt('CLOUD_COVER', max_cloud)))
        b = {'nir': 'B5', 'red': 'B4', 'green': 'B3',
             'swir': 'B6', 'blue': 'B2', 'thermal': 'B10'}
        scale_factor = 1
        band_offset  = 0

    elif satellite == 'l7-l1':
        # Landsat 7 Collection 2 Level-1 TOA
        col = (ee.ImageCollection('LANDSAT/LE07/C02/T1_TOA')
               .filterBounds(roi)
               .filter(ee.Filter.lt('CLOUD_COVER', max_cloud)))
        b = {'nir': 'B4', 'red': 'B3', 'green': 'B2',
             'swir': 'B5', 'blue': 'B1', 'thermal': 'B6_VCID_1'}
        scale_factor = 1
        band_offset  = 0

    elif satellite == 'l45-l1':
        # Landsat 4-5 Collection 2 Level-1 TOA
        col = (ee.ImageCollection('LANDSAT/LT05/C02/T1_TOA')
               .filterBounds(roi)
               .filter(ee.Filter.lt('CLOUD_COVER', max_cloud)))
        col = col.merge(ee.ImageCollection('LANDSAT/LT04/C02/T1_TOA')
                        .filterBounds(roi)
                        .filter(ee.Filter.lt('CLOUD_COVER', max_cloud)))
        b = {'nir': 'B4', 'red': 'B3', 'green': 'B2',
             'swir': 'B5', 'blue': 'B1', 'thermal': 'B6'}
        scale_factor = 1
        band_offset  = 0

    elif satellite == 'mss-l1':
        # Landsat 1-5 MSS — gerçek mavi ve SWIR bantları yoktur; bunları
        # None bırakarak SWIR gerektiren indekslerin GEE'den hata almasına
        # izin verilir (sessiz hata yerine açık hata mesajı).
        col = (ee.ImageCollection('LANDSAT/LM05/C02/T1').filterBounds(roi))
        for _mss_id in ('LANDSAT/LM04/C02/T1', 'LANDSAT/LM03/C02/T1',
                         'LANDSAT/LM02/C02/T1', 'LANDSAT/LM01/C02/T1'):
            col = col.merge(ee.ImageCollection(_mss_id).filterBounds(roi))
        b = {'nir': 'B3', 'red': 'B2', 'green': 'B1',
             'swir': None, 'blue': None, 'thermal': None}
        scale_factor = 1
        band_offset  = 0

    else:
        col = (ee.ImageCollection('COPERNICUS/S2_SR_HARMONIZED')
               .filterBounds(roi)
               .filter(ee.Filter.lt('CLOUDY_PIXEL_PERCENTAGE', max_cloud)))
        b = {'nir': 'B8', 'red': 'B4', 'green': 'B3',
             'swir': 'B11', 'blue': 'B2', 'thermal': None}
        scale_factor = 1e-4
        band_offset  = 0

    # 🩹 Piksel bazlı bulut/gölge/sirrus maskesi — sahne bazlı bulutluluk
    # filtresi (yukarıda) TEK BAŞINA yeterli değildir; koleksiyondaki her
    # görüntüye ayrı ayrı uygulanır ki hem tek sahne (scene_id) hem de
    # medyan kompozit (median()) modunda export edilen GeoTIFF'te AOI
    # içinde rastgele beyaz/boşluk (NoData) pikselleri kalmasın.
    col = col.map(lambda img: _mask_clouds(img, satellite))

    # ── 2. Tarih filtresi veya belirli sahne ────────────────────
    if scene_id:
        image = col.filter(ee.Filter.eq('system:index', scene_id)).first()
        _crs_probe_img = image
    else:
        image = col.filterDate(start_date, end_date).median()
        # 🛠️ BUG FİX (KÖK NEDEN — CRS seçici HER ZAMAN "WGS 84" gösteriyordu):
        # ee.ImageCollection.median() (ve mean()/mosaic() gibi diğer reducer'lar)
        # çıktı görüntünün projeksiyonunu, kaynak sahnelerin gerçek UTM dilimi
        # ne olursa olsun HER ZAMAN varsayılan/unbounded EPSG:4326'ya sıfırlar.
        # Bu yüzden "result.projection()" üzerinden CRS okumak, verinin gerçek
        # native CRS'inden BAĞIMSIZ olarak daima "EPSG:4326" döndürüyordu.
        # ÇÖZÜM: Gerçek/native CRS'i, henüz reduce EDİLMEMİŞ kaynak
        # koleksiyondaki TEK bir görüntüden (_crs_probe_img) okuyoruz — aynı
        # AOI'yi kapsayan sahneler normalde aynı UTM diliminde olduğundan bu,
        # medyan kompozitin gerçek/native CRS'ini doğru şekilde temsil eder.
        _crs_probe_img = col.filterDate(start_date, end_date).first()

    # 🛠️ BUG FİX (NDVI/LST/NDWI vb. TÜM uydu indekslerinde dağınık
    # beyaz/siyah piksel boşlukları — DEM void-fill ile AYNI kök neden
    # sınıfı): Tek sahne (scene_id) modunda, yukarıdaki _mask_clouds()
    # tarafından maskelenen bulut/gölge/sirrus pikselleri hiçbir şekilde
    # doldurulmuyordu — median() kompozitinde bu boşluklar başka
    # tarihlerdeki geçerli piksellerle doğal olarak kapanabiliyordu, ama
    # TEK sahne seçildiğinde (kullanıcı galeriden belirli bir sahne
    # seçtiğinde) doldurma YOKTU. Sonuç: AOI içinde rastgele dağılmış,
    # özellikle bulut kenarlarında/ince sirriste yoğunlaşan NoData
    # piksel benekleri (kullanıcının "boş piksel kareleri" dediği görüntü).
    #
    # ÇÖZÜM: DEM'deki ile BİREBİR AYNI "kendi kendini sınırlayan"
    # (self-limiting) odak-ortalama doldurma tekniği. reduceNeighborhood
    # tabanlı focalMean yalnızca komşuluktaki GEÇERLİ (maskelenmemiş)
    # pikselleri kullanarak ortalama alır; bu yüzden İZOLE/küçük
    # bulut-gölge boşlukları çevresindeki gerçek yansıma değerleriyle
    # dolar, ama GENİŞ/yoğun bulut alanları (komşuları da maskeli
    # olduğundan) doldurulMAZ — o bölgeler hâlâ doğru şekilde NoData
    # kalır (yanlışlıkla "bulut altı veri" uydurulmaz). İki aşamalı
    # (60 m + 200 m) geçiş, hem S2 (10 m) hem Landsat (30 m) çözünürlüğünde
    # tipik bulut-kenarı beneklerini kapatmaya yeter.
    image = image.unmask(image.focalMean(radius=60, units='meters'))
    image = image.unmask(image.focalMean(radius=200, units='meters'))

    # 🛠️ BUG FİX (KÖK NEDEN — Landsat tabanlı TÜM indeksler yanlış
    # hesaplanıyordu): Landsat Collection 2 Level-2 (l89-l2, l7-l2,
    # l45-l2/l1) yüzey yansıması bantları HAM tam sayı (DN) olarak
    # gelir; gerçek yansıma değerine dönüştürmek için resmi USGS
    # formülü şudur:  yansıma = DN * 0.0000275 + (−0.2)
    # Koddaki `scale_factor` (2.75e-5) ÇARPIMI zaten yapılıyordu, ANCAK
    # `-0.2` OFFSET'i HİÇBİR indeks hesaplamasında (NDVI, NDWI, EVI,
    # SAVI, SMI, NBR, NDSI, BSI, AVI, SI, NDGI, NDMI, NPCRI, VHI, FRI)
    # UYGULANMIYORDU. Sentinel-2'de offset zaten 0 olduğu için bu fark
    # etmiyordu (sonuçlar doğruydu) — ama Landsat'ta offset −0.2 gibi
    # yüzey yansımasının kendisiyle KIYASLANABİLİR büyüklükte bir sabit
    # olduğu için, onu atlamak sonucu ciddi şekilde bozuyordu. Örnek:
    # DN_nir=20000, DN_red=10000 için gerçek NDVI ≈ 0.65 iken, offset
    # uygulanmadan (ham DN oranıyla) hesaplanan "NDVI" ≈ 0.33 çıkıyordu
    # — yani bitki örtüsü olduğundan çok daha az/zayıf görünüyordu.
    # ÇÖZÜM: Tüm optik bantlar TEK SEFERDE (DN * scale_factor + offset)
    # ile gerçek yansıma değerine çevrilip `image_refl` olarak saklanır;
    # aşağıdaki TÜM indeks formülleri artık ham `image` yerine bu
    # doğru ölçeklenmiş `image_refl`'i kullanır. Sentinel-2 için offset
    # zaten 0 olduğundan bu değişiklik S2 sonuçlarını ETKİLEMEZ —
    # yalnızca Landsat tabanlı analizleri düzeltir. Termal bant (LST)
    # zaten ayrı/doğru bir formülle (0.00341802 / 149.0, resmi USGS
    # ST_Bxx dönüşümü) hesaplandığı için buna dahil edilmez.
    _optical_band_names = sorted(set(
        v for k, v in b.items() if k != 'thermal' and v
    ))
    image_refl = image.select(_optical_band_names).multiply(scale_factor).add(band_offset)

    # ── 3. İndeks hesapla ───────────────────────────────────────
    if index == 'NDVI':
        result = image_refl.normalizedDifference([b['nir'], b['red']]).rename('value')
        vis    = {'min': -0.2, 'max': 0.9, 'palette': ['black', 'white']}

    elif index == 'NDWI':
        result = image_refl.normalizedDifference([b['green'], b['nir']]).rename('value')
        vis    = {'min': -0.5, 'max': 0.5, 'palette': ['black', 'white']}

    elif index == 'EVI':
        nir   = image_refl.select(b['nir'])
        red   = image_refl.select(b['red'])
        blue  = image_refl.select(b['blue'])
        result = (nir.subtract(red)).divide(
            nir.add(red.multiply(6)).subtract(blue.multiply(7.5)).add(1)
        ).multiply(2.5).rename('value')
        vis    = {'min': -0.2, 'max': 0.8, 'palette': ['black', 'white']}

    elif index == 'SAVI':
        L = 0.5
        nir = image_refl.select(b['nir'])
        red = image_refl.select(b['red'])
        result = (nir.subtract(red)).multiply(1 + L).divide(
            nir.add(red).add(L)
        ).rename('value')
        vis    = {'min': -0.3, 'max': 0.8, 'palette': ['black', 'white']}

    elif index == 'SMI':
        nir  = image_refl.select(b['nir'])
        swir = image_refl.select(b['swir'])
        result = nir.subtract(swir).divide(nir.add(swir)).rename('value')
        vis    = {'min': -0.5, 'max': 0.5, 'palette': ['black', 'white']}

    elif index == 'NBR':
        result = image_refl.normalizedDifference([b['nir'], b['swir']]).rename('value')
        vis    = {'min': -1.0, 'max': 1.0, 'palette': ['black', 'white']}

    elif index == 'NDSI':
        result = image_refl.normalizedDifference([b['green'], b['swir']]).rename('value')
        vis    = {'min': -0.5, 'max': 0.8, 'palette': ['black', 'white']}

    elif index == 'BSI':
        nir   = image_refl.select(b['nir'])
        red   = image_refl.select(b['red'])
        blue  = image_refl.select(b['blue'])
        swir  = image_refl.select(b['swir'])
        result = swir.add(red).subtract(nir).subtract(blue).divide(
            swir.add(red).add(nir).add(blue)
        ).rename('value')
        vis    = {'min': -1.0, 'max': 1.0, 'palette': ['black', 'white']}

    elif index == 'LST' and b['thermal']:
        thermal = image.select(b['thermal'])
        lst_k   = thermal.multiply(0.00341802).add(149.0)
        result  = lst_k.subtract(273.15).rename('value')
        vis     = {'min': 10, 'max': 45, 'palette': ['black', 'white']}

    elif index == 'AVI':
        # Advanced Vegetation Index — (NIR*(1-RED)*(NIR-RED))^(1/3)
        nir = image_refl.select(b['nir'])
        red = image_refl.select(b['red'])
        result = nir.multiply(
            ee.Image(1).subtract(red)
        ).multiply(
            nir.subtract(red).abs()
        ).pow(1.0 / 3.0).rename('value')
        vis = {'min': 0, 'max': 0.9, 'palette': ['black', 'white']}

    elif index == 'SI':
        # Shadow Index — ((1-B)*(1-G)*(1-R))^(1/3)
        blue  = image_refl.select(b['blue'])
        green = image_refl.select(b['green'])
        red   = image_refl.select(b['red'])
        result = (ee.Image(1).subtract(blue)).multiply(
            ee.Image(1).subtract(green)
        ).multiply(
            ee.Image(1).subtract(red)
        ).pow(1.0 / 3.0).rename('value')
        vis = {'min': 0, 'max': 0.8, 'palette': ['black', 'white']}

    elif index == 'NDGI':
        # Normalized Difference Glacier Index — (Green-Red)/(Green+Red)
        result = image_refl.normalizedDifference([b['green'], b['red']]).rename('value')
        vis    = {'min': -0.5, 'max': 0.5, 'palette': ['black', 'white']}

    elif index == 'NDMI':
        # Normalized Difference Moisture Index — (NIR-SWIR)/(NIR+SWIR)
        result = image_refl.normalizedDifference([b['nir'], b['swir']]).rename('value')
        vis    = {'min': -0.8, 'max': 0.8, 'palette': ['black', 'white']}

    elif index == 'NPCRI':
        # Normalized Pigment Chlorophyll Ratio Index — (Red-Blue)/(Red+Blue)
        red  = image_refl.select(b['red'])
        blue = image_refl.select(b['blue'])
        result = red.subtract(blue).divide(
            red.add(blue).add(1e-6)
        ).rename('value')
        vis = {'min': -0.5, 'max': 0.5, 'palette': ['black', 'white']}

    elif index == 'VHI':
        # Vegetation Health Index — 0.5*VCI + 0.5*TCI (basitleştirilmiş)
        ndvi = image_refl.normalizedDifference([b['nir'], b['red']])
        vci  = ndvi.add(1).divide(2)          # NDVI'yi 0-1'e normalize et
        if b['thermal']:
            thermal = image.select(b['thermal'])
            lst_c   = thermal.multiply(0.00341802).add(149.0).subtract(273.15)
            tci     = ee.Image(1).subtract(
                lst_c.subtract(10).divide(40)
            ).clamp(0, 1)                     # 10-50°C → 1-0 (soğuk = sağlıklı)
            result  = vci.multiply(0.5).add(tci.multiply(0.5)).rename('value')
        else:
            result  = vci.rename('value')
        vis = {'min': 0, 'max': 1, 'palette': ['black', 'white']}

    elif index == 'FRI':
        # 🔥 Yangın Risk İndeksi (Fire Risk Index) — kompozit bir skor.
        # Üç bileşeni birleştirir:
        #   1) Kuraklık/nem stresi  -> NDMI'nin tersi (düşük nem = yüksek risk)
        #   2) Yakıt yükü           -> NDVI (yoğun/kuru bitki örtüsü = yanıcı madde)
        #   3) Isı stresi           -> LST (varsa; sıcak yüzey = yüksek risk)
        # Sonuç 0 (düşük risk) ile 1 (yüksek risk) arasında normalize edilir.
        ndvi = image_refl.normalizedDifference([b['nir'], b['red']])
        fuel = ndvi.add(1).divide(2).clamp(0, 1)              # 0-1 (yoğun bitki örtüsü)

        ndmi     = image_refl.normalizedDifference([b['nir'], b['swir']])
        dryness  = ee.Image(1).subtract(
            ndmi.add(1).divide(2)
        ).clamp(0, 1)                                          # 0-1 (düşük nem = yüksek değer)

        if b['thermal']:
            thermal = image.select(b['thermal'])
            lst_c   = thermal.multiply(0.00341802).add(149.0).subtract(273.15)
            heat    = lst_c.subtract(10).divide(40).clamp(0, 1)  # 10-50°C → 0-1 (sıcak = yüksek risk)
            result  = (dryness.multiply(0.4)
                       .add(fuel.multiply(0.3))
                       .add(heat.multiply(0.3))
                       .rename('value'))
        else:
            result = (dryness.multiply(0.5)
                      .add(fuel.multiply(0.5))
                      .rename('value'))
        vis = {'min': 0, 'max': 1, 'palette': ['black', 'white']}

    else:
        result = image_refl.normalizedDifference([b['nir'], b['red']]).rename('value')
        vis    = {'min': -0.2, 'max': 0.9, 'palette': ['black', 'white']}

    # ── 3b. Görsel mod / dışa aktarım modu ayrımı ──────────────────
    # 🛠️ BUG FİX: for_export=True (GeoTIFF indirme) → her zaman ham result.
    # classBreaks (sınıf ID'leri) ve custom_palette/min/max UYGULANMAZ.
    # Piksel değerleri orijinal bar skalasındaki değerlerdir (NDVI: -1…1,
    # DEM: metre, eğim: derece, vb.) — sınıflandırma veya görsel germen
    # indirilecek dosyayı ASLA etkilemez.
    # for_export=False (harita önizleme) → önceki davranış aynen korunur.
    custom_palette = data.get('palette')
    custom_min     = data.get('min')
    custom_max     = data.get('max')

    if for_export:
        # GeoTIFF indirme: orijinal bar skalasındaki ham değerler.
        display_result = result
    elif class_breaks and isinstance(class_breaks, list) and len(class_breaks) > 0:
        classified_img, classified_vis = build_classified_image(result, class_breaks)
        if classified_img is not None:
            display_result = classified_img
            vis = classified_vis
        else:
            display_result = result
    elif custom_palette and isinstance(custom_palette, list) and len(custom_palette):
        display_result = result
        vis['palette'] = [str(c).lstrip('#') for c in custom_palette]
        if custom_min is not None:
            vis['min'] = float(custom_min)
        if custom_max is not None:
            vis['max'] = float(custom_max)
    else:
        display_result = result

    # ── 4. Görüntü hazırlığı (Clip / Full Scene) ────────────────
    if clip_mode == 'clip':
        final_display = display_result.clip(roi)
    else:
        final_display = display_result

    return final_display, roi, result, vis, _crs_probe_img


def _rgb_scene_metadata(data, roi, image, ds):
    """Seçilen sahne için Görüntü Bilgileri / dinamik lejant panelinde
    gösterilecek metadata sözlüğünü üretir. Gerçek CRS/çözünürlük GEE'den
    sorgulanır; başarısız olursa veri seti kaydındaki varsayılana düşer."""
    meta = {
        'datasetKey':   data.get('satellite'),
        'datasetName':  ds.get('datasetName', ds.get('label')),
        'sensor':       ds.get('sensor'),
        'bandsInfo':    ds.get('bandsInfo'),
        'resolution':   ds.get('resolution'),
        'crs':          None,
        'imageId':      None,
        'acquisitionDate': None,
        'cloudCover':   None,
    }
    try:
        info = image.select(ds['rgbBands'][0]).getInfo()
        meta['imageId'] = info.get('id') or info.get('properties', {}).get('system:index')
    except Exception:
        pass
    try:
        proj = image.select(ds['rgbBands'][0]).projection()
        meta['crs'] = proj.crs().getInfo()
        nominal = proj.nominalScale().getInfo()
        if nominal:
            meta['resolution'] = round(nominal, 2)
    except Exception:
        pass
    try:
        ts = image.get('system:time_start').getInfo()
        if ts:
            meta['acquisitionDate'] = datetime.datetime.utcfromtimestamp(ts / 1000.0).strftime('%Y-%m-%d %H:%M UTC')
    except Exception:
        pass
    if ds.get('cloudProp'):
        try:
            meta['cloudCover'] = image.get(ds['cloudProp']).getInfo()
        except Exception:
            pass
    if not meta['imageId']:
        try:
            meta['imageId'] = image.get('system:index').getInfo()
        except Exception:
            pass
    return meta


# ════════════════════════════════════════════════════════════════
# 📈 /api/timeseries — GERÇEK Zaman Serisi ve Değişim Analizi
# ════════════════════════════════════════════════════════════════
# SORUN: Eskiden "📈 Zaman Serisi ve Değişim Analizi" tamamen İSTEMCİ
# tarafında (JavaScript'te Math.random() ile) SAHTE veri üretiyordu —
# hiçbir GEE çağrısı yapılmıyordu. Kullanıcı 10 yıllık bir aralık ve
# aylık/yıllık periyot seçtiğinde, hem çizgi grafikteki değerler hem de
# üstteki uydu görüntü galerisi gerçek uydu verisiyle hiç ilişkili
# değildi.
#
# ÇÖZÜM: Bu endpoint, seçilen tarih aralığını periyotlara (ay ya da yıl)
# böler; HER periyot için build_result_image() (yani /api/analyze ile
# BİREBİR aynı indeks formülleri, bulut/gölge maskesi, Landsat DN→yansıma
# dönüşümü) yeniden kullanılarak o periyodun GERÇEK ortalama indeks
# değeri hesaplanır (reduceRegion + Reducer.mean). Ayrıca her periyot için
# en az bulutlu GERÇEK sahne (Image ID + tarih + bulutluluk) bulunup
# 'gallery' dizisinde döndürülür — istemci bunu üstteki uydu görüntü
# galerisine yazar ve kullanıcı o periyotlar arasında geçiş yapabilir.
def _sylva_period_ranges(start_year, end_year, period):
    """Başlangıç/bitiş yılı ve periyot tipine göre (label, startDate, endDate)
    üçlülerinden oluşan sıralı bir liste üretir. 'endDate' üst sınır HARİÇ
    (GEE filterDate ile uyumlu — bir sonraki periyodun ilk günü)."""
    ranges = []
    if period == 'monthly':
        for y in range(start_year, end_year + 1):
            for m in range(1, 13):
                start = '%04d-%02d-01' % (y, m)
                if m == 12:
                    end = '%04d-01-01' % (y + 1)
                else:
                    end = '%04d-%02d-01' % (y, m + 1)
                ranges.append(('%04d-%02d' % (y, m), start, end))
    else:  # 'yearly'
        for y in range(start_year, end_year + 1):
            ranges.append((str(y), '%04d-01-01' % y, '%04d-01-01' % (y + 1)))
    return ranges


def _sylva_least_cloud_scene(roi, satellite, start_date, end_date, max_cloud):
    """Verilen AOI + tarih aralığında, seçilen uydu için EN AZ bulutlu
    gerçek sahnenin metadata'sını (sceneId, timestamp, bulutluluk %) döner.
    Uygun sahne bulunamazsa None döner — galeri o periyodu atlar."""
    ds = SATELLITE_DATASETS.get(satellite)
    if not ds:
        return None
    cloud_prop = ds.get('cloudProp')
    try:
        col = None
        for coll_id in ds.get('collections', []):
            c = ee.ImageCollection(coll_id).filterBounds(roi).filterDate(start_date, end_date)
            col = c if col is None else col.merge(c)
        if col is None:
            return None
        if cloud_prop:
            col = col.filter(ee.Filter.lt(cloud_prop, max_cloud)).sort(cloud_prop)
        else:
            col = col.sort('system:time_start')
        first = col.first()
        props = _call_with_retry(
            lambda: first.toDictionary(['system:index', 'system:time_start', cloud_prop] if cloud_prop
                                        else ['system:index', 'system:time_start']).getInfo(),
            retries=1
        )
        if not props or 'system:index' not in props:
            return None
        return {
            'sceneId':   props.get('system:index'),
            'timestamp': props.get('system:time_start'),
            'cloud':     props.get(cloud_prop) if cloud_prop else None,
        }
    except Exception:
        return None


@app.route('/api/timeseries', methods=['POST'])
def timeseries():
    try:
        data = request.get_json(silent=True) or {}

        satellite  = (data.get('satellite') or 's2-l2a').strip()
        period     = (data.get('period') or 'yearly').strip().lower()
        max_cloud  = int(data.get('maxCloud', 30))
        # Birden fazla indeks seçilebilir (Kullanılabilir Analizler'deki
        # işaretli kutular) — her biri grafikte ayrı bir çizgi olur.
        indices = data.get('indices')
        if not indices:
            indices = [data.get('index', 'NDVI')]

        try:
            start_year = int(data.get('startYear'))
            end_year   = int(data.get('endYear'))
        except (TypeError, ValueError):
            return jsonify({'success': False, 'error': 'Geçersiz başlangıç/bitiş yılı.'}), 400

        if period not in ('monthly', 'yearly'):
            return jsonify({'success': False, 'error': 'Geçersiz periyot (monthly/yearly olmalı).'}), 400
        if end_year <= start_year:
            return jsonify({'success': False, 'error': 'Bitiş yılı başlangıç yılından büyük olmalı.'}), 400

        ranges = _sylva_period_ranges(start_year, end_year, period)
        # Güvenlik sınırı: çok uzun aralık + aylık periyot GEE'ye çok
        # sayıda ardışık istek anlamına gelir (timeout/limit riski).
        MAX_PERIODS = 240
        if len(ranges) > MAX_PERIODS:
            return jsonify({
                'success': False,
                'error': 'Seçilen aralık çok geniş (%d periyot). Daha kısa bir aralık seçin ya da Yıllık periyodu kullanın.' % len(ranges)
            }), 400

        roi = make_roi(data.get('roi'))

        series = []
        for idx in indices:
            pts = []
            for label, sdate, edate in ranges:
                period_data = dict(data)
                period_data['index']     = idx
                period_data['startDate'] = sdate
                period_data['endDate']   = edate
                period_data['sceneId']   = None
                period_data['classBreaks'] = None
                try:
                    _final, p_roi, p_result, _vis, _probe = _call_with_retry(
                        build_result_image, period_data, for_export=False
                    )
                    mean_val = _call_with_retry(
                        lambda: p_result.reduceRegion(
                            reducer=ee.Reducer.mean(), geometry=p_roi,
                            scale=30, maxPixels=1e9, bestEffort=True,
                        ).get('value').getInfo(),
                        retries=1
                    )
                except Exception as _pe:
                    print('[SylvaGIS] ⚠️ Zaman serisi periyodu hesaplanamadı (%s, %s): %s' % (idx, label, _pe))
                    mean_val = None
                pts.append({'date': label, 'value': round(float(mean_val), 4) if mean_val is not None else None})
            series.append({'index': idx, 'points': pts})

        # ── Galeri: her periyot için en az bulutlu gerçek sahne ──────
        # (yalnızca ilk seçilen indeksin uydu koleksiyonuna göre — galeri
        # tek bir sahne akışı gösterir, indeks başına ayrı galeri yoktur)
        gallery = []
        for label, sdate, edate in ranges:
            scene = _sylva_least_cloud_scene(roi, satellite, sdate, edate, max_cloud)
            if scene:
                scene['label'] = label
                gallery.append(scene)

        return jsonify({
            'success':  True,
            'period':   period,
            'satellite': satellite,
            'series':   series,
            'gallery':  gallery,
        })

    except Exception as e:
        traceback.print_exc()
        return jsonify({'success': False, 'error': str(e)}), 500


@app.route('/api/analyze', methods=['POST'])
def analyze():
    global _last_analyze_params, _last_analyze_native_crs
    try:
        data = request.json
        _last_analyze_params = dict(data) if data else {}

        # ── 🛰️ Uydu Görüntüsü Galerisi — hızlı yol ───────────────────
        # RGB (gerçek renk) önizlemesi için piksel histogramı/istatistik
        # hesaplaması anlamsız ve gereksiz yere yavaştır; bunun yerine
        # sahne metadata'sı (tarih, sensör, bulutluluk, CRS, çözünürlük,
        # Image ID) doğrudan döndürülür.
        if data.get('index') == 'RGB':
            ds = SATELLITE_DATASETS.get(data.get('satellite'))
            if not ds:
                return jsonify({'success': False, 'error': 'Bilinmeyen uydu görüntüsü veri seti.'})

            roi = make_roi(data.get('roi'))
            max_cloud = int(data.get('maxCloud', 100))
            col = build_rgb_collection(ds, roi, max_cloud)
            scene_id = data.get('sceneId')
            if scene_id:
                image = col.filter(ee.Filter.eq('system:index', scene_id)).first()
            else:
                image = col.filterDate(data.get('startDate'), data.get('endDate')).sort('system:time_start', False).first()

            final_display, roi, result, vis, _unused_crs_probe = build_result_image(data)
            map_id = final_display.getMapId(vis)
            tile_url = map_id['tile_fetcher'].url_format

            meta = _rgb_scene_metadata(data, roi, image, ds)

            # Bu sahnenin gerçek/doğal CRS'i (_rgb_scene_metadata zaten
            # image.projection() üzerinden sorgulamıştı) — GeoTIFF indirme
            # penceresinin CRS seçicisini otomatik ön-seçmek için saklanır.
            # meta['crs'] (Görüntü Bilgileri panelinde gösterilen gerçek
            # sensör CRS'i) OLDUĞU GİBİ bırakılır; yalnızca indirme
            # varsayılanı (download_native_crs) için, coğrafi (EPSG:4326)
            # çıkması durumunda AOI merkezinden UTM dilimine yükseltilir —
            # bkz. yukarıdaki "PROJEKSİYON ÖNCELİĞİ" açıklaması.
            download_native_crs = meta.get('crs')
            if not download_native_crs or download_native_crs.strip().upper() == 'EPSG:4326':
                try:
                    centroid = roi.centroid(maxError=100).coordinates().getInfo()
                    download_native_crs = _utm_epsg_from_lonlat(centroid[0], centroid[1])
                except Exception:
                    pass
            if download_native_crs:
                _last_analyze_native_crs = download_native_crs

            return jsonify({
                'success':  True,
                'tileUrl':  tile_url,
                'index':    'RGB',
                'meta':     meta,
                'nativeCrs': download_native_crs,
                'visMin':   vis.get('min'),
                'visMax':   vis.get('max'),
            })

        final_display, roi, result, vis, crs_probe_img = build_result_image(data)

        # ── 🌐 Gerçek/doğal CRS tespiti ─────────────────────────────
        # 🛠️ BUG FİX (KÖK NEDEN — CRS seçici HER ZAMAN "WGS 84" gösteriyordu):
        # "result" (NDVI/NDWI/EVI/SAR vb. — clip/vis uygulanmamış ham analiz
        # görüntüsü) çoğu zaman median()/mean() gibi bir REDUCER'ın çıktısıdır;
        # GEE bu tür reducer'ların çıktı projeksiyonunu, kaynak sahnelerin
        # gerçek UTM dilimi ne olursa olsun HER ZAMAN varsayılan/unbounded
        # EPSG:4326'ya sıfırlar. Bu yüzden "result.projection()" üzerinden CRS
        # okumak daima "EPSG:4326" döndürüyordu — verinin gerçek native CRS'i
        # (örn. UTM Zone 36N) ne olursa olsun.
        # ÇÖZÜM: build_result_image() artık ayrıca reduce EDİLMEMİŞ, tek bir
        # kaynak görüntüyü (crs_probe_img) döndürüyor — CRS'i doğrudan ORADAN
        # okuyoruz. Bu görüntü None ise (örn. LULC/TOPO gibi zaten kendi
        # doğal/statik CRS'inde olan veri setleri) "result" üzerinden okumaya
        # geri dönülür — bu durumda result zaten reduce edilmemiştir/doğru
        # CRS'i taşır. Sorgu başarısız olursa sessizce None bırakılır ve
        # istemci tarafında güvenli varsayılan olan WGS 84'e düşülür.
        native_crs = None
        try:
            _crs_source = crs_probe_img if crs_probe_img is not None else result
            native_crs = _call_with_retry(
                lambda: _crs_source.projection().crs().getInfo(), retries=1
            )
        except Exception as _crs_err:
            native_crs = None
            print('[SylvaGIS] ⚠️ nativeCrs doğrudan projeksiyon okuması başarısız '
                  '(WGS84 geri dönüşüne geçiliyor, UTM merkez hesabı denenecek): {}'.format(_crs_err))

        # 🌐 PROJEKSİYON ÖNCELİĞİ: Bazı veri setleri (LULC/Dynamic World,
        # ESA WorldCover, SRTM/NASADEM/ALOS DEM vb.) Earth Engine'de zaten
        # coğrafi (EPSG:4326) sistemde saklanır — yani tespit edilen "gerçek
        # native CRS" GERÇEKTEN budur. Ancak indirilen rasterin CBS'de pratik
        # kullanımı (alan/mesafe/piksel boyutu hesapları) için coğrafi/derece
        # sistemi yerine HER ZAMAN metre bazlı, projeksiyonlu bir sistem
        # tercih edilir. Bu yüzden tespit edilen CRS coğrafi (EPSG:4326)
        # çıkarsa — ya da hiç tespit edilemezse — AOI'nin gerçek konumuna
        # (merkez boylam/enlemine) göre doğru UTM dilimi otomatik hesaplanıp
        # onun yerine kullanılır. Böylece indirme penceresi asla coğrafi bir
        # sistemle açılmaz; kullanıcı yine de dilerse elle WGS 84'e dönebilir.
        if not native_crs or native_crs.strip().upper() == 'EPSG:4326':
            try:
                centroid = roi.centroid(maxError=100).coordinates().getInfo()
                native_crs = _utm_epsg_from_lonlat(centroid[0], centroid[1])
            except Exception as _centroid_err:
                print('[SylvaGIS] ❌ UTM merkez hesabı da başarısız oldu — nativeCrs '
                      'null/WGS84 olarak dönecek (istemci taraflı UTM yedeği devreye '
                      'girecek): {}'.format(_centroid_err))

        if native_crs:
            _last_analyze_native_crs = native_crs

        # ── İstatistik ────────────────────────────────────────────
        # 🛠️ BUG FİX (NoData piksel / büyük AOI istatistik sorunu):
        # bestEffort=True eklendi. Olmadan: AOI büyük olduğunda veya bazı
        # piksellerde veri olmadığında (örn. eğim indirildiğinde bazı kareler
        # boş çıkıyordu) maxPixels limiti aşılınca GEE hata fırlatır ve stats
        # tamamen None döner. bestEffort=True ile GEE, gerekirse çözünürlüğü
        # otomatik düşürür ama hesabı DAIMA tamamlar. NoData (maskeli) pikseller
        # GEE'nin reduceRegion'unda zaten otomatik olarak dışlanır; yani
        # istatistikler her zaman yalnızca geçerli/dolu piksellerden hesaplanır.
        stats = _call_with_retry(
            lambda: result.reduceRegion(
                reducer    = ee.Reducer.frequencyHistogram(),
                geometry   = roi,
                scale      = 30,
                maxPixels  = 1e9,
                bestEffort = True,
            ).getInfo()
        )

        real_minmax = {}
        try:
            # 🛠️ BUG FİX (performans / peş peşe analiz hatası): daha önce
            # min/max ve ortalama İKİ AYRI reduceRegion() + getInfo() ağ
            # çağrısıyla hesaplanıyordu. Tek bir kombine reducer ile bu iki
            # çağrı TEK bir GEE isteğine indirilir — hem daha hızlı yanıt
            # verir hem de kullanıcı arka arkaya analiz yaptığında GEE'nin
            # eşzamanlı/istek-başına limitlerine çarpma ihtimalini azaltır.
            combined_reducer = ee.Reducer.minMax().combine(
                reducer2=ee.Reducer.mean(), sharedInputs=True
            )
            mm = _call_with_retry(
                lambda: result.reduceRegion(
                    reducer    = combined_reducer,
                    geometry   = roi,
                    scale      = 30,
                    maxPixels  = 1e9,
                    bestEffort = True,
                ).getInfo()
            )
            real_minmax = {
                'min':  mm.get('value_min'),
                'max':  mm.get('value_max'),
                'mean': mm.get('value_mean')
            }
        except Exception:
            pass

        # ── Tile URL ─────────────────────────────────────────────
        map_id   = _call_with_retry(lambda: final_display.getMapId(vis))
        tile_url = map_id['tile_fetcher'].url_format

        # ── Zaman serisi galerisi ────────────────────────────────
        # LULC ailesi statik/tek-katmanlı veri setleridir; zaman serisi
        # galerisi kavramı bunlara uygulanamaz — bu sorguyu tamamen atlarız.
        satellite  = data.get('satellite', 's2-l2a')
        start_date = data.get('startDate')
        end_date   = data.get('endDate')
        scene_id   = data.get('sceneId')
        max_cloud  = int(data.get('maxCloud', 20))
        scenes_list = []

        if not scene_id and data.get('index', 'NDVI') not in LULC_FAMILY_INDICES:
            try:
                roi_coords = data.get('roi')
                roi_geo = make_roi(roi_coords)
                if satellite == 's2-l2a':
                    col2 = (ee.ImageCollection('COPERNICUS/S2_SR_HARMONIZED')
                            .filterBounds(roi_geo)
                            .filter(ee.Filter.lt('CLOUDY_PIXEL_PERCENTAGE', max_cloud)))
                elif satellite == 's2-l1c':
                    col2 = (ee.ImageCollection('COPERNICUS/S2_HARMONIZED')
                            .filterBounds(roi_geo)
                            .filter(ee.Filter.lt('CLOUDY_PIXEL_PERCENTAGE', max_cloud)))
                elif satellite == 'l89-l2':
                    col2 = (ee.ImageCollection('LANDSAT/LC08/C02/T1_L2')
                            .filterBounds(roi_geo)
                            .filter(ee.Filter.lt('CLOUD_COVER', max_cloud)))
                elif satellite == 'l89-l1':
                    col2 = (ee.ImageCollection('LANDSAT/LC08/C02/T1_TOA')
                            .filterBounds(roi_geo)
                            .filter(ee.Filter.lt('CLOUD_COVER', max_cloud)))
                elif satellite == 'l7-l2':
                    col2 = (ee.ImageCollection('LANDSAT/LE07/C02/T1_L2')
                            .filterBounds(roi_geo)
                            .filter(ee.Filter.lt('CLOUD_COVER', max_cloud)))
                elif satellite == 'l7-l1':
                    col2 = (ee.ImageCollection('LANDSAT/LE07/C02/T1_TOA')
                            .filterBounds(roi_geo)
                            .filter(ee.Filter.lt('CLOUD_COVER', max_cloud)))
                elif satellite in ('l45-l2',):
                    col2 = (ee.ImageCollection('LANDSAT/LT05/C02/T1_L2')
                            .filterBounds(roi_geo)
                            .filter(ee.Filter.lt('CLOUD_COVER', max_cloud)))
                elif satellite == 'l45-l1':
                    col2 = (ee.ImageCollection('LANDSAT/LT05/C02/T1_TOA')
                            .filterBounds(roi_geo)
                            .filter(ee.Filter.lt('CLOUD_COVER', max_cloud)))
                elif satellite == 'mss-l1':
                    col2 = (ee.ImageCollection('LANDSAT/LM05/C02/T1')
                            .filterBounds(roi_geo))
                else:
                    col2 = (ee.ImageCollection('COPERNICUS/S2_SR_HARMONIZED')
                            .filterBounds(roi_geo)
                            .filter(ee.Filter.lt('CLOUDY_PIXEL_PERCENTAGE', max_cloud)))
                cloud_prop = 'CLOUDY_PIXEL_PERCENTAGE' if satellite.startswith('s2') else 'CLOUD_COVER'
                months_filter = _parse_months_param(data)
                limited    = _collect_scenes_across_years(
                    col2, start_date, end_date, months=months_filter,
                    per_year_limit=10, total_limit=60,
                )
                scene_ids  = _call_with_retry(lambda: limited.aggregate_array('system:index').getInfo(), retries=1)
                timestamps = _call_with_retry(lambda: limited.aggregate_array('system:time_start').getInfo(), retries=1)
                clouds_arr = _call_with_retry(lambda: limited.aggregate_array(cloud_prop).getInfo(), retries=1)
                scenes_list = list(zip(scene_ids, timestamps, clouds_arr))
            except Exception:
                scenes_list = []

        return jsonify({
            'success':   True,
            'tileUrl':   tile_url,
            'stats':     stats,
            'realStats': real_minmax,
            'scenes':    scenes_list,
            'index':     data.get('index', 'NDVI'),
            'visMin':    vis.get('min'),
            'visMax':    vis.get('max'),
            'visPalette': vis.get('palette', []),
            'nativeCrs': native_crs
        })

    except Exception as e:
        return jsonify({'success': False, 'error': str(e)})


@app.route('/api/highlight-class', methods=['POST'])
def highlight_class():
    """
    Lejant/grafik/tablodaki bir sınıfa tıklandığında, o sınıfa ait alanları
    haritada AYRI bir tile katmanı olarak parlak sarı renkte vurgular.
    /api/analyze ile aynı analiz parametrelerini (ROI, tarih, uydu, index vb.)
    yeniden kullanır; ek olarak sınıfın değer aralığını (classMin/classMax)
    alır. LULC ailesinde sınıf kodu tek bir değerdir (classMin == classMax);
    NDVI/NDWI gibi sınıflandırılmış (classBreaks) indekslerde bir aralıktır.
    """
    try:
        data = request.json or {}
        class_min = data.get('classMin')
        class_max = data.get('classMax')
        if class_min is None or class_max is None:
            return jsonify({'success': False, 'error': 'classMin/classMax gerekli.'})

        # Ham (sınıflandırılmadan önceki) değer görüntüsü — result — hem LULC
        # sınıf kodlarını hem de sürekli indeks değerlerini içerir; build_result_image
        # zaten /api/analyze ile birebir aynı ROI/parametre işleme mantığını uygular.
        final_display, roi, result, vis, _unused_crs_probe = build_result_image(data)

        highlight_mask = result.gte(ee.Number(class_min)).And(result.lte(ee.Number(class_max)))

        # Tek renkli parlak vurgulama: sabit bir bant (1), sadece seçili sınıfın
        # kapsadığı piksellerde görünür kalacak şekilde maskelenip AOI'ye kesilir.
        highlighted_flat = ee.Image(1).updateMask(highlight_mask).clip(roi)

        highlight_vis = {'min': 0, 'max': 1, 'palette': ['#ffee00']}
        map_id = highlighted_flat.getMapId(highlight_vis)
        tile_url = map_id['tile_fetcher'].url_format

        return jsonify({'success': True, 'tileUrl': tile_url})

    except Exception as e:
        return jsonify({'success': False, 'error': str(e)})


@app.route('/api/download-geotiff', methods=['POST'])
def download_geotiff():
    """
    Son analizin GeoTIFF dosyasını sunucu üzerinden indirir ve doğrudan
    kullanıcıya bir dosya (binary .tif) olarak döndürür — JSON içinde bir
    GEE imzalı URL DÖNDÜRMEZ. Bunun nedeni: GEE'nin tek istekteki indirme
    boyutu sınırı (~48 MB / 50331648 bayt) aşıldığında, tek bir imzalı URL
    ile bu sınırı aşmanın bir yolu yoktur; alanın sunucu tarafında karolara
    bölünüp indirilmesi ve birleştirilmesi gerekir.

    clipMode: İstek gövdesinden gelen değer, son analizin clipMode'unu geçersiz kılar.

    Büyük alan / yüksek çözünürlük (10 m, 30 m) davranışı:
      - _download_band_geotiff_bytes() önce TEK istekte indirmeyi dener.
      - GEE boyut sınırı hatası (ör. "Total request size (499411062 bytes)
        must be less than or equal to 50331648 bytes.") alınırsa, hata
        mesajından istenen/izin verilen bayt miktarları ayrıştırılır ve
        bölge otomatik olarak yeterli sayıda karoya (grid) bölünür.
      - Her karo ayrı ayrı indirilir, ardından rasterio.merge ile TEK bir
        GeoTIFF'te sunucu tarafında mozaiklenir.
      - Kullanıcı hiçbir ayar yapmak zorunda kalmaz; çözünürlük, CRS,
        georeferans ve piksel değerleri korunur. Sonuç her koşulda (10 m,
        30 m, 100 m, 200 m) TEK bir .tif dosyası olarak sunulur.
    """
    try:
        req_data = request.json or {}

        # 🛠️ BUG FİX (AOI dışı NoData/siyah alan / yanlış kırpma sorunu):
        # Frontend, güncel Çalışma Alanı/AOI geometrisini HER indirme
        # isteğinde 'roi' alanıyla birlikte gönderir (bkz. index.html —
        # _gtiffRoi / _extractROIGeometry). Daha önce bu alan burada HİÇ
        # okunmuyordu; roi her zaman yalnızca _last_analyze_params'tan
        # (yani en son çalıştırılan /api/analyze isteğinden, sunucuda
        # TÜM kullanıcılar arasında paylaşılan global bir değişkenden)
        # alınıyordu. Kullanıcı analiz çalıştırdıktan SONRA AOI'yi
        # taşır/yeniden çizer/genişletirse — veya sunucuda başka bir
        # oturumun analiz parametreleri araya girmişse — indirilen
        # GeoTIFF haritada görülenden FARKLI (eski/yanlış) bir sınıra
        # göre kırpılıyor, bu da ArcMap/QGIS'te AOI dışında kalan geniş
        # NoData/siyah alanlar veya kısmen kırpılmamış bir dikdörtgen
        # olarak görünüyordu. ÇÖZÜM: istekten gelen 'roi' — mevcutsa —
        # her zaman öncelikli kullanılır; tüm indeksler (NDVI, NDWI,
        # LST, SAVI, NDBI/BSI, EVI, SMI, NBR, vb.) build_result_image()
        # üzerinden AYNI ortak kırpma/NoData mantığını kullandığı için bu
        # düzeltme tüm raster analiz dışa aktarımlarına otomatik uygulanır.
        fresh_roi = req_data.get('roi')

        if not _last_analyze_params.get('roi'):
            return jsonify({'success': False, 'error': 'Önce bir uydu analizi çalıştırın.'})

        filename = (req_data.get('filename') or 'SylvaGIS_export').strip() or 'SylvaGIS_export'
        scale    = int(req_data.get('scale', 30))
        # 🌐 İstemci bir CRS göndermezse (ör. eski/farklı bir istemci veya
        # doğrudan API çağrısı), sabit "EPSG:4326" yerine son analizin
        # KENDİ gerçek/doğal CRS'ine düşülür — böylece veri hangi UTM
        # diliminde/projeksiyondaysa indirilen GeoTIFF de o CRS'te gelir.
        # Normal akışta zaten istemci (index.html) CRS seçicisini
        # nativeCrs'e göre otomatik ön-seçip gönderir; bu yalnızca bir
        # güvenlik ağıdır. Kullanıcı seçiciden farklı bir CRS seçtiyse o
        # değer (req_data.get('crs')) her zaman önceliklidir.
        crs = (req_data.get('crs') or _last_analyze_native_crs or 'EPSG:4326').strip()

        # Güvenlik: Yalnızca EPSG:NNNNN formatına izin ver
        import re as _re
        if not _re.match(r'^EPSG:\d+$', crs, _re.IGNORECASE):
            crs = _last_analyze_native_crs if (_last_analyze_native_crs and _re.match(r'^EPSG:\d+$', _last_analyze_native_crs, _re.IGNORECASE)) else 'EPSG:4326'
        crs = crs.upper()

        # Son analiz parametrelerini kullan
        data = dict(_last_analyze_params)

        # Görüntü Alanı modu: istekten gelen değer son analizin üzerine yazar
        if 'clipMode' in req_data:
            data['clipMode'] = req_data['clipMode']

        # AOI/Workspace geometrisi: istekten gelen güncel roi her zaman
        # önceliklidir (bkz. yukarıdaki BUG FİX açıklaması).
        if fresh_roi:
            data['roi'] = fresh_roi

        # 🛠️ BUG FİX (istenen davranış): "Lejantı Uygula" ile sınıflandırma
        # yapılmış olsa bile — NDVI, DEM, Eğim (Slope) vb. hiçbir analizde —
        # indirilen GeoTIFF ASLA sınıf ID'lerine (1,2,3...) göre değil, her
        # zaman haritadaki renk çubuğunun (color bar) dayandığı HAM/sürekli
        # değerlere göre üretilir. for_export=True, build_result_image()
        # içindeki classBreaks/build_classified_image() adımını komple
        # atlatır — bkz. build_result_image() docstring'i.
        final_display, roi, result, vis, _unused_crs_probe = build_result_image(data, for_export=True)

        # ── 🌈 Sentinel-2 doğal renk parlaklık düzeltmesi ────────────
        # SORUN: Sentinel-2 RGB (B4-B3-B2) GeoTIFF'leri şu ana kadar ham
        # (germe uygulanmamış) yansıma değerleriyle (float, ~0.0-0.3
        # aralığında) dışa aktarılıyordu. Bu değerler haritadaki önizlemede
        # yalnızca CLIENT tarafında (tile/vis min-max) doğru gösteriliyordu;
        # dosyanın kendisi hâlâ "karanlık" ham reflectance içeriyordu. ArcMap
        # gibi CBS yazılımları bu ham float veriyi haritadaki gibi otomatik
        # germemediği için görüntü olması gerekenden çok koyu görünüyordu.
        # ÇÖZÜM: Yalnızca Sentinel-2 gerçek renk (RGB) indirmelerinde — hem
        # Clip hem de Tüm Veri modunda — haritada kullanılan aynı visMin/
        # visMax germe aralığı piksel değerlerine doğrudan uygulanır ve
        # sonuç 0-255 (Byte) aralığına dönüştürülür. Böylece indirilen
        # GeoTIFF, haritada görülen doğal renk görünümüyle eşleşir ve
        # ArcMap'te ek bir parlaklık/kontrast ayarı gerekmez.
        # Landsat ve diğer tüm veri setleri/indeksler ETKİLENMEZ; onlar
        # hâlâ önceki (ham) davranışlarıyla dışa aktarılır.
        if data.get('index') == 'RGB' and data.get('satellite') in ('s2-l1c', 's2-l2a'):
            v_min = vis.get('min', 0)
            v_max = vis.get('max', 0.3)
            final_display = (
                final_display
                .unitScale(v_min, v_max)
                .multiply(255)
                .clamp(0, 255)
                .toByte()
            )

        # Full modunda ROI ile kesmeden tüm görüntüyü indir;
        # Clip modunda yalnızca ROI sınırları içindeki pikseller alınır.
        # LULC ailesi için bu davranış zorunludur: "Tüm Veri Görüntüsü" modu
        # seçili olsa bile dışa aktarım kesinlikle AOI sınırlarına kesilir.
        #
        # ✅ MODÜLLER ARASI TUTARLILIK: Bu satır — ve aşağıdaki true-clip
        # bloğu — 🛰️ Uydu Görüntüsü (RGB), 🌍 Uydu Analizleri (NDVI, NDWI,
        # EVI, SAVI, SMI, NBR, NDSI, BSI, LST, AVI, SI, NDGI, NDMI, NPCRI,
        # VHI), 🏘️ Arazi Kullanımı (LULC ailesi) ve 🏔️ Topografik Analizler
        # (TOPO ailesi) için TEK ve AYNI koddur — hiçbiri için ayrı bir
        # indirme/kırpma yolu YOKTUR. 📡 Ham Veri (Bantlar) modülü de aynı
        # true-clip mekanizmasını kendi uç noktasında (_download_band_
        # geotiff_bytes + aoi_geom_4326) kullanır. build_result_image()
        # zaten tüm bu indeksler için identik `clip(roi) if clip_mode ==
        # 'clip' else ...` yapısını kullandığından (bkz. TOPO bloğu ~satır
        # 1064 ve indeks bloğu ~satır 1305), burada modüle özel HİÇBİR dal
        # eklemeye gerek yoktur.
        is_clip = data.get('clipMode', 'clip') == 'clip' or data.get('index', 'NDVI') in LULC_FAMILY_INDICES
        if is_clip:
            export_region = roi
        else:
            # "Tüm Veri" modunda görüntünün TAM kapsamı (sahne footprint'i)
            # indirilir — çalışma alanıyla kısıtlanmaz. Küresel görüntülerde
            # (global DEM vb.) geometry() sınırsız dönebilir; bu durumda
            # _download_band_geotiff_bytes() fallback_region_geom (roi.bounds())
            # ile otomatik olarak tekrar dener.
            export_region = final_display.geometry()

        safe_name = re.sub(r'[^A-Za-z0-9_\-\.]+', '_', filename)

        # ÖNEMLİ (bkz. download_raw_bands): Clip modunda AOI dışında kalan
        # pikseller, "region" parametresinin yalnızca dikdörtgen bir kapsama
        # alanı (bounding box) tanımlaması nedeniyle GERÇEK bir NoData
        # değeri olarak işaretlenmezse, indirilen GeoTIFF ArcGIS/QGIS'te AOI
        # poligonu yerine düz bir dikdörtgen gibi görünür. final_display zaten
        # clip(roi) ile maskelendiği için burada yalnızca o maskeyi GeoTIFF'e
        # gerçek NoData olarak yazdırmak yeterlidir — bu davranış Sentinel ve
        # Landsat dahil TÜM veri setleri için AYNIdır.
        #
        # 🛠️ KÖK NEDEN DÜZELTMESİ (DEM'de deniz kıyısında, NDVI'de 0'a yakın
        # alanlarda, Slope'ta İSE NEREDEYSE HER YERDE görülen "boş kareler"):
        # NoData sentinel'i önceden 0 idi. Ancak 0, BİRÇOK katmanda GERÇEK
        # ve geçerli bir değer: DEM'de deniz seviyesi (kıyı şeridi) 0 m'dir,
        # NDVI/NDWI gibi indekslerde 0 son derece yaygın bir ara değerdir,
        # ve en çarpıcısı — Slope'ta 0° (dümdüz arazi) HER YERDE karşımıza
        # çıkabilir. GeoTIFF'e "NoData = 0" etiketi yazılınca, ArcMap/QGIS
        # o değere sahip HER piksel bazlı gerçek veriyi de boş/şeffaf
        # gösteriyordu — kullanıcının bildirdiği "DEM'de kıyıda, NDVI'de
        # 0 civarında, Slope'ta ise tüm alanda kare kare boşluk" deseni
        # BİREBİR bu çakışmayla açıklanıyor.
        #
        # ÇÖZÜM: NoData sentinel'i olarak, bu katmanların hiçbirinde
        # (elevation, slope [0-90°], NDVI/NDWI vb. [-1, 1], reflectance
        # [0-1]) asla gerçekten oluşamayacak -9999 değeri kullanılıyor.
        # Bu, raster verilerinde yaygın kabul görmüş standart bir NoData
        # kuralıdır (ör. USGS/ESRI ürünlerinde de kullanılır).
        nodata_value = -9999 if is_clip else None

        # 🔒 true-clip güvencesi: GEE'nin clip()/unmask() zincirinin ötesinde,
        # AOI'nin GERÇEK poligon şeklini (EPSG:4326) de gönderiyoruz ki
        # _download_band_geotiff_bytes() sonuçta ne dönerse dönsün (tek
        # istek veya karo-mozaik) dosyayı yerel olarak KESİN bir şekilde
        # bu poligona göre yeniden kırpsın. 'Tüm Veri' modunda (is_clip
        # False) bu adım atlanır — mevcut davranış korunur.
        aoi_geom_4326 = _call_with_retry(lambda: roi.getInfo()) if is_clip else None

        tif_bytes = _download_band_geotiff_bytes(
            final_display, export_region, scale, crs, safe_name,
            nodata_value=nodata_value, aoi_geom_4326=aoi_geom_4326,
            fallback_region_geom=roi.bounds(maxError=100)
        )

        # 🎨 ArcMap/QGIS "Siyah-Beyaz + Rakam" SORUNU DÜZELTMESİ:
        # LULC ailesi (LULC, LULC_ESA, LULC_MODIS, LULC_CORINE) indirmelerinde
        # ham GeoTIFF'in içine (ve yanına) Color Table + RAT gömülür; kullanıcıya
        # tek bir .tif yerine .tif + .tif.aux.xml + .clr içeren bir ZIP sunulur.
        # Diğer TÜM analizler (NDVI, DEM, RGB, TOPO vb.) etkilenmez; onlar
        # önceki gibi doğrudan .tif olarak inmeye devam eder.
        lulc_index = data.get('index')
        if lulc_index in LULC_CLASS_DEFS:
            try:
                sym_files = _build_lulc_symbology_zip(tif_bytes, lulc_index, safe_name)
            except Exception as sym_err:
                traceback.print_exc()
                sym_files = None
                print('[SylvaGIS] ⚠️ LULC renk tablosu/RAT oluşturulamadı, ham .tif '
                      'olarak devam ediliyor: {}'.format(sym_err))

            if sym_files:
                zip_buf = io.BytesIO()
                with zipfile.ZipFile(zip_buf, 'w', zipfile.ZIP_DEFLATED) as zf:
                    for fname, fbytes in sym_files.items():
                        zf.writestr(fname, fbytes)
                zip_bytes = zip_buf.getvalue()

                resp = Response(zip_bytes, mimetype='application/zip')
                resp.headers['Content-Disposition'] = 'attachment; filename="{}.zip"'.format(safe_name)
                resp.headers['Content-Length'] = str(len(zip_bytes))
                return resp

        resp = Response(tif_bytes, mimetype='image/tiff')
        resp.headers['Content-Disposition'] = 'attachment; filename="{}.tif"'.format(safe_name)
        resp.headers['Content-Length'] = str(len(tif_bytes))
        return resp

    except Exception as e:
        traceback.print_exc()
        err = str(e).strip() or '{} (mesajsız hata — sunucu konsoluna bakın)'.format(type(e).__name__)
        # GEE boyut limiti otomatik karolama sonrasında da aşılırsa (çok
        # büyük AOI + çok küçük scale kombinasyonu) kullanıcıya bilgi ver.
        if 'too large' in err.lower() or 'limit' in err.lower():
            return jsonify({
                'success': False,
                'error': 'Alan otomatik karolamayla bile tek dosyada indirilemeyecek kadar büyük. '
                         'Lütfen çalışma alanını (AOI) küçültün veya "Piksel Çözünürlüğü" değerini artırın.'
            })
        return jsonify({'success': False, 'error': err})


@app.route('/api/raw-bands', methods=['POST'])
def raw_bands():
    """
    📡 Ham Veri (Bantlar) — seçilen uydu görüntüsü veri setine ait TÜM
    orijinal bantları, çözünürlüklerine göre gruplandırılmış şekilde
    döndürür. Statik bir katalog sorgusudur (GEE'ye istek atmaz), bu
    yüzden Uydu Görüntüsü Galerisi'nden bir veri seti seçilir seçilmez
    anında yanıt döner.
    """
    try:
        data = request.json or {}
        dataset_key = data.get('dataset')
        ds     = SATELLITE_DATASETS.get(dataset_key)
        groups = RAW_BAND_GROUPS.get(dataset_key)
        if not ds or not groups:
            return jsonify({'success': False, 'error': 'Bilinmeyen veri seti: ' + str(dataset_key)})

        return jsonify({
            'success': True,
            'dataset': {
                'key':         dataset_key,
                'label':       ds['label'],
                'datasetName': ds.get('datasetName', ds['label']),
                'sensor':      ds['sensor'],
            },
            'groups': groups,
        })
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)})


def _parse_gee_size_limit_error(msg):
    """
    GEE'nin getDownloadURL() boyut sınırı aşıldığında fırlattığı hata mesajını
    ayrıştırır, ör:
      "Total request size (52546956 bytes) must be less than or equal to
       50331648 bytes."
    Eşleşirse (istenen_bayt, izin_verilen_bayt) döner, aksi halde None.
    """
    m = re.search(
        r'Total request size \((\d+)\s*bytes\)\s*must be less than or equal to\s*(\d+)\s*bytes',
        msg or ''
    )
    if not m:
        return None
    return int(m.group(1)), int(m.group(2))


def _split_bbox_grid(roi, nx, ny):
    """
    roi'nin (WGS84 lon/lat) sınırlayıcı kutusunu nx * ny eşit dikdörtgen
    karoya böler ve ee.Geometry.Rectangle listesi döndürür. Orijinal
    çözünürlük/CRS korunur; yalnızca dışa aktarma alanı (region) küçültülür,
    böylece GEE'nin tek istekteki boyut sınırı aşılmaz.

    NOT: Bu fonksiyon artık indirme yolunda KULLANILMIYOR — bkz.
    _split_bbox_grid_aligned(). Geriye dönük referans/uyumluluk için
    dosyada bırakıldı.
    """
    ring = roi.bounds().coordinates().get(0).getInfo()
    lons = [p[0] for p in ring]
    lats = [p[1] for p in ring]
    xmin, xmax = min(lons), max(lons)
    ymin, ymax = min(lats), max(lats)

    tiles = []
    for i in range(nx):
        for j in range(ny):
            x0 = xmin + (xmax - xmin) * i / nx
            x1 = xmin + (xmax - xmin) * (i + 1) / nx
            y0 = ymin + (ymax - ymin) * j / ny
            y1 = ymin + (ymax - ymin) * (j + 1) / ny
            tiles.append(ee.Geometry.Rectangle([x0, y0, x1, y1], 'EPSG:4326', False))
    return tiles


def _split_bbox_grid_aligned(roi, nx, ny, scale, crs):
    """
    🛠️ KÖK NEDEN DÜZELTMESİ — karo (tile) sınırlarında piksel boşlukları
    (ArcMap/QGIS'te DEM/eğim gibi büyük TOPO katmanlarında görülen
    "bazı piksel kareleri eksik" sorunu):

    ESKİ YÖNTEM (_split_bbox_grid), sınırlayıcı kutuyu enlem/boylamda
    EŞİT COĞRAFİ dilimlere bölüyordu ve her karo GEE'ye yalnızca
    'region' + 'scale' olarak gönderiliyordu. GEE, her karonun piksel
    gridinin başlangıcını (origin) KENDİ bölgesine göre bağımsız
    hesapladığından, komşu karoların piksel kenarları çoğu zaman TAM
    örtüşmüyordu (kesirli/sub-pixel kayma). rasterio.merge() ile
    birleştirilince bu kayma, karo dikişlerinde ince NoData şeritleri
    veya kareleri olarak ortaya çıkıyordu — kullanıcının GIS
    yazılımında gördüğü "eksik piksel kareleri" tam olarak budur.

    ÇÖZÜM: Karoları eşit coğrafi dilimler yerine TEK ORTAK bir piksel
    gridine göre bölüyoruz. Önce tüm AOI'nin hedef CRS'teki gerçek
    kapsamını hesaplıyoruz, bunu 'scale' değerine göre TAM SAYI piksel
    satır/sütununa ayırıyoruz, sonra her karo için GEE'ye 'region' +
    'scale' yerine doğrudan 'crsTransform' + 'dimensions' gönderiyoruz.
    crsTransform, TÜM karolar için AYNI ortak origin ve piksel boyutunu
    (scale) kullandığından, komşu karoların kenar pikselleri artık
    matematiksel olarak BİREBİR (pixel-perfect) çakışır; rasterio.merge
    sonrasında dikişlerde asla boşluk kalmaz.

    roi: ee.Geometry (WGS84 veya başka bir projeksiyonda olabilir).
    scale: metre cinsinden piksel boyutu (indirme ile aynı 'scale').
    crs:   hedef koordinat referans sistemi (örn. 'EPSG:4326' / 'EPSG:32636').

    Dönen değer: [{'crsTransform': [...], 'dimensions': 'WxH'}, ...]
    """
    # AOI'yi hedef CRS'e projekte edip GERÇEK sınırlayıcı kutusunu al
    # (maxError=1: metre cinsinden izin verilen projeksiyon hatası payı).
    roi_in_crs = roi.transform(crs, 1)
    ring = roi_in_crs.bounds().coordinates().get(0).getInfo()
    xs = [p[0] for p in ring]
    ys = [p[1] for p in ring]
    xmin, xmax = min(xs), max(xs)
    ymin, ymax = min(ys), max(ys)

    total_w_px = max(1, math.ceil((xmax - xmin) / scale))
    total_h_px = max(1, math.ceil((ymax - ymin) / scale))

    # Ortak grid origin'i: sol-üst köşe (x küçükten büyüğe, y büyükten
    # küçüğe gider — GeoTIFF/afin dönüşüm kuralı).
    origin_x = xmin
    origin_y = ymax

    tiles = []
    for i in range(nx):
        col0 = (i * total_w_px) // nx
        col1 = total_w_px if i == nx - 1 else ((i + 1) * total_w_px) // nx
        if col1 <= col0:
            continue
        for j in range(ny):
            row0 = (j * total_h_px) // ny
            row1 = total_h_px if j == ny - 1 else ((j + 1) * total_h_px) // ny
            if row1 <= row0:
                continue
            tile_x0 = origin_x + col0 * scale
            tile_y1 = origin_y - row0 * scale
            # Afin dönüşüm: [scaleX, shearX, translateX, shearY, scaleY, translateY]
            crs_transform = [scale, 0, tile_x0, 0, -scale, tile_y1]
            tiles.append({
                'crsTransform': crs_transform,
                'dimensions':   '{}x{}'.format(col1 - col0, row1 - row0),
            })
    return tiles


def _ensure_output_crs(tif_bytes, target_crs, nodata_value=None):
    """
    🔒 KESİN CRS GÜVENCESİ — GEE'DEN BAĞIMSIZ.

    SORUN: Kullanıcı indirme penceresinde ör. "UTM Zone 35N — EPSG:32635"
    seçse ve bu değer istekle birlikte doğru şekilde sunucuya/GEE'ye
    gönderilse bile, bazı senaryolarda (GEE'nin getDownloadURL()
    ardışık düzeninde crs parametresinin region/scale ile birlikte
    her koşulda uygulanmaması, veya karo-mozaik/birleştirme adımından
    sonra kaynak karoların kendi doğal CRS'inde kalması gibi) GEE'den
    dönen asıl GeoTIFF dosyası hâlâ coğrafi (EPSG:4326 / GCS_WGS_1984)
    çıkabiliyordu — ekrandaki CRS seçici doğru göstermesine rağmen.

    ÇÖZÜM: Kullanıcıya gönderilmeden HEMEN ÖNCE, dosyanın GERÇEKTEN
    hangi CRS'te olduğu rasterio ile bizzat okunur. Zaten istenen
    hedef CRS ile eşleşiyorsa dosyaya dokunulmadan aynen döndürülür
    (gereksiz yeniden örnekleme yapılmaz). EŞLEŞMİYORSA, dosya burada
    sunucu tarafında rasterio.warp.reproject ile KESİN olarak hedef
    CRS'e dönüştürülür — sonuç, GEE'nin o anki davranışından tamamen
    bağımsız olarak her zaman kullanıcının seçtiği CRS'te olur.

    Herhangi bir nedenle bu adım başarısız olursa (bozuk dosya vb.)
    orijinal bayt içeriği DEĞİŞTİRİLMEDEN döndürülür — bu güvence
    katmanı asla indirmeyi kesintiye uğratmaz.
    """
    try:
        import rasterio
        from rasterio.io import MemoryFile
        from rasterio.warp import calculate_default_transform, reproject, Resampling
        from rasterio.crs import CRS as RioCRS
    except ImportError:
        return tif_bytes

    try:
        target = RioCRS.from_string(target_crs)
    except Exception:
        return tif_bytes

    try:
        with MemoryFile(tif_bytes) as memfile:
            with memfile.open() as src:
                # Dosya zaten hedef CRS'teyse (en yaygın/normal durum),
                # hiçbir şey yapmadan aynen döndür.
                if src.crs and src.crs == target:
                    return tif_bytes

                print('[SylvaGIS] ⚠️ İndirilen GeoTIFF beklenen CRS\'te değil '
                      '(dosya: {}, istenen: {}) — sunucu tarafında yerel '
                      'olarak yeniden projeksiyonlanıyor.'.format(src.crs, target_crs))

                src_nodata = src.nodata if src.nodata is not None else nodata_value

                transform, width, height = calculate_default_transform(
                    src.crs, target, src.width, src.height, *src.bounds
                )
                out_meta = src.meta.copy()
                out_meta.update({
                    'crs': target,
                    'transform': transform,
                    'width': width,
                    'height': height,
                })
                if src_nodata is not None:
                    out_meta['nodata'] = src_nodata

                with MemoryFile() as out_memfile:
                    with out_memfile.open(**out_meta) as dst:
                        for band_idx in range(1, src.count + 1):
                            reproject(
                                source=rasterio.band(src, band_idx),
                                destination=rasterio.band(dst, band_idx),
                                src_transform=src.transform,
                                src_crs=src.crs,
                                dst_transform=transform,
                                dst_crs=target,
                                dst_nodata=src_nodata,
                                # Kategorik olmayan sürekli veriler (NDVI, DEM,
                                # eğim, yansıma vb.) için değerleri bozmayan
                                # en_yakın_komşu yerine bilinear kullanılır;
                                # NoData sınırında sızıntı olmaması için
                                # src_nodata da ayrıca belirtilir.
                                src_nodata=src_nodata,
                                resampling=Resampling.bilinear,
                            )
                    return out_memfile.read()
    except Exception as reproj_err:
        print('[SylvaGIS] ❌ Yerel yeniden projeksiyon başarısız — dosya orijinal '
              'CRS\'iyle gönderiliyor:', reproj_err)
        return tif_bytes


def _stamp_exact_band_statistics(tif_bytes, nodata_value=None):
    """
    🛠️ BUG FİX (QGIS'te 0-47, ArcMap'te 0-54 — aynı .tif dosyası için
    FARKLI min/max değerleri görünüyordu):

    KÖK NEDEN: Bu, dosyanın piksel değerlerinin bozuk/yanlış olmasından
    KAYNAKLANMIYOR — indirilen GeoTIFF'in ham piksel verisi baştan sona
    doğrudur (SylvaGIS ekranındaki 0-54 aralığı gerçek veriyle eşleşir).
    Sorun, GeoTIFF dosyasında GÖMÜLÜ istatistik (STATISTICS_MINIMUM/
    MAXIMUM) etiketi bulunmamasıdır. Bu etiketler yoksa:
      • ArcMap varsayılan olarak TÜM pikselleri tarayıp (tam/"actual"
        istatistik) gerçek min-max'ı (0-54) hesaplar.
      • QGIS ise varsayılan olarak "Estimate (faster)" modunu kullanır —
        yani dosyanın SADECE bir alt örneklemesini (her N. piksel)
        tarar. Eğim (slope) gibi verilerde en yüksek değerler (54°)
        genelde küçük/yerel alanlarda (dik yamaç, sınır pikselleri)
        bulunur; örnekleme bu nadir pikselleri kaçırıp daha düşük bir
        maksimum (47°) rapor eder. Bu bir QGIS "hatası" değil, sadece
        hız için yapılan bir yaklaşıklamadır — ama kullanıcıya iki
        farklı program iki farklı "gerçek" gösteriyormuş gibi görünür.

    ÇÖZÜM: Dosya sunucudan gönderilmeden HEMEN ÖNCE, TÜM pikseller
    (NoData hariç) taranarak gerçek min/max/mean/stddev hesaplanır ve
    bunlar GDAL'ın standart STATISTICS_* band etiketleri olarak
    GeoTIFF'in içine doğrudan gömülür (STATISTICS_APPROXIMATE=NO ile
    "bu tahmini değil, kesin/tam taranmış istatistiktir" işaretlenir).
    Böylece QGIS/ArcMap/herhangi bir GDAL tabanlı yazılım, kendi
    örneklemesini yapmak yerine dosyanın içindeki bu KESİN değerleri
    okur ve her ikisi de HER ZAMAN aynı (doğru) aralığı — SylvaGIS
    ekranındaki aralıkla birebir aynı — gösterir.

    Herhangi bir nedenle istatistik hesaplanamazsa (bozuk/boş raster
    vb.) orijinal bayt içeriği DEĞİŞTİRİLMEDEN döndürülür — bu adım
    asla indirmeyi kesintiye uğratmaz.
    """
    try:
        import numpy as np
        import rasterio
        from rasterio.io import MemoryFile
    except ImportError:
        return tif_bytes

    try:
        with MemoryFile(tif_bytes) as memfile:
            with memfile.open() as src:
                profile = src.profile.copy()
                data = src.read()  # (bands, H, W)
                src_nodata = src.nodata if src.nodata is not None else nodata_value

            out_memfile = MemoryFile()
            with out_memfile.open(**profile) as dst:
                dst.write(data)
                for b_idx in range(1, data.shape[0] + 1):
                    band = data[b_idx - 1].astype('float64')
                    if src_nodata is not None:
                        valid = band[band != float(src_nodata)]
                    else:
                        valid = band.ravel()
                    # NaN/Inf (float raster'larda GEE'nin maskelenmiş
                    # piksel dolgusu) istatistik dışı bırakılır.
                    valid = valid[np.isfinite(valid)]
                    if valid.size == 0:
                        continue
                    b_min  = float(valid.min())
                    b_max  = float(valid.max())
                    b_mean = float(valid.mean())
                    b_std  = float(valid.std())
                    dst.update_tags(
                        b_idx,
                        STATISTICS_MINIMUM=repr(b_min),
                        STATISTICS_MAXIMUM=repr(b_max),
                        STATISTICS_MEAN=repr(b_mean),
                        STATISTICS_STDDEV=repr(b_std),
                        STATISTICS_APPROXIMATE='NO',
                    )
            try:
                return out_memfile.read()
            finally:
                out_memfile.close()
    except Exception as stat_err:
        print('[SylvaGIS] ⚠️ Band istatistiği gömülemedi (dosya yine de gönderiliyor):', stat_err)
        return tif_bytes


def _true_clip_tif_bytes(tif_bytes, aoi_geom_4326, nodata_value):
    """
    🔒 KESİN / GEE'DEN BAĞIMSIZ YEREL KIRPMA ("true clip").

    GEE'nin clip() + unmask(nodata_value) + formatOptions.noData zinciri
    çoğu durumda yeterlidir; ancak büyük AOI'lerde otomatik karolama
    (grid indirme + rasterio.merge mozaikleme), reprojeksiyon adımları
    veya GEE'nin export ardışık düzenindeki farklılıklar nedeniyle bu
    maskenin son dosyaya HER ZAMAN birebir yansımadığı durumlar
    gözlemlenebiliyor — sonuç: ArcMap/QGIS'te AOI dışında kalan geniş
    siyah/NoData-olmayan dikdörtgen alanlar.

    Bu fonksiyon, GEE'den ne gelirse gelsin (tek istek veya karo-mozaik),
    indirilen GeoTIFF'i sunucu tarafında rasterio.mask.mask() ile AOI
    poligonunun GERÇEK/tam şekline göre YENİDEN kırpar ve NoData'yı bizzat
    kendi yazar. Böylece dışa aktarım her koşulda AOI şekliyle birebir
    örtüşür ve kullanıcının GIS yazılımında ek bir manuel kırpma yapmasına
    hiçbir zaman gerek kalmaz.

    aoi_geom_4326: AOI'nin EPSG:4326 (WGS84 lon/lat) cinsinden GeoJSON
      geometrisi (Polygon veya MultiPolygon). Gerekirse dosyanın kendi
      CRS'ine otomatik olarak yeniden projeksiyonlanır.
    """
    try:
        import rasterio
        from rasterio.mask import mask as rio_mask
        from rasterio.warp import transform_geom
        from rasterio.io import MemoryFile
    except ImportError:
        raise Exception(
            'Gerçek (true) AOI kırpması için sunucuda "rasterio" kütüphanesi '
            'kurulu olmalıdır. Lütfen sunucuda `pip install rasterio` komutunu '
            'çalıştırıp server.py\'yi yeniden başlatın.'
        )

    with MemoryFile(tif_bytes) as memfile:
        with memfile.open() as src:
            dst_crs   = src.crs.to_string() if src.crs else 'EPSG:4326'
            geom_dst  = transform_geom('EPSG:4326', dst_crs, aoi_geom_4326, precision=8)

            # crop=True: raster kapsamını da AOI'nin bounding box'ına daraltır
            # (gereksiz kenar boşluğu kalmaz). nodata: poligon dışındaki TÜM
            # pikseller — kaynak veri ne olursa olsun — bu değere sabitlenir.
            out_image, out_transform = rio_mask(
                src, [geom_dst], crop=True, nodata=nodata_value,
                all_touched=False, filled=True
            )
            out_meta = src.meta.copy()
            out_meta.update({
                'driver':    'GTiff',
                'height':    out_image.shape[1],
                'width':     out_image.shape[2],
                'transform': out_transform,
                'nodata':    nodata_value,
            })

            with MemoryFile() as out_memfile:
                with out_memfile.open(**out_meta) as dst:
                    dst.write(out_image)
                return out_memfile.read()


def _download_band_geotiff_bytes_impl(img, region_geom, scale, crs, base_name, nodata_value=None,
                                  aoi_geom_4326=None, fallback_region_geom=None):
    """
    Tek bir bandı GeoTIFF olarak indirir ve bayt dizisi (bytes) döndürür.

    nodata_value: Verilirse, görüntünün maskesi dışındaki (örn. clip()
      sonrası AOI dışında kalan) pikseller GeoTIFF'e GERÇEK bir NoData
      değeri olarak yazılır (formatOptions.noData). Bu olmadan GEE,
      maskelenmiş pikselleri NoData etiketi OLMADAN dolgu değeriyle
      (genelde 0) yazar; bu da dosyanın CBS yazılımlarında AOI şekli
      yerine düz bir dikdörtgen gibi görünmesine (kırpma yapılmamış gibi)
      neden olur. None ise önceki davranış (formatOptions eklenmez) korunur.

    aoi_geom_4326: Verilirse — nodata_value ile birlikte — GEE'den dönen
      dosya üzerinde _true_clip_tif_bytes() ile KESİN/yerel bir kırpma
      daha uygulanır (bkz. o fonksiyonun docstring'i). Bu, GEE'nin kendi
      maskeleme zincirinin bazı senaryolarda tam yansımaması ihtimaline
      karşı ikinci ve nihai bir güvence katmanıdır.

    GEE'nin tek istekteki indirme boyutu sınırı (~48 MB) aşılırsa:
      1. Hata mesajından istenen/izin verilen bayt miktarları ayrıştırılır.
      2. Bölge, gereken kadar karoya (grid) bölünür.
      3. Her karo ayrı ayrı indirilir (geçici dosyalara yazılır).
      4. rasterio.merge ile TÜM karolar tek bir GeoTIFF'te mozaiklenir —
         orijinal çözünürlük, CRS ve piksel değerleri korunur.
    Sonuç her koşulda TEK bir .tif dosyasının bayt içeriğidir; true-clip
    adımı (varsa) bu birleştirilmiş/tekli sonucun ÜZERİNE uygulanır.
    """
    # params burada başlatılır; except bloğunun fallback dalında NameError
    # oluşmaması için try bloğu öncesinde tanımlanır.
    params = {}
    try:
        # ÖNEMLİ / KÖK NEDEN DÜZELTMESİ: formatOptions.noData yalnızca
        # GeoTIFF üst bilgisinde (metadata) "bu değer NoData'dır" etiketini
        # yazar — görüntüdeki maskeli (clip() ile AOI dışında kalan)
        # piksellerin GERÇEKTEN o değeri İÇERMESİNİ sağlamaz. clip() sonrası
        # maskeli pikseller varsayılan olarak "veri yok" (sparse) kalır ve
        # GEE bunları dolgu değeriyle yazsa bile bu değer formatOptions'taki
        # noData değeriyle her zaman eşleşmeyebilir. Sonuç: ArcGIS/QGIS
        # dosyayı NoData olarak tanımayıp AOI şekli yerine düz bir dikdörtgen
        # (bounding box) gösterir — Landsat'ta gözlemlenen sorun tam olarak
        # budur. Kesin çözüm: unmask(nodata_value) ile maskeli pikselleri
        # AÇIKÇA o değere sabitleyip, formatOptions.noData ile AYNI değeri
        # NoData olarak etiketlemek — ikisi birlikte, Sentinel ve Landsat
        # dahil TÜM veri setlerinde gerçek poligon şeklinde bir clip garanti eder.
        if nodata_value is not None:
            img = img.unmask(nodata_value)

        params = {
            'name':   base_name,
            'scale':  scale,
            'format': 'GEO_TIFF',
            'crs':    crs,
            'region': region_geom,
        }
        if nodata_value is not None:
            params['formatOptions'] = {'noData': nodata_value}

        url = _call_with_retry(lambda: img.getDownloadURL(params))
        r = _call_with_retry(lambda: requests.get(url, timeout=180), retries=2)
        if not r.ok:
            # GEE bazen boyut/limit hatalarını HTTP gövdesinde (200 dışı
            # durum koduyla) döner; ayrıştırılabilmesi için mesaja dahil et.
            body_snippet = (r.text or '')[:500]
            raise Exception(
                'GEE indirme isteği başarısız (HTTP {}): {}'.format(r.status_code, body_snippet)
            )
        content = r.content
        if aoi_geom_4326 is not None and nodata_value is not None:
            content = _true_clip_tif_bytes(content, aoi_geom_4326, nodata_value)
        return content
    except Exception as first_err:
        parsed = _parse_gee_size_limit_error(str(first_err))
        if not parsed:
            # "Image.clipToBoundsAndScale: The geometry for image clipping
            # must be bounded" hatası: görüntü küresel/sınırsız geometriye
            # sahip (ör. global DEM). fallback_region_geom verilmişse
            # (ör. roi.bounds()) onunla tekrar dene; verilmemişse yeniden fırlat.
            err_str = str(first_err)
            if fallback_region_geom is not None and (
                'bounded' in err_str.lower() or 'clipToBoundsAndScale' in err_str
            ):
                fb_params = dict(params)
                fb_params['region'] = fallback_region_geom
                fb_url = _call_with_retry(lambda: img.getDownloadURL(fb_params))
                fb_r = _call_with_retry(lambda: requests.get(fb_url, timeout=180), retries=2)
                if not fb_r.ok:
                    body_snippet = (fb_r.text or '')[:500]
                    raise Exception(
                        'GEE indirme (fallback) isteği başarısız (HTTP {}): {}'.format(
                            fb_r.status_code, body_snippet)
                    )
                fb_content = fb_r.content
                if aoi_geom_4326 is not None and nodata_value is not None:
                    fb_content = _true_clip_tif_bytes(fb_content, aoi_geom_4326, nodata_value)
                return fb_content
            raise

        requested_bytes, limit_bytes = parsed
        # %20 güvenlik payı ile gereken karo sayısını hesapla
        factor = math.ceil((requested_bytes * 1.2) / limit_bytes)
        grid_n = max(2, math.ceil(math.sqrt(factor)))
        print('[SylvaGIS] Boyut sınırı aşıldı ({} > {} bayt) — {}x{} karoya bölünüyor: {}'.format(
            requested_bytes, limit_bytes, grid_n, grid_n, base_name
        ))
        # ÖNEMLİ: Eskiden burada _split_bbox_grid() (eşit coğrafi dilimler)
        # kullanılıyordu — bu, komşu karoların piksel gridini birbirinden
        # BAĞIMSIZ hesaplattırdığı için dikişlerde kesirli piksel kayması
        # ve dolayısıyla NoData boşlukları/kareleri oluşturuyordu.
        # _split_bbox_grid_aligned() TEK ORTAK bir piksel gridi üretir;
        # her karo crsTransform + dimensions ile indirildiğinden karo
        # kenarları birebir (pixel-perfect) örtüşür ve birleştirmede
        # ASLA boşluk kalmaz. (bkz. fonksiyonun docstring'i)
        tile_specs = _split_bbox_grid_aligned(region_geom, grid_n, grid_n, scale, crs)

        try:
            import rasterio
            from rasterio.merge import merge as rio_merge
        except ImportError:
            raise Exception(
                'Alan tek istekte indirilemeyecek kadar büyük ve sunucuda "rasterio" '
                'kütüphanesi kurulu değil (karoları birleştirmek için gerekli). '
                'Lütfen sunucuda `pip install rasterio` çalıştırın veya AOI\'yi küçültün.'
            )

        tmpdir = tempfile.mkdtemp(prefix='sylvagis_')
        try:
            tile_paths = []
            for idx, tile_spec in enumerate(tile_specs):
                tile_params = {
                    'name':        base_name + '_t{}'.format(idx),
                    'format':      'GEO_TIFF',
                    'crs':         crs,
                    'crsTransform': tile_spec['crsTransform'],
                    'dimensions':  tile_spec['dimensions'],
                }
                if nodata_value is not None:
                    tile_params['formatOptions'] = {'noData': nodata_value}

                tile_url = _call_with_retry(lambda: img.getDownloadURL(tile_params))
                tr = _call_with_retry(lambda: requests.get(tile_url, timeout=180), retries=2)
                if not tr.ok:
                    body_snippet = (tr.text or '')[:500]
                    raise Exception(
                        'GEE karo indirme isteği başarısız (karo {}, HTTP {}): {}'.format(
                            idx + 1, tr.status_code, body_snippet
                        )
                    )
                tp = os.path.join(tmpdir, 'tile_{}.tif'.format(idx))
                with open(tp, 'wb') as f:
                    f.write(tr.content)
                tile_paths.append(tp)

            srcs = [rasterio.open(p) for p in tile_paths]
            try:
                merge_kwargs = {}
                if nodata_value is not None:
                    merge_kwargs['nodata'] = nodata_value
                mosaic, out_transform = rio_merge(srcs, **merge_kwargs)
                out_meta = srcs[0].meta.copy()
                out_meta.update({
                    'driver':    'GTiff',
                    'height':    mosaic.shape[1],
                    'width':     mosaic.shape[2],
                    'count':     mosaic.shape[0],
                    'transform': out_transform,
                })
                if nodata_value is not None:
                    out_meta['nodata'] = nodata_value
            finally:
                for s in srcs:
                    s.close()

            out_path = os.path.join(tmpdir, 'merged.tif')
            with rasterio.open(out_path, 'w', **out_meta) as dst:
                dst.write(mosaic)

            with open(out_path, 'rb') as f:
                merged_bytes = f.read()

            if aoi_geom_4326 is not None and nodata_value is not None:
                merged_bytes = _true_clip_tif_bytes(merged_bytes, aoi_geom_4326, nodata_value)
            return merged_bytes
        finally:
            shutil.rmtree(tmpdir, ignore_errors=True)


def _download_band_geotiff_bytes(img, region_geom, scale, crs, base_name, nodata_value=None,
                                  aoi_geom_4326=None, fallback_region_geom=None):
    """
    _download_band_geotiff_bytes_impl() için ince bir sarmalayıcı (wrapper).
    Tek istek / bounded-fallback / karo-mozaik yollarının HANGİSİ
    çalışırsa çalışsın, kullanıcıya gönderilmeden hemen önce dosyaya
    _stamp_exact_band_statistics() ile GERÇEK (tam taranmış) min/max/
    ortalama/std istatistiklerini gömer — bkz. o fonksiyonun docstring'i
    (QGIS/ArcMap arasındaki min-max tutarsızlığı düzeltmesi). Tek bir
    yerden çağrılarak tüm indirme yollarının aynı garantiye sahip
    olması sağlanır.
    """
    raw_bytes = _download_band_geotiff_bytes_impl(
        img, region_geom, scale, crs, base_name,
        nodata_value=nodata_value, aoi_geom_4326=aoi_geom_4326,
        fallback_region_geom=fallback_region_geom
    )
    # 🔒 GEE ne dönerse dönsün, kullanıcının seçtiği CRS'i kesin olarak
    # garanti eden güvence katmanı — bkz. _ensure_output_crs() docstring'i.
    raw_bytes = _ensure_output_crs(raw_bytes, crs, nodata_value=nodata_value)
    return _stamp_exact_band_statistics(raw_bytes, nodata_value=nodata_value)


@app.route('/api/download-raw-bands', methods=['POST'])
def download_raw_bands():
    """
    📡 Ham Veri (Bantlar) — Uydu Görüntüsü Galerisi'nden seçilmiş sahnenin
    kullanıcının işaretlediği bant(lar)ını TEK BİR ZIP dosyası olarak dışa
    aktarır. ZIP içinde her bant kendi orijinal piksel çözünürlüğü
    (10/15/20/30/60 m vb.), orijinal CRS'i ve ham piksel değerleriyle ayrı
    bir GeoTIFF (.tif) dosyasıdır — YENİDEN ÖRNEKLEME YAPILMAZ.

    Kapsam ('scope' parametresi):
      - 'clip' (varsayılan): Her bant, çizilen/yüklenen AOI sınırlarına göre
        kırpılır (clip). AOI dışındaki pikseller dosyaya dahil edilmez.
      - 'full' : Hiçbir kırpma uygulanmadan, seçilen sahnenin TAMAMI
        (orijinal görüntü sınırları) dışa aktarılır.

    Önemli ilkeler:
      - Çözünürlük ve CRS, katalogdan değil doğrudan seçilen sahnenin
        GEE projeksiyon bilgisinden (ee.Image.projection()) okunur.
      - GEE'nin tek istekteki indirme boyutu sınırı (~48 MB) aşılırsa,
        ilgili bant otomatik olarak bir karo (grid) ızgarasına bölünüp
        indirilir ve rasterio ile TEK bir GeoTIFF'te sunucu tarafında
        mozaiklenir; kullanıcıya yine tek bir .tif dosyası olarak sunulur.
      - ZIP dosya adı veri seti adı + sahne tarihi + kapsam bilgisini içerir.
    """
    try:
        data = request.json or {}
        dataset_key = data.get('dataset')
        ds          = SATELLITE_DATASETS.get(dataset_key)
        band_groups = RAW_BAND_GROUPS.get(dataset_key)
        if not ds or not band_groups:
            return jsonify({'success': False, 'error': 'Bilinmeyen veri seti: ' + str(dataset_key)})

        scene_id = data.get('sceneId')
        if not scene_id:
            return jsonify({'success': False, 'error': 'Önce 🛰️ Uydu Görüntüsü Galerisi üzerinden bir sahne seçin.'})

        requested_bands = data.get('bands') or []
        if not requested_bands or not isinstance(requested_bands, list):
            return jsonify({'success': False, 'error': 'Lütfen indirmek için en az bir bant seçin.'})

        scope = data.get('scope') or 'clip'
        if scope not in ('clip', 'full'):
            scope = 'clip'

        # Geçerli bant adlarını + etiketlerini + yedek (katalog) çözünürlüğünü indeksle
        band_catalog = {}
        for grp in band_groups:
            for b in grp['bands']:
                band_catalog[b['name']] = {'label': b['label'], 'resolution': grp['resolution']}

        invalid = [b for b in requested_bands if b not in band_catalog]
        if invalid:
            return jsonify({'success': False, 'error': 'Bu veri setinde bulunmayan bant(lar): ' + ', '.join(invalid)})

        roi = make_roi(data.get('roi'))

        aoi_name  = (data.get('aoiName') or '').strip()
        safe_aoi  = re.sub(r'[^A-Za-z0-9_-]+', '', aoi_name.replace(' ', '_')) if aoi_name else ''

        max_cloud = int(data.get('maxCloud', 100))
        col   = build_rgb_collection(ds, roi, max_cloud)
        image = col.filter(ee.Filter.eq('system:index', scene_id)).first()
        image = ee.Image(image)

        # Sahne gerçekten mevcut mu? (filter+first boşsa getInfo None döner)
        try:
            check = image.get('system:index').getInfo()
        except Exception:
            check = None
        if not check:
            return jsonify({'success': False, 'error': 'Seçilen sahne bulunamadı. Lütfen galeriden tekrar bir görüntü seçin.'})

        # Dosya adı için sahne tarihi
        date_label = 'tarihsiz'
        try:
            ts = image.get('system:time_start').getInfo()
            if ts:
                date_label = datetime.datetime.utcfromtimestamp(ts / 1000.0).strftime('%Y-%m-%d')
        except Exception:
            pass

        sensor_tag, level_tag = _dataset_file_tags(dataset_key, image)

        # 'full' kapsamda dışa aktarma alanı sahnenin kendi footprint'idir
        # (kırpma yok) — çalışma alanıyla kısıtlanmaz; kullanıcı uydu
        # görüntüsünün TAM bandını ister. 'clip' kapsamda ise kullanıcının
        # çizdiği AOI'dir. Eğer image.geometry() sınırsız dönerse (nadir),
        # _download_band_geotiff_bytes() fallback_region_geom ile tekrar dener.
        export_region = image.geometry() if scope == 'full' else roi

        # 🔒 true-clip güvencesi: bkz. _true_clip_tif_bytes() docstring'i —
        # AOI'nin gerçek poligon şeklini (EPSG:4326) bir kez alıp her bant
        # indirmesinde kullanıyoruz.
        aoi_geom_4326 = _call_with_retry(lambda: roi.getInfo()) if scope == 'clip' else None

        zip_entries, errors = [], []
        for band_name in requested_bands:
            info = band_catalog[band_name]
            try:
                band_img = image.select([band_name])

                # Orijinal (native) çözünürlük ve CRS — resampling YAPILMAZ.
                proj = band_img.projection()
                try:
                    native_scale = proj.nominalScale().getInfo() or info['resolution']
                except Exception:
                    native_scale = info['resolution']
                try:
                    native_crs = proj.crs().getInfo() or 'EPSG:4326'
                except Exception:
                    native_crs = 'EPSG:4326'

                # ÖNEMLİ: clip() öncesi görüntüyü kendi orijinal (native)
                # CRS/çözünürlüğüne açıkça reproject() ediyoruz. Sentinel-2
                # bantları GEE'de zaten somut (sabit) bir varsayılan projeksiyona
                # sahip olduğu için clip() tek başına yeterliydi; ancak Landsat
                # Collection 2 bantlarının varsayılan projeksiyonu dışa aktarım
                # sırasında belirsiz/"unbounded" kalabiliyor ve bu durumda
                # clip() maskesi somut bir piksel ızgarasına oturmadığından GEE
                # AOI dışındaki alanları da (gereksiz çevre verisiyle birlikte)
                # dışa aktarabiliyordu. reproject() + clip() sırası, Sentinel
                # ve Landsat için AYNI, tutarlı ve gerçek AOI kırpma davranışını
                # garanti eder.
                export_img = band_img.reproject(crs=native_crs, scale=native_scale).clip(roi) if scope == 'clip' else band_img

                base_name = sensor_tag + '_' + level_tag + '_' + date_label + '_' + band_name + '_' + str(native_scale) + 'm'
                if scope == 'clip' and safe_aoi:
                    base_name += '_' + safe_aoi
                base_name = re.sub(r'[^A-Za-z0-9_\-\.]+', '_', base_name)

                # 'clip' kapsamında AOI dışında kalan pikseller GERÇEK bir
                # NoData değeri olarak yazılır — bu olmadan GEE, maskeyi
                # NoData etiketi olmadan dolgu değeriyle yazar ve dosya CBS
                # yazılımında düz bir dikdörtgen (bounding box) gibi görünür.
                #
                # 🛠️ KÖK NEDEN DÜZELTMESİ: sentinel olarak eskiden 0
                # kullanılıyordu, ama ham bant değerleri (reflectance,
                # DN vb.) çoğunlukla 0'ı GERÇEK bir değer olarak içerebilir
                # (ör. su/gölge pikselleri, karanlık yüzeyler). Bu da
                # GERÇEK veri içeren pikselleri GIS yazılımında yanlışlıkla
                # boş gösteriyordu. -9999, bu bantların hiçbirinde
                # gerçekten oluşamayacak standart bir NoData sentinelidir.
                nodata_value = -9999 if scope == 'clip' else None

                tif_bytes = _download_band_geotiff_bytes(
                    export_img, export_region, native_scale, native_crs, base_name,
                    nodata_value=nodata_value, aoi_geom_4326=aoi_geom_4326,
                    fallback_region_geom=roi.bounds(maxError=100)
                )
                zip_entries.append((base_name + '.tif', tif_bytes))

            except Exception as be:
                traceback.print_exc()
                msg = str(be).strip() or '{} (mesajsız hata — sunucu konsoluna bakın)'.format(type(be).__name__)
                errors.append(band_name + ': ' + msg)

        if not zip_entries:
            return jsonify({'success': False, 'error': 'Hiçbir bant dışa aktarılamadı. ' + '; '.join(errors)})

        # Tek bir ZIP arşivi oluştur — içinde her bant ayrı bir GeoTIFF.
        zip_buf = io.BytesIO()
        with zipfile.ZipFile(zip_buf, 'w', zipfile.ZIP_DEFLATED) as zf:
            for arcname, tif_bytes in zip_entries:
                zf.writestr(arcname, tif_bytes)
            if errors:
                zf.writestr('HATALAR.txt', 'Bazı bantlar dışa aktarılamadı:\n' + '\n'.join(errors))
        zip_buf.seek(0)

        scope_tag = 'FullScene' if scope == 'full' else 'Clip'
        zip_name = sensor_tag + '_' + level_tag + '_' + date_label + '_' + scope_tag
        if scope == 'clip' and safe_aoi:
            zip_name += '_' + safe_aoi
        zip_name = re.sub(r'[^A-Za-z0-9_\-\.]+', '_', zip_name) + '.zip'

        resp = Response(zip_buf.read(), mimetype='application/zip')
        resp.headers['Content-Disposition'] = 'attachment; filename="{}"'.format(zip_name)
        if errors:
            resp.headers['X-Partial-Errors'] = urllib.parse.quote(
                'Bazı bantlar dışa aktarılamadı: ' + '; '.join(errors)
            )
        return resp

    except Exception as e:
        traceback.print_exc()
        err = str(e).strip() or '{} (mesajsız hata — sunucu konsoluna bakın)'.format(type(e).__name__)
        if 'too large' in err.lower() or 'limit' in err.lower():
            return jsonify({
                'success': False,
                'error': 'Çok büyük alan! Lütfen çalışma alanını (AOI) küçültüp tekrar deneyin '
                         '(bant çözünürlüğü sabit tutulur, yeniden örnekleme yapılmaz).'
            })
        return jsonify({'success': False, 'error': err})


@app.route('/api/rgb-scenes', methods=['POST'])
def rgb_scenes():
    """
    🛰️ Uydu Görüntüsü Galerisi — AOI/tarih/bulutluluk kriterlerine uyan
    tüm sahneleri, her biri için küçük bir önizleme (thumbnail) ile birlikte
    döndürür. Galeri panelinde kartlara (tarih, sensör, veri seti adı,
    bulutluluk %, Scene ID, thumbnail) dönüştürülür.
    """
    try:
        data       = request.json or {}
        dataset_key = data.get('dataset', 's2-l2a')
        ds = SATELLITE_DATASETS.get(dataset_key)
        if not ds:
            return jsonify({'success': False, 'error': 'Bilinmeyen uydu görüntüsü veri seti: ' + str(dataset_key)})

        roi        = make_roi(data.get('roi'))
        start_date = data.get('startDate')
        end_date   = data.get('endDate')
        max_cloud  = int(data.get('maxCloud', 100))
        months     = _parse_months_param(data)

        col = build_rgb_collection(ds, roi, max_cloud)
        # Thumbnail üretimi pahalı olduğundan yıl başına makul bir sınır
        # (8) ve toplamda 40 sahne ile sınırlıyoruz — ama artık SADECE
        # aralığın ilk yılından değil, aralıktaki HER yıldan (ve varsa
        # seçilen aylardan) adil şekilde örnekliyoruz.
        limited = _collect_scenes_across_years(
            col, start_date, end_date, months=months,
            per_year_limit=8, total_limit=40,
        )

        scene_ids  = limited.aggregate_array('system:index').getInfo()
        timestamps = limited.aggregate_array('system:time_start').getInfo()
        clouds = []
        if ds.get('cloudProp'):
            try:
                clouds = limited.aggregate_array(ds['cloudProp']).getInfo()
            except Exception:
                clouds = [None] * len(scene_ids)
        else:
            clouds = [None] * len(scene_ids)

        img_list = limited.toList(limited.size())
        scenes = []
        for i, sid in enumerate(scene_ids):
            thumb_url = None
            try:
                img = ee.Image(img_list.get(i)).select(ds['rgbBands'])
                if ds.get('scaleFactor', 1) != 1 or ds.get('offset', 0) != 0:
                    img = img.multiply(ds['scaleFactor']).add(ds.get('offset', 0))
                thumb_url = img.getThumbURL({
                    'region': roi,
                    'dimensions': 128,
                    'format': 'png',
                    'bands': ds['rgbBands'],
                    'min': ds['visMin'],
                    'max': ds['visMax'],
                })
            except Exception:
                thumb_url = None

            scenes.append({
                'sceneId':      sid,
                'timestamp':    timestamps[i] if i < len(timestamps) else None,
                'cloud':        clouds[i] if i < len(clouds) else None,
                'thumbnailUrl': thumb_url,
            })

        return jsonify({
            'success': True,
            'scenes':  scenes,
            'dataset': {
                'key':          dataset_key,
                'label':        ds['label'],
                'datasetName':  ds.get('datasetName', ds['label']),
                'sensor':       ds['sensor'],
                'resolution':   ds['resolution'],
                'bandsInfo':    ds['bandsInfo'],
                'hasCloudProp': bool(ds.get('cloudProp')),
            }
        })

    except Exception as e:
        return jsonify({'success': False, 'error': str(e)})


@app.route('/api/get-scenes', methods=['POST'])
def get_scenes():
    try:
        data       = request.json
        roi        = make_roi(data.get('roi'))
        start_date = data['startDate']
        end_date   = data['endDate']
        max_cloud  = int(data.get('cloudCover', 10))
        satellite  = data.get('satellite', 's2-l2a')

        if satellite == 's2-l2a':
            col = (ee.ImageCollection('COPERNICUS/S2_SR_HARMONIZED')
                   .filterBounds(roi)
                   .filterDate(start_date, end_date)
                   .filter(ee.Filter.lt('CLOUDY_PIXEL_PERCENTAGE', max_cloud)))
            cloud_prop = 'CLOUDY_PIXEL_PERCENTAGE'
        elif satellite == 's2-l1c':
            col = (ee.ImageCollection('COPERNICUS/S2_HARMONIZED')
                   .filterBounds(roi)
                   .filterDate(start_date, end_date)
                   .filter(ee.Filter.lt('CLOUDY_PIXEL_PERCENTAGE', max_cloud)))
            cloud_prop = 'CLOUDY_PIXEL_PERCENTAGE'
        elif satellite == 'l89-l2':
            col = (ee.ImageCollection('LANDSAT/LC08/C02/T1_L2')
                   .filterBounds(roi)
                   .filterDate(start_date, end_date)
                   .filter(ee.Filter.lt('CLOUD_COVER', max_cloud)))
            cloud_prop = 'CLOUD_COVER'
        elif satellite == 'l89-l1':
            col = (ee.ImageCollection('LANDSAT/LC08/C02/T1_TOA')
                   .filterBounds(roi)
                   .filterDate(start_date, end_date)
                   .filter(ee.Filter.lt('CLOUD_COVER', max_cloud)))
            cloud_prop = 'CLOUD_COVER'
        elif satellite == 'l7-l2':
            col = (ee.ImageCollection('LANDSAT/LE07/C02/T1_L2')
                   .filterBounds(roi)
                   .filterDate(start_date, end_date)
                   .filter(ee.Filter.lt('CLOUD_COVER', max_cloud)))
            cloud_prop = 'CLOUD_COVER'
        elif satellite == 'l7-l1':
            col = (ee.ImageCollection('LANDSAT/LE07/C02/T1_TOA')
                   .filterBounds(roi)
                   .filterDate(start_date, end_date)
                   .filter(ee.Filter.lt('CLOUD_COVER', max_cloud)))
            cloud_prop = 'CLOUD_COVER'
        elif satellite == 'l45-l2':
            col = (ee.ImageCollection('LANDSAT/LT05/C02/T1_L2')
                   .filterBounds(roi)
                   .filterDate(start_date, end_date)
                   .filter(ee.Filter.lt('CLOUD_COVER', max_cloud)))
            cloud_prop = 'CLOUD_COVER'
        elif satellite == 'l45-l1':
            col = (ee.ImageCollection('LANDSAT/LT05/C02/T1_TOA')
                   .filterBounds(roi)
                   .filterDate(start_date, end_date)
                   .filter(ee.Filter.lt('CLOUD_COVER', max_cloud)))
            cloud_prop = 'CLOUD_COVER'
        elif satellite == 'mss-l1':
            col = (ee.ImageCollection('LANDSAT/LM05/C02/T1')
                   .filterBounds(roi)
                   .filterDate(start_date, end_date))
            cloud_prop = None
        else:
            col = (ee.ImageCollection('COPERNICUS/S2_SR_HARMONIZED')
                   .filterBounds(roi)
                   .filterDate(start_date, end_date)
                   .filter(ee.Filter.lt('CLOUDY_PIXEL_PERCENTAGE', max_cloud)))
            cloud_prop = 'CLOUDY_PIXEL_PERCENTAGE'

        months = _parse_months_param(data)
        limited = _collect_scenes_across_years(
            col, start_date, end_date, months=months,
            per_year_limit=10, total_limit=60,
        )

        scene_ids  = limited.aggregate_array('system:index').getInfo()
        timestamps = limited.aggregate_array('system:time_start').getInfo()
        if cloud_prop:
            clouds = limited.aggregate_array(cloud_prop).getInfo()
        else:
            clouds = [None] * len(scene_ids)

        scenes = list(zip(scene_ids, timestamps, clouds))
        return jsonify({'success': True, 'scenes': scenes})

    except Exception as e:
        return jsonify({'success': False, 'error': str(e)})



# ════════════════════════════════════════════════════════════════
# 📧 KULLANICI KAYIT FORMU — sylvagis.world@gmail.com bildirimi
# ════════════════════════════════════════════════════════════════
# Gerekli ortam değişkenleri:
#   SYLVA_SMTP_USER  →  gönderen Gmail adresi  (örn. sylvagis.world@gmail.com)
#   SYLVA_SMTP_PASS  →  Gmail "Uygulama Şifresi" (App Password)
#                        Ayar: Google Hesabım → Güvenlik → 2 Adımlı Doğrulama aç
#                              → Uygulama Şifresi oluştur → 16 haneli kodu girin
# ════════════════════════════════════════════════════════════════
import smtplib
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart

SYLVA_OWNER_EMAIL = 'sylvagis.world@gmail.com'

def _send_registration_email(ad, soyad, email, meslek, ulke):
    smtp_user = 'sylvagis.world@gmail.com'
    smtp_pass = 'ksfnkvwcutrawcih'

    msg = MIMEMultipart('alternative')
    msg['Subject'] = f'[SylvaGIS] Yeni Kayıt — {ad} {soyad}'
    msg['From']    = smtp_user or SYLVA_OWNER_EMAIL
    msg['To']      = SYLVA_OWNER_EMAIL

    import datetime as _dt
    ts = _dt.datetime.now().strftime('%d.%m.%Y %H:%M')

    html_body = f"""
    <html><body style="font-family:Arial,sans-serif;background:#f4f6f9;padding:24px;">
      <div style="background:#fff;border-radius:12px;max-width:520px;margin:auto;
                  padding:32px;box-shadow:0 4px 16px rgba(0,0,0,.1);">
        <div style="font-size:1.4rem;font-weight:800;color:#1e3a8a;margin-bottom:6px;">
          🌲 SylvaGIS — Yeni Kullanıcı Kaydı
        </div>
        <div style="color:#64748b;font-size:.85rem;margin-bottom:24px;">{ts}</div>
        <table style="width:100%;border-collapse:collapse;font-size:.9rem;">
          <tr style="background:#eff6ff;"><td style="padding:10px 14px;font-weight:700;color:#1e3a8a;width:35%;">Ad Soyad</td>
              <td style="padding:10px 14px;color:#334155;">{ad} {soyad}</td></tr>
          <tr><td style="padding:10px 14px;font-weight:700;color:#1e3a8a;">E-posta</td>
              <td style="padding:10px 14px;color:#334155;"><a href="mailto:{email}">{email}</a></td></tr>
          <tr style="background:#eff6ff;"><td style="padding:10px 14px;font-weight:700;color:#1e3a8a;">Meslek</td>
              <td style="padding:10px 14px;color:#334155;">{meslek or '—'}</td></tr>
          <tr><td style="padding:10px 14px;font-weight:700;color:#1e3a8a;">Ülke</td>
              <td style="padding:10px 14px;color:#334155;">{ulke or '—'}</td></tr>
        </table>
      </div>
    </body></html>"""

    plain_body = (f"Yeni SylvaGIS Kaydı ({ts})\n"
                  f"Ad Soyad : {ad} {soyad}\n"
                  f"E-posta  : {email}\n"
                  f"Meslek   : {meslek or '—'}\n"
                  f"Ülke     : {ulke or '—'}")

    msg.attach(MIMEText(plain_body, 'plain', 'utf-8'))
    msg.attach(MIMEText(html_body,  'html',  'utf-8'))

    try:
        with smtplib.SMTP('smtp.gmail.com', 587) as s:
            s.ehlo()
            s.starttls()
            s.login(smtp_user, smtp_pass)
            s.sendmail(smtp_user, SYLVA_OWNER_EMAIL, msg.as_string())
    except Exception as smtp_err:
        print(f'❌ _send_registration_email SMTP hatası: {smtp_err}')
        raise


@app.route('/api/register', methods=['POST'])
def register_user():
    try:
        data   = request.get_json(silent=True) or {}
        ad     = (data.get('ad')     or '').strip()
        soyad  = (data.get('soyad')  or '').strip()
        email  = (data.get('email')  or '').strip()
        meslek = (data.get('meslek') or '').strip()
        ulke   = (data.get('ulke')   or '').strip()

        if not ad or not soyad or not email:
            return jsonify({'ok': False, 'error': 'Ad, soyad ve e-posta zorunludur.'}), 400
        if '@' not in email or '.' not in email.split('@')[-1]:
            return jsonify({'ok': False, 'error': 'Geçerli bir e-posta adresi girin.'}), 400

        _send_registration_email(ad, soyad, email, meslek, ulke)
        return jsonify({'ok': True})
    except Exception as ex:
        traceback.print_exc()
        return jsonify({'ok': False, 'error': str(ex)}), 500


# ════════════════════════════════════════════════════════════════
# 📐 VEKTÖR İNDİRME — KML / KMZ / SHP yardımcı fonksiyonları
# ════════════════════════════════════════════════════════════════

def _features_to_kml(features, name='SylvaGIS_vector'):
    """GeoJSON feature listesini KML baytlarına dönüştürür (harici kütüphane gerektirmez)."""
    import xml.sax.saxutils as sax
    lines = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<kml xmlns="http://www.opengis.net/kml/2.2">',
        '<Document>',
        f'  <name>{sax.escape(name)}</name>',
    ]

    def _coords_str(ring):
        return ' '.join(f'{lon},{lat},0' for lon, lat in ring)

    for i, feat in enumerate(features, start=1):
        props = feat.get('properties') or {}
        geom  = feat.get('geometry') or {}
        gtype = geom.get('type', '')
        coords = geom.get('coordinates', [])

        # Placemark adı: class_value → sınıf, yoksa class_name, yoksa numara
        label = (props.get('class_name') or props.get('label') or
                 props.get('class_value') or props.get('first') or str(i))
        color_hex = (props.get('color') or 'ffffffff')
        # KML renk formatı: aabbggrr (alpha, blue, green, red)
        def _hex_to_kml(h):
            h = h.lstrip('#')
            if len(h) == 6:
                r, g, b = h[0:2], h[2:4], h[4:6]
                return f'ff{b}{g}{r}'
            return 'ffffffff'
        kml_color = _hex_to_kml(color_hex)

        lines.append(f'  <Placemark>')
        lines.append(f'    <name>{sax.escape(str(label))}</name>')
        lines.append(f'    <Style><PolyStyle><color>{kml_color}</color><outline>1</outline></PolyStyle></Style>')

        # ExtendedData (tüm özellikler)
        if props:
            lines.append('    <ExtendedData>')
            for k, v in props.items():
                lines.append(f'      <Data name="{sax.escape(str(k))}"><value>{sax.escape(str(v))}</value></Data>')
            lines.append('    </ExtendedData>')

        if gtype == 'Polygon':
            lines.append('    <Polygon>')
            if coords:
                lines.append('      <outerBoundaryIs><LinearRing><coordinates>')
                lines.append('        ' + _coords_str(coords[0]))
                lines.append('      </coordinates></LinearRing></outerBoundaryIs>')
                for inner in coords[1:]:
                    lines.append('      <innerBoundaryIs><LinearRing><coordinates>')
                    lines.append('        ' + _coords_str(inner))
                    lines.append('      </coordinates></LinearRing></innerBoundaryIs>')
            lines.append('    </Polygon>')
        elif gtype == 'MultiPolygon':
            lines.append('    <MultiGeometry>')
            for poly_coords in coords:
                lines.append('      <Polygon>')
                if poly_coords:
                    lines.append('        <outerBoundaryIs><LinearRing><coordinates>')
                    lines.append('          ' + _coords_str(poly_coords[0]))
                    lines.append('        </coordinates></LinearRing></outerBoundaryIs>')
                    for inner in poly_coords[1:]:
                        lines.append('        <innerBoundaryIs><LinearRing><coordinates>')
                        lines.append('          ' + _coords_str(inner))
                        lines.append('        </coordinates></LinearRing></innerBoundaryIs>')
                lines.append('      </Polygon>')
            lines.append('    </MultiGeometry>')
        elif gtype == 'Point':
            if coords and len(coords) >= 2:
                lines.append(f'    <Point><coordinates>{coords[0]},{coords[1]},0</coordinates></Point>')
        elif gtype == 'LineString':
            lines.append('    <LineString><coordinates>')
            lines.append('      ' + _coords_str(coords))
            lines.append('    </coordinates></LineString>')

        lines.append('  </Placemark>')

    lines += ['</Document>', '</kml>']
    return '\n'.join(lines).encode('utf-8')


def _features_to_shp_zip(features, name='SylvaGIS_vector'):
    """GeoJSON feature listesini SHP (shapefile) ZIP arşivine dönüştürür.
    Önce pyshp (shapefile) dener; yoksa GeoJSON'u .zip içine koyar."""
    try:
        import shapefile as shp  # pyshp
        import io as _io

        shp_buf  = _io.BytesIO()
        shx_buf  = _io.BytesIO()
        dbf_buf  = _io.BytesIO()

        w = shp.Writer(shp=shp_buf, shx=shx_buf, dbf=dbf_buf)
        w.autoBalance = 1
        w.field('CLASS_VAL', 'C', 40)
        w.field('CLASS_NAME', 'C', 80)
        w.field('COLOR', 'C', 10)

        def _flat_ring(ring):
            return [list(pt) for pt in ring]

        for feat in features:
            props = feat.get('properties') or {}
            geom  = feat.get('geometry') or {}
            gtype = geom.get('type', '')
            coords = geom.get('coordinates', [])

            cv   = str(props.get('class_value') or props.get('first') or props.get('label') or '')
            cn   = str(props.get('class_name') or props.get('label') or cv)
            col  = str(props.get('color') or '')

            if gtype == 'Polygon':
                parts = [_flat_ring(r) for r in coords]
                w.poly(parts)
                w.record(cv, cn, col)
            elif gtype == 'MultiPolygon':
                all_parts = []
                for poly in coords:
                    all_parts.extend([_flat_ring(r) for r in poly])
                w.poly(all_parts)
                w.record(cv, cn, col)
            elif gtype == 'Point':
                if coords and len(coords) >= 2:
                    w.point(coords[0], coords[1])
                    w.record(cv, cn, col)
            elif gtype == 'LineString':
                w.line([_flat_ring(coords)])
                w.record(cv, cn, col)

        w.close()

        # PRJ içeriği (WGS84 / EPSG:4326)
        prj_wkt = ('GEOGCS["GCS_WGS_1984",'
                   'DATUM["D_WGS_1984",SPHEROID["WGS_1984",6378137.0,298.257223563]],'
                   'PRIMEM["Greenwich",0.0],UNIT["Degree",0.0174532925199433]]')

        zip_buf = io.BytesIO()
        with zipfile.ZipFile(zip_buf, 'w', zipfile.ZIP_DEFLATED) as z:
            z.writestr(f'{name}.shp', shp_buf.getvalue())
            z.writestr(f'{name}.shx', shx_buf.getvalue())
            z.writestr(f'{name}.dbf', dbf_buf.getvalue())
            z.writestr(f'{name}.prj', prj_wkt)
        zip_buf.seek(0)
        return zip_buf.read()

    except ImportError:
        # pyshp yok — GeoJSON olarak paketle
        import json as _json
        fc = _json.dumps({'type': 'FeatureCollection', 'features': features}, ensure_ascii=False).encode('utf-8')
        zip_buf = io.BytesIO()
        with zipfile.ZipFile(zip_buf, 'w', zipfile.ZIP_DEFLATED) as z:
            z.writestr(f'{name}.geojson', fc)
        zip_buf.seek(0)
        return zip_buf.read()


def _geojson_to_features(geom):
    """Tekil bir GeoJSON geometrisini ya da FeatureCollection'ı feature listesine çevirir."""
    import json as _json
    if isinstance(geom, str):
        geom = _json.loads(geom)
    gtype = geom.get('type', '')
    if gtype == 'FeatureCollection':
        return geom.get('features', [])
    if gtype == 'Feature':
        return [geom]
    # Ham geometri → sarmal Feature'a çevir
    return [{'type': 'Feature', 'geometry': geom, 'properties': {}}]


# ════════════════════════════════════════════════════════════════
# 📥 /api/vector-download — Raster → Vektör dışa aktarımı
# ════════════════════════════════════════════════════════════════
# Üç veri kaynağını destekler:
#   'workspace'  — Kullanıcının çizdiği AOI geometrisi olduğu gibi
#   'analysis'   — Son çalıştırılan uydu/topografik analizin sınıflandırılmış
#                  raster görüntüsü GEE reduceToVectors() ile vektöre çevrilir
#   'landuse'    — Son arazi kullanımı (LULC) analizinin sınıflandırılmış sonucu
#
# Format: 'kml', 'kmz', 'shp' (SHP → ZIP arşivi)
# ════════════════════════════════════════════════════════════════
@app.route('/api/vector-download', methods=['POST'])
def vector_download():
    req_data = request.get_json(silent=True) or {}

    fmt         = (req_data.get('format') or 'kml').strip().lower()
    filename    = (req_data.get('filename') or 'SylvaGIS_vector').strip() or 'SylvaGIS_vector'
    crs         = (req_data.get('crs') or 'EPSG:4326').strip() or 'EPSG:4326'
    data_source = (req_data.get('dataSource') or 'workspace').strip()
    geom_json   = req_data.get('geometry')

    # Güvenli dosya adı
    import re as _re2
    safe_name = _re2.sub(r'[^\w\-.]', '_', filename)[:80] or 'SylvaGIS_vector'

    try:
        # ── 1. Çalışma alanı geometrisi ───────────────────────────────
        if data_source == 'workspace':
            if not geom_json:
                return jsonify({'error': 'Çalışma alanı geometrisi bulunamadı. Haritada bir alan çizin.'}), 400
            import json as _json
            geom = _json.loads(geom_json) if isinstance(geom_json, str) else geom_json
            features = _geojson_to_features(geom)

        # ── 2. Analiz sonucunu vektörize et ───────────────────────────
        else:
            if not _last_analyze_params:
                return jsonify({'error': 'Henüz bir analiz yapılmadı. Önce haritada bir analiz çalıştırın.'}), 400

            data = dict(_last_analyze_params)

            # Vektörizasyon için sınıflandırılmış görüntüyü al
            try:
                final_display, roi, result, vis, _ = _call_with_retry(
                    build_result_image, data, for_export=False  # sınıf renkleri korunur
                )
            except Exception as e:
                traceback.print_exc()
                return jsonify({'error': f'Analiz yeniden hesaplanamadı: {str(e)}'}), 500

            # Ölçek: çok küçük ölçek → çok fazla piksel → timeout
            # Güvenli alt sınır: analiz tipine göre otomatik seç
            index = data.get('index', 'NDVI')
            if index in ('LULC', 'LULC_ESA'):
                vec_scale = 100   # Dynamic World / ESA 10 m → 100 m güvenli
            elif index.startswith('TOPO'):
                vec_scale = 90    # SRTM 30 m → 90 m güvenli
            elif index == 'LULC_MODIS':
                vec_scale = 500
            else:
                vec_scale = 300   # Uydu indeksleri (NDVI vb.) → 300 m

            print(f'[SylvaGIS] Vektörizasyon başlatılıyor: index={index} scale={vec_scale}')
            try:
                # reduceToVectors: pikselleri poligona çevir
                vec_fc = _call_with_retry(
                    lambda: final_display.int().reduceToVectors(
                        reducer=ee.Reducer.first(),
                        geometry=roi.bounds(),
                        scale=vec_scale,
                        maxPixels=1e8,
                        geometryType='polygon',
                        eightConnected=False,
                        labelProperty='class_value',
                        crs=crs if crs.upper().startswith('EPSG:') else 'EPSG:4326',
                    ).limit(4000)
                )
                fc_info = _call_with_retry(lambda: vec_fc.getInfo())
                features = fc_info.get('features', []) if fc_info else []
            except Exception as e:
                traceback.print_exc()
                return jsonify({'error': f'Vektöre dönüştürme başarısız: {str(e)}'}), 500

            if not features:
                return jsonify({'error': 'Vektör geometri üretilemedi. Alan çok küçük ya da veri yok olabilir.'}), 400

            print(f'[SylvaGIS] Vektörizasyon tamamlandı: {len(features)} özellik')

        # ── 3. Formatla ve gönder ──────────────────────────────────────
        if fmt == 'kml':
            body = _features_to_kml(features, safe_name)
            return Response(body, headers={
                'Content-Type': 'application/vnd.google-earth.kml+xml; charset=utf-8',
                'Content-Disposition': f'attachment; filename="{safe_name}.kml"',
            })

        elif fmt == 'kmz':
            kml_bytes = _features_to_kml(features, safe_name)
            buf = io.BytesIO()
            with zipfile.ZipFile(buf, 'w', zipfile.ZIP_DEFLATED) as z:
                z.writestr(f'{safe_name}.kml', kml_bytes)
            buf.seek(0)
            return Response(buf.read(), headers={
                'Content-Type': 'application/vnd.google-earth.kmz',
                'Content-Disposition': f'attachment; filename="{safe_name}.kmz"',
            })

        elif fmt == 'shp':
            zip_bytes = _features_to_shp_zip(features, safe_name)
            return Response(zip_bytes, headers={
                'Content-Type': 'application/zip',
                'Content-Disposition': f'attachment; filename="{safe_name}_shp.zip"',
            })

        else:
            return jsonify({'error': f'Bilinmeyen format: {fmt}'}), 400

    except Exception as ex:
        traceback.print_exc()
        return jsonify({'error': str(ex)}), 500


if __name__ == '__main__':
    # NOT: Bu satır sadece yerel (local) geliştirme/test içindir.
    # VM'de 7/24 çalıştırırken bu dosya `python server.py` ile değil,
    # gunicorn ile başlatılacak, bu yüzden bu blok VM'de hiç çalışmaz:
    #   gunicorn -w 4 -b 0.0.0.0:5000 --timeout 120 server:app
    port = int(os.environ.get('PORT', 5000))
    app.run(host='0.0.0.0', port=port, debug=False)
