import ee
import re
import io
import os
import math
import time
import shutil
import zipfile
import tempfile
import datetime
import traceback
import urllib.parse
import requests
from flask import Flask, request, jsonify, Response
from flask_cors import CORS

app = Flask(__name__)
CORS(app)
print('SylvaGIS server.py yüklendi — versiyon: zip-export-v2-tiling')


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
        credentials = ee.ServiceAccountCredentials(
            GEE_SERVICE_ACCOUNT_EMAIL, GEE_SERVICE_ACCOUNT_KEY
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
    smtp_pass = 'aaaaaaaaaaaaaaaa'

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
            if meta.get('crs'):
                _last_analyze_native_crs = meta['crs']

            return jsonify({
                'success':  True,
                'tileUrl':  tile_url,
                'index':    'RGB',
                'meta':     meta,
                'nativeCrs': meta.get('crs'),
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
        except Exception:
            native_crs = None
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
                limited    = col2.filterDate(start_date, end_date).sort('system:time_start').limit(10)
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

        col = build_rgb_collection(ds, roi, max_cloud)
        limited = col.filterDate(start_date, end_date).sort('system:time_start').limit(12)

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

        limited = col.sort('system:time_start').limit(10)

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
    smtp_pass = 'aaaaaaaaaaaaaaaaaa'

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

if __name__ == '__main__':
    # NOT: Bu satır sadece yerel (local) geliştirme/test içindir.
    # VM'de 7/24 çalıştırırken bu dosya `python server.py` ile değil,
    # gunicorn ile başlatılacak, bu yüzden bu blok VM'de hiç çalışmaz:
    #   gunicorn -w 4 -b 0.0.0.0:5000 --timeout 120 server:app
    port = int(os.environ.get('PORT', 5000))
    app.run(host='0.0.0.0', port=port, debug=False)
