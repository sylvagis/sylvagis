# Temel Python imajı
FROM python:3.10-slim

# Rasterio ve Shapely için gerekli sistem bağımlılıklarını (GDAL) kur
RUN apt-get update && apt-get install -y \
    gdal-bin \
    libgdal-dev \
    && rm -rf /var/lib/apt/lists/*

# GDAL ortam değişkenlerini ayarla
ENV CPLUS_INCLUDE_PATH=/usr/include/gdal
ENV C_INCLUDE_PATH=/usr/include/gdal

# Çalışma dizinini belirle
WORKDIR /app

# Kütüphaneleri kopyala ve kur
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Uygulama kodlarını kopyala
COPY . .

# Gunicorn ile Flask uygulamasını başlat. 
# GEE indirmelerinin kesilmemesi için timeout süresi 180 saniye olarak ayarlandı.
CMD exec gunicorn --bind :$PORT --workers 2 --timeout 180 server:app
