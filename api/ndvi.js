// api/ndvi.js
const ee = require('@google/ee');

export default async function handler(req, res) {
  try {
    // Vercel'deki Environment Variables'tan anahtarı oku
    const privateKey = JSON.parse(process.env.GEE_JSON);
    
    ee.data.authenticateViaPrivateKey(privateKey, () => {
      ee.initialize(null, null, async () => {
        
        // Kullanıcıdan gelen verileri al (Poligon, Başlangıç, Bitiş)
        const { geometry, startDate, endDate } = req.body;

        // Sentinel-2 Verisi ile NDVI Analizi
        const collection = ee.ImageCollection('COPERNICUS/S2_SR_HARMONIZED')
          .filterBounds(geometry)
          .filterDate(startDate, endDate)
          .filter(ee.Filter.lt('CLOUDY_PIXEL_PERCENTAGE', 10));

        const ndvi = collection.map(image => 
          image.normalizedDifference(['B8', 'B4']).rename('NDVI')
        ).median().clip(geometry);

        // Harita Katmanı için URL üret
        ndvi.getMap({min: 0, max: 1, palette: ['red', 'yellow', 'green']}, (map) => {
          res.status(200).json({ url: map.urlFormat });
        });
      });
    });
  } catch (error) {
    res.status(500).json({ error: "Analiz sırasında hata oluştu: " + error.message });
  }
}
