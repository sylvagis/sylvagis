// api/ndvi.js
const ee = require('@google/ee');

export default async function handler(req, res) {
  // 1. Yetkilendirme (Vercel'e eklediğin gizli anahtarı kullanır)
  const privateKey = JSON.parse(process.env.GEE_JSON);
  
  ee.data.authenticateViaPrivateKey(privateKey, () => {
    ee.initialize(null, null, async () => {
      
      // 2. Kullanıcıdan gelen koordinatları ve tarihleri al
      const { geometry, startDate, endDate } = req.body;

      // 3. GEE üzerinde NDVI analizi
      const collection = ee.ImageCollection('COPERNICUS/S2_SR_HARMONIZED')
        .filterBounds(geometry)
        .filterDate(startDate, endDate)
        .filter(ee.Filter.lt('CLOUDY_PIXEL_PERCENTAGE', 10));

      const ndvi = collection.map(image => 
        image.normalizedDifference(['B8', 'B4']).rename('NDVI')
      ).median().clip(geometry);

      // 4. Sonucu Leaflet'in okuyabileceği bir harita URL'ine çevir
      ndvi.getMap({min: 0, max: 1, palette: ['red', 'yellow', 'green']}, (map) => {
        res.status(200).json({ url: map.urlFormat });
      });
    });
  });
}
