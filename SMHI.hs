module SMHI where
import Data.Maybe
import Haste
import Haste.Ajax
import Haste.JSON
import Haste.Graphics.Canvas
import Network.HTTP

-- Several month from gothenburg
-- check http://opendata-download-metobs.smhi.se/api/version/1.0/parameter/1/station/
-- for all stations
dataUrl = "http://opendata-download-metobs.smhi.se/api/version/1.0/parameter/1/station/71420/period/latest-months/data.json"

getData :: IO JSON
getData =
  do
    rsp <- simpleHTTP (getRequest dataUrl)
      

plotData :: Canvas -> JSON -> IO ()
plotData canvas dat =
  do
    let Arr dataPoints = ( dat ! (toJSString "value"))
    let points = dataToPoints 0 dataPoints
    let picture = fill $ pointsToShape points 
    render canvas $ do
      setFillColor (RGB 128 128 128)
      picture
    
