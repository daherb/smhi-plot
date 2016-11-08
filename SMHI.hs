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
    writeLog dataUrl
    let req = getRequest dataUrl
    rsp <- simpleHTTP req
    writeLog "foobar"
--    body <- getResponseBody rsp
--    let decode = decodeJSON $ toJSString body
--    return $ either (\_ -> Null) id decode
    return Null

pointsToShape :: [Point] -> Shape ()
pointsToShape [] =
  return ()
pointsToShape ((x,y):ps) =
  do
    rect (x,0) (x,y)
    pointsToShape ps

dataToPoints :: Double -> [JSON] -> [Point]
dataToPoints _ [] = []
dataToPoints pos (j:js) =
  let
    Str json =  j ! toJSString "value" 
    y =  read $ fromJust $ fromJSString json
  in
    (pos,y):(dataToPoints (pos + 1) js)

plotData :: Canvas -> JSON -> IO ()
plotData canvas dat =
  do
    let Arr dataPoints = ( dat ! (toJSString "value"))
    let points = dataToPoints 0 dataPoints
    let picture = fill $ pointsToShape points 
    render canvas $ do
      setFillColor (RGB 128 128 128)
      picture
    
