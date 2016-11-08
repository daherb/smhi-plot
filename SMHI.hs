module SMHI where
import Data.Maybe
import Haste
import Haste.Ajax
import Haste.JSON
import Haste.Graphics.Canvas

-- Several month from gothenburg
-- check http://opendata-download-metobs.smhi.se/api/version/1.0/parameter/1/station/
-- for all stations
dataUrl = "http://opendata-download-metobs.smhi.se/api/version/1.0/parameter/1/station/71420/period/latest-months/data.json"


pointsToShape :: [Point] -> Shape ()
pointsToShape [] =
  return ()
pointsToShape ((x,y):ps) =
  do
    rect (x,300) (x+1,200-y*5)
    pointsToShape ps

dataToPoints :: Double -> [JSON] -> [Point]
dataToPoints _ [] = []
dataToPoints pos (j:js) =
  let
    Str json =  j ! toJSString "value" 
    y =  read $ fromJust $ fromJSString json
  in
    (pos,y):(dataToPoints (pos + 1) js)

takeFromEnd :: Int -> [a] -> [a]
takeFromEnd num l =
  reverse $ take num $ reverse l
  
plotData :: Canvas -> IO ()
plotData canvas =
  let callback :: Maybe JSON -> IO ()
      callback (Just dat) =
        do
          let Arr dataPoints = ( dat ! (toJSString "value"))
          let points = dataToPoints 0 $ takeFromEnd 800 $ dataPoints
          let picture = fill $ pointsToShape points
          render canvas $ do
            setFillColor (RGB 128 128 128)
            picture
            setStrokeColor (RGB 0 0 0)
            stroke $ do
              line (0,250) (800,250)
              line (0,200) (800,200)
              line (0,150) (800,150)
              line (0,100) (800,100)
              line (0, 50) (800, 50)
            setFillColor (RGB 0 0 0)
            text (10,290) "-20° C"
            text (10,240) "-10° C"
            text (10,190) "0° C"
            text (10,140) "10° C"
            text (10, 90) "20° C"
            text (10, 40) "30° C"
      callback Nothing = return ()
  in
  do
    writeLog dataUrl
    ajaxRequest GET dataUrl noParams callback
    
