module SMHI where
import Data.Maybe
import Data.Char
import Haste
import Haste.Ajax
import Haste.JSON
import Haste.Graphics.Canvas

-- Several month from gothenburg
-- check http://opendata-download-metobs.smhi.se/api/version/1.0/parameter/1/station/
-- for all stations
dataUrlPre = "http://opendata-download-metobs.smhi.se/api/version/1.0/parameter/1/station/71420/period/latest-"


pointsToShape :: [Point] -> Double -> Shape ()
pointsToShape [] _ =
  return ()
pointsToShape ((x,y):ps) width =
  do
    rect (x*width,300) ((x+1) * width,200-y*5)
    pointsToShape ps width

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

plotData :: String -> IO ()
plotData period =
  let callback :: Maybe JSON -> IO ()
      callback (Just dat) =
        do
          Just canvas <- getCanvasById $ "canvas" ++ period
          let Arr dataPoints = ( dat ! (toJSString "value"))
          let scopePoints = takeFromEnd 800 $ dataPoints
          let start = head scopePoints
          let Num tstart = start ! (toJSString "date")
          -- let startDate = "" --show $ startBStr
          let end = last scopePoints
          let Num tend = end ! (toJSString "date")
          eval $ toJSString $
            "var start = new Date(" ++ (show tstart) ++ ");" ++
            "var end = new Date (" ++ (show tend) ++ "); " ++
            "document.getElementById(\"title" ++ period ++"\").innerHTML = \"Hourly Temparature in Gothenburg from \" + start.toDateString() + \" \" + start.toTimeString() + \" to \" + end.toDateString() + \" \" + end.toTimeString();"
          let points = dataToPoints 0 scopePoints
          let picture = fill $ pointsToShape points (800 / ( fromIntegral $ length points ) )
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
    let dataUrl = dataUrlPre ++ (map toLower period) ++ "/data.json"
    writeLog dataUrl
    ajaxRequest GET dataUrl noParams callback
    
