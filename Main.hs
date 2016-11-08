import SMHI
import Haste
import Haste.Graphics.Canvas

main :: IO ()
main =
  do
    writeLog "Starting"
    Just canvas <- getCanvasById "canvas"
    dat <- getData
    writeLog $ show dat
    plotData canvas dat
    return ()
