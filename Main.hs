import SMHI
import Haste
import Haste.Graphics.Canvas

main :: IO ()
main =
  do
    writeLog "Starting"
    Just canvas <- getCanvasById "canvas"
    plotData canvas
    return ()
