module Main where

import qualified Data.ByteString.Lazy as BL
import Control.Monad (forM_)
import Tracing
import Data.Map as Map

main :: IO ()
main = do
  bl <- BL.readFile "tetris.ch8"
  let callback s TraceContext { currentAddress = addr, currentInstruction = inst } =
        Map.insert addr inst s
  case trace bl callback Map.empty of
    Left str -> error str
    Right res -> forM_ (Map.assocs res) $ \(addr, inst) ->
      putStrLn $ show addr ++ ":\t" ++ show inst
