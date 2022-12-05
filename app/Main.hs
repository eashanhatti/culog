module Main where

import Relude
import Norm
import Prove
import Parse
import Data.Text.IO as TIO

main :: IO ()
main = pure ()

run n s =
  let (goal, mv) = parse "" s
  in runProve n mv $ prove mempty mempty (eval mempty goal)

runFile n fn = do
  s <- TIO.readFile fn
  TIO.putStrLn "Parsed file..."
  pure (run n s)
