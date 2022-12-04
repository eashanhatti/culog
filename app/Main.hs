module Main where

import Relude
import Norm
import Prove
import Parse

main :: IO ()
main = pure ()

run s =
  let (goal, mv) = parse "" s
  in runProve mv $ prove mempty mempty (eval mempty goal)
