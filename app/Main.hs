module Main where

import Relude
import Norm
import Prove
import Parse
import Data.Text.IO as TIO
import Data.IntMap qualified as IM
import Data.Map qualified as M

main :: IO ()
main = pure ()

run n s =
  let (goal, (mv, mc)) = parse "" s
  in runProve mc n mv $ prove mempty (eval mempty goal)

runFile n fn = do
  s <- TIO.readFile fn

  forM_ (run n s) \(term, state) -> do
    let metaCtx = unMetaCtx state
    TIO.putStrLn ("Proof term:\n    " <> prettyPrint (readback (Zonk metaCtx) 0 (eval mempty term)))
    forM_ (M.toList (allMetas state)) \(name, mv) ->
      case IM.lookup mv (unMetaCtx state) of
        Just sol -> TIO.putStrLn (name <> " = " <> prettyPrint (readback (Zonk metaCtx) 0 sol))
        Nothing -> TIO.putStrLn (name <> " is unsolved")
    -- TIO.putStrLn ("Raw term:\n    " <> show term)
    -- TIO.putStrLn ("State:\n    " <> show state)
