module Norm where

import Relude hiding(force)
import Data.Sequence((<|), index)
import Data.IntMap qualified as IM
import Syntax.Core qualified as C
import Syntax.Semantic qualified as S
import Control.Monad

force :: S.MetaContext -> S.Term -> S.Term
force mc = \case
  tm@(S.Neutral _ iTm) ->
    case iTm mc of
      Just iTm' -> force mc iTm'
      Nothing -> tm
  tm -> tm

eval :: S.Context -> C.Term -> S.Term
eval ctx = \case
  C.Pi inTy outTy -> S.Pi (eval ctx inTy) \x -> eval (x <| ctx) outTy
  C.Lam body -> S.Lam \x -> eval (x <| ctx) body
  C.Univ -> S.Univ
  C.App lam arg ->
    let
      sLam = eval ctx lam
      sArg = eval ctx arg
      reded =
        \mc -> case force mc sLam of
          S.Lam body -> Just (body sArg)
          tm -> Nothing
    in S.Neutral (S.App sLam sArg) reded
  C.BVar ix -> ctx `index` (fromIntegral ix)
  C.MVar mv ->
    S.Neutral
      (S.MVar mv)
      (\mc -> IM.lookup mv mc)

readback :: Natural -> S.Term -> C.Term
readback lvl = \case
  S.Pi inTy outTy -> C.Pi (readback lvl inTy) (readback (lvl + 1) (outTy (S.BVar lvl)))
  S.Lam body -> C.Lam (readback (lvl + 1) (body (S.BVar lvl)))
  S.Univ -> C.Univ
  S.BVar lvl' -> C.BVar (lvl - lvl' - 1)
  S.Neutral (S.MVar mv) _ -> C.MVar mv
  S.Neutral (S.App lam arg) _ -> C.App (readback lvl lam) (readback lvl arg)
