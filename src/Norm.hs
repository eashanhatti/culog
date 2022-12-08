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
  C.Pi name inTy outTy -> S.Pi name (eval ctx inTy) \x -> eval (x <| ctx) outTy
  C.Lam name body -> S.Lam name \x -> eval (x <| ctx) body
  C.Univ -> S.Univ
  C.App lam arg ->
    let
      sLam = eval ctx lam
      sArg = eval ctx arg
      reded =
        \mc -> case force mc sLam of
          S.Lam _ body -> Just (body sArg)
          tm -> Nothing
    in S.Neutral (S.App sLam sArg) reded
  C.BVar _ ix -> ctx `index` (fromIntegral ix)
  C.MVar name mv ->
    S.Neutral
      (S.MVar name mv)
      (\mc -> IM.lookup mv mc)

data ReadbackKind
  = NoUnfold
  | Zonk S.MetaContext

readback :: ReadbackKind -> Natural -> S.Term -> C.Term
readback rbk lvl = \case
  S.Pi name inTy outTy -> C.Pi name (readback rbk lvl inTy) (readback rbk (lvl + 1) (outTy (S.BVar name lvl)))
  S.Lam name body -> C.Lam name (readback rbk (lvl + 1) (body (S.BVar name lvl)))
  S.Univ -> C.Univ
  S.BVar name lvl' -> C.BVar name (lvl - lvl' - 1)
  S.Neutral (S.MVar name mv) _ ->
    case rbk of
      NoUnfold -> C.MVar name mv
      Zonk mc -> case IM.lookup mv mc of
        Just sol -> readback rbk lvl sol
        Nothing -> C.MVar ("<UNSOLVED: " <> name <> ">") mv
  S.Neutral (S.App lam arg) _ -> C.App (readback rbk lvl lam) (readback rbk lvl arg)
