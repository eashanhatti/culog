module Prove where

import Relude hiding(force, zip)
import Data.Sequence((<|), (|>), zip)
import Syntax.Semantic qualified as S
import Syntax.Core qualified as C
import Data.IntMap qualified as IM
import Data.Map qualified as M
import Control.Monad.Logic
import Control.Applicative
import Control.Monad
import Data.Bifunctor
import Data.Function
import Norm

data ProveState = ProveState
  { unNextMV :: Int
  , unMetaCtx :: S.MetaContext
  , unDelayed :: M.Map (Int, Int) (S.Term, S.Term) }
  deriving (Show)

type Prove a = StateT ProveState Logic a

runProve :: Int -> Prove a -> [(a, ProveState)]
runProve mv = observeAll . flip runStateT (ProveState mv mempty mempty)

type Assumptions = Seq S.Term

solve :: Int -> S.Term -> Prove ()
solve mv sol = modify \st -> st { unMetaCtx = IM.insert mv sol (unMetaCtx st) }

delayProblem :: Int -> Int -> S.Term -> S.Term -> Prove ()
delayProblem mv1 mv2 term1 term2 =
  modify \st -> st { unDelayed = M.insert (mv1, mv2) (term1, term2) (unDelayed st) }

freshMV :: S.Context -> Prove S.Term
freshMV ctx = do
  mv <- unNextMV <$> get
  modify \st -> st { unNextMV = unNextMV st + 1 }
  pure (eval ctx (C.MVar mv))

redex :: S.Term -> (S.Term, Seq S.Term)
redex = \case
  S.Neutral (S.App lam arg) _ ->
    let (lam', args) = redex lam
    in (lam', args |> arg)
  tm -> (tm, mempty)

notMV :: S.Term -> Bool
notMV (S.Neutral (S.MVar _) _) = False
notMV _ = True

unify :: Natural -> S.Term -> S.Term -> Prove ()
unify lvl term1 term2 = do
  mc <- unMetaCtx <$> get
  case (term1, term2) of
    (redex -> (S.BVar bLvl1, args1), redex -> (S.BVar bLvl2, args2))
      | bLvl1 == bLvl2
      , length args1 == length args2
      -> traverse_ (uncurry (unify lvl)) (zip args1 args2)
    (redex -> (S.Neutral (S.MVar mv1) _, args1), redex -> (S.Neutral (S.MVar mv2) _, args2))
      | mv1 == mv2
      , length args1 == length args2
      -> traverse_ (uncurry (unify lvl)) (zip args1 args2)
    (redex -> (S.Neutral (S.MVar mv) _, args1), redex -> (lam, args2))
      | length args1 == length args2
      , notMV lam
      -> trace ("_______" ++ show (term1, term2, args1, args2)) do
        let !_ = trace ("A" ++ show (term1, term2))
        traverse_ (uncurry (unify lvl)) (zip args1 args2)
        let !_ = trace ("B" ++ show (term1, term2))
        solve mv lam
        let !_ = trace ("B" ++ show (term1, term2))
        pure ()
    (redex -> (lam, args1), redex -> (S.Neutral (S.MVar mv) _, args2))
      | length args1 == length args2
      , notMV lam
      -> do
        traverse_ (uncurry (unify lvl)) (zip args1 args2)
        solve mv lam
    (redex -> (S.Neutral (S.MVar mv1) _, args1), redex -> (S.Neutral (S.MVar mv2) _, args2))
      | length args1 == length args2
      -> delayProblem mv1 mv2 term1 term2
    (S.Pi inTy1 outTy1, S.Pi inTy2 outTy2) -> do
      unify lvl inTy1 inTy2
      unify (lvl + 1) (outTy1 (S.BVar lvl)) (outTy2 (S.BVar lvl))
    (S.Lam body1, S.Lam body2) ->
      unify (lvl + 1) (body1 (S.BVar lvl)) (body2 (S.BVar lvl))
    (S.Univ, S.Univ) -> pure ()
    (S.BVar bLvl1, S.BVar bLvl2) | bLvl1 == bLvl2 ->
      pure ()
    (S.Neutral _ tm, _) -> case tm mc of
      Just tm -> unify lvl tm term2
      Nothing -> empty
    (_, S.Neutral _ tm) -> case tm mc of
      Just tm -> unify lvl term1 tm
      Nothing -> empty
    _ -> empty

prove :: Assumptions -> S.Context -> S.Term -> Prove ()
prove asps ctx goal =
  forM_ asps (search asps ctx goal) <|>
  do
    mc <- unMetaCtx <$> get
    case force mc goal of
      S.Pi inTy outTy ->
        let arg = S.BVar (fromIntegral (length ctx))
        in prove (inTy <| asps) (arg <| ctx) (outTy arg)
      _ -> empty

search :: Assumptions -> S.Context -> S.Term -> S.Term -> Prove ()
search asps ctx goal asp =
  unify (fromIntegral (length ctx)) goal asp <|>
  do
    mc <- unMetaCtx <$> get
    case force mc asp of
      S.Pi inTy outTy -> do
        arg <- freshMV ctx
        search (inTy <| asps) (arg <| ctx) goal (outTy arg)
        prove asps ctx inTy
      _ -> empty
