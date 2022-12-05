module Prove where

import Relude hiding(force, zip, State)
import Data.Sequence((<|), (|>), zip)
import Syntax.Semantic qualified as S
import Syntax.Core qualified as C
import Data.IntMap qualified as IM
import Data.Map qualified as M
import Control.Monad.Logic
import Control.Monad.State.Strict
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

runProve :: Int -> Int -> Prove a -> [(a, ProveState)]
runProve n mv act =
  observeMany n
  -- observeAll
    (flip runStateT (ProveState mv mempty mempty) do
      x <- act
      d <- unDelayed <$> get
      if M.size d > 0 then
        empty
      else
        pure x)

type Assumptions = Seq S.Term

traceState :: String -> Prove a -> Prove a
traceState msg act = do
  s <- get
  x <- {-trace (msg ++ ":\n    " ++ show s) -}act
  pure x

solve :: Natural -> Int -> S.Term -> Prove ()
solve lvl mv sol = do
  st <- get
  case IM.lookup mv (unMetaCtx st) of
    Just sol' -> unify lvl sol sol'
    Nothing -> put (st { unMetaCtx = IM.insert mv sol (unMetaCtx st) })

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

occursCheck :: Natural -> Int -> S.Term -> Prove ()
occursCheck lvl mv = \case
  S.Pi inTy outTy -> do
    occursCheck lvl mv inTy
    occursCheck (lvl + 1) mv (outTy (S.BVar lvl))
  S.Lam body -> occursCheck (lvl + 1) mv (body (S.BVar lvl))
  S.Univ -> pure ()
  S.BVar _ -> pure ()
  S.Neutral (S.App lam arg) _ -> do
    occursCheck lvl mv lam
    occursCheck lvl mv arg
  S.Neutral (S.MVar mv') _ ->
    if mv == mv' then
      empty
    else
      pure ()

unify :: Natural -> S.Term -> S.Term -> Prove ()
unify lvl term1 term2 = do
  mc <- unMetaCtx <$> get
  delayed <- unDelayed <$> get
  forM delayed (uncurry (unify lvl))
  traceState ("unify" ++ show term1 ++ " === " ++ show term2) $
    case (term1, term2) of
      (redex -> (S.BVar bLvl1, args1), redex -> (S.BVar bLvl2, args2))
        | bLvl1 == bLvl2
        , length args1 == length args2
        -> traverse_ (uncurry (unify lvl)) (zip args1 args2)
      -- (redex -> (S.Neutral (S.MVar mv1) _, args1), redex -> (S.Neutral (S.MVar mv2) _, args2))
      --   | mv1 == mv2
      --   , length args1 == length args2
      --   -> traverse_ (uncurry (unify lvl)) (zip args1 args2)
      (redex -> (S.Neutral (S.MVar mv) _, args1), redex -> (lam, args2))
        | length args1 == length args2
        , notMV lam
        -> do
          occursCheck lvl mv term2
          traverse_ (uncurry (unify lvl)) (zip args1 args2)
          solve lvl mv lam
      (redex -> (lam, args1), redex -> (S.Neutral (S.MVar mv) _, args2))
        | length args1 == length args2
        , notMV lam
        -> do
          occursCheck lvl mv term1
          traverse_ (uncurry (unify lvl)) (zip args1 args2)
          solve lvl mv lam
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
  asum (fmap (search asps ctx goal) asps) <|>
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
