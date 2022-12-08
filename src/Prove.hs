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
  , allMetas :: M.Map Text Int
  , unMetaCtx :: S.MetaContext
  , unDelayed :: M.Map (Int, Int) (S.Term, S.Term) }
  deriving (Show)

type Prove a = StateT ProveState Logic a

runProve :: M.Map Text Int -> Int -> Int -> Prove a -> [(a, ProveState)]
runProve mc n mv act =
  observeMany n
  -- observeAll
    (flip runStateT (ProveState mv mc mempty mempty) do
      x <- act
      d <- unDelayed <$> get
      if M.size d > 0 then
        empty
      else
        pure x)

type Assumptions = Seq (S.Term, S.Term)

toCtx :: Assumptions -> S.Context
toCtx = fmap snd

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

freshMV :: Text -> Assumptions -> Prove S.Term
freshMV name asps = do
  mv <- unNextMV <$> get
  modify \st -> st
    { unNextMV = unNextMV st + 1
    , allMetas = M.insert name mv (allMetas st) }
  pure (eval (toCtx asps) (C.MVar name mv))

redex :: S.Term -> (S.Term, Seq S.Term)
redex = \case
  S.Neutral (S.App lam arg) _ ->
    let (lam', args) = redex lam
    in (lam', args |> arg)
  tm -> (tm, mempty)

notMV :: S.Term -> Bool
notMV (S.Neutral (S.MVar _ _) _) = False
notMV _ = True

occursCheck :: Natural -> Int -> S.Term -> Prove ()
occursCheck lvl mv = \case
  S.Pi name inTy outTy -> do
    occursCheck lvl mv inTy
    occursCheck (lvl + 1) mv (outTy (S.BVar name lvl))
  S.Lam name body -> occursCheck (lvl + 1) mv (body (S.BVar name lvl))
  S.Univ -> pure ()
  S.BVar _ _ -> pure ()
  S.Neutral (S.App lam arg) _ -> do
    occursCheck lvl mv lam
    occursCheck lvl mv arg
  S.Neutral (S.MVar _ mv') _ ->
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
      (redex -> (S.BVar _ bLvl1, args1), redex -> (S.BVar _ bLvl2, args2))
        | bLvl1 == bLvl2
        , length args1 == length args2
        -> traverse_ (uncurry (unify lvl)) (zip args1 args2)
      -- (redex -> (S.Neutral (S.MVar mv1) _, args1), redex -> (S.Neutral (S.MVar mv2) _, args2))
      --   | mv1 == mv2
      --   , length args1 == length args2
      --   -> traverse_ (uncurry (unify lvl)) (zip args1 args2)
      (redex -> (S.Neutral (S.MVar _ mv) _, args1), redex -> (lam, args2))
        | length args1 == length args2
        , notMV lam
        -> do
          occursCheck lvl mv term2
          traverse_ (uncurry (unify lvl)) (zip args1 args2)
          solve lvl mv lam
      (redex -> (lam, args1), redex -> (S.Neutral (S.MVar _ mv) _, args2))
        | length args1 == length args2
        , notMV lam
        -> do
          occursCheck lvl mv term1
          traverse_ (uncurry (unify lvl)) (zip args1 args2)
          solve lvl mv lam
      (redex -> (S.Neutral (S.MVar _ mv1) tm1, args1), redex -> (S.Neutral (S.MVar _ mv2) tm2, args2))
        | length args1 == length args2
        -> case (tm1 mc, tm2 mc) of
          (Just tm1, Just tm2) -> unify lvl tm1 tm2
          (Nothing, Just tm2) -> unify lvl term1 tm2
          (Just tm1, Nothing) -> unify lvl tm1 term2
          (Nothing, Nothing) -> delayProblem mv1 mv2 term1 term2
      (S.Pi name1 inTy1 outTy1, S.Pi name2 inTy2 outTy2) -> do
        unify lvl inTy1 inTy2
        unify (lvl + 1) (outTy1 (S.BVar name1 lvl)) (outTy2 (S.BVar name2 lvl))
      (S.Lam name1 body1, S.Lam name2 body2) ->
        unify (lvl + 1) (body1 (S.BVar name1 lvl)) (body2 (S.BVar name2 lvl))
      (S.Univ, S.Univ) -> pure ()
      (S.BVar _ bLvl1, S.BVar _ bLvl2) | bLvl1 == bLvl2 ->
        pure ()
      (S.Neutral _ tm, _) -> case tm mc of
        Just tm -> unify lvl tm term2
        Nothing -> empty
      (_, S.Neutral _ tm) -> case tm mc of
        Just tm -> unify lvl term1 tm
        Nothing -> empty
      _ -> empty

prove :: Assumptions -> S.Term -> Prove C.Term
prove asps goal =
  asum (fmap (search asps goal) asps) <|>
  do
    mc <- unMetaCtx <$> get
    case force mc goal of
      S.Pi name inTy outTy ->
        let arg = S.BVar name (fromIntegral (length asps))
        in C.Lam name <$> prove ((inTy, arg) <| asps) (outTy arg)
      _ -> empty

search :: Assumptions -> S.Term -> (S.Term, S.Term) -> Prove C.Term
search asps goal (asp, term) =
  let lvl = fromIntegral (length asps)
  in
    (unify lvl goal asp *> pure (readback NoUnfold lvl term)) <|>
    do
      mc <- unMetaCtx <$> get
      case force mc asp of
        S.Pi name inTy outTy -> do
          arg <- freshMV name asps
          let
            term' =
              eval
                (toCtx asps)
                (C.App
                  (readback NoUnfold lvl term)
                  (readback NoUnfold lvl arg))
          search ((inTy, arg) <| asps) goal (outTy arg, term')
        _ -> empty
