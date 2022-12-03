module Syntax.Semantic where

import Relude
import Prelude qualified as Prelude
import Data.IntMap
import Syntax.Core qualified as C

type MetaContext = IntMap Term

type Context = Seq Term

type Level = Natural

data Term
  = Pi Term (Term -> Term)
  | Lam (Term -> Term)
  | Univ
  | BVar Natural
  | Neutral Redex (MetaContext -> Maybe Term)

instance Prelude.Show Term where
  show = show' 0 where
    show' lvl = \case
      Pi inTy outTy -> "(Pi " ++ show' lvl inTy ++ " " ++ show' (lvl + 1) (outTy (BVar lvl)) ++ ")"
      Lam body -> "(Lam " ++ show' (lvl + 1) (body (BVar lvl))
      Univ -> "Univ"
      BVar bLvl -> "(BVar " ++ show bLvl ++ ")"
      Neutral (MVar mv) _ -> "(MVar " ++ show mv ++ ")"
      Neutral (App lam arg) _ -> "(App " ++ show' lvl lam ++ " " ++ show' lvl arg ++ ")"

data Redex
  = MVar Int
  | App Term Term
  deriving (Show)
