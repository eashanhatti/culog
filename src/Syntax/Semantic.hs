module Syntax.Semantic where

import Relude
import Prelude qualified as Prelude
import Data.IntMap
import Syntax.Core qualified as C

type MetaContext = IntMap Term

type Context = Seq Term

type Level = Natural

data Term
  = Pi Text Term (Term -> Term)
  | Lam Text (Term -> Term)
  | Univ
  | BVar Text Natural
  | Neutral Redex (MetaContext -> Maybe Term)

instance Prelude.Show Term where
  show = show' 0 where
    show' lvl = \case
      Pi name inTy outTy -> "(Pi " ++ show name ++ " " ++ show' lvl inTy ++ " " ++ show' (lvl + 1) (outTy (BVar name lvl)) ++ ")"
      Lam name body -> "(Lam " ++ show name ++ " " ++ show' (lvl + 1) (body (BVar name lvl))
      Univ -> "Univ"
      BVar name bLvl -> "(BVar " ++ show name ++ " " ++ show bLvl ++ ")"
      Neutral (MVar name mv) _ -> "(MVar " ++ show name ++ " " ++ show mv ++ ")"
      Neutral (App lam arg) _ -> "(App " ++ show' lvl lam ++ " " ++ show' lvl arg ++ ")"

data Redex
  = MVar Text Int
  | App Term Term
  deriving (Show)
