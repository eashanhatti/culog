module Syntax.Core where

import Relude

data Term
  = Pi Text Term Term
  | Lam Text Term
  | App Term Term
  | Univ
  | BVar Text Natural
  | MVar Text Int
  deriving (Show)
