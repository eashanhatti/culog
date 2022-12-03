module Syntax.Core where

import Relude

data Term
  = Pi Term Term
  | Lam Term
  | App Term Term
  | Univ
  | BVar Natural
  | MVar Int
  deriving (Show)
