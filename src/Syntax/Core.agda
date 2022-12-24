module Syntax.Core where

open import Data.Nat
open import Syntax.Common

DBIndex : Set
DBIndex = ℕ

data Term : Set where
    var : DBIndex -> Term
    fun-intro : Term -> Term
    fun-elim : Term -> Term -> Term
    metavar : MVName -> Term