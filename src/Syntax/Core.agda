module Syntax.Core where

open import Data.Nat
open import Syntax.Common

DBIndex : Set
DBIndex = ℕ

data Term : Set where
    var : (ix : DBIndex) → Term
    fun-intro : (body : Term) → Term
    fun-elim : (lam : Term) (arg : Term) → Term
    fun-type : (inTy : Term) (outTy : Term) → Term
    type-type : (ul : UnivLevel) → Term