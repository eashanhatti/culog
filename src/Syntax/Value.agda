module Syntax.Value where

open import Data.List
open import Data.Maybe
open import Syntax.Common
open import Data.Nat
import Syntax.Core as C 

DBLevel : Set
DBLevel = ℕ

data Redex : Set

data Term : Set where
    fun-intros : List Term -> ℕ -> C.Term -> Term
    neutral : Redex -> Maybe Term -> Term

data FunElimHead : Set where
    mv-head : MVName -> FunElimHead
    rv-head : DBLevel -> FunElimHead

data Redex where
    fun-elims : FunElimHead -> List Term -> Redex