module Syntax.Value where

open import Data.List
open import Syntax.Common
open import Data.Nat
import Syntax.Core as C

DBLevel : Set
DBLevel = ℕ

data Term : Set
data Redex : Set

data Type : Set where
    fun-type : Type -> Type -> Type
    el : Term -> Type

data Term where
    var : DBLevel -> Term
    fun-intro : List Term -> ℕ -> C.Term -> Term
    neutral : Redex -> Term

data FunElimHead : Set where
    mv-head : MVName -> FunElimHead
    rv-head : DBLevel -> FunElimHead

data Redex where
    fun-elims : FunElimHead -> List Term -> Redex