module Syntax.Value where

open import Data.List
open import Data.Maybe
open import Syntax.Common
open import Data.Nat
import Syntax.Core as C 

DBLevel : Set
DBLevel = ℕ

data Redex : Set

data Term : Set

Env : Set
Env = List Term

data Term where
    fun-intros : (env : Env) (n : ℕ) (body : C.Term) -> Term
    fun-type : (inTy : Term) (env : Env) (outTy : C.Term) -> Term
    type-type : (ul : UnivLevel) -> Term
    neutral : (redex : Redex) (reded : Maybe Term) -> Term

data FunElimHead : Set where
    mv-head : (mv : MVName) -> FunElimHead
    rv-head : (lvl : DBLevel) -> FunElimHead

data Redex where
    fun-elims : (head : FunElimHead) (args : List Term) -> Redex

var : DBLevel -> Term
var lvl = neutral (fun-elims (rv-head lvl) []) nothing