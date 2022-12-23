module Semantics where

import Syntax.Core as C
import Syntax.Value as V
open import Data.Maybe hiding(map)
open import Data.List hiding(lookup)
open import Data.Fin
open import Data.Nat
open import Data.Product hiding(map)

lookup : C.DBIndex -> List V.Term -> Maybe V.Term
lookup _ [] = nothing
lookup zero (v ∷ _) = just v
lookup (suc n) (_ ∷ env) = lookup n env

bunchFunIntros : C.Term -> ℕ × C.Term
bunchFunIntros (C.fun-intro body) =
    let n , body' = bunchFunIntros body
    in (suc n) , body'
bunchFunIntros term = 0 , term

funElimSpine : C.Term -> C.Term × List C.Term
funElimSpine (C.fun-elim lam arg) =
    let lam' , args = funElimSpine lam
    in lam' , arg ∷ args
funElimSpine term = term , []


{-# TERMINATING #-}
evaluate : List V.Term -> C.Term -> Maybe V.Term

evalFunElim : V.Term -> List V.Term -> Maybe V.Term
evalFunElim (V.var ix) args = just (V.neutral (V.fun-elims (V.rv-head ix) args) nothing)
evalFunElim (V.fun-intro env n body) args = evaluate (args ++ env) body
evalFunElim (V.neutral redex (just term)) args = evalFunElim term args
evalFunElim (V.neutral redex nothing) args = nothing

liftMaybe : {A : Set} -> List (Maybe A) -> Maybe (List A)
liftMaybe [] = just []
liftMaybe (just x ∷ xs) = do
    xs' <- liftMaybe xs
    just (x ∷ xs')
liftMaybe (nothing ∷ _) = nothing

evaluate env (C.var ix) = lookup ix env
evaluate env (C.fun-intro term) =
    let n , body = bunchFunIntros term
    in just (V.fun-intro env n body)
evaluate env (C.fun-elim lam arg) = do
    let lam' , args = funElimSpine lam
    args' <- liftMaybe (map (evaluate env) (arg ∷ reverse args))
    lam'' <- evaluate env lam'
    evalFunElim lam'' args'
evaluate env (C.metavar mv) = just (V.neutral (V.fun-elims (V.mv-head mv) []) nothing)

readback : V.Term -> C.Term
readback term = {!   !}
