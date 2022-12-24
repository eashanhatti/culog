module Semantics where

import Syntax.Core as C
import Syntax.Value as V
open import Data.Maybe hiding(map)
open import Data.List hiding(lookup)
open import Data.Nat
open import Data.Bool
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Tree.AVL.Map (<-strictTotalOrder) hiding(map)
open import Data.Product hiding(map)

lookupVar : C.DBIndex -> List V.Term -> Maybe V.Term
lookupVar _ [] = nothing
lookupVar zero (v ∷ _) = just v
lookupVar (suc n) (_ ∷ env) = lookupVar n env

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
evaluate : Map V.Term -> List V.Term -> C.Term -> Maybe V.Term

evalFunElim : Map V.Term -> V.Term -> List V.Term -> Maybe V.Term
evalFunElim menv (V.fun-intro env n body) args = evaluate menv (args ++ env) body
evalFunElim menv (V.neutral redex (just term)) args = evalFunElim menv term args
evalFunElim _ (V.neutral redex nothing) args = nothing

liftMaybe : {A : Set} -> List (Maybe A) -> Maybe (List A)
liftMaybe [] = just []
liftMaybe (just x ∷ xs) = do
    xs' <- liftMaybe xs
    just (x ∷ xs')
liftMaybe (nothing ∷ _) = nothing

evaluate _ env (C.var ix) = lookupVar ix env
evaluate _ env (C.fun-intro term) =
    let n , body = bunchFunIntros term
    in just (V.fun-intro env n body)
evaluate menv env (C.fun-elim lam arg) = do
    let lam' , args = funElimSpine lam
    args' <- liftMaybe (map (evaluate menv env) (arg ∷ reverse args))
    lam'' <- evaluate menv env lam'
    evalFunElim menv lam'' args'
evaluate menv env (C.metavar mv) with lookup menv mv
... | just sol = just (V.neutral (V.fun-elims (V.mv-head mv) []) (just sol))
... | nothing = just (V.neutral (V.fun-elims (V.mv-head mv) []) nothing)

data Unfolding : Set where
    full : Unfolding
    zonk : Unfolding
    none : Unfolding

iter : {A : Set} -> ℕ -> (A -> A) -> A -> A
iter zero f x = x
iter (suc n) f x = f (iter n f x)

headToTerm : V.DBLevel -> V.FunElimHead -> Maybe C.Term
headToTerm lvl (V.rv-head lvl') =
    if not (lvl ≤ᵇ lvl') then
        just (C.var (lvl ∸ lvl' ∸ 1))
    else
        nothing
headToTerm _ (V.mv-head mv) = just (C.metavar mv)

{-# TERMINATING #-}
readback : Unfolding -> V.DBLevel -> V.Term -> Maybe C.Term
readback unf lvl (V.fun-intro _ n body) = just (iter n C.fun-intro body)
readback full lvl (V.neutral (V.fun-elims lam args) (just term)) = readback full lvl term
readback zonk lvl (V.neutral (V.fun-elims (V.mv-head mv) args) (just term)) = readback zonk lvl term
readback _ lvl (V.neutral (V.fun-elims lam args) _) = do
    lam' <- headToTerm lvl lam
    cArgs <- liftMaybe (map (readback none lvl) args)
    just (foldl C.fun-elim lam' cArgs)
