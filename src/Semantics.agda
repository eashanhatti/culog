module Semantics where

open import Syntax.Core as C
open import Syntax.Value as V
open import Data.Maybe hiding(map)
open import Data.List hiding(lookup)
open import Data.Nat
open import Data.Bool
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Tree.AVL.Map (<-strictTotalOrder) hiding(map)
open import Data.Product hiding(map)
open import Relation.Binary.PropositionalEquality hiding([_])

MEnv : Set
MEnv = Map V.Term

mempty = empty

extend : Env -> Env
extend env = V.var (length env) ∷ env

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
evaluate : MEnv -> List V.Term -> C.Term -> Maybe V.Term

_==_ : ℕ -> ℕ -> Bool
zero == zero = true
suc n == suc m = n == m
_ == _ = false

evalFunElim : MEnv -> V.Term -> List V.Term -> Maybe V.Term
evalFunElim menv (V.fun-intros env n _ body) args =
    if n == length args then
        evaluate menv (args ++ env) body
    else
        nothing
evalFunElim menv (V.neutral redex (just term)) args = evalFunElim menv term args
evalFunElim _ _ _ = nothing

liftMaybe : {A : Set} -> List (Maybe A) -> Maybe (List A)
liftMaybe [] = just []
liftMaybe (just x ∷ xs) = do
    xs' <- liftMaybe xs
    just (x ∷ xs')
liftMaybe (nothing ∷ _) = nothing

evaluate _ env (C.var ix) = lookupVar ix env
evaluate _ _ (C.type-type ul) = just (V.type-type ul)
evaluate _ env (C.fun-intro term) =
    let n , body = bunchFunIntros term
    in just (V.fun-intros env (suc n) refl body)
evaluate menv env (C.fun-type inTy outTy) = do
    vInTy <- evaluate menv env inTy
    just (V.fun-type vInTy env outTy)
evaluate menv env (C.fun-elim lam arg) = do
    let lam' , args = funElimSpine lam
    args' <- liftMaybe (map (evaluate menv env) (arg ∷ reverse args))
    lam'' <- evaluate menv env lam'
    evalFunElim menv lam'' args'

data Unfolding : Set where
    full : Unfolding
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

{-# TERMINATING #-}
readback : Unfolding -> V.DBLevel -> V.Term -> Maybe C.Term
readback _ _ (V.type-type ul) = just (C.type-type ul)
readback unf lvl (V.fun-intros _ n _ body) = just (iter n C.fun-intro body)
readback unf lvl (V.fun-type inTy _ outTy) = do
    cInTy <- readback unf lvl inTy
    just (C.fun-type cInTy outTy)
readback full lvl (V.neutral (V.fun-elims lam args) (just term)) = readback full lvl term
readback _ lvl (V.neutral (V.fun-elims lam args) _) = do
    lam' <- headToTerm lvl lam
    cArgs <- liftMaybe (map (readback none lvl) args)
    just (foldl C.fun-elim lam' cArgs)
