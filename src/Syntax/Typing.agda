module Syntax.Typing where

open import Data.Nat
open import Syntax.Core

data Context : Set
data Type : Context -> Set

data Context where
    ∙ : Context
    _,_ : (Γ : Context) (ty : Type Γ) -> Context

variable
    Γ Δ : Context

data Type where
    fun-type : (inTy : Type Γ) (outTy : Type (Γ , inTy)) -> Type Γ
    unit-type : Type Γ

_++_ : Context -> Context -> Context
weakenType : Type Γ -> Type (Δ ++ Γ)

Γ ++ ∙ = Γ
Γ ++ (Δ , ty) = (Γ ++ Δ) , weakenType ty

weakenType (fun-type inTy outTy) = fun-type (weakenType inTy) (weakenType outTy)
weakenType unit-type = unit-type

data HasVar : (Γ Δ : Context) -> DBIndex -> Type Δ -> Set where
    hv-here : ∀{ty} -> HasVar (Δ , ty) Δ 0 ty
    hv-there : ∀{ix ty ty'} (hv : HasVar Γ Δ ix ty) -> HasVar (Γ , ty') Δ (suc ix) ty

data _⊢_∶_ : (Γ : Context) -> Term -> Type Γ -> Set where
    type-fun-intro : ∀{inTy outTy body} (typeBody : (Γ , inTy) ⊢ body ∶ outTy) -> Γ ⊢ fun-intro body ∶ fun-type inTy outTy
    type-var : ∀{ix} (Δ : Context) {ty : Type Δ} (hv : HasVar (Γ ++ Δ) Δ ix ty) -> (Γ ++ Δ) ⊢ var ix ∶ weakenType ty

_ : ∙ ⊢ fun-intro (var 0) ∶ fun-type unit-type unit-type
_ = type-fun-intro (type-var ∙ hv-here)