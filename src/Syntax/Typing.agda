module Syntax.Typing where

open import Syntax.Core as C
open import Syntax.Value as V
open import Data.Nat
open import Semantics
open import Data.List
open import Data.Maybe
open import Data.Product renaming(_,_ to _P,_)
open import Relation.Binary.PropositionalEquality hiding([_])

data Context : Set where
    ∙ : Context
    _,_∶_ : (ctx : Context) (tm : V.Term) (ty : V.Term) -> Context

ctxToEnv : Context -> Env
ctxToEnv ∙ = []
ctxToEnv (Γ , tm ∶ _) = tm ∷ ctxToEnv Γ

_,_ : Context -> V.Term -> Context
Γ , ty = Γ , (V.var (length (ctxToEnv Γ))) ∶ ty

variable
    Γ Δ : Context

data _⊢_∶_ : Context -> C.Term -> V.Term -> Set

evaluateIsJust : ∀{ty} -> (ctm : C.Term) -> Γ ⊢ ctm ∶ ty -> ∃[ vtm ] (evaluate (ctxToEnv Γ) ctm ≡ just vtm)
safeEvaluate : ∀{ty} -> (Γ : Context) -> (tm : C.Term) -> Γ ⊢ tm ∶ ty -> V.Term

data _⊢_~_ : Context -> V.Term -> V.Term -> Set where
    ~-refl : ∀{tm} -> Γ ⊢ tm ~ tm
    ~-left-norm : ∀{tm tm' redex} (conv : Γ ⊢ tm ~ tm') -> Γ ⊢ V.neutral redex (just tm) ~ tm'
    ~-right-norm : ∀{tm tm' redex} (conv : Γ ⊢ tm ~ tm') -> Γ ⊢ tm ~ V.neutral redex (just tm')
    ~-fun-intros : ∀{env n inTy body1 body2 outTy}
                   (typeBody1 : (Γ , inTy) ⊢ body1 ∶ outTy)
                   (typeBody2 : (Γ , inTy) ⊢ body2 ∶ outTy)
                   (conv : (Γ , inTy) ⊢ safeEvaluate (Γ , inTy) body1 typeBody1 ~ safeEvaluate (Γ , inTy) body2 typeBody2) ->
                   Γ ⊢ V.fun-intros env (suc n) refl body1 ~ V.fun-intros env (suc n) refl body2

data HasVar : Context -> C.DBIndex -> V.Term -> Set where
    hv-here : ∀{ty ty' def} (conv : Γ ⊢ ty ~ ty') -> HasVar (Γ , def ∶ ty) 0 ty'
    hv-there : ∀{ix ty ty' def} (hv : HasVar Γ ix ty) -> HasVar (Γ , def ∶ ty') (suc ix) ty

data _⊢_∶_ where
    type-type-type : ∀{ul} -> Γ ⊢ C.type-type ul ∶ V.type-type (suc ul)
    type-var : ∀{ix ty} (hv : HasVar Γ ix ty) -> Γ ⊢ C.var ix ∶ ty
    type-fun-intro : ∀{ul body inTy outTy}
                     (typeOutTy : (Γ , inTy) ⊢ outTy ∶ V.type-type ul)
                     (typeBody : (Γ , inTy) ⊢ body ∶ safeEvaluate (Γ , inTy) outTy typeOutTy) ->
                     Γ ⊢ C.fun-intro body ∶ V.fun-type inTy (ctxToEnv Γ) outTy
    type-fun-type : ∀{inTy outTy ul1 ul2}
                     (typeInTy : Γ ⊢ inTy ∶ V.type-type ul1)
                     (typeOutTy : (Γ , safeEvaluate Γ inTy typeInTy) ⊢ outTy ∶ V.type-type ul2) ->
                     Γ ⊢ C.fun-type inTy outTy ∶ V.type-type (ul1 ⊔ ul2)
    type-fun-elim : ∀{ul lam arg inTy outTy}
                     (typeOutTy : {arg' : V.Term} -> (Γ , arg' ∶ inTy) ⊢ outTy ∶ V.type-type ul)
                     (typeLam : Γ ⊢ lam ∶ V.fun-type inTy (ctxToEnv Γ) outTy)
                     (typeArg : Γ ⊢ arg ∶ inTy) ->
                     Γ ⊢ C.fun-elim lam arg ∶ safeEvaluate (Γ , safeEvaluate Γ arg typeArg ∶ inTy) outTy typeOutTy
    conversion : ∀{tm ty ty'}
                 (conv : Γ ⊢ ty ~ ty')
                 (typeTm : Γ ⊢ tm ∶ ty) ->
                 Γ ⊢ tm ∶ ty'

>>=just≡ : ∀{x y f} -> x ≡ just y -> (x >>= f) ≡ f y
>>=just≡ refl = refl

evaluateIsJust {ty = ty} (C.var ix) (type-var {Γ} hv) = help ix hv where
    help : ∀{Γ} -> (ix : DBIndex) -> HasVar Γ ix ty -> ∃[ vtm ] (evaluate (ctxToEnv Γ) (C.var ix) ≡ just vtm)
    help {Γ} zero (hv-here {Δ} {def = def} conv) = def P, refl
    help (suc ix) (hv-there hv) = help ix hv
evaluateIsJust {Γ} (C.fun-intro body) (type-fun-intro typeOutTy typeBody) =
    let n P, body' = bunchFunIntros body
    in V.fun-intros (ctxToEnv Γ) (suc n) refl body' P, refl
evaluateIsJust (C.fun-elim lam arg) (type-fun-elim typeOutTy typeLam typeArg) =
    let
        lam' P, args = funElimSpine lam

    in V.neutral (V.fun-elims {!   !} {!   !}) {!   !} P, {!  !}
evaluateIsJust {Γ} (C.fun-type inTy outTy) (type-fun-type typeInTy typeOutTy) =
    let vInTy P, eq = evaluateIsJust inTy typeInTy
    in V.fun-type vInTy (ctxToEnv Γ) outTy P, >>=just≡ eq
evaluateIsJust (C.type-type ul) type-type-type = V.type-type ul P, refl
evaluateIsJust tm (conversion conv typeTm) = evaluateIsJust tm typeTm

safeEvaluate Γ tm typeTm =
    let vtm P, _ = evaluateIsJust tm typeTm
    in vtm

_ : {ty : V.Term} -> (∙ , ty) ⊢ C.var 0 ∶ ty
_ = type-var (hv-here ~-refl)

_ : ∙ ⊢ C.fun-intro (C.fun-intro (C.var 0)) ∶ V.fun-type (V.type-type 0) [] (C.fun-type (C.var 0) (C.var 1))
_ = {!   !}

_ : ∙ ⊢ C.fun-intro (C.fun-intro (C.var 1)) ∶ V.fun-type (V.type-type 0) [] (C.fun-type (C.type-type 1) (C.type-type 0))
_ = {!   !}

_ : ∙ ⊢ C.fun-type (C.type-type 0) (C.type-type 0) ∶ V.type-type 1
_ = {!   !}

_ : ∙ ⊢ C.fun-type (C.type-type 0) (C.type-type 1) ∶ V.type-type 2
_ = {!   !}

_ : ∙ ⊢ C.fun-type (C.type-type 2) (C.type-type 1) ∶ V.type-type 3
_ = {!   !}

_ : ∙ ⊢ C.fun-elim (C.fun-intro (C.var 0)) (C.type-type 0) ∶ V.type-type 1
_ = {!   !} 