module Syntax.Typing where

open import Syntax.Core as C
open import Syntax.Value as V
open import Data.Nat
open import Semantics
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality hiding([_])

data _~_ : V.Term -> V.Term -> Set where
    ~-refl : ∀{tm} -> tm ~ tm

data Context : Set where
    ∙ : Context
    _,_ : (ctx : Context) (ty : V.Term) -> Context

_,_∣_~>_ : MEnv -> Env -> C.Term -> V.Term -> Set
menv , env ∣ ctm ~> vtm = evaluate menv env ctm ≡ just vtm

variable
    Γ Δ : Context

data HasVar : Context -> C.DBIndex -> V.Term -> Set where
    hv-here : ∀{ty ty'} (conv : ty ~ ty') -> HasVar (Γ , ty) 0 ty'
    hv-there : ∀{ix ty ty'} (hv : HasVar Γ ix ty) -> HasVar (Γ , ty') (suc ix) ty

data _⊢_∶_ : Context -> C.Term -> V.Term -> Set where
    type-type-type : ∀{ul} -> Γ ⊢ C.type-type ul ∶ V.type-type (suc ul)
    type-var : ∀{ix ty} (hv : HasVar Γ ix ty) -> Γ ⊢ C.var ix ∶ ty
    type-fun-intro : ∀{body env inTy vOutTy}
                     (menv : MEnv)
                     (cOutTy : C.Term)
                     (_ : menv , extend env ∣ cOutTy ~> vOutTy)
                     (typeBody : (Γ , inTy) ⊢ body ∶ vOutTy) ->
                     Γ ⊢ C.fun-intro body ∶ V.fun-type inTy env cOutTy
    type-fun-type : ∀{cInTy vInTy outTy ul1 ul2}
                     (menv : MEnv)
                     (env : Env)
                     (_ : menv , env ∣ cInTy ~> vInTy)
                     (typeInTy : Γ ⊢ cInTy ∶ V.type-type ul1)
                     (typeOutTy : (Γ , vInTy) ⊢ outTy ∶ V.type-type ul2) ->
                     Γ ⊢ C.fun-type cInTy outTy ∶ V.type-type (ul1 ⊔ ul2)
    type-fun-elim : ∀{lam cArg vArg inTy cOutTy vOutTy}
                     (env tyEnv : Env)
                     (menv : MEnv)
                     (_ : menv , env ∣ cArg ~> vArg)
                     (_ : menv , (vArg ∷ tyEnv) ∣ cOutTy ~> vOutTy)
                     (typeLam : Γ ⊢ lam ∶ V.fun-type inTy tyEnv cOutTy)
                     (typeArg : Γ ⊢ cArg ∶ inTy) ->
                     Γ ⊢ C.fun-elim lam cArg ∶ vOutTy

_ : {ty : V.Term} -> (∙ , ty) ⊢ C.var 0 ∶ ty
_ = type-var (hv-here ~-refl)

_ : ∙ ⊢ C.fun-intro (C.fun-intro (C.var 0)) ∶ V.fun-type (V.type-type 0) [] (C.fun-type (C.var 0) (C.var 1))
_ = type-fun-intro mempty ((C.fun-type (C.var 0) (C.var 1))) refl (type-fun-intro mempty (C.var 1) refl (type-var (hv-here ~-refl)))

_ : ∙ ⊢ C.fun-intro (C.fun-intro (C.var 1)) ∶ V.fun-type (V.type-type 0) [] (C.fun-type (C.type-type 1) (C.type-type 0))
_ = type-fun-intro mempty ((C.fun-type (C.type-type 1) (C.type-type 0))) refl (type-fun-intro mempty (C.type-type 0) refl (type-var (hv-there (hv-here ~-refl))))

_ : ∙ ⊢ C.fun-type (C.type-type 0) (C.type-type 0) ∶ V.type-type 1
_ = type-fun-type mempty [] refl type-type-type type-type-type

_ : ∙ ⊢ C.fun-type (C.type-type 0) (C.type-type 1) ∶ V.type-type 2
_ = type-fun-type mempty [] refl type-type-type type-type-type

_ : ∙ ⊢ C.fun-type (C.type-type 2) (C.type-type 1) ∶ V.type-type 3
_ = type-fun-type mempty [] refl type-type-type type-type-type

_ : ∙ ⊢ C.fun-elim (C.fun-intro (C.var 0)) (C.type-type 0) ∶ V.type-type 1
_ = type-fun-elim [] [] mempty refl refl (type-fun-intro mempty (C.type-type 1) refl (type-var (hv-here ~-refl))) type-type-type