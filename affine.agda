{-# OPTIONS --cubical #-}
open import Cubical.Core.Glue
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Nat renaming (ℕ to Nat)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool renaming (_≤_ to _≤ᵇ_)
open import Cubical.Data.Fin renaming (_/_ to _/f_)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Level using (_⊔_)

infix 7 _⟦_⟧

variable
  m n : Nat
  b : Bool
  la lb lc : Level
  A : Set la
  B : Set lb
  C : Set lc

data These {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  this  : A     → These A B
  that  :     B → These A B
  these : A → B → These A B

_∘′_ : (B → C) → (A → B) → (A → C)
f ∘′ g = _∘_ f g

alignWith : (These A B → C) → Vec A m → Vec B n → Vec C (max m n)
alignWith f []         bs       = map (f ∘′ that) bs
alignWith f as@(_ ∷ _) []       = map (f ∘′ this) as
alignWith f (a ∷ as)   (b ∷ bs) = f (these a b) ∷ alignWith f as bs

-- We need to change Ctx a bit to solve injectiveness problems that arises from cubical
Ctx : Nat → Type₀
Ctx = Vec Bool

_∪_ : ∀ {n m} → Ctx n → Ctx m → Ctx (max n m)
xs ∪ ys = alignWith combineThese xs ys
  where
    combineThese : These Bool Bool → Bool
    combineThese (this x)    = x
    combineThese (that y)    = y
    combineThese (these x y) = x or y

variable
  Γ Δ : Ctx n

mutual
  data Term : Ctx n → Type where
    var  : (i : Fin n) → Term Γ 
    lam  : Term (true ∷ Γ)→ Term Γ
    app  : Term Γ → Term Δ → Term (Γ ∪ Δ)
    era  : Term (false ∷ Γ) → Term Γ
    _⟦_⟧ : Term Γ → Sig Δ → Term Δ -- instantiation of substitution

  data Sig : Ctx n → Type where
    _/   : Term Δ → Sig (Γ ∪ Δ) -- cons
    ⇑_   : Sig Γ → Sig (b ∷ Γ) -- shift
    ↑    : Sig Γ -- lift

βred : Term Γ → Term Γ
βred (app {nm} {Γ} {m} {Δ} (lam bod) arg) = bod ⟦ _/ {m} {Δ} {nm} {Γ} arg ⟧
βred (lam trm) = lam (βred trm)
βred (app fun arg) = app (βred fun) (βred arg)
βred trm = trm

-- we omitted some var cases as they are simplified by Fin as dependent pair
step : Term Γ → Term Γ
step (lam bod ⟦ sig ⟧) = lam (bod ⟦ ⇑ sig ⟧)
-- we can simplify next case if we manage different sized contexts
step (app fun arg ⟦ trm / ⟧) = app (fun ⟦ (_/ {{!!}} trm) ⟧) (arg ⟦ (trm /) ⟧)
step (app fun arg ⟦ ⇑ sig ⟧) = app (fun ⟦ (⇑ sig) ⟧) (arg ⟦ {!!} ⟧)
step {n} (app {nm} {Γ} {m} {Δ = Δ} fun arg ⟦ ↑ ⟧) = app {max {!nm!} {!!}} (fun ⟦ ↑ ⟧) (arg ⟦ ↑ ⟧)
step (trm ⟦ sig ⟧ ⟦ sig′ ⟧) = step (trm ⟦ sig ⟧) ⟦ sig′ ⟧
step (var fzero ⟦ trm / ⟧) = era {!!}
step (var idx ⟦ ⇑_  _ ⟧) = var (fsuc idx)
step (var idx ⟦ ↑ ⟧) = var (fsuc idx)
step t = t

-- distributed substitutions
multi-step : Nat → Term Γ → Term Γ
multi-step (suc gas) ((trm ⟦ sig ⟧) ⟦ sig′ ⟧) = multi-step gas (multi-step gas ((trm ⟦ sig ⟧) ⟦ sig′ ⟧))
multi-step (suc gas) (trm ⟦ sig ⟧) = multi-step gas (step (trm ⟦ sig ⟧))
multi-step zero (trm ⟦ sig ⟧) = trm ⟦ sig ⟧
multi-step gas (app fun arg) = app (multi-step gas fun) (multi-step gas arg)
multi-step gas (lam bod) = lam (multi-step gas bod)
multi-step zero (era trm) = era trm
multi-step (suc gas) (era trm) = era (multi-step gas trm)
multi-step _ (var idx) = var idx

normalise : Nat → Term Γ → Term Γ
normalise zero t = t
normalise (suc gas) (app (lam bod) arg) = normalise gas (multi-step (suc gas) (βred (app (lam bod) arg)))
normalise gas (app {nm} {ΓΔ} (var idx) arg) = app {nm} {ΓΔ} (var idx) (normalise gas arg)
normalise (suc gas) (app fun arg) = normalise gas (app (normalise gas fun) (normalise gas arg))
normalise (suc gas) (t ⟦ s ⟧) = normalise gas (multi-step (suc gas) (t ⟦ s ⟧))
normalise gas (lam t) = lam (normalise gas t)
normalise gas t = t

--lets prove normalise works
_~c_ : Term Γ → Term Γ → Type
_~c_ {Γ = Γ} t t' = Path (Term Γ) t t'

step-preserves-~c : ∀ (trm : Term Γ) → trm ~c step trm
step-preserves-~c (var _) = refl
step-preserves-~c (lam _) = refl
step-preserves-~c (app _ _) = refl
step-preserves-~c (era _) = refl
step-preserves-~c (var idx ⟦ sig ⟧) = {!!}
step-preserves-~c (lam bod ⟦ sig ⟧) = {!!}
step-preserves-~c (app fun arg ⟦ sig ⟧) = {!!}
step-preserves-~c (era trm ⟦ sig ⟧) = refl
step-preserves-~c ((trm ⟦ sig ⟧) ⟦ sig′ ⟧) = {!!}

ms-preserves-~c : ∀ (gas : Nat) (trm : Term Γ) → (trm ~c multi-step gas trm)
ms-preserves-~c zero (var idx) = refl
ms-preserves-~c (suc gas) (var idx) = refl
ms-preserves-~c gas (lam bod) = {!!} 
ms-preserves-~c gas (app fun arg) = {!!}
ms-preserves-~c gas (era trm) = {!!}
ms-preserves-~c gas (trm ⟦ x ⟧) = {!!}

normalise-preserves-~c : ∀ (gas : Nat) (trm : Term Γ) → (trm ~c normalise gas trm)
normalise-preserves-~c zero (var _) = refl
normalise-preserves-~c zero (lam _) = refl
normalise-preserves-~c zero (app _ _) = refl
normalise-preserves-~c zero (era _) = refl
normalise-preserves-~c zero (_ ⟦ _ ⟧) = refl
normalise-preserves-~c (suc gas) (var _) = refl
normalise-preserves-~c (suc gas) (lam trm) =  {!!}
normalise-preserves-~c (suc gas) (app fun arg) = {!!}
normalise-preserves-~c (suc gas) (era _) = refl
normalise-preserves-~c (suc gas) (trm ⟦ x ⟧) = {!!}
