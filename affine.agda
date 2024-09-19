open import Data.Nat renaming (ℕ to Nat)
open import Data.Bool renaming (_≤_ to _≤ᵇ_)
open import Data.Fin 
open import Data.Vec
open import Data.These using (These;that; this; these)

infix 7 _⟦_⟧

variable
  m n : Nat
  b : Bool
  A : Set 
  B : Set 
  C : Set 

-- We need to change Ctx a bit to solve injectiveness problems that arises from cubical
Ctx : Nat → Set₀
Ctx = Vec Bool

_∪_ : Ctx n → Ctx n → Ctx n
_∪_ = zipWith _∨_

data Split : (l r : Nat) -> Set where
  N : Split 0 0
  L : {l r : Nat} -> Split l r -> Split (suc l) r
  R : {l r : Nat} -> Split l r -> Split l (suc r)

variable
  Γ Δ Γ' Δ' : Ctx n

mutual
  data Term : Ctx n → Set where
    var  : (i : Fin n) → Term Γ
    lam  : Term (true ∷ Γ) → Term Γ
    app  : Term Γ → Term Δ → Term (Γ ∪ Δ)
    era  : Term Γ → Term Γ
    _⟦_⟧ : Term Δ → Sig Γ Δ' → Term Δ' -- instantiation of substitution

  data Sig : Ctx n → Ctx m → Set where
    id  : ∀ {Δ = Γ} → Sig {n} {n} Γ Δ -- we need this declaration with pattern synonyms for unification
    ↑   : Sig Γ (b ∷ Γ)
    _∘_ : Sig Γ Δ → Sig Γ' Δ' → Sig Γ Δ'
    _⨾_ : Term Δ → Sig Γ Δ → Sig Γ Δ'

pattern _⨾ trm = _⨾_ trm id

β-red : Term Γ → Term Γ
β-red {n} (app {Δ = Δ} (lam bod) arg) = bod ⟦ _⨾_ {n} {Δ} {n} {Δ} arg id ⟧
β-red trm = trm

step : Term Γ → Term Γ
step (trm ⟦ sig ⟧ ⟦ sig' ⟧) = trm ⟦ (sig ∘ sig') ⟧
step {nm@_} {ΓΔ} (_⟦_⟧ {n} {Γ} (lam bod) sig) = lam (bod ⟦ sig ∘ ↑ ⟧)
step {nm@.(_)} {ΓΔ} (app {Γ = Γ} {Δ} fun arg ⟦ sig ⟧) = app (fun ⟦ sig ⟧) (arg ⟦ sig ⟧) ⟦ id {nm} {ΓΔ} {ΓΔ}⟧
step (var (suc idx) ⟦ _ ⨾ _ ⟧ ) = var idx
step {nm@_} {ΓΔ} ((var {Γ = true ∷ []} zero) ⟦ trm ⨾ _ ⟧) = trm ⟦ id  {nm} {ΓΔ} {ΓΔ} ⟧
step (var idx ⟦ ↑ ⟧) = var (suc idx)
step {nm@.(_)} {ΓΔ} (var i ⟦ id {nm} {ΓΔ} {Δ = _} ⟧) = var i
step {nm@.(_)} {ΓΔ} (era trm ⟦ id {nm₁} {ΓΔ} {Δ = _} ⟧) = era (var {suc nm} zero)
step trm = trm
-- unreachable step (trm ⟦ id ⟧) = trm as we solved all possible cases!!!

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
normalise (suc gas) (app (lam bod) arg) = normalise gas (multi-step (suc gas) (β-red (app (lam bod) arg)))
normalise gas (app {nm} {ΓΔ} (var idx) arg) = app {nm} {ΓΔ} (var idx) (normalise gas arg)
normalise (suc gas) (app fun arg) = normalise gas (app (normalise gas fun) (normalise gas arg))
normalise (suc gas) (t ⟦ s ⟧) = normalise gas (multi-step (suc gas) (t ⟦ s ⟧))
normalise gas (lam t) = lam (normalise gas t)
normalise gas t = t
