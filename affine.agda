open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Product
open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin renaming (_+_ to _+f_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

infixr 5 _∷_
infix 7 _[_]
infix 6 _—→_ 

data Context : Nat → Set where
  ∅   : Context zero
  _∷_ : ∀ {n} → Bool → Context n → Context (suc n)

_∪_ : ∀ {n} → Context n → Context n → Context n
∅ ∪ ∅ = ∅
(x ∷ Γ) ∪ (y ∷ Δ) = (x ∨ y) ∷ (Γ ∪ Δ)

variable
  m n : Nat
  b : Bool
  Γ Δ : Context n

mutual
  data Term : Context n → Set where
    var  : (i : Fin n) → Term Γ
    lam  : Term (true ∷ Γ) → Term Γ
    app  : Term Γ → Term Δ → Term (Γ ∪ Δ)
    era  : Term (false ∷ Γ) → Term Γ
    _[_] : Term Γ → Sig Γ Δ → Term Δ -- instantiation of substitution

  data Sig : Context n → Context m → Set where
    _/   : Term Δ → Sig (true ∷ Γ) (Γ ∪ Δ) -- cons
    ⇑_   : Sig Γ Δ → Sig (b ∷ Γ) (b ∷ Δ) -- shift
    ↑    : Sig Γ (b ∷ Γ) -- lift

-- reduction step
data _—→_ : Term Γ → Term Γ → Set where
  β-red : ∀ {m n : Nat} {bod : Term (true ∷ Γ)} {arg : Term Δ} →
          app (lam bod) arg —→ bod [ arg / ]

  app-l : ∀ {fun fun' : Term Γ} {arg : Term Δ} →
          fun —→ fun' → app fun arg —→ app fun' arg

  app-r : ∀ {fun : Term Γ} {arg arg' : Term Δ} →
          arg —→ arg' → app fun arg —→ app fun arg'

  lam : ∀ {bod bod' : Term (true ∷ Γ)} →
        bod —→ bod' → lam bod —→ lam bod'

  era : ∀ {trm trm' : Term (false ∷ Γ)} →
        trm —→ trm' → era trm —→ era trm'

-- reflexive and transitive closure
data _—→*_ : Term Γ → Term Γ → Set where
  refl  : ∀ {trm : Term Γ} → trm —→* trm
  trans : ∀ {trm₁ trm₂ trm₃ : Term Γ} → trm₁ —→ trm₂ → trm₂ —→* trm₃ → trm₁ —→* trm₃
  -- Next case seems a bit weird because termination checker can't infer implicit args correctly
  -- it is just `(ρ (app fun arg)) —→* (app (ρ fun) (ρ arg))` or currying on app if you prefer
  cong : ∀ (fun : Term Γ) (arg : Term Δ) (ρ : ∀ {m n} {Γ : Context m} {Δ : Context n} → Term Γ → Term Δ)
         →  (ρ (app {n} {Γ} {Δ} fun arg))
          —→*
         (app {n} {Γ} {Δ} (ρ {n} {n} {Γ} fun) (ρ {n} {n} {Δ} arg)) 

-- helper lemma to magase λ _ → _ [ sig ] easier to instantiate substitution on applications
-- note that I choose to note try to recursively apply it on subterms as it would make it really hard to maintain the structure of the term
-- this implementation doesn't require to use predicates to assert non-overlaping variables between subterms of app
-- which is easier but really inefficient
βred : Term Γ → Term Γ
βred (app (lam bod) arg) = bod [ arg / ] -- it looks inverted but it is correct (de Bruijn indices manipulation)
βred trm = trm

applySubst : ∀ {m n} {Γ : Context m} {Δ : Context n} → Sig Γ Δ → Term Γ → Term Δ
applySubst sig t = t [ sig ]

contractυ : Term Γ → Term Γ
contractυ (lam bod [ sig ]) = lam (bod [ ⇑ sig ])
contractυ (app {Γ = Γ} fun arg [ sig ]) = applySubst sig (app fun arg)
contractυ (trm [ sig ] [ sig' ]) = contractυ (trm [ sig ]) [ sig' ]
contractυ (var zero [ _/ {n} _ ]) = era (var {suc n} zero)
contractυ (var (suc idx) [ trm / ]) = var idx
contractυ (var zero [ ⇑_ {n} _ ]) = var {suc n} zero
contractυ (_[_] {suc n} (var (suc idx)) (⇑_ {n} s)) = (var idx [ s ]) [ ↑ ]
contractυ (var idx [ ↑ ]) = var (suc idx)
contractυ t = t

-- distributed substitutions
contractυ* : Nat → Term Γ → Term Γ
contractυ* (suc gas) ((trm [ sig ]) [ sig' ]) = contractυ* gas (contractυ* gas ((trm [ sig ]) [ sig' ]))
contractυ* (suc gas) (trm [ sig ]) = contractυ* gas (contractυ (trm [ sig ]))
contractυ* zero (trm [ sig ]) = trm [ sig ]
contractυ* gas (app fun arg) = app (contractυ* gas fun) (contractυ* gas arg)
contractυ* gas (lam bod) = lam (contractυ* gas bod)
contractυ* zero (era trm) = era trm
contractυ* (suc gas) (era trm) = era (contractυ* gas trm)
contractυ* _ (var idx) = var idx

normalise : Nat → Term Γ → Term Γ
normalise (suc gas) (app (lam bod) arg) = normalise gas (contractυ* (suc gas) (βred (app (lam bod) arg)))
normalise gas (app (var idx) arg) = app (var idx) (normalise gas arg)
normalise (suc gas) (app fun arg) = normalise gas (app (normalise gas fun) (normalise gas arg))
normalise (suc gas) (t [ s ]) = normalise gas (contractυ* (suc gas) (t [ s ]))
normalise gas (lam t) = lam (normalise gas t)
normalise gas t = t

isNormal : ∀ {n} {Γ : Context n} → Term Γ → Set
isNormal (var _) = ⊤
isNormal (lam bod) = isNormal bod
isNormal (app fun arg) = ⊥
isNormal (era trm) = isNormal trm
isNormal (trm [ sig ]) = ⊥

normalizesTo : Term Γ → Term Γ → Set
normalizesTo {n} trm nt = (normalise (n) trm ≡ nt) × isNormal nt

lemma : ∀ (trm : Term Γ) → ∃[ nt ] isNormal nt × trm —→* nt -- a bit redundant but it makes the intent clear
lemma = {!!}

