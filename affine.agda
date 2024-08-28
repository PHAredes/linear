{-# OPTIONS --cubical #-}

module affine where
{-
This code requires lots of mutual recursion and are not the best way to represent affine lambda calculus
I'm sorry if you had to read this
-}

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty
open import Cubical.Data.Bool renaming (_≤_ to lt)
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat renaming (ℕ to Nat)

variable
  m n i idx j : Nat

data _≤_ : Nat → Nat → Type where
  z≤n : zero ≤ n
  s≤s : m ≤ n → suc m ≤ suc n 

_<_ : Nat → Nat → Type
m < n = suc m ≤ n

pattern z<s     {n}     = s≤s (z≤n {n})
pattern s<s {m} {n} m<n = s≤s {m} {n} m<n
pattern sz<ss   {n}     = s<s (z<s {n})

z<sn : zero < n → zero < suc n
z<sn = λ _ → s≤s z≤n

mutual
  data Linear : Nat → Type where
    var : (idx : Nat) → idx < n → Linear n
    app : Linear n → Linear n → Linear n
    lam : (bod : Linear (suc n)) → (n ∈! bod) → Linear n

  data _∈!_ : (i : Nat) → Linear n → Type where
    ∈!var   : (p : idx < n) → i ≡ idx → i ∈! (var idx p)
    ∈!app-l : {fun arg : Linear n} → i ∈! fun → i ∉ arg → i ∈! (app fun arg)
    ∈!app-r : {fun arg : Linear n} → i ∉ fun → i ∈! arg → i ∈! (app fun arg)
    ∈!lam   : {bod : Linear (suc n)} → {p : n ∈! bod} → suc i ∈! bod → i ∈! (lam bod p)
  
  data _∉_ : (i : Nat) → Linear n → Type where
    ∉var : (p : idx < n) → ¬ (i ≡ idx) → i ∉ (var idx p)
    ∉app : {fun arg : Linear n} → i ∉ fun → i ∉ arg → i ∉ (app fun arg)
    ∉lam : {bod : Linear (suc n)} → {p : n ∈! bod} → suc i ∉ bod → i ∉ (lam bod p)

-- shift provides both weakening and swap rules
mutual
  shift : (Nat → Nat) → Linear n -> Linear (suc n)
  shift f (var idx p) = var (suc idx) (s<s p)
  shift f (app fun arg) = app (shift f fun) (shift f arg)
  shift f (lam bod p) = lam (shift (λ x → suc x) bod) (shift∈! p)

  shift∈! : ∀ {bod : Linear n} -> i ∈! bod -> (suc i) ∈! (shift (λ x → suc x) bod)
  shift∈! (∈!var p eq)   = ∈!var (s<s p) (cong suc (eq)) 
  shift∈! (∈!app-l p np) = ∈!app-l (shift∈! p) (shift∉ np)
  shift∈! (∈!app-r np p) = ∈!app-r (shift∉ np) (shift∈! p)
  shift∈! (∈!lam p)      = ∈!lam (shift∈! p)

  shift∉ : ∀ {bod : Linear n} -> i ∉ bod -> (suc i) ∉ (shift (λ x → suc x) bod)
  shift∉ (∉var p neq) = ∉var (s<s p) (λ r → neq (cong predℕ r))
  shift∉ (∉app p q)   = ∉app (shift∉ p) (shift∉ q)
  shift∉ (∉lam p)     = ∉lam (shift∉ p)

ext : (Nat → Linear n) → (Nat → Linear (suc n))
ext σ zero    = var zero (s≤s z≤n)
ext σ (suc x) = shift (λ z → suc z) (σ x)

-- Good, now we can raise index up by one
-- we can with this weaidxen a term
-- we need to reduce index even tho we cannot contract ???
-- I hope this is enough for us to woridx with

mutual
  subs : (Nat → Linear n) → Linear (suc n) → Linear n
  subs σ (var idx p) = σ idx
  subs σ (app fun arg) = app (subs σ fun) (subs σ arg)
  subs σ (lam bod p) = lam (subs (ext σ) bod) (subs∈! p)

  subs∈! : ∀ {bod : Linear (suc (suc n))} → (suc i) ∈! bod → {σ : Nat → Linear n} → i ∈! subs (ext σ) bod
  subs∈! {n} {i = i} {.(var _ idx)} (∈!var idx eq) {σ} = subst (λ x → i ∈! x)
    (sym subs-ext-var) ({!!}) where
         ext∈! : ∀ {n i idx} {σ : Nat → Linear n} → i ≡ idx → i ∈! ext σ idx
         ext∈! {idx = zero} eq = ∈!var (s<s z≤n) eq
         ext∈! {idx = suc j} eq = {!shift∈!!}
  

  subs∈! (∈!app-l p np) = ∈!app-l (subs∈! p) (subs∉ np)
  subs∈! (∈!app-r np p) = ∈!app-r (subs∉ np) (subs∈! p)
  subs∈! (∈!lam p)      = ∈!lam (subs∈! p)

  subs∉ : ∀ {bod : Linear (suc (suc n))} → (suc i) ∉ bod → {σ : Nat → Linear n} → i ∉ subs (ext σ) bod
  subs∉ {i = i} {N} (∉var _ p) {σ} = {!   !}
  subs∉ (∉app p q)   = ∉app (subs∉ p) (subs∉ q)
  subs∉ (∉lam p)     = ∉lam (subs∉ p)

  subs-ext-var : ∀ {n} {σ : Nat → Linear n} {idx} {p : idx < suc (suc n)} 
      → subs (ext σ) (var idx p) ≡ ext σ idx
  subs-ext-var = refl


subs-zero : Linear n → Nat → Linear n
subs-zero t zero = t
subs-zero {n} t (suc idx) = var idx (pred<n {n} {idx})
  where
    pred<n : ∀ {n idx} → idx < n
    pred<n {zero} {idx} = {!!}
    pred<n {suc n} {zero} = z<s
    pred<n {suc n} {suc idx} = s<s (pred<n {n} {idx})


sub : Linear (suc n) → Linear n → Linear n
sub bod arg = subs (subs-zero arg) bod

-- Definitional equality
infix 0 _~_

data _~_ : Linear n -> Linear n -> Type where
  -- yeah, it is inverted, but to solve this I need to also invert some stuff bruh
  ~β      : ∀ {fun : Linear (suc n)} {arg : Linear n} {ρ} → app (lam fun ρ) arg ~ sub fun arg
  -- ~η : ?
  ~abs    : ∀ {bod₁ bod₂ : Linear (suc n)} {ρ₁ : n ∈! bod₁} {ρ₂ : n ∈! bod₂} -> (bod₁ ~ bod₂) -> lam bod₁ ρ₁ ~ lam bod₂ ρ₂
  ~app    : ∀ {fun₁ fun₂ arg₁ arg₂ : Linear n} -> (fun₁ ~ fun₂) -> (arg₁ ~ arg₂) -> app fun₁ arg₁ ~ app fun₂ arg₂
  ~refl   : ∀ {t : Linear n} -> (t ~ t)
  ~sym    : ∀ {t₁ t₂ : Linear n} -> t₁ ~ t₂ -> t₂ ~ t₁
  ~trans  : ∀ {t₁ t₂ t₃ : Linear n} -> t₁ ~ t₂ -> t₂ ~ t₃ -> t₁ ~ t₃
  app-cong : ∀ (f : Nat -> Linear n -> Linear m) {fun arg : Linear n}
    -> (f n (app fun arg)) ~ (app (f m fun) (f m arg))

-- Propositional equality implies definitional equality
≡→~ : ∀ {t : Linear n} -> t ≡ t -> t ~ t
≡→~ pe = ~refl

-- a bit verbose but woridxs (as we don't have rewrite)
≡→~² : ∀ {t₁ t₂ : Linear n} → t₁ ≡ t₂ → t₁ ~ t₂
≡→~² {t₁ = t₁} {t₂ = t₂} p = subst (λ x → t₁ ~ x) p (≡→~ refl)
