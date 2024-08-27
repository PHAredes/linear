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
  m n i k j : Nat

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
    var : (k : Nat) → k < n → Linear n
    app : Linear n → Linear n → Linear n
    lam : (N : Linear (suc n)) → (n ∈! N) → Linear n

  data _∈!_ : (i : Nat) → Linear n → Type where
    ∈!var   : (p : k < n) → i ≡ k → i ∈! (var k p)
    ∈!app-l : {L M : Linear n} → i ∈! L → i ∉ M → i ∈! (app L M)
    ∈!app-r : {L M : Linear n} → i ∉ L → i ∈! M → i ∈! (app L M)
    ∈!lam   : {N : Linear (suc n)} → {p : n ∈! N} → suc i ∈! N → i ∈! (lam N p)
  
  data _∉_ : (i : Nat) → Linear n → Type where
    ∉var : (p : k < n) → ¬ (i ≡ k) → i ∉ (var k p)
    ∉app : {L M : Linear n} → i ∉ L → i ∉ M → i ∉ (app L M)
    ∉lam : {N : Linear (suc n)} → {p : n ∈! N} → suc i ∉ N → i ∉ (lam N p)

-- rename provides both weakening and swap rules
mutual
  rename : (Nat → Nat) → Linear n -> Linear (suc n)
  rename f (var k p) = var (suc k) (s≤s p)
  rename f (app L M) = app (rename f L) (rename f M)
  rename f (lam N p) = lam (rename (λ x → suc x) N) (rename∈! p)

  rename∈! : ∀ {N : Linear n} -> i ∈! N -> (suc i) ∈! (rename (λ x → suc x) N)
  rename∈! (∈!var p eq)   = ∈!var (s<s p) (cong suc (eq)) 
  rename∈! (∈!app-l p np) = ∈!app-l (rename∈! p) (rename∉ np)
  rename∈! (∈!app-r np p) = ∈!app-r (rename∉ np) (rename∈! p)
  rename∈! (∈!lam p)      = ∈!lam (rename∈! p)

  rename∉ : ∀ {N : Linear n} -> i ∉ N -> (suc i) ∉ (rename (λ x → suc x) N)
  rename∉ (∉var p neq) = ∉var (s<s p) (λ r → neq (cong predℕ r))
  rename∉ (∉app p q)   = ∉app (rename∉ p) (rename∉ q)
  rename∉ (∉lam p)     = ∉lam (rename∉ p)

ext : (Nat → Linear n) → (Nat → Linear (suc n))
ext σ zero    = var zero (s≤s z≤n)
ext σ (suc x) = rename (λ z → suc z) (σ x)

mutual
  subs : (Nat → Linear (suc n)) → Linear n → Linear (suc n)
  subs σ (var k p) = σ k
  subs σ (app L M) = app (subs σ L) (subs σ M)
  subs σ (lam N p) = lam (subs (ext σ) N) (subs∈! p)

  subs∈! : ∀ {N : Linear n} → i ∈! N → {σ : Nat → Linear n} → suc i ∈! subs (ext σ) N
  subs∈! {i = i} {N} (∈!var k p) {σ} = {!   !}
  subs∈! (∈!app-l p np) = ∈!app-l (subs∈! p) (subs∉ np)
  subs∈! (∈!app-r np p) = ∈!app-r (subs∉ np) (subs∈! p)
  subs∈! (∈!lam p)      = ∈!lam (subs∈! p)

  subs∉ : ∀ {N : Linear n} → i ∉ N → {σ : Nat → Linear n} → suc i ∉ subs (ext σ) N
  subs∉ {i = i} {N} (∉var _ p) {σ} = {!   !}
  subs∉ (∉app p q)   = ∉app (subs∉ p) (subs∉ q)
  subs∉ (∉lam p)     = ∉lam (subs∉ p)
