module NbE where

open import Data.Product

infix  2  _⟶_
infix  5  s_
infix  6  ƛ_
infixl 7  _∙_

data Nat : Set where
  suc  : Nat → Nat
  zero : Nat
{-# BUILTIN NATURAL Nat #-}

data Var : Nat → Set where -- ≃ Fin
  z : ∀ {n} → Var (suc n)
  s_ : ∀ {n} → Var n → Var (suc n)

data Term (n : Nat) : Set where
  var : Var n → Term n
  _∙_ : Term n → Term n → Term n
  ƛ_ : Term (suc n) → Term n

extᵣ : ∀ {m n} → (Var m → Var n) → (Var (suc m) → Var (suc n))
extᵣ p z = z  
extᵣ p (s k) = s (p k)

ren : ∀ {m n} → (Var m → Var n) → (Term m → Term n)
ren p (var k) = var (p k)
ren p (L ∙ M) = (ren p L) ∙ (ren p M) 
ren p (ƛ N) = ƛ (ren (extᵣ p) N)

extₛ : ∀ {m n} → (Var m → Term n) → (Var (suc m) → Term (suc n))
extₛ p z = var z
extₛ p (s k) = ren s_ (p k)

subs : ∀ {m n} → (Var m → Term n) → (Term m → Term n)
subs p (var k) = p k
subs p (L ∙ M) = (subs p L) ∙ (subs p M)
subs p (ƛ N)   = ƛ (subs (extₛ p) N)

_⟨_⟩  : ∀ {n} → Term (suc n) → Term n → Term n 
_⟨_⟩ {n} N M  = subs {suc n} {n} ρ N
  where
  ρ : Var (suc n) → Term n
  ρ z     =  M
  ρ (s k)  =  var k

mutual
  data Normal : ∀ {n} → Term n → Set where
    Λ_  : ∀ {n} {N : Term (suc n)} → Normal N → Normal (ƛ N)
    ∣_∣ : ∀ {n} {M : Term n} → Neutral M → Normal M

  data Neutral : ∀ {n} → Term n → Set where
    varₙ  : ∀ {n} → (k : Var n) → Neutral (var k)
    _°_  : ∀ {n} → {L : Term n} {M : Term n} → Neutral L → Normal M → Neutral (L ∙ M)

-- reduction step
data _⟶_ : ∀ {n} → Term n → Term n → Set where
  -- app left
  ξ₁ : ∀ {n} {L L′ M : Term n}
    → L ⟶ L′
      -----------------
    → L ∙ M ⟶ L′ ∙ M
  -- app right
  ξ₂ : ∀ {n} {V M M′ : Term n}
    → Normal V
    → M ⟶ M′
      ----------------
    → V ∙ M ⟶ V ∙ M′
  -- inside λ
  ζ : ∀ {n} {N N′ : Term (suc n)}
    → N ⟶ N′
      -----------
    → ƛ N ⟶ ƛ N′
  -- β reduction
  β : ∀ {n} {N : Term (suc n)} {V : Term n}
    → Normal V
      ----------------------------
    → (ƛ N) ∙ V ⟶  N ⟨ V ⟩

-- Reflexive and transitive closure
data _⟶*_ : ∀ {n} → Term n → Term n → Set where

  _∎ : ∀ {n} (M : Term n)
      ---------------------
    → M ⟶* M

  _⟶⟨_⟩_ : ∀ {n} (L : Term n) {M N : Term n}
    → L ⟶ M
    → M ⟶* N
      ---------
    → L ⟶* N

data Progress {n} (M : Term n) : Set where
  step : ∀ (N : Term n) → M ⟶ N → Progress M
  done : Normal M → Progress M

progress : ∀ {n} → (M : Term n) → Progress M
progress (var k) = done ∣ varₙ k ∣
progress (ƛ N)  with progress N
...    | step N′ r  =  step (ƛ N′) (ζ r)
...    | done NmV   =  done (Λ NmV)
progress (L ∙ M)  with progress L
progress (L ∙ M)  | step L′ r  =  step (L′ ∙ M) (ξ₁ r)
progress (V ∙ M)  | done NmV     with progress M
progress (V ∙ M)        | done NmV        | step M′ r   =  step (V ∙ M′) (ξ₂ NmV r)
progress (V ∙ W)        | done ∣ NeV ∣    | done NmW    =  done ∣ NeV ° NmW ∣
progress ((ƛ V) ∙ W)    | done (Λ NmV)    | done NmW    =  step ( V ⟨ W ⟩ ) (β NmW)

Gas : Set
Gas = Nat

data Normalise {n} (M : Term n) : Set where

  out-of-gas : ∀ {N : Term n}
    → M ⟶* N
      -------------
    → Normalise M

  normal : ∀ {N : Term n}
    → Gas
    → M ⟶* N
    → Normal N
     --------------
    → Normalise M

normalise : ∀ {n}
  → Gas
  → ∀ (M : Term n)
    -------------
  → Normalise M
normalise zero    L                       =  out-of-gas (L ∎)
normalise (suc g) L with progress L
...  | done VL                            =  normal (suc g) (L ∎) VL
...  | step M L⟶M with normalise g M
...          | out-of-gas M⟶*N           =  out-of-gas (L ⟶⟨ L⟶M ⟩ M⟶*N)
...          | normal h M⟶*N VN          =  normal h (L ⟶⟨ L⟶M ⟩ M⟶*N) VN

-- I'll not adapt it as it would be time consuming and pointless