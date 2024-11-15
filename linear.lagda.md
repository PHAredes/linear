Some types we will need

```agda
open import Data.Maybe
open import Data.Fin using (Fin) renaming (fromℕ to fromNat; toℕ to toNat; zero to fzero; suc to fsuc)
open import Data.Nat using (zero; suc; _+_; _*_; _∸_) renaming (ℕ to Nat)

data _≺_ : Nat -> Nat -> Set where
  z≺s : {n : Nat} -> zero ≺ suc n
  s≺s : {n m : Nat} -> n ≺ m -> suc n ≺ suc m

data _=ᵣ_ : Nat -> Nat -> Set where -- recursive equality over Nat
  z=ᵣz : zero =ᵣ zero
  s=ᵣs : {m n : Nat} -> m =ᵣ n -> (suc m) =ᵣ (suc n)

data _≠_ : Nat -> Nat -> Set where
  z≠s : {n : Nat} -> zero ≠ suc n
  s≠z : {n : Nat} -> suc n ≠ zero
  s≠s : {n m : Nat} -> n ≠ m -> suc n ≠ suc m

_=ᵣ?_ : (n m : Nat) -> Maybe (n =ᵣ m)
zero =ᵣ? zero = just z=ᵣz
zero =ᵣ? (suc _) = nothing
(suc _) =ᵣ? zero = nothing
(suc n) =ᵣ? (suc m) with (n =ᵣ? m)
(suc n) =ᵣ? (suc m) | nothing = nothing
(suc n) =ᵣ? (suc m) | just p = just (s=ᵣs p)

```

Instead of representing variable names as straight natural numbers, we parameterise terms by the 
number of available variables n, and then only allow available variables to be referenced inside 
the term by using the type of finite sets to represent variable names. This way, we tame some of 
the error-prone nature of de Bruijn indices by asSigning different types to terms with differing 
numbers of available variables. Closed terms are represented as values of type Term 0.
I first encountered this trick in McBride (2003), but I know not from whence it originated.
[Liamoc](http://liamoc.net/posts/2zero14-zero1-zero1-context-split/index.html)

```agda
data Term (n : Nat) : Set where
  varₜ : Fin n -> Term n
  appₜ : Term n -> Term n -> Term n
  lamₜ : Term (suc n) -> Term n

{-
It is common to use unit type for ULC, but this is not required for implicit contexts
and Nat representations, as Nat type represent the idea of indices without adding
typing judgements to the system
-} 
```

Let's improve this idea. 
For a var to be named, it not only requires to be parameterized by `n` which will lead to the correct typeness,
it will also require that a natural number `k` (which is the argument to construct a variable) is lesser than `n`; 
it means that, for a var to be named, it must have a name which is a number smaller than the number of available variables

```agda
data TaggedTerm (n : Nat) : Set where
  tvar¹ : Fin n -> (k : Nat) -> k ≺ n -> TaggedTerm n
  tapp¹ : TaggedTerm n -> TaggedTerm n -> TaggedTerm n
  tlam¹ : TaggedTerm (suc n) -> TaggedTerm n
```

Now, we can define Linear terms by extending this to terms that contains terms

```agda
mutual
  data Linear (n : Nat) : Set where
    -- (k ≺ n) turns Fin n unnecessary as it achieves the same property
    varₗ : (k : Nat) -> (k ≺ n) -> Linear n
    appₗ : Linear n -> Linear n -> Linear n
    -- Type is also not need as we have no types
    lamₗ : (t : Linear (suc n)) -> (zero ∈! t) -> Linear n

  data _∈!_ {n : Nat} : (i : Nat) -> Linear n -> Set where
    ∈!varₗ   : {i k : Nat} -> (p : k ≺ n) -> (i =ᵣ k) -> i ∈! (varₗ k p)
    ∈!appₗ-l : {i : Nat} -> {x y : Linear n} -> i ∈! x -> i ∉ y -> i ∈! (appₗ x y)
    ∈!appₗ-r : {i : Nat} -> {x y : Linear n} -> i ∉ x -> i ∈! y -> i ∈! (appₗ x y)
    ∈!lamₗ   : {i : Nat} -> {t : Linear (suc n)} -> {p : zero ∈! t} -> suc i ∈! t -> i ∈! (lamₗ t p)

  data _∉_ {n : Nat} : (i : Nat) -> Linear n -> Set where
    ∉varₗ : {i k : Nat} -> (p : k ≺ n) -> (i ≠ k) -> i ∉ (varₗ k p)
    ∉appₗ : {i : Nat} -> {x y : Linear n} -> i ∉ x -> i ∉ y -> i ∉ (appₗ x y)
    ∉lamₗ : {i : Nat} -> {t : Linear (suc n)} -> {p : zero ∈! t} -> suc i ∉ t -> i ∉ (lamₗ t p)

closed : Linear zero -- (λx.x) y
closed = appₗ (lamₗ (varₗ zero z≺s) (∈!varₗ z≺s z=ᵣz)) (lamₗ (varₗ zero z≺s) (∈!varₗ z≺s z=ᵣz))
```
Now we have a linear small calculus. Particularly:

- Each lambda abstraction can only capture variables that are not already in its scope.
- Each variable can only be used once, as it is associated with a specific index `k` an
can only be referenced once.
- The `∈!` relation ensures that variables are not duplicated across applications.

It ensures linearity and is simple to read, while also ensuring
that subterms of an app aren't "ill-typed" for Agda type checker; it single-handed solve the
issue of traversing back the AST, by abstracting it in a membership relation by
applying simple equivalence checks between the size `n` and the variable name `k`

Note that this is untyped as the correctness of the terms in this system is based on variables 
being well-scoped and the correctness of their usage, but this is a syntactic property, not a semantic one.

Yet there are still some problems with using this representation directly:
We would be required to give proofs of linearity for each single `var` and `lam`
all over again within terms representation.

To solve this, we will create a map from `Linear` to `Term`:

```agda
-- this map is straightforward
λl->λ : {n : Nat} -> Linear n -> Term n
λl->λ {n} (varₗ x k) = varₜ (db x k)
  -- takes a de Bruijn index and maps to a Fin index
  where db : {n : Nat} -> (x : Nat) -> (x ≺ n) -> Fin n 
        db (zero) (z≺s) = fzero
        db (suc t) (s≺s f) = fsuc (db t f)
λl->λ (appₗ x y) = appₜ (λl->λ x) (λl->λ y)
λl->λ (lamₗ x _) = lamₜ (λl->λ x)
```

For the `Term` to `Linear` map, we first need some auxiliar functions; Although they look a bit tricky,
all we need to do is to make a version of previously defined functions and types to work with `Maybe` monad.
This is a consequence of this mapping only being possible for linear terms

```agda
-- given two naturals n and m, maybe n ≺ m is maybe a proof that suc n ≺ suc m
S≺S : {n m : Nat} -> Maybe (n ≺ m) -> Maybe (suc n ≺ suc m)
S≺S nothing = nothing
S≺S (just p) = just (s≺s p)

-- given two naturals n and m, n ≺? m is maybe a proof of n ≺ m
_≺?_ : (n m : Nat) -> Maybe (n ≺ m)
_ ≺? zero = nothing
zero ≺? (suc n) = just z≺s
(suc n) ≺? (suc m) = S≺S (n ≺? m)

S≠S : {n m : Nat} -> Maybe (n ≠ m) -> Maybe (suc n ≠ suc m)
S≠S nothing = nothing
S≠S (just p) = just (s≠s p)

-- given two naturals n and m, n ≠? m is maybe a proof of n ≠ m
_≠?_ : (n m : Nat) -> Maybe (n ≠ m)
zero ≠? zero = nothing
zero ≠? (suc _) = just z≠s
(suc _) ≠? zero = just s≠z
(suc n) ≠? (suc m) = S≠S (n ≠? m)

-- given a linear term, maybe a proof that i ∉ t
_∉?_ : {n : Nat} -> (i : Nat) -> (t : Linear n) -> Maybe (i ∉ t)
i ∉? (varₗ k p) = case-var (i ≠? k)
  where case-var : {i : Nat} -> Maybe (i ≠ k) -> Maybe (i ∉ varₗ k p)
        case-var nothing = nothing
        case-var (just p≠) = just (∉varₗ p p≠)
i ∉? (appₗ x y) = case-app (i ∉? x) (i ∉? y)
  where case-app : {n i : Nat} -> {x y : Linear n} -> Maybe (i ∉ x) -> Maybe (i ∉ y) -> Maybe (i ∉ (appₗ x y))
        case-app nothing _ = nothing
        -- exhaustive pattern matching, can't delete next case
        case-app _ nothing = nothing
        case-app (just x) (just y) = just (∉appₗ x y)
i ∉? (lamₗ t f) = case-lam ((suc i) ∉? t)
  where case-lam : {n i : Nat} -> {t : Linear (suc n)} -> {p : zero ∈! t} -> Maybe (suc i ∉ t) -> Maybe (i ∉ (lamₗ t p))
        case-lam nothing = nothing
        case-lam (just p) = just (∉lamₗ p)

-- given a linear term, maybe a proof that i ∈! t
_∈!?_ : {n : Nat} -> (i : Nat) -> (t : Linear n) -> Maybe (i ∈! t)
i ∈!? (varₗ k p) = case-var (i =ᵣ? k)
  where case-var : {i : Nat} -> Maybe (i =ᵣ k) -> Maybe (i ∈! varₗ k p)
        case-var nothing = nothing
        case-var (just p=ᵣ) = just (∈!varₗ p p=ᵣ)
i ∈!? (appₗ x y) = choose (i ∉? x) -- or  (i ∉? y)
  where case-app-x : {n i : Nat} -> {x y : Linear n} -> Maybe (i ∈! x) -> Maybe ((i ∉ y) -> i ∈! (appₗ x y))
        case-app-x nothing = nothing
        case-app-x (just p) = just (∈!appₗ-l p)
                
        case-app-y : {n i : Nat} -> {x y : Linear n} -> Maybe (i ∈! y) -> Maybe ((i ∉ x) -> i ∈! (appₗ x y))
        case-app-y nothing =  nothing
        case-app-y (just p)= just (λ z -> ∈!appₗ-r z p)

        choose : Maybe (i ∉ x) -> Maybe (i ∈! (appₗ x y))
        -- order of subterms is inverted, you need to swap if you choose y
        choose nothing =  ap (case-app-x (i ∈!? x)) (i ∉? y)
        choose (just _) = ap (case-app-y (i ∈!? y)) (i ∉? x)
i ∈!? (lamₗ t x) = case-lam (suc i ∈!? t)
  where case-lam : {n i : Nat} -> {t : Linear (suc n)} -> {p : zero ∈! t} -> Maybe (suc i ∈! t) -> Maybe (i ∈! (lamₗ t p))
        case-lam nothing = nothing
        case-lam (just p) = just (∈!lamₗ p)
```

Now, we have all the tools to map from closed `Terms` to Linear terms;
Again, we are just recursively checking that the terms ASTs are linear


```agda
λ->λl : {n : Nat} -> Term n -> Maybe (Linear n)
λ->λl {n} (varₜ x) = case-var ((toNat x) ≺? n)
  where case-var : Maybe (toNat x ≺ n) -> Maybe (Linear n)
        case-var nothing = nothing
        case-var (just p) = just (varₗ (toNat x) p)
λ->λl {n} (appₜ x y) = case-app (λ->λl {n} x) (λ->λl {n} y)
  where case-app : Maybe (Linear n) -> Maybe (Linear n) -> Maybe (Linear n)
        case-app nothing _ = nothing
        -- The next clause is marked as "soft" unreachable but it cannot be erased because of exhaustive pattern matching
        case-app _ nothing = nothing
        case-app (just x) (just y) = just (appₗ x y)
λ->λl {n} (lamₜ t) = case-lam (λ->λl {suc n} t)
  where case-lam : Maybe (Linear (suc n)) -> Maybe (Linear n)
        case-lam nothing = nothing
        case-lam (just u) = build-lamₗ (zero ∈!? u)
          where build-lamₗ : Maybe (zero ∈! u) -> Maybe (Linear n)
                build-lamₗ nothing = nothing
                build-lamₗ (just p) = just (lamₗ u p)
```

A function to prove consistency; the goal is to show that t->t is t -> just t, if t is linear.

```agda
t->t : Term 0 -> Maybe (Term 0)
t->t t = mb-λl->λl (λ->λl t)
  where mb-λl->λl : {n : Nat} -> Maybe (Linear n) ->  Maybe (Term n)
        mb-λl->λl nothing = nothing
        mb-λl->λl (just t) = just (λl->λ t)
```

So now may you ask why implementing two different calculus with a mapping from one to another
Well, you can choose two paths with this:

-- for non-linear terms, normalisation works just as in PLFA
-- for linear terms, you can use `Term n` and then apply `t->t` to ensure linearity;

This provides an useful framework for both ULC and UALC, keeping the expressiveness of both systems
while only dealing with the issues of UALC syntax if strictly necessary


## Notes

Some may look at the reference untyped linear λ calculus as described in 
"L-types for resource awareness: an implicit name approach" and think this is just a replication.
Although the linear λ calculus and the translation to a regular λ calculus described here are
almost equal, there are subtle but important differences.

Here, the type of linear and regular terms are parameterized by a Nat representing the amount of
available (free) variables. It allows to represent L-type of terms without using lists and also
allows the representation of partial environments in simple terms (as we will see later on).

##  Tests

```agda
-- helper vars
var-zero : {n : Nat} -> Term (suc n)
var-zero = varₜ fzero

var-one : {n : Nat} -> Term (suc (suc n))
var-one = varₜ (fsuc fzero)

var-two : {n : Nat} -> Term (suc (suc (suc n)))
var-two = varₜ (fsuc (fsuc fzero))

var0 : {n : Nat} -> Linear (suc n)
var0 = varₗ zero z≺s

var1 : {n : Nat} -> Linear (suc (suc n))
var1 = varₗ (suc zero) (s≺s z≺s)

var2 : {n : Nat} -> Linear (suc (suc (suc n)))
var2 = varₗ (suc (suc zero)) (s≺s (s≺s z≺s))

-- tests
flipₜ : Term 0
flipₜ = lamₜ (lamₜ (lamₜ (appₜ (appₜ var-two var-zero) var-one)))

flipₜt->t : Term 0
flipₜt->t = from-just (t->t (lamₜ (lamₜ (lamₜ (appₜ (appₜ var-two var-zero) var-one)))))
-- returns unit type if not linear, thus doesn't typecheck

-- Proofs of linearity are straightforward to built with auto solver
flipₗ : Linear 0
flipₗ = lamₗ (lamₗ (lamₗ (appₗ (appₗ var2 var0) var1) -- the term
  -- proof of applications
  (∈!appₗ-l (∈!appₗ-r (∉varₗ (s≺s (s≺s z≺s)) z≠s) (∈!varₗ z≺s z=ᵣz)) (∉varₗ (s≺s z≺s) z≠s)))
  -- proof of inner λ
  (∈!lamₗ (∈!appₗ-r (∉appₗ (∉varₗ (s≺s (s≺s z≺s)) (s≠s z≠s)) (∉varₗ z≺s s≠z)) (∈!varₗ (s≺s z≺s) (s=ᵣs z=ᵣz)))))
  -- proof of outer λ
  (∈!lamₗ (∈!lamₗ (∈!appₗ-l  (∈!appₗ-l (∈!varₗ (s≺s (s≺s z≺s)) (s=ᵣs (s=ᵣs z=ᵣz)))  (∉varₗ z≺s s≠z))  (∉varₗ (s≺s z≺s) (s≠s s≠z)))))

curryₜ : Term 0
curryₜ = lamₜ (lamₜ (lamₜ (appₜ var-two (appₜ var-one var-zero))))

curryₜt->t : Term 0
curryₜt->t = from-just (t->t (lamₜ (lamₜ (lamₜ (appₜ var-two (appₜ var-one var-zero))))))

curryₗ : Linear 0
curryₗ = lamₗ (lamₗ (lamₗ (appₗ var2 (appₗ var1 var0)) 
   (∈!appₗ-r (∉varₗ (s≺s (s≺s z≺s)) z≠s) 
   (∈!appₗ-r (∉varₗ (s≺s z≺s) z≠s) (∈!varₗ z≺s z=ᵣz))))
   (∈!lamₗ (∈!appₗ-r (∉varₗ (s≺s (s≺s z≺s)) (s≠s z≠s)) (∈!appₗ-l (∈!varₗ (s≺s z≺s) (s=ᵣs z=ᵣz)) (∉varₗ z≺s s≠z))))) 
   (∈!lamₗ (∈!lamₗ (∈!appₗ-l (∈!varₗ (s≺s (s≺s z≺s)) (s=ᵣs (s=ᵣs z=ᵣz))) (∉appₗ (∉varₗ (s≺s z≺s) (s≠s s≠z)) (∉varₗ z≺s s≠z)))))

joinₜ : Term 0
joinₜ = lamₜ (lamₜ (appₜ (appₜ var-one var-zero) (var-one)))

-- joinₜt->t : Term 0
-- joinₜt->t = {!   !} -- from-just (t->t (lamₜ (lamₜ (appₜ (appₜ var-one var-zero) (var-one)))))
-- {-
-- Level.Lift Agda.Primitive.lzero Agda.Builtin.Unit.⊤ !=< Term 0
-- when checking that the expression
-- from-just
-- (t->t (lamₜ (lamₜ (appₜ (appₜ var-one var-zero) var-one))))
-- has type Term 0
-- -}

-- joinₗ : Linear 0
-- joinₗ = lamₗ (lamₗ (appₗ (appₗ var1 var0) (var1)) 
--   (∈!appₗ-l (∈!appₗ-r (∉varₗ (s≺s z≺s) z≠s) (∈!varₗ z≺s z=ᵣz)) (∉varₗ (s≺s z≺s) z≠s))) 
--   (∈!lamₗ (∈!appₗ-l (∈!appₗ-l (∈!varₗ (s≺s z≺s) (s=ᵣs z=ᵣz)) (∉varₗ z≺s s≠z)) 
--   (∉varₗ (s≺s z≺s) {!   !})))
```

## Normalisation (explicit substitution)

Implementing normalisation for UALC directly will fall in a rabbit hole of using `Maybe` monads
for proofs of linearity; we can instead implement normalisation for ULC and just use the previous map.

```agda

mutual 
  data Lam : Set where
    var : (n : Nat) -> Lam
    _∙_ : Lam -> Lam -> Lam
    ƛ   : Lam -> Lam
    _〚_〛 : Lam -> Sig -> Lam -- instantiation of substitution

  data Sig : Set where 
    _/ : Lam -> Sig -- cons
    ⇑_ : Sig -> Sig -- shift
    ↑  : Sig       -- lift

-- Term to Lam
t->l : {n : Nat} -> Term n -> Lam
t->l (varₜ k) = (var (toNat k))
t->l (appₜ t₁ t₂) = (t->l t₁) ∙ (t->l t₂)
t->l (lamₜ t) = ƛ (t->l t)

-- Lam to Term
l->t : {n : Nat} -> Lam -> Maybe (Term n)
l->t {suc n} (var k) = just (varₜ (fromNat n))
l->t {zero} (var k) = nothing -- there is no var with Term 0
l->t (x ∙ y) with (l->t x) | (l->t y)
... | (just x) | (just y) = just (appₜ x y)
... | _ | _ = nothing
l->t (ƛ x) with l->t x
... | just x = just (lamₜ x)
... | nothing = nothing
l->t (_ 〚 _ 〛) = nothing
-- we can use with to pattern match on intermediate steps or declare a intermediary function with where

-- β reduction
β-red : Lam -> Lam
β-red (((ƛ x) ∙ y)) = x 〚 y / 〛
β-red t = t

contractυ : Lam -> Lam
contractυ (ƛ t 〚 s 〛) = ƛ (t 〚 ⇑ s 〛)
contractυ ((t₁ ∙ t₂)〚 s 〛) = (t₁ 〚 s 〛) ∙ (t₂ 〚 s 〛)
contractυ (var zero 〚 t / 〛) = t
contractυ (var (suc k) 〚 t / 〛) = var k
contractυ (var zero 〚 ⇑ _ 〛) = var zero
contractυ (var (suc k) 〚 ⇑ s 〛) = (var k 〚 s 〛) 〚 ↑ 〛
contractυ (var x 〚 ↑ 〛) = var x
contractυ t = t

-- distribute substitutions
contractυ* : Nat -> Lam -> Lam
contractυ* (suc k) ((t 〚 s 〛)〚 s' 〛) = contractυ* k (contractυ* k (contractυ (t 〚 s 〛)) 〚 s' 〛)
contractυ* (suc k) (t 〚 s 〛) = contractυ* k (contractυ (t 〚 s 〛))
contractυ* zero (t 〚 s 〛) = t 〚 s 〛
contractυ* k (t₁ ∙ t₂) = (contractυ* k t₁) ∙ (contractυ* k t₂)
contractυ* k (ƛ t) = ƛ (contractυ* k t)
contractυ* _ (var k) = var k

-- normalisation in Lam 
normalise : Nat -> Lam -> Lam
normalise (suc k) ((ƛ t₁) ∙ t₂) = normalise k (contractυ* (suc k) (t₁ 〚 t₂ / 〛))
normalise k ((var i) ∙ t) = var i ∙ normalise k t
normalise (suc k) (t₁ ∙ t₂) = normalise k ((normalise (suc k) t₁) ∙ normalise (suc k) t₂)
normalise (suc k) (t 〚 s 〛) = normalise k (contractυ* (suc k) (t 〚 s 〛))
normalise k (ƛ t) = ƛ (normalise k t)
normalise k t = t

-- normalisation in Linear
normLinear : {n : Nat} -> Nat -> Linear n -> Maybe (Linear n)
normLinear {n} k t = case (l->t (normalise k (t->l (λl->λ t))))
                         where case : Maybe (Term n) -> Maybe (Linear n)
                               case nothing = nothing
                               case (just t) = λ->λl t
    
```

## Proof of normalisation

```agda

open import Data.Product
open import Data.Empty
open import Data.Bool
open import Data.Unit
open import Data.Empty
import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning

infix 5 _==_ 
infix 4 _∙_

-- Definitional equality
data _==_ : Lam -> Lam -> Set where
  β : ∀ {x y : Lam} -> (((ƛ x) ∙ y)) == (x 〚 y / 〛)
--  η : ∀ {x y : Lam} -> (ƛ (x ∙ (var zero 〚 y / 〛))) == (x 〚 y / 〛)
  abs==  : ∀ {x y : Lam} -> (x == y) -> (ƛ x == ƛ y)
  app==  : ∀ {t₁ t₂ p₁ p₂ : Lam} -> (t₁ == p₁) -> (t₂ == p₂) -> ((t₁ ∙ t₂) == (p₁ ∙ p₂))
  refl==  : ∀ {t : Lam} -> (t == t)
  sym==   : ∀ {t₁ t₂ : Lam} -> t₁ == t₂ -> t₂ == t₁
  trans== : ∀ {t₁ t₂ t₃ : Lam} -> t₁ == t₂ -> t₂ == t₃ -> t₁ == t₃
  app-cong : ∀ (f : Nat -> Lam -> Lam) (n : Nat) {t₁ t₂ : Lam}
  -- f (M N) ≡ (f M) (f N)
    -> _==_ (f n (_∙_ (t₁) (t₂))) (_∙_ (f n t₁) (f n t₂))

-- Propositional equality implies definitional equality
≡→== : ∀ {t₁ t₂ : Lam} -> t₁ ≡ t₂ -> t₁ == t₂
≡→== pe rewrite pe = refl==

isNormal : Nat -> Lam -> Set
isNormal n (var x) = ⊤
isNormal n (ƛ x) with isNormal n x
... | yup = ⊤
isNormal (suc n) (x 〚 x₁ 〛) with isNormal n (contractυ* n (x 〚 x₁ 〛))
... | yup = ⊤
isNormal _ _ = ⊥ 

σ-norm : Lam -> Lam -> Set
σ-norm t nf = (nf == t) × isNormal 0 nf

test1 : σ-norm (var 0) (var 0)
test1 = (refl== , tt)

-- test2 : σ-norm ((ƛ (var 0)) ∙ var 1) (var 0)
-- test2 = ({!   !} , tt) -- requires an absurd to be proveable

absurd : ⊥ -> ∀ {A : Set} -> A
absurd ()

mutual
  norm0lam : ∀ {t} → ƛ (normalise 0 t) ≡ ƛ t
  norm0lam {var n} = refl
  norm0lam {t ∙ t₁} = cong ƛ norm0app
  norm0lam {ƛ t} = cong ƛ norm0lam
  norm0lam {t 〚 x 〛} = refl
  
  norm0app : ∀ {t₁ t₂ : Lam} → normalise 0 (t₁ ∙ t₂) ≡ (t₁ ∙ t₂)
  norm0app {var n} {var n₁} = (cong₂ _∙_ refl refl)
  norm0app {var n} {t₂ ∙ t₃} = (cong₂ _∙_ refl norm0app)
  norm0app {var n} {ƛ t₂} = (cong₂ _∙_ refl (norm0lam))
  norm0app {var n} {t₂ 〚 x 〛} = (cong₂ _∙_ refl refl)
  norm0app {t₁ ∙ t₃} {t₂} = refl
  norm0app {ƛ t₁} {t₂} = refl
  norm0app {t₁ 〚 x 〛} {t₂} = refl

norm-eq : ∀ {t} → normalise 0 t ≡ t
norm-eq {var n} = refl
norm-eq {t ∙ t₁} = norm0app
norm-eq {ƛ t} = norm0lam
norm-eq {t 〚 x 〛} = refl

norm-terminates : ∀ (t : Lam) (gas : Nat) -> σ-norm t (normalise gas t)
-- var always in normal form
norm-terminates (var x) zero = refl== , tt
norm-terminates (var x) (suc gas) = refl== , tt
-- if t in normal form, λ t is in normal form
norm-terminates (ƛ t) n with norm-terminates t n
norm-terminates (ƛ t) zero    | eq , _  = abs== eq , tt
norm-terminates (ƛ t) (suc n) | eq , _  = abs== eq , tt
-- depends on gas to normalise further
norm-terminates (t 〚 x 〛) n with (contractυ* n (t 〚 x 〛))  
norm-terminates (t 〚 x 〛) zero    | eq = refl== , {!!}
norm-terminates (t 〚 x 〛) (suc n) | eq = {!   !} , {!   !}
-- i hate applications
norm-terminates (t₁ ∙ t₂) zero with isNormal zero t₁ | isNormal zero t₂
norm-terminates (t₁ ∙ t₂) zero | p | q = ≡→== norm0app  , subst (λ x → {!!}) (norm0app {t₁} {t₂}) {!!}
norm-terminates (t₁ ∙ t₂) (suc gas) with isNormal (suc gas) t₁ | isNormal (suc gas) t₂
... | p | q = {!!} , {!!}

```
 
       
