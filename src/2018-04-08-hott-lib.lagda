---
layout: "post"
title: "HoTT basics in Agda"
date: "2018-07-05"
categories: type-theory
toc: true
---

This is my attempt to collect in just one-file, a basic overview of HoTT in Agda.
This source code was type-checked by Agda 2.5.4.

Based on:

<div class="references" markdown="1">
- https://github.com/HoTT/HoTT-Agda/
- https://mroman42.github.io/ctlc/agda-hott/Total.html
</div>

Agda has a pragma to work with HoTT (`--without-K`):

\begin{code}
{-# OPTIONS --without-K #-}
open import Agda.Primitive public

_ = Set -- trick for avoiding Agda module errors (jekyll)
\end{code}

Universes
-------------------------------------------------------------------------------
Type universe hierarchy. It hides Agda primitive
hierarchy and the keyword `Set`. It uses `Type` instead.

\begin{code}

module Universes where

  -- Our Universe hierarchy. It is implemented over the primitive
  -- Agda universe hierarchy but it uses Type instead of Set, the
  -- usual name for the Universe in Agda.
  Type : (ℓ : Level) → Set (lsuc ℓ)
  Type ℓ = Set ℓ

  -- First levels of the universe hierarchy
  Type0 : Type (lsuc lzero)
  Type0 = Type lzero

  Type1 : Type (lsuc (lsuc lzero))
  Type1 = Type (lsuc lzero)

  Type2 : Type (lsuc (lsuc (lsuc lzero)))
  Type2 = Type (lsuc (lsuc lzero))

open Universes
\end{code}

Types
-------------------------------------------------------------------------------

### Empty Type

The empty type, representing falsehood.

\begin{code}
-- A datatype without constructors is the empty type.
data ⊥ {ℓᵢ} : Type ℓᵢ where
Empty = ⊥

-- Ex falso quodlibet
exfalso : ∀{ℓ ℓᵢ} {A : Type ℓ} → ⊥ {ℓᵢ} → A
exfalso ()

⊥-elim = exfalso
Empty-elim = ⊥-elim

-- Negation
¬ : ∀ {ℓ} → Type ℓ → Type ℓ
¬ A = (A → ⊥ {lzero})
\end{code}

### Unit

The unit type is defined as record so that we also get the η-rule definitionally.

\begin{code}
-- A record without fields is the unit type with a single
-- constructor.
record ⊤ : Type0 where
  constructor ★

unit = ★

{-# BUILTIN UNIT ⊤ #-}
\end{code}

Basic types of Martin-Löf type theory and some basic
functions.

### Σ-types

Sigma types are a particular case of records, but records can be
constructed using only sigma types. Note that l ⊔ q is the maximum
of two hierarchy levels l and q. This way, we define sigma types in
full generality, at each universe.

\begin{code}
infixr 60 _,_
record Σ {ℓᵢ ℓⱼ} (S : Type ℓᵢ)(T : S → Type ℓⱼ) : Type (ℓᵢ ⊔ ℓⱼ) where
  constructor _,_
  field
    fst : S
    snd : T fst
open Σ public
\end{code}

### Π-types
Shorter notation for Π-types.

\begin{code}
Π : ∀ {ℓᵢ ℓⱼ} (A : Type ℓᵢ) (P : A → Type ℓⱼ) → Type (ℓᵢ ⊔ ℓⱼ)
Π A P = (x : A) → P x
\end{code}

### Products (×)

Product type as a particular case of the sigma

\begin{code}
_×_ : ∀{ℓᵢ ℓⱼ} (S : Type ℓᵢ) (T : Type ℓⱼ) → Type (ℓᵢ ⊔ ℓⱼ)
A × B = Σ A (λ _ → B)
\end{code}

### Coproducts (+)

Sum types as inductive types
\begin{code}
infixr 80 _+_
data _+_ {ℓᵢ ℓⱼ} (S : Type ℓᵢ) (T : Type ℓⱼ) : Type (ℓᵢ ⊔ ℓⱼ) where
  inl : S → S + T
  inr : T → S + T
\end{code}

### Boolean

Boolean type, two constants true and false

\begin{code}
data Bool : Type0 where
  true  : Bool
  false : Bool
\end{code}

* Booleans can be defined by using a coproduct.

### Natural numbers

Natural numbers are the initial algebra for a constant and a
successor function. The BUILTIN declaration allows us to use
natural numbers in arabic notation.

\begin{code}
data ℕ : Type0 where
  zero : ℕ
  succ : ℕ → ℕ

Nat = ℕ

{-# BUILTIN NATURAL ℕ #-}
\end{code}


### Common functions

#### Identity function
The identity function with implicit type.
\begin{code}
id : ∀ {ℓ} {A : Type ℓ} → A → A
id a = a
\end{code}

The identity function on a type `A` is `idf A`.
\begin{code}
idf : ∀ {i} (A : Type i) → (A → A)
idf A = λ x → x
\end{code}

#### Constant function

Constant function at some point `b` is `cst b`

\begin{code}
cst : ∀ {i j} {A : Type i} {B : Type j} (b : B) → (A → B)
cst b = λ _ → b
\end{code}

#### Composition

A more sofisticated composition function that can handle dependent functions.

\begin{code}
infixr 80 _∘_
_∘_ : ∀{ℓᵢ ℓⱼ ℓₖ}
    {A : Type ℓᵢ}
    {B : A → Type ℓⱼ}
    {C : (a : A) → (B a → Type ℓₖ)}
    → (g : {a : A} → Π (B a) (C a)) → (f : Π A B) → Π A (λ a → C a (f a))
g ∘ f = λ x → g (f x)
\end{code}

#### Application

\begin{code}
infixr 0 _$_
_$_ : ∀ {i j} {A : Type i} {B : A → Type j}
    → (∀ x → B x) → (∀ x → B x)
f $ x = f x
\end{code}

The common symbol use to be dollar sign (\$) but it produces
some errors for my jekyll configuration.

#### Curryfication

\begin{code}
curry : ∀ {i j k} {A : Type i} {B : A → Type j} {C : Σ A B → Type k}
      → (∀ s → C s)
      → (∀ x y → C (x , y))
curry f x y = f (x , y)
\end{code}

#### Uncurryfication

\begin{code}
uncurry : ∀ {i j k} {A : Type i} {B : A → Type j} {C : ∀ x → B x → Type k}
        → (∀ x y → C x y)
        → (∀ s → C (fst s) (snd s))
uncurry f (x , y) = f x y
\end{code}

#### Instance Searh

\begin{code}
-- TODO : How to use this?
⟨⟩ : ∀ {i} {A : Type i} {{a : A}} → A
⟨⟩ {{a}} = a
\end{code}

### Identity Type

Equality is defined as an inductive type. Its induction principle
is the J-eliminator.

\begin{code}
infix 30 _==_
data _==_ {ℓ} {A : Type ℓ} : A → A → Type ℓ where
  refl :(a : A) → a == a

Path = _==_
{-# BUILTIN EQUALITY _==_ #-}
\end{code}

#### J eliminator

From [HoTT-Agda](https://github.com/HoTT/HoTT-Agda/blob/master/core/lib/Base.agda#L115) *Paulin-Mohring J rule*

\begin{code}
J : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {a : A} (B : (a' : A) (p : a == a') → Type ℓⱼ) (d : B a (refl a))
  {a' : A} (p : a == a') → B a' p
J {a = a} B d (refl a) = d

J' : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {a : A} (B : (a' : A) (p : a' == a) → Type ℓⱼ) (d : B a (refl a))
  {a' : A} (p : a' == a) → B a' p
J' {a = a} B d (refl a) = d
\end{code}

Composition of paths

\begin{code}
infixl 50 _·_
_·_ : ∀ {ℓ} {A : Type ℓ}  {a b c : A} → a == b → b == c → a == c
(refl a) · q = q
\end{code}

### PathOver

If you have a dependent type `B` over `A`, a path `p : x == y` in `A` and two
points `u : B x` and `v : B y`, there is a **type** `[u == v [ B ↓ p]]` of paths
from `u` to `v` lying over the path `p`.  By definition, if `p` is a constant
path, then `[u == v [ B ↓ p ]]` is just an ordinary path in the fiber.
[More info here](https://github.com/HoTT/HoTT-Agda/blob/master/core/lib/Base.agda#L115).

\begin{code}
PathOver : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} (B : A → Type ℓⱼ)
  {x y : A} (p : x == y) (u : B x) (v : B y) → Type ℓⱼ
PathOver {A = A} B {x} (refl x) u v = u == v
--
infix 30 PathOver
syntax PathOver B p u v = u == v [ B ↓ p ]
\end{code}

## Equational Reasoning

Equational reasoning is a way to write readable chains of equalities.
The idea is that you can write the following:

{% raw %}
```agda
  t : a == e
  t = a =⟨ p ⟩
      b =⟨ q ⟩
      c =⟨ r ⟩
      d =⟨ s ⟩
      e ∎
```
{% endraw %}

where `p` is a path from `a` to `b`, `q` is a path from `b` to `c`, and so on.
You often have to apply some equality in some context, for instance `p` could be
`ap ctx thm` where `thm` is the interesting theorem used to prove that `a` is
equal to `b`, and `ctx` is the context. [More info here](https://github.com/HoTT/HoTT-Agda/blob/master/core/lib/Base.agda#L270).

\begin{code}

module EquationalReasoning {ℓᵢ} {A : Type ℓᵢ} where

  -- Common combinators for equational reasoning. They allow us to
  -- write proof in an equational style. These versions have been
  -- adapted from the old version of the HoTT-agda library.

  infixr 2 _==⟨⟩_
  _==⟨⟩_ : ∀ (x {y} : A) → x == y → x == y
  _ ==⟨⟩ p = p

  infixr 2 _==⟨_⟩_
  _==⟨_⟩_ :  (x : A) {y z : A} → x == y → y == z → x == z
  _ ==⟨ p1 ⟩ p2 = p1 · p2

  infix  3 _∎
  _∎ : (x : A) → x == x
  _∎ = refl

  infix  1 begin_
  begin_ : {x y : A} → x == y → x == y
  begin_ p = p

open EquationalReasoning
\end{code}

## Actions on paths I

Properties and structure of the equality type.

### Equality

Types are higher groupoids.  If we see equalities as paths, this
is the inverse of a path. If we see equalities classically, this
is the symmetric property of equality.
\begin{code}
inv : ∀{ℓ} {A : Type ℓ}  {a b : A}
  → a == b
  → b == a
inv (refl a) = refl a
\end{code}
Functions are functors to equalities.  In other words, functions
preserve equalities.
\begin{code}
ap : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ}  {a b : A} → (f : A → B)
  →   a == b
  → f a == f b
ap f (refl a) = refl (f a)
\end{code}

#### Associativity of composition

Properties of function composition.

\begin{code}

-- Left associativity
∘-lassoc
  : ∀{ℓ} {A B C D : Type ℓ}
  → (h : C → D) → (g : B → C) → (f : A → B)
  → (h ∘ (g ∘ f)) == ((h ∘ g) ∘ f)
∘-lassoc h g f = refl (λ x → h (g (f x)))

-- Right associativity
∘-rassoc
  : ∀{ℓ} {A B C D : Type ℓ}
  → (h : C → D) → (g : B → C) → (f : A → B)
  → ((h ∘ g) ∘ f) == (h ∘ (g ∘ f))
∘-rassoc h g f = inv (∘-lassoc h g f)
\end{code}


## Properties on the groupoid
Some properties on the groupoid structure of equalities
\begin{code}
module ·-Properties {ℓ} {A : Type ℓ} where
  ·-runit : {a b : A} (p : a == b) → p == p · (refl b)
  ·-runit (refl a) = refl (refl a)

  ·-lunit : {a b : A} (p : a == b) → p == (refl _) · p
  ·-lunit (refl a) = refl (refl a)

  ·-assoc : {a b c d : A} (p : a == b) → (q : b == c) → (r : c == d)
          → (p · q) · r == p · (q · r)
  ·-assoc (refl a) q r = refl (q · r)

  ·-linv : {a b : A} (p : a == b) → (inv p) · p == refl b
  ·-linv (refl a) = refl (refl a)

  ·-rinv : {a b : A} (p : a == b) → p · (inv p) == refl a
  ·-rinv (refl a) = refl (refl a)

  ·-cancellation : {a : A} (p : a == a) → (q : a == a) → p · q == p → q == refl a
  ·-cancellation {a} p q α =
    begin
      q                   ==⟨ ap (_· q) (inv (·-linv p)) ⟩
      inv p · p · q       ==⟨ (·-assoc (inv p) _ _) ⟩
      inv p · (p · q)     ==⟨ (ap (inv p ·_) α) ⟩
      inv p · p           ==⟨ ·-linv p ⟩
      refl a
    ∎
open ·-Properties
\end{code}

## Transport

When we transport a proof of `(P a)` over an equality `(a == b)`, we
get a proof of `(P b)`.

\begin{code}
module Transport {ℓᵢ} {A : Type ℓᵢ} where
  -- Transport
  transport : ∀{ℓⱼ} (P : A → Type ℓⱼ) {a b : A}
    → a == b
    → P a
    → P b
  transport P (refl a) = id

  -- Some lemmas on the transport operation.
  transport-concat-r : {a : A} {x y : A} → (p : x == y) → (q : a == x) →
    transport (λ x → a == x) p q == q · p
  transport-concat-r (refl a) q = ·-runit q

  transport-concat-l : {a : A} {x y : A} → (p : x == y) → (q : x == a) →
    transport (λ x → x == a) p q == (inv p) · q
  transport-concat-l (refl a) q = refl q

  transport-concat : {x y : A} → (p : x == y) → (q : x == x) →
    transport (λ x → x == x) p q == (inv p) · q · p
  transport-concat (refl a) q = ·-runit q

  transport-eq-fun : ∀{ℓⱼ} {B : Type ℓⱼ} (f g : A → B) {x y : A} (p : x == y) (q : f x == g x)
                    → transport (λ z → f z == g z) p q == inv (ap f p) · q · (ap g p)
  transport-eq-fun f g (refl a) q = ·-runit q

  transport-comp : ∀{ℓⱼ} {a b c : A} {P : A → Type ℓⱼ} (p : a == b) (q : b == c)
                   → ((transport P q) ∘ (transport P p)) == transport P (p · q)
  transport-comp {P = P} (refl a) q = refl (transport P q)

  transport-comp-h : ∀{ℓⱼ} {a b c : A} {P : A → Type ℓⱼ} (p : a == b) (q : b == c) (x : P a)
                   → ((transport P q) ∘ (transport P p)) x == transport P (p · q) x
  transport-comp-h {P = P} (refl a) q x = refl (transport P q x)

  -- A shorter notation for transport.
  _✶ : ∀{ℓⱼ} {P : A → Type ℓⱼ} {a b : A} → a == b → P a → P b
  _✶ = transport _
open Transport public
\end{code}

## Actions on paths II

More properties and lemmas on equality, transporting and function application.

\begin{code}
ap-id : ∀{ℓᵢ} {A : Type ℓᵢ} {a b : A} (p : a == b) → ap id p == p
ap-id (refl a) = refl (refl a)

ap-comp : ∀{ℓᵢ ℓⱼ ℓₖ} {A : Type ℓᵢ} {B : Type ℓⱼ} {C : Type ℓₖ}  {a b : A}
        → (f : A → B) → (g : B → C) → (p : a == b)
        → ap g (ap f p) == ap (g ∘ f) p
ap-comp f g (refl a) = refl (refl (g (f a)))

ap-const : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {C : Type ℓⱼ} {a b : A} {c : C} (p : a == b)
         → ap (λ _ → c) p == refl c
ap-const {c = c} (refl a) = refl (refl c)

ap-· : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} {a b c : A}
     → (f : A → B) → (p : a == b) → (q : b == c)
     → ap f (p · q) == ap f p · ap f q
ap-· f (refl a) q = refl (ap f q)

ap-inv : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} {a b : A}
       → (f : A → B) → (p : a == b)
       → ap f (inv p) == inv (ap f p)
ap-inv f (refl a) = refl (refl (f a))

transport-eq-fun-l : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} {b : B} (f : A → B) {x y : A}
                     → (p : x == y) (q : f x == b)
                     → transport (λ z → f z == b) p q == inv (ap f p) · q
transport-eq-fun-l {b = b} f p q =
  begin
    transport (λ z → f z == b) p q      ==⟨ transport-eq-fun f (λ _ → b) p q ⟩
    inv (ap f p) · q · ap (λ _ → b) p   ==⟨ ap (inv (ap f p) · q ·_) (ap-const p) ⟩
    inv (ap f p) · q · refl b           ==⟨ inv (·-runit _) ⟩
    inv (ap f p) · q
  ∎

transport-eq-fun-r : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} {b : B} (g : A → B) {x y : A}
                     → (p : x == y) (q : b == g x)
                     → transport (λ z → b == g z) p q == q · (ap g p)
transport-eq-fun-r {b = b} g p q =
  begin
    transport (λ z → b == g z) p q      ==⟨ transport-eq-fun (λ _ → b) g p q ⟩
    inv (ap (λ _ → b) p) · q · ap g p   ==⟨ ·-assoc (inv (ap (λ _ → b) p)) q (ap g p) ⟩
    inv (ap (λ _ → b) p) · (q · ap g p) ==⟨ ap (λ u → inv u · (q · ap g p)) (ap-const p) ⟩
    (q · ap g p)
  ∎

transport-inv-l : ∀{ℓ} {A B : Type ℓ} → (p : A == B) → (b : B)
              → transport (λ v → v) p (transport (λ v → v) (inv p) b) == b
transport-inv-l (refl a) b = refl b

transport-inv-r : ∀{ℓ} {A B : Type ℓ} → (p : A == B) → (a : A)
              → transport (λ v → v) (inv p) (transport (λ v → v) p a) == a
transport-inv-r (refl a) b = refl b

transport-family : ∀{ℓᵢ ℓⱼ ℓₖ} {A : Type ℓᵢ} {B : Type ℓⱼ} {P : B → Type ℓₖ}
                 → {f : A → B} → {x y : A} → (p : x == y) → (u : P (f x))
                 → transport (P ∘ f) p u == transport P (ap f p) u
transport-family (refl a) u = refl u

transport-fun : ∀{ℓᵢ ℓⱼ ℓₖ} {X : Type ℓᵢ} {x y : X} {A : X → Type ℓⱼ} {B : X → Type ℓₖ}
                → (p : x == y) → (f : A x → B x)
                → transport (λ x → (A x → B x)) p f == (λ x → transport B p (f (transport A (inv p) x)))
transport-fun (refl a) f = refl f

apd : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ}  {P : A → Type ℓⱼ} {a b : A}
    → (f : (a : A) → P a) → (p : a == b)
    → transport P p (f a) == f b
apd f (refl a) = refl (f a)
\end{code}

## Homotopy

In a type-theoretical sense, a homotopy between two
functions is a family of equalities between their applications.

\begin{code}
module Homotopy {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {P : A → Type ℓⱼ} where
  -- A homotopy is a natural isomorphism between two functions, we will write
  -- f ∼ g when (f x == g x) for all x.
  homotopy : (f g : ((x : A) → P x)) → Type (ℓᵢ ⊔ ℓⱼ)
  homotopy f g = (x : A) → f x == g x

  _∼_ : (f g : ((x : A) → P x)) → Type (ℓᵢ ⊔ ℓⱼ)
  f ∼ g = homotopy f g

  -- Homotopy is an equivalence relation
  h-refl : (f : (x : A) → P x) → f ∼ f
  h-refl f x = refl (f x)

  h-simm : (f g : (x : A) → P x) → f ∼ g → g ∼ f
  h-simm f g u x = inv (u x)

  h-comp : (f g h : (x : A) → P x) → f ∼ g → g ∼ h → f ∼ h
  h-comp f g h u v x = (u x)·(v x)

  _●_ : {f g h : (x : A) → P x} → f ∼ g → g ∼ h → f ∼ h
  α ● β = h-comp _ _ _ α β

open Homotopy
\end{code}

## Homotopy Composition

\begin{code}
-- Composition with homotopies
module HomotopyComposition {ℓᵢ ℓⱼ ℓₖ} {A : Type ℓᵢ} {B : Type ℓⱼ} {C : Type ℓₖ} where
  hl-comp : (f g : A → B) → (j k : B → C) → f ∼ g → j ∼ k → (j ∘ f) ∼ (k ∘ g)
  hl-comp f g j k α β x = ap j (α x) · β (g x)

  rcomp-∼ : (f : A → B) → {j k : B → C} → j ∼ k → (j ∘ f) ∼ (k ∘ f)
  rcomp-∼ f β = hl-comp _ _ _ _ (h-refl f) β

  lcomp-∼ : {f g : A → B} → (j : B → C) → f ∼ g → (j ∘ f) ∼ (j ∘ g)
  lcomp-∼ j α = hl-comp _ _ _ _ α (h-refl j)

open HomotopyComposition
\end{code}

## Naturality

Homotopy is natural, meaning that it satisfies the following
square commutative diagram.

\begin{code}

module Naturality {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where
  h-naturality : {f g : A → B} (H : f ∼ g) → {x y : A} → (p : x == y)
               → H x · ap g p == ap f p · H y
  h-naturality H (refl a) = inv (·-runit (H a))
open Naturality
\end{code}

A particular case of naturality on the identity function.
\begin{code}
h-naturality-id : ∀{ℓ} {A : Type ℓ} {f : A → A} (H : f ∼ id) → {x : A}
                → H (f x) == ap f (H x)
h-naturality-id {f = f} H {x = x} =
  begin
    H (f x)                            ==⟨ ·-runit (H (f x)) ⟩
    H (f x) · (refl (f x))             ==⟨ ap (H (f x) ·_) (inv (·-rinv (H x))) ⟩
    H (f x) · (H x · inv (H x))        ==⟨ inv (·-assoc (H (f x)) _ (inv (H x))) ⟩
    H (f x) · H x · inv (H x)          ==⟨ ap (λ u → H (f x) · u · inv (H x)) (inv (ap-id _)) ⟩
    H (f x) · ap id (H x) · inv (H x)  ==⟨ ap (_· inv (H x)) (h-naturality H (H x)) ⟩
    ap f (H x) · H x · inv (H x)       ==⟨ ·-assoc (ap f (H x)) _ (inv (H x)) ⟩
    ap f (H x) · (H x · inv (H x))     ==⟨ ap (ap f (H x) ·_) (·-rinv (H x)) ⟩
    ap f (H x) · refl (f x)            ==⟨ inv (·-runit (ap f (H x))) ⟩
    ap f (H x)
  ∎
\end{code}

## Fibers

Contractible types with a center of contraction.

\begin{code}
module Fibers {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ}  where

  -- The fiber of a map over a point is given by
  fib : (f : A → B) → B → Type (ℓᵢ ⊔ ℓⱼ)
  fib f b = Σ A (λ a → f a == b)

  -- A function applied over the fiber returns the original point
  fib-eq : {f : A → B} → {b : B} → (h : fib f b) → f (fst h) == b
  fib-eq (a , α) = α

  -- Each point is on the fiber of its image
  fib-image : {f : A → B} → {a : A} → fib f (f a)
  fib-image {f} {a} = a , refl (f a)

open Fibers
\end{code}

## Contractible types

\begin{code}
-- Contractible.  Contractible types with a center of contraction.
module Contractible where

  -- Contractible types. A contractible type is a type such that every
  -- element is equal to a center of contraction.
  isContr : ∀{ℓ}  (A : Type ℓ) → Type ℓ
  isContr A = Σ A (λ a → ((x : A) → a == x))
open Contractible public

\end{code}

## Equivalence

\begin{code}


module Equivalence where

  module DefinitionOfEquivalence {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where
    -- Contractible maps. A map is contractible if the fiber in any
    -- point is contractible, that is, each element has a unique
    -- preimage.
    isContrMap : (f : A → B) → Type (ℓᵢ ⊔ ℓⱼ)
    isContrMap f = (b : B) → isContr (fib f b)

    -- There exists an equivalence between two types if there exists a
    -- contractible function between them.
    isEquiv : (f : A → B) → Type (ℓᵢ ⊔ ℓⱼ)
    isEquiv = isContrMap
  open DefinitionOfEquivalence public

  -- Equivalence of types.
  _≃_ : ∀{ℓᵢ ℓⱼ}  (A : Type ℓᵢ) (B : Type ℓⱼ) → Type (ℓᵢ ⊔ ℓⱼ)
  A ≃ B = Σ (A → B) isEquiv

  module EquivalenceMaps {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where

    -- Maps of an equivalence
    lemap : A ≃ B → (A → B)
    lemap = fst

    remap : A ≃ B → (B → A)
    remap (f , contrf) b = fst (fst (contrf b))

    -- The maps of an equivalence are inverses in particular
    lrmap-inverse : (eq : A ≃ B) → {b : B} → (lemap eq) ((remap eq) b) == b
    lrmap-inverse (f , eqf) {b} = fib-eq (fst (eqf b))

    rlmap-inverse : (eq : A ≃ B) → {a : A} → (remap eq) ((lemap eq) a) == a
    rlmap-inverse (f , eqf) {a} = ap fst ((snd (eqf (f a))) fib-image)

    lrmap-inverse-h : (eq : A ≃ B) → ((lemap eq) ∘ (remap eq)) ∼ id
    lrmap-inverse-h eq = λ x → lrmap-inverse eq {x}

    rlmap-inverse-h : (eq : A ≃ B) → ((remap eq) ∘ (lemap eq)) ∼ id
    rlmap-inverse-h eq = λ x → rlmap-inverse eq {x}
  open EquivalenceMaps public

open Equivalence
\end{code}

## Function extesionality

\begin{code}

module FunctionExtensionality {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : A → Type ℓⱼ} {f g : (a : A) → B a} where
  -- Application of an homotopy
  happly : f == g → ((x : A) → f x == g x)
  happly (refl f) x = refl (f x)

  -- The axiom of function extensionality postulates that the
  -- application of homotopies is an equivalence.
  postulate axiomFunExt : isEquiv happly

  eqFunExt : (f == g) ≃ ((x : A) → f x == g x)
  eqFunExt = happly , axiomFunExt

  -- From this, the usual notion of function extensionality follows.
  funext : ((x : A) → f x == g x) → f == g
  funext = remap eqFunExt

  -- Beta and eta rules for function extensionality
  funext-β : (h : ((x : A) → f x == g x)) → happly (funext h) == h
  funext-β h = lrmap-inverse eqFunExt

  funext-η : (p : f == g) → funext (happly p) == p
  funext-η p = rlmap-inverse eqFunExt

open FunctionExtensionality

-- Function extensionality in the transport case
module FunctionExtensionalityTransport
  {ℓᵢ ℓⱼ} {X : Type ℓᵢ} {A B : X → Type ℓⱼ} {x y : X} where

  funext-transport
    : (p : x == y) → (f : A x → B x) → (g : A y → B y)
    → ((p ✶) f == g) ≃ ((a : A(x)) → (p ✶) (f a) == g ((p ✶) a))
  funext-transport (refl a) f g = eqFunExt

  funext-transport-l
    : (p : x == y) → (f : A x → B x) → (g : A y → B y)
    → ((p ✶) f == g) → ((a : A(x)) → (p ✶) (f a) == g ((p ✶) a))
  funext-transport-l p f g = lemap (funext-transport p _ _)

  funext-transport-r
    : (p : x == y) → (f : A x → B x) → (g : A y → B y)
    → ((a : A(x)) → (p ✶) (f a) == g ((p ✶) a)) → ((p ✶) f == g)
  funext-transport-r p f g = remap (funext-transport p _ _)

open FunctionExtensionalityTransport
\end{code}

## Sigma

\begin{code}
module Sigma {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {P : A → Type ℓⱼ} where

  -- Two dependent pairs are equal if they are componentwise equal.
  Σ-componentwise : {v w : Σ A P} → v == w → Σ (fst v == fst w) (λ p → (p ✶) (snd v) == snd w)
  Σ-componentwise {v} {.v} (refl .v) = refl (fst v) , refl (snd v)

  Σ-bycomponents : {v w : Σ A P} → Σ (fst v == fst w) (λ p → (p ✶) (snd v) == snd w) → v == w
  Σ-bycomponents {(a , f)} {(.a , .f)} (refl .a , refl .f) = refl (a , f)
open Sigma
\end{code}

## Cartesian Product

\begin{code}
module CartesianProduct {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where

  -- In a pair, the equality of the two components of the pairs is
  -- equivalent to equality of the two pairs.
  prodComponentwise : {x y : A × B} → (x == y) → ((fst x == fst y) × (snd x == snd y))
  prodComponentwise (refl a) = refl (fst a) , refl (snd a)

  prodByComponents : {x y : A × B} → ((fst x == fst y) × (snd x == snd y)) → (x == y)
  prodByComponents {x = a , b} (refl .a , refl .b) = refl (a , b)

  -- This is in fact an equivalence.
  prodCompInverse : {x y : A × B} (b : ((fst x == fst y) × (snd x == snd y))) →
                    prodComponentwise (prodByComponents b) == b
  prodCompInverse {x} (refl .(fst x) , refl .(snd x)) = refl (refl (fst x) , refl (snd x))

  prodByCompInverse : {x y : A × B} (b : x == y) →
                    prodByComponents (prodComponentwise b) == b
  prodByCompInverse (refl a) = refl (refl a)

open CartesianProduct
\end{code}


## DecidableEquality

A type has decidable equality if any two of its
elements are equal or different. This would be a particular
instance of the Law of Excluded Middle that holds even if we do not
assume Excluded Middle.

\begin{code}
module DecidableEquality {ℓ} where

  -- A type has decidable equality if we can prove that any two of its
  -- elements are equal or different.
  decEq : (A : Type ℓ) → Type ℓ
  decEq A = (a b : A) → (a == b) + ¬ (a == b)

  -- The product of types with decidable equality is a type with
  -- decidable equality.
  decEqProd : {A B : Type ℓ} → decEq A → decEq B → decEq (A × B)
  decEqProd da db (a1 , b1) (a2 , b2) with (da a1 a2) | (db b1 b2)
  decEqProd da db (a1 , b1) (a2 , b2) | inl aeq | inl beq = inl (prodByComponents (aeq , beq))
  decEqProd da db (a1 , b1) (a2 , b2) | inl aeq | inr bnq = inr λ b → bnq (ap snd b)
  decEqProd da db (a1 , b1) (a2 , b2) | inr anq | u       = inr λ b → anq (ap fst b)

open DecidableEquality
\end{code}

## Propositions

Propositions as described on the main text. A type
is a proposition if we can create a function making any two of its
elements equal. We create a type of propositions.

\begin{code}

module Propositions where

  -- A type is a mere proposition if any two inhabitants of the type
  -- are equal
  isProp : ∀{ℓ}  (A : Type ℓ) → Type ℓ
  isProp A = ((x y : A) → x == y)

  -- The type of mere propositions
  hProp : ∀{ℓ} → Type (lsuc ℓ)
  hProp {ℓ} = Σ (Type ℓ) isProp


  -- The dependent function type to proposition types is itself a
  -- proposition.
  piProp : ∀{ℓᵢ ℓⱼ} → {A : Type ℓᵢ} → {B : A → Type ℓⱼ}
         → ((a : A) → isProp (B a)) → isProp ((a : A) → B a)
  piProp props f g = funext λ a → props a (f a) (g a)

  -- The product of propositions is itself a proposition.
  isProp-prod : ∀{ℓᵢ ℓⱼ} → {A : Type ℓᵢ} → {B : Type ℓⱼ}
              → isProp A → isProp B → isProp (A × B)
  isProp-prod p q x y = prodByComponents ((p _ _) , (q _ _))

open Propositions
\end{code}


## Sets

Sets are types without any higher dimensional structure, all
parallel paths are homotopic and the homotopy is given by a
continuous function on the two paths.

\begin{code}
module Sets where

  -- A type is a "set" by definition if any two equalities on the type
  -- are equal.
  isSet : ∀{ℓ}  (A : Type ℓ) → Type ℓ
  isSet A = (x y : A) → isProp (x == y)

  -- The type of sets.
  hSet : ∀{ℓ} → Type (lsuc ℓ)
  hSet {ℓ} = Σ (Type ℓ) isSet

  -- Product of sets is a set.
  isSet-prod : ∀{ℓᵢ ℓⱼ}  {A : Type ℓᵢ} → {B : Type ℓⱼ}
             → isSet A → isSet B → isSet (A × B)
  isSet-prod sa sb (a , b) (c , d) p q = begin
     p
      ==⟨ inv (prodByCompInverse p) ⟩
     prodByComponents (prodComponentwise p)
      ==⟨ ap prodByComponents (prodByComponents (sa a c _ _ , sb b d _ _)) ⟩
     prodByComponents (prodComponentwise q)
      ==⟨ prodByCompInverse q ⟩
     q
    ∎

open Sets
\end{code}

## HLevels

Higher levels of the homotopical structure, where the
first levels are:

- Contractible types (0)
- Propositions (1)
- Sets (2)

They would correspond to homotopy levels. We only work with
these first levels.

\begin{code}

module HLevels where

  -- Propositions are Sets.
  propIsSet : ∀{ℓ} {A : Type ℓ} → isProp A → isSet A
  propIsSet {A = A} f a _ p q = lemma p · inv (lemma q)
    where
      triang : {y z : A} {p : y == z} → (f a y) · p == f a z
      triang {p = refl b} = inv (·-runit (f a b))

      lemma : {y z : A} (p : y == z) → p == inv (f a y) · (f a z)
      lemma {y} {z} p =
        begin
          p                         ==⟨ ap (_· p) (inv (·-linv (f a y))) ⟩
          inv (f a y) · f a y · p   ==⟨ ·-assoc (inv (f a y)) (f a y) p ⟩
          inv (f a y) · (f a y · p) ==⟨ ap (inv (f a y) ·_) triang ⟩
          inv (f a y) · (f a z)
        ∎

  -- Contractible types are Propositions.
  contrIsProp : ∀{ℓ}  {A : Type ℓ} → isContr A → isProp A
  contrIsProp (a , p) x y = inv (p x) · p y

  -- To be contractible is itself a proposition.
  isContrIsProp : ∀{ℓ}  {A : Type ℓ} → isProp (isContr A)
  isContrIsProp {_} {A} (a , p) (b , q) = Σ-bycomponents (inv (q a) , piProp (AisSet b) _ q)
    where
      AisSet : isSet A
      AisSet = propIsSet (contrIsProp (a , p))

open HLevels
\end{code}


## EquivalenceProp

Equivalence of two types is a proposition
Moreover, equivalences preserve propositions.

\begin{code}

module EquivalenceProp {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where

  -- Contractible maps are propositions
  isContrMapIsProp : (f : A → B) → isProp (isContrMap f)
  isContrMapIsProp f = piProp λ a → isContrIsProp

  isEquivIsProp : (f : A → B) → isProp (isEquiv f)
  isEquivIsProp = isContrMapIsProp

  -- Equality of same-morphism equivalences
  sameEqv : {α β : A ≃ B} → fst α == fst β → α == β
  sameEqv {(f , σ)} {(g , τ)} p = Σ-bycomponents (p , (isEquivIsProp g _ τ))

  -- Equivalences preserve propositions
  isProp-≃ : (A ≃ B) → isProp A → isProp B
  isProp-≃ eq prop x y =
    begin
      x                       ==⟨ inv (lrmap-inverse eq) ⟩
      lemap eq ((remap eq) x) ==⟨ ap (λ u → lemap eq u) (prop _ _) ⟩
      lemap eq ((remap eq) y) ==⟨ lrmap-inverse eq ⟩
      y
    ∎

open EquivalenceProp
\end{code}


## Half-Adjoints

Half-adjoints are an auxiliary notion that helps us
to define a suitable notion of equivalence, meaning that it is a
proposition and that it captures the usual notion of equivalence.

\begin{code}
module Halfadjoints {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where

  -- Half adjoint equivalence.
  record ishae (f : A → B) : Type (ℓᵢ ⊔ ℓⱼ) where
    constructor hae
    field
      g : B → A
      η : (g ∘ f) ∼ id
      ε : (f ∘ g) ∼ id
      τ : (x : A) → ap f (η x) == ε (f x)

  -- Half adjoint equivalences give contractible fibers.
  ishae-contr : (f : A → B) → ishae f → isContrMap f
  ishae-contr f (hae g η ε τ) y = ((g y) , (ε y)) , contra
    where
      lemma : (c c' : fib f y) → Σ (fst c == fst c') (λ γ → (ap f γ) · snd c' == snd c) → c == c'
      lemma c c' (p , q) = Σ-bycomponents (p , lemma2)
        where
          lemma2 : transport (λ z → f z == y) p (snd c) == snd c'
          lemma2 =
            begin
              transport (λ z → f z == y) p (snd c)
                ==⟨ transport-eq-fun-l f p (snd c) ⟩
              inv (ap f p) · (snd c)
                ==⟨ ap (inv (ap f p) ·_) (inv q) ⟩
              inv (ap f p) · ((ap f p) · (snd c'))
                ==⟨ inv (·-assoc (inv (ap f p)) (ap f p) (snd c')) ⟩
              inv (ap f p) · (ap f p) · (snd c')
                ==⟨ ap (_· (snd c')) (·-linv (ap f p)) ⟩
              snd c'
            ∎

      contra : (x : fib f y) → (g y , ε y) == x
      contra (x , p) = lemma (g y , ε y) (x , p) (γ , lemma3)
        where
          γ : g y == x
          γ = inv (ap g p) · η x

          lemma3 : (ap f γ · p) == ε y
          lemma3 =
            begin
              ap f γ · p
                ==⟨ ap (_· p) (ap-· f (inv (ap g p)) (η x)) ⟩
              ap f (inv (ap g p)) · ap f (η x) · p
                ==⟨ ·-assoc (ap f (inv (ap g p))) _ p ⟩
              ap f (inv (ap g p)) · (ap f (η x) · p)
                ==⟨ ap (_· (ap f (η x) · p)) (ap-inv f (ap g p)) ⟩
              inv (ap f (ap g p)) · (ap f (η x) · p)
                ==⟨ ap (λ u → inv (ap f (ap g p)) · (u · p)) (τ x) ⟩
              inv (ap f (ap g p)) · (ε (f x) · p)
                ==⟨ ap (λ u → inv (ap f (ap g p)) · (ε (f x) · u)) (inv (ap-id p)) ⟩
              inv (ap f (ap g p)) · (ε (f x) · ap id p)
                ==⟨ ap (inv (ap f (ap g p)) ·_) (h-naturality ε p) ⟩
              inv (ap f (ap g p)) · (ap (f ∘ g) p · ε y)
                ==⟨ ap (λ u → inv u · (ap (f ∘ g) p · ε y)) (ap-comp g f p) ⟩
              inv (ap (f ∘ g) p) · (ap (f ∘ g) p · ε y)
                ==⟨ inv (·-assoc (inv (ap (f ∘ g) p)) _ (ε y)) ⟩
              (inv (ap (f ∘ g) p) · ap (f ∘ g) p) · ε y
                ==⟨ ap (_· ε y) (·-linv (ap (λ z → f (g z)) p)) ⟩
              ε y
            ∎

  -- Half-adjointness implies equivalence.
  ishae-≃ : {f : A → B} → ishae f → A ≃ B
  ishae-≃ ishaef = _ , (ishae-contr _ ishaef)

open Halfadjoints
\end{code}


## Quasiinverses

Two functions are quasiinverses if we can construct
a function providing gfx = x and fgy = y for any given x and y.

\begin{code}
module Quasiinverses {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where

  -- Definitions for quasiinverses, left-inverses, right-inverses and
  -- biinverses.
  qinv : (A → B) → Type (ℓᵢ ⊔ ℓⱼ)
  qinv f = Σ (B → A) (λ g → ((f ∘ g) ∼ id) × ((g ∘ f) ∼ id))

  linv : (A → B) → Type (ℓᵢ ⊔ ℓⱼ)
  linv f = Σ (B → A) (λ g → (g ∘ f) ∼ id)

  rinv : (A → B) → Type (ℓᵢ ⊔ ℓⱼ)
  rinv f = Σ (B → A) λ g → (f ∘ g) ∼ id

  biinv : (A → B) → Type (ℓᵢ ⊔ ℓⱼ)
  biinv f = linv f × rinv f

  qinv-biinv : (f : A → B) → qinv f → biinv f
  qinv-biinv f (g , (u1 , u2)) = (g , u2) , (g , u1)

  biinv-qinv : (f : A → B) → biinv f → qinv f
  biinv-qinv f ((h , α) , (g , β)) = g , (β , δ)
    where
      γ1 : g ∼ ((h ∘ f) ∘ g)
      γ1 = rcomp-∼ g (h-simm (h ∘ f) id α)

      γ2 : ((h ∘ f) ∘ g) ∼ (h ∘ (f ∘ g))
      γ2 x = refl (h (f (g x)))

      γ : g ∼ h
      γ = γ1 ● (γ2 ● (lcomp-∼ h β))

      δ : (g ∘ f) ∼ id
      δ = (rcomp-∼ f γ) ● α

  equiv-biinv : (f : A → B) → isContrMap f → biinv f
  equiv-biinv f contrf =
    (remap eq , rlmap-inverse-h eq) , (remap eq , lrmap-inverse-h eq)
    where
      eq : A ≃ B
      eq = f , contrf

  -- Quasiinverses are halfadjoint equivalences.
  qinv-ishae : {f : A → B} → qinv f → ishae f
  qinv-ishae {f} (g , (ε , η)) = record {
      g = g ;
      η = η ;
      ε = λ b → inv (ε (f (g b))) · ap f (η (g b)) · ε b ;
      τ = τ
    }
    where
      lemma1 : (a : A) → ap f (η (g (f a))) · ε (f a) == ε (f (g (f a))) · ap f (η a)
      lemma1 a =
        begin
          ap f (η ((g ∘ f) a)) · ε (f a)
            ==⟨ ap (λ u → ap f u · ε (f a)) (h-naturality-id η) ⟩
          ap f (ap (g ∘ f) (η a)) · ε (f a)
            ==⟨ ap (_· ε (f a)) (ap-comp (g ∘ f) f (η a)) ⟩
          ap (f ∘ (g ∘ f)) (η a) · ε (f a)
            ==⟨ inv (h-naturality (λ x → ε (f x)) (η a)) ⟩
          ε (f (g (f a))) · ap f (η a)
        ∎

      τ : (a : A) → ap f (η a) == (inv (ε (f (g (f a)))) · ap f (η (g (f a))) · ε (f a))
      τ a =
        begin
          ap f (η a)
            ==⟨ ap (_· ap f (η a)) (inv (·-linv (ε (f (g (f a)))))) ⟩
          inv (ε (f (g (f a)))) · ε (f (g (f a))) · ap f (η a)
            ==⟨ ·-assoc (inv (ε (f (g (f a))))) _ (ap f (η a)) ⟩
          inv (ε (f (g (f a)))) · (ε (f (g (f a))) · ap f (η a))
            ==⟨ ap (inv (ε (f (g (f a)))) ·_) (inv (lemma1 a)) ⟩
          inv (ε (f (g (f a)))) · (ap f (η (g (f a))) · ε (f a))
            ==⟨ inv (·-assoc (inv (ε (f (g (f a))))) _ (ε (f a))) ⟩
          inv (ε (f (g (f a)))) · ap f (η (g (f a))) · ε (f a)
        ∎

  -- Quasiinverses create equivalences.
  qinv-≃ : (f : A → B) → qinv f → A ≃ B
  qinv-≃ f = ishae-≃ ∘ qinv-ishae

  ≃-qinv : A ≃ B → Σ (A → B) qinv
  ≃-qinv eq = lemap eq , (remap eq , (lrmap-inverse-h eq , rlmap-inverse-h eq))

  -- Half-adjoint equivalences are quasiinverses.
  ishae-qinv : {f : A → B} → ishae f → qinv f
  ishae-qinv {f} (hae g η ε τ) = g , (ε , η)

open Quasiinverses
\end{code}


## Equivalence composition

Composition of equivalences and properties of that composition.

\begin{code}
module EquivalenceComposition where

  -- Composition of quasiinverses
  qinv-comp : ∀{ℓ} {A B C : Type ℓ} → Σ (A → B) qinv → Σ (B → C) qinv → Σ (A → C) qinv
  qinv-comp (f , (if , (εf , ηf))) (g , (ig , (εg , ηg))) = (g ∘ f) , ((if ∘ ig) ,
     ( (λ x → ap g (εf (ig x)) · εg x)
     ,  λ x → ap if (ηg (f x)) · ηf x))

  qinv-inv : ∀{ℓ} {A B : Type ℓ} → Σ (A → B) qinv → Σ (B → A) qinv
  qinv-inv (f , (g , (ε , η))) = g , (f , (η , ε))

  -- Composition of equivalences
  idEqv : ∀{ℓ} {A : Type ℓ} → A ≃ A
  idEqv = id , λ a → (a , refl a) , λ { (_ , refl _) → refl (a , refl a) }

  compEqv : ∀{ℓ} {A B C : Type ℓ} → A ≃ B → B ≃ C → A ≃ C
  compEqv {ℓ} {A} {B} {C} eqf eqg = qinv-≃ (fst qcomp) (snd qcomp)
   where
     qcomp : Σ (A → C) qinv
     qcomp = qinv-comp (≃-qinv eqf) (≃-qinv eqg)

  invEqv : ∀{ℓ} {A B : Type ℓ} → A ≃ B → B ≃ A
  invEqv {ℓ} {A} {B} eqf = qinv-≃ (fst qcinv) (snd qcinv)
   where
     qcinv : Σ (B → A) qinv
     qcinv = qinv-inv (≃-qinv eqf)

  -- Lemmas about composition
  compEqv-inv : ∀{ℓ} {A B : Type ℓ} → (α : A ≃ B) → compEqv α (invEqv α) == idEqv
  compEqv-inv {_} {A} {B} α = sameEqv (
   begin
     fst (compEqv α (invEqv α)) ==⟨ refl _ ⟩
     fst (invEqv α) ∘ fst α     ==⟨ funext (rlmap-inverse-h α) ⟩
     id
   ∎)

open EquivalenceComposition
\end{code}


## Univalence

Voevodsky's univalence axiom is postulated. It induces
an equality between any two equivalent types. Some β and η rules
are provided.

\begin{code}
module Univalence where

  -- Voevodsky's Univalence Axiom.
  module UnivalenceAxiom {ℓ} {A B : Type ℓ} where
    idtoeqv : A == B → A ≃ B
    idtoeqv p = qinv-≃
      (transport (λ x → x) p)
      (transport (λ x → x) (inv p) , (transport-inv-l p , transport-inv-r p))

    -- The Univalence axiom induces an equivalence between equalities
    -- and equivalences.
    postulate axiomUnivalence : isEquiv idtoeqv
    eqvUnivalence : (A == B) ≃ (A ≃ B)
    eqvUnivalence = idtoeqv , axiomUnivalence

    -- Introduction rule for equalities.
    ua : A ≃ B → A == B
    ua = remap eqvUnivalence

    -- Computation rules
    ua-β : (eqv : A ≃ B) → idtoeqv (ua eqv) == eqv
    ua-β eqv = lrmap-inverse eqvUnivalence

    ua-η : (p : A == B) → ua (idtoeqv p) == p
    ua-η p = rlmap-inverse eqvUnivalence
  open UnivalenceAxiom public

\end{code}

Somme lemmas about Univelance

{: .foldable}
\begin{code}
--
--   module UnivalenceLemmas {ℓ} where
--     -- The identity equivalence creates the trivial path.
--     ua-id : {A : Type ℓ} → ua idEqv == refl A
--     ua-id {A} =
--       begin
--         ua idEqv              ==⟨ ap ua (sameEqv (refl id)) ⟩
--         ua (idtoeqv (refl A)) ==⟨ ua-η (refl A) ⟩
--         refl A
--       ∎
--
--     -- The composition of equivalences is preserved into composition
--     -- of equalities.
--     ua-comp : {A B C : Type ℓ} → (α : A ≃ B) → (β : B ≃ C) → ua (compEqv α β) == ua α · ua β
--     ua-comp α β =
--       begin
--         ua (compEqv α β)                               ==⟨ ap (λ x → ua (compEqv x β)) (inv (ua-β α)) ⟩
--         ua (compEqv (idtoeqv (ua α)) β)                ==⟨ ap (λ x → ua (compEqv (idtoeqv (ua α)) x))
--                                                            (inv (ua-β β)) ⟩
--         ua (compEqv (idtoeqv (ua α)) (idtoeqv (ua β))) ==⟨ ap ua lemma ⟩
--         ua (idtoeqv (ua α · ua β))                     ==⟨ ua-η (ua α · ua β) ⟩
--         ua α · ua β
--       ∎
--       where
--         lemma : compEqv (idtoeqv (ua α)) (idtoeqv (ua β)) == idtoeqv (ua α · ua β)
--         lemma = sameEqv (
--           begin
--             fst (idtoeqv (ua β)) ∘ fst (idtoeqv (ua α))                 ==⟨ refl _ ⟩
--             (transport (λ x → x) (ua β)) ∘ (transport (λ x → x) (ua α)) ==⟨ transport-comp (ua α) (ua β) ⟩
--             transport (λ x → x) (ua α · ua β)                           ==⟨ refl _ ⟩
--             fst (idtoeqv (ua α · ua β))
--           ∎)
--
--     -- Inverses are preserved.
--     ua-inv-r : {A B : Type ℓ} → (α : A ≃ B) → ua α · ua (invEqv α) == refl A
--     ua-inv-r α =
--       begin
--         ua α · ua (invEqv α)      ==⟨ inv (ua-comp α (invEqv α)) ⟩
--         ua (compEqv α (invEqv α)) ==⟨ ap ua (compEqv-inv α) ⟩
--         ua idEqv                  ==⟨ ua-id ⟩
--         refl _
--       ∎
--
--     ua-inv : {A B : Type ℓ} → (α : A ≃ B) → ua (invEqv α) == inv (ua α)
--     ua-inv α =
--       begin
--         ua (invEqv α)                       ==⟨ ap (_· ua (invEqv α)) (inv (·-linv (ua α))) ⟩
--         inv (ua α) · ua α · ua (invEqv α)   ==⟨ ·-assoc (inv (ua α)) _ _ ⟩
--         inv (ua α) · (ua α · ua (invEqv α)) ==⟨ ap (inv (ua α) ·_) (ua-inv-r α) ⟩
--         inv (ua α) · refl _                 ==⟨ inv (·-runit (inv ((ua α)))) ⟩
--         inv (ua α)
--       ∎
--   open UnivalenceLemmas public
--
-- open Univalence
\end{code}
