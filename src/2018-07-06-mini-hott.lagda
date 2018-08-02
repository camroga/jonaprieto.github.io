---
layout: "post"
title: "Mini HoTT library in Agda"
date: "2018-07-06"
categories: type-theory
toc: true
agda: true
---

The following is an basic overview of homotopy type theory (HoTT) formalized in
Agda in just one-file. The present development was type-checked by Agda 2.5.4.
No other libraries are required to type-check this one.

To be consistent with homotopy type theory, we tell Agda to not use Axiom K for
type-checking by using the option `without-K`. Without Axiom K, Agda's `Set` is
not a good name for universes in HoTT and we rename `Set` to `Type`.

This code mutates constantly and stands for only learning purposes. At the
end of this article, the reader can find the references to the agda libraries in
which we are based on.

{% comment %}
Some marks to accompany the code:

- 👏 looks great!
- 🔍 review please!
- 🆘 needs refactor
{% endcomment %}

\begin{code}
{-# OPTIONS --without-K #-}
\end{code}

\begin{code}
open import Agda.Primitive using ( Level ; lsuc; lzero; _⊔_ ) public

Type : (ℓ : Level) → Set (lsuc ℓ)
Type ℓ = Set ℓ

Type₀ : Type (lsuc lzero)
Type₀ = Type lzero
\end{code}

## Basic types

### Empty type

The Empty type, representing falsehood.

\begin{code}
-- A datatype without constructors is the empty type.
data ⊥ {ℓᵢ} : Type ℓᵢ where

-- synonyms of ⊥
Empty = ⊥
𝟘     = ⊥
\end{code}

Its eliminator:

\begin{code}
-- Ex falso quodlibet
exfalso : ∀ {ℓ ℓᵢ} {A : Type ℓ} → ⊥ {ℓᵢ} → A
exfalso ()

-- synonyms of exfalso
Empty-elim = exfalso
⊥-elim     = exfalso
\end{code}

A useful convention
\begin{code}
-- Negation
¬ : ∀ {ℓ} → Type ℓ → Type ℓ
¬ A = (A → ⊥ {lzero})
\end{code}

### Unit type

The unit type is defined as record so that we also get the η-rule definitionally.

\begin{code}
record ⊤ : Type₀ where
  constructor ★

{-# BUILTIN UNIT ⊤ #-}

-- synonyms for the data constructor
unit = ★

-- synonyms for the Unit type
Unit = ⊤
𝟙    = ⊤
\end{code}

### Σ-type

Sigma types are a particular case of records, but records can be
constructed using only sigma types. Note that l ⊔ q is the maximum
of two hierarchy levels l and q. This way, we define sigma types in
full generality, at each universe.

\begin{code}
infixr 60 _,_
record Σ {ℓᵢ ℓⱼ} (A : Type ℓᵢ)(C : A → Type ℓⱼ) : Type (ℓᵢ ⊔ ℓⱼ) where
  constructor _,_
  field
    π₁ : A
    π₂ : C π₁

  -- synonyms for data constructors
  proj₁ = π₁
  proj₂ = π₂
  fst   = π₁
  snd   = π₂
open Σ public
\end{code}

### Π-types
Shorter notation for Π-types.

\begin{code}
Π : ∀ {ℓᵢ ℓⱼ} (A : Type ℓᵢ) (P : A → Type ℓⱼ) → Type (ℓᵢ ⊔ ℓⱼ)
Π A P = (x : A) → P x
\end{code}

### Product type

Product type as a particular case of the sigma

\begin{code}
_×_ : ∀ {ℓᵢ ℓⱼ} (A : Type ℓᵢ) (B : Type ℓⱼ) → Type (ℓᵢ ⊔ ℓⱼ)
A × B = Σ A (λ _ → B)
\end{code}

### Coproduct

Sum types as inductive types

\begin{code}
infixr 80 _+_
data _+_ {ℓᵢ ℓⱼ} (A : Type ℓᵢ) (B : Type ℓⱼ) : Type (ℓᵢ ⊔ ℓⱼ) where
  inl : A → A + B
  inr : B → A + B
\end{code}

### Boolean

Boolean type, two constants true and false

\begin{code}
data Bool : Type₀ where
  true  : Bool
  false : Bool
\end{code}

*Booleans can be also defined using the coproduct.*

### Natural numbers

Natural numbers are the initial algebra for a constant and a
successor function. The `BUILTIN` declaration allows us to use
natural numbers in Arabic notation.

\begin{code}
data ℕ : Type₀ where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- synonyms for natural numbers
Nat = ℕ

\end{code}


## Functions

### Identity function

The identity function with implicit type.
\begin{code}
id : ∀ {ℓ} {A : Type ℓ} → A → A
id a = a
\end{code}

The identity function on a type `A` is `idf A`.
\begin{code}
idf : ∀ {ℓᵢ} (A : Type ℓᵢ) → (A → A)
idf A = λ x → x
\end{code}

### Constant function

Constant function at some point `b` is `cst b`

\begin{code}
cst : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ}
    → (b : B)
    ---------
    → (A → B)
cst b = λ _ → b
\end{code}

### Composition

A more sophisticated composition function that can handle dependent functions.

\begin{code}
infixr 80 _∘_
_∘_ : ∀ {ℓᵢ ℓⱼ ℓₖ} {A : Type ℓᵢ} {B : A → Type ℓⱼ} {C : (a : A) → (B a → Type ℓₖ)}
    → (g : {a : A} → Π (B a) (C a))
    → (f : Π A B)
    -------------------------------
    → Π A (λ a → C a (f a))
g ∘ f = λ x → g (f x)

-- synonym for composition
_//_ : ∀ {ℓᵢ ℓⱼ ℓₖ} {A : Type ℓᵢ} {B : A → Type ℓⱼ} {C : (a : A) → (B a → Type ℓₖ)}
    → (f : Π A B)
    → (g : {a : A} → Π (B a) (C a))
    -------------------------------
    → Π A (λ a → C a (f a))
f // g = g ∘ f
\end{code}

### Application

\begin{code}
infixr 0 _$_
_$_ : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : A → Type ℓⱼ}
    → (∀ x → B x) → (∀ x → B x)
f $ x = f x
\end{code}

### Curryfication

\begin{code}
curry : ∀ {i j k} {A : Type i} {B : A → Type j} {C : Σ A B → Type k}
      → (∀ s → C s)
      ---------------------
      → (∀ x y → C (x , y))
curry f x y = f (x , y)
\end{code}

### Uncurryfication

\begin{code}
uncurry : ∀ {i j k} {A : Type i} {B : A → Type j} {C : ∀ x → B x → Type k}
        → (∀ x y → C x y)
        -------------------------
        → (∀ s → C (π₁ s) (π₂ s))
uncurry f (x , y) = f x y
\end{code}

### Instance search

\begin{code}
-- how to use it ❓
⟨⟩ : ∀ {i} {A : Type i} {{a : A}} → A
⟨⟩ {{a}} = a
\end{code}

## Equality type

### Homogeneous equality

The Identity type is defined as an inductive type. Its induction principle is
the J-eliminator.

\begin{code}
infix 30 _==_
data _==_ {ℓᵢ} {A : Type ℓᵢ} (a : A) : A → Type ℓᵢ where
  idp : a == a

{-# BUILTIN EQUALITY _==_ #-}

-- synonyms for identity type
Path = _==_
\end{code}

\begin{code}
refl : ∀ {ℓᵢ} {A : Type ℓᵢ} (a : A) → a == a
refl {ℓᵢ}{A} a = idp {ℓᵢ = ℓᵢ}{A = A}
\end{code}

#### J eliminator

*Paulin-Mohring J rule*

\begin{code}
J : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {a : A} (B : (a' : A) (p : a == a') → Type ℓⱼ) (d : B a idp)
  {a' : A} (p : a == a') → B a' p
J {a = a} B d idp = d
\end{code}

\begin{code}
J' : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {a : A} (B : (a' : A) (p : a' == a) → Type ℓⱼ) (d : B a idp)
  {a' : A} (p : a' == a) → B a' p
J' {a = a} B d idp = d
\end{code}

##### Composition of paths

![path](/assets/ipe-images/path-concatenation.png)

\begin{code}
infixl 50 _·_
_·_ : ∀ {ℓ} {A : Type ℓ} {x y z : A}
    → (p : x == y)
    → (q : y == z)
    --------------
    → x == z
_·_ idp q = q
\end{code}

##### Inverse of paths

\begin{code}
inv : ∀ {ℓ} {A : Type ℓ} {a b : A} → a == b → b == a
inv idp = idp

-- synonyms for inverse path
infixl 60 _⁻¹
_⁻¹ = inv

infixr 60 !_
!_  = inv
\end{code}

\begin{code}
-- another common notation
_² : ∀ {ℓ} {A : Type ℓ} {a : A} → a == a → a == a
p ² = p · p
\end{code}

##### Associativity of composition
- Left associativity
\begin{code}
∘-lassoc
  : ∀ {ℓ} {A B C D : Type ℓ}
  → (h : C → D) → (g : B → C) → (f : A → B)
  -----------------------------------------
  → (h ∘ (g ∘ f)) == ((h ∘ g) ∘ f)
∘-lassoc h g f = idp {a = (λ x → h (g (f x)))}
\end{code}

- Right associativity
\begin{code}
∘-rassoc
  : ∀ {ℓ} {A B C D : Type ℓ}
  → (h : C → D) → (g : B → C) → (f : A → B)
  -----------------------------------------
  → ((h ∘ g) ∘ f) == (h ∘ (g ∘ f))
∘-rassoc h g f = (∘-lassoc h g f) ⁻¹
\end{code}

### Heterogeneous equality

\begin{code}
data HEq {ℓ} (A : Type ℓ)
            : (B : Type ℓ)
            → (α : A == B) (a : A) (b : B)
            → Type ℓ where
  idp : ∀ {a : A} → HEq A A idp a a
\end{code}

## Equational reasoning

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

\begin{code}

module EquationalReasoning {ℓᵢ} {A : Type ℓᵢ} where

  infixr 2 _==⟨⟩_
  _==⟨⟩_ : ∀ (x {y} : A) → x == y → x == y
  _ ==⟨⟩ p = p

  -- synonyms for _==⟨⟩
  _==⟨idp⟩_ = _==⟨⟩_
  _==⟨refl⟩_ = _==⟨⟩_

  infixr 2 _==⟨_⟩_
  _==⟨_⟩_ :  (x : A) {y z : A} → x == y → y == z → x == z
  _ ==⟨ p1 ⟩ p2 = p1 · p2

  infix  3 _∎
  _∎ : (x : A) → x == x
  _∎ = λ x → idp

  infix  1 begin_
  begin_ : {x y : A} → x == y → x == y
  begin_ p = p

open EquationalReasoning public
\end{code}

## Actions on paths

Functions are functors to equalities.  In other words, functions
preserve equalities.

\begin{code}
ap : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ}
   → (f : A → B) {a₁ a₂ : A}
   → a₁ == a₂
   --------------
   → f a₁ == f a₂
ap f idp = idp
\end{code}

Now, we can define a convenient syntax sugar for `ap` in
equational reasoning.

\begin{code}
infixl 40 ap
syntax ap f p = p |in-ctx f
\end{code}

Let's suppose we have a lemma:
{% raw %}
```agda
  lemma : a == b
  lemma = _
```
{% endraw %}
used in an equational reasoning like:
{% raw %}
```agda
  t : a == e
  t = f a =⟨ ap f lemma ⟩
      f b
      ∎
```
{% endraw %}

Then, we can now put the lemma in front:
{% raw %}
```agda
  t : a == e
  t = f a =⟨ lemma |in-ctx f ⟩
      f b
      ∎
```
{% endraw %}

Lastly, we can also define actions on two paths:

\begin{code}
ap₂ : ∀ {ℓᵢ ℓⱼ ℓₖ} {A : Type ℓᵢ} {B : Type ℓⱼ} {C : Type ℓₖ}  {b₁ b₂ : B}
    → (f : A → B → C)
    → {a₁ a₂ : A} → (a₁ == a₂)
    → {b₁ b₂ : B} → (b₁ == b₂)
    --------------------------
    → f a₁ b₁  == f a₂ b₂
ap₂ f idp idp = idp
\end{code}

### Lemmas

\begin{code}
ap-· : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} {a b c : A}
     → (f : A → B) → (p : a == b) → (q : b == c)
     -------------------------------------------
     → ap f (p · q) == ap f p · ap f q
ap-· f idp q = refl (ap f q)
\end{code}

\begin{code}
ap-inv : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} {a b : A}
       → (f : A → B) → (p : a == b)
       ----------------------------
       → ap f (p ⁻¹) == (ap f p) ⁻¹
ap-inv f idp = idp

-- synonyms
ap-! = ap-inv
\end{code}

\begin{code}
ap-comp
  : ∀ {ℓᵢ ℓⱼ ℓₖ} {A : Type ℓᵢ} {B : Type ℓⱼ} {C : Type ℓₖ} {a b : A}
  → (f : A → B)
  → (g : B → C)
  → (p : a == b)
  -------------------------------
  → ap g (ap f p) == ap (g ∘ f) p
ap-comp f g idp = idp
\end{code}

\begin{code}
ap-id : ∀ {ℓᵢ} {A : Type ℓᵢ} {a b : A}
      → (p : a == b)
      --------------
      → ap id p == p
ap-id idp = idp
\end{code}

\begin{code}
ap-const : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {C : Type ℓⱼ} {a b : A} {c : C}
         → (p : a == b)
         -----------------------
         → ap (λ _ → c) p == idp
ap-const {c = c} idp = refl (refl c)
\end{code}

## Properties on the groupoid

Some properties on the groupoid structure of equalities

\begin{code}
module ·-Properties {ℓ} {A : Type ℓ} where


  ·-runit : {a b : A}
          → (p : a == b)
          --------------
          → p == p · idp
  ·-runit idp = idp

  ·-lunit : {a b : A}
          → (p : a == b)
          --------------
          → p == idp · p
  ·-lunit idp = idp

  ·-linv : {a b : A}
          → (p : a == b)
          ----------------
          → ! p · p == idp
  ·-linv idp = idp

  ·-rinv : {a b : A}
        → (p : a == b)
        ----------------
        → p · ! p == idp
  ·-rinv idp = idp

  involution : {a b : A} {p : a == b}
            ---------------
             → ! (! p) == p
  involution {p = idp} = idp

  ·-assoc : {a b c d : A}
          → (p : a == b) → (q : b == c) → (r : c == d)
          --------------------------------------------
          → p · q · r == p · (q · r)
  ·-assoc idp q r = idp

  ·-cancellation : {a : A}
                 → (p : a == a) → (q : a == a)
                 → p · q == p
                 -----------------------------
                 → q == idp
  ·-cancellation {a} p q α =
      begin
        q             ==⟨ ap (_· q) (! (·-linv p)) ⟩
        ! p · p · q   ==⟨ (·-assoc (! p) _ _) ⟩
        ! p · (p · q) ==⟨ (ap (! p ·_) α) ⟩
        ! p · p       ==⟨ ·-linv p ⟩
        idp
      ∎
  !-· : {a b : A}
      → (p : a == b)
      → (q : b == a)
      --------------------------
      → ! (p · q) == ! q · ! p
  !-· idp q = ·-runit (! q)

open ·-Properties public
\end{code}



## Transport

![path](/assets/ipe-images/transport-fiber-minihott.png)

\begin{code}
transport : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ}
          → (C : A → Type ℓⱼ) {a₁ a₂ : A}
          → (p : a₁ == a₂)
          -------------------------------
          → (C a₁ → C a₂)
transport C idp = (λ x → x)

-- synonyms
tr     = transport
transp = transport

-- Star notation for transport
_✶ : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ}
   → {C : A → Type ℓⱼ} {a₁ a₂ : A}
   → (p : a₁ == a₂)
   -------------------------------
   → (C a₁ → C a₂)
_✶ {ℓᵢ}{ℓⱼ}{A}{C} = transport {ℓᵢ = ℓᵢ} {ℓⱼ = ℓⱼ} C

\end{code}

\begin{code}
coe
  : ∀ {ℓ} {A B : Type ℓ}
  → A == B
  ---------
  → (A → B)
coe p A = transport (λ X → X) p A
\end{code}

### Pathover

Let be `A : Type`, `a₁, a₂ : A`, `C : A → Type`, `c₁ : C a₁` and `c₂ : C a₂`.
Using the same notation from {% cite hottbook %}, one of the definitions for the
Pathover type is as the shorthand for the path between the transport along a
path `α : a₁ = a₂` of the point `c₁ : C a₁` and the point `c₂` in the fiber `C
a₂`. That is, a pathover is a term that inhabit the type `transport C α c₁ = c₂`
also denoted by `PathOver C α c₁ c₂`.

![path](/assets/ipe-images/pathover-3-minihott.png)

\begin{code}
PathOver : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ}(C : A → Type ℓⱼ) {a₁ a₂ : A}
        → (α : a₁ == a₂) (c₁ : C a₁)(c₂ : C a₂) → Type ℓⱼ
PathOver C α c₁ c₂ = transport C α c₁ == c₂

infix 30 PathOver
syntax PathOver B p u v = u == v [ B ↓ p ]
\end{code}

## 🚧 Reviewing below…

### Lemmas
Some lemmas on the transport operation

\begin{code}
module Transport-Properties {ℓᵢ} {A : Type ℓᵢ} where

  lift : ∀ {a₁ a₂ : A} {ℓⱼ} {C : A → Type ℓⱼ}
       → (u : C a₁)
       → (α : a₁ == a₂)
       -----------------------------------
       → (a₁ , u) == (a₂ , transport C α u)
  lift {a₁ = a₁} u idp = refl (a₁ , u)

  transport-const
    : ∀ {a₁  a₂ : A} {ℓⱼ} {B : Type ℓⱼ}
    → (p : a₁ == a₂)
    → (b : B)
    ------------------------------
    → transport (λ _ → B) p b == b
  transport-const idp _ = idp
  transportconst = transport-const

  transport-concat-r
    : {a : A} {x y : A}
    → (p : x == y) → (q : a == x)
    →
    transport (λ x → a == x) p q == q · p
  transport-concat-r idp q = ·-runit q

  transport-concat-l : {a : A} {x y : A} → (p : x == y) → (q : x == a) →
    transport (λ x → x == a) p q == (inv p) · q
  transport-concat-l idp q = idp

  transport-concat : {x y : A} → (p : x == y) → (q : x == x) →
    transport (λ x → x == x) p q == (inv p) · q · p
  transport-concat idp q = ·-runit q

  transport-eq-fun
    : ∀ {ℓⱼ} {B : Type ℓⱼ}
    → (f g : A → B) {x y : A}
    → (p : x == y)
    → (q : f x == g x)
    ---------------------------------------------------------------
    → transport (λ z → f z == g z) p q == ! (ap f p) · q · (ap g p)
  transport-eq-fun f g idp q = ·-runit q

  transport-comp : ∀{ℓⱼ} {a b c : A} {P : A → Type ℓⱼ} (p : a == b) (q : b == c)
                   → ((transport P q) ∘ (transport P p)) == transport P (p · q)
  transport-comp {P = P} idp q = idp {a = (transport P q)}

  transport-comp-h : ∀{ℓⱼ} {a b c : A} {P : A → Type ℓⱼ} (p : a == b) (q : b == c) (x : P a)
                   → ((transport P q) ∘ (transport P p)) x == transport P (p · q) x
  transport-comp-h {P = P} idp q x = idp {a =  (transport P q x)}

open Transport-Properties public
\end{code}

\begin{code}
transport-eq-fun-l : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} {b : B} (f : A → B) {x y : A}
                     → (p : x == y) (q : f x == b)
                     → transport (λ z → f z == b) p q == inv (ap f p) · q
transport-eq-fun-l {b = b} f p q =
  begin
    transport (λ z → f z == b) p q     ==⟨ transport-eq-fun f (λ _ → b) p q ⟩
    inv (ap f p) · q · ap (λ _ → b) p  ==⟨ ap (inv (ap f p) · q ·_) (ap-const p) ⟩
    inv (ap f p) · q · idp             ==⟨ inv (·-runit _) ⟩
    inv (ap f p) · q
  ∎
\end{code}
\begin{code}
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
\end{code}

\begin{code}
transport-inv-l : ∀{ℓ} {A B : Type ℓ} → (p : A == B) → (b : B)
              → transport (λ v → v) p (transport (λ v → v) (inv p) b) == b
transport-inv-l idp b = idp

transport-inv-r : ∀{ℓ} {A B : Type ℓ} → (p : A == B) → (a : A)
              → transport (λ v → v) (inv p) (transport (λ v → v) p a) == a
transport-inv-r idp b = idp
\end{code}
\begin{code}
transport-family : ∀{ℓᵢ ℓⱼ ℓₖ} {A : Type ℓᵢ} {B : Type ℓⱼ} {P : B → Type ℓₖ}
                 → {f : A → B} → {x y : A} → (p : x == y) → (u : P (f x))
                 → transport (P ∘ f) p u == transport P (ap f p) u
transport-family idp u = idp

transport-family-id
  : ∀{ℓᵢ ℓₖ} {A : Type ℓᵢ} {P : A → Type ℓₖ}
  → {x y : A} → (p : x == y) → (u : P x)
  → transport (λ a → P a) p u == transport P p u
transport-family-id idp u = idp
\end{code}

\begin{code}
transport-fun
  : ∀{ℓᵢ ℓⱼ ℓₖ} {X : Type ℓᵢ} {x y : X} {A : X → Type ℓⱼ} {B : X → Type ℓₖ}
  → (p : x == y) → (f : A x → B x)
  → tr (λ x → (A x → B x)) p f == (λ x → tr B p (f (tr A (inv p) x)))
transport-fun idp f = idp
\end{code}

![path](/assets/ipe-images/transport-fun.png)

\begin{code}
transport-fun-h
  : ∀ {ℓᵢ ℓⱼ ℓₖ} {X : Type ℓᵢ} {A : X → Type ℓⱼ} {B : X → Type ℓₖ} {x y : X}
  → (p : x == y) → (f : A x → B x)
  → (b : A y)
  → (tr (λ x → (A x → B x)) p f) b == tr B p (f (tr A (inv p) b))
transport-fun-h idp f b = idp
\end{code}

Now, let us see when we transport dependent functions:

![path](/assets/ipe-images/transport-fun-dependent.png)

\begin{code}
transport-fun-dependent
  : ∀ {ℓᵢ ℓⱼ ℓₖ} {X : Type ℓᵢ} {A : X → Type ℓⱼ} {B : (x : X) → (a : A x) → Type ℓₖ}{x y : X}
  → (p : x == y)
  → (f : (a : A x) → B x a)
  → (a' : A y)
  → (tr (λ x → (a : A x) → B x a) p f) a'
    == tr (λ w → B (π₁ w) (π₂ w)) (! lift a' (! p)) (f (tr A (! p) a'))
transport-fun-dependent idp f a' = idp
\end{code}

## Basic type lemmas

### Sigma type

\begin{code}
module Sigma {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {P : A → Type ℓⱼ} where

  -- Two dependent pairs are equal if they are componentwise equal.
  Σ-componentwise
    : {v w : Σ A P}
    → v == w
    → Σ (π₁ v == π₁ w) (λ p → (p ✶) (π₂ v) == π₂ w)
  Σ-componentwise  idp = (idp , idp)

  Σ-bycomponents
    : {v w : Σ A P}
    → Σ (π₁ v == π₁ w) (λ p → (p ✶) (π₂ v) == π₂ w)
    → v == w
  Σ-bycomponents (idp , idp) = idp

  pair= = Σ-bycomponents

  uppt : (x : Σ A P) → (π₁ x , π₂ x) == x
  uppt (a , b) = idp

  Σ-ap-π₁
    : {a₁ a₂ : A} {b₁ : P a₁} {b₂ : P a₂}
    → (α : a₁ == a₂) → (γ : transport P α b₁ == b₂)
    → ap π₁ (pair= (α , γ)) == α
  Σ-ap-π₁ idp idp = idp

  ap-π₁-pair= = Σ-ap-π₁

open Sigma public
\end{code}


### Cartesian product

\begin{code}
module CartesianProduct {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where

  -- In a pair, the equality of the two components of the pairs is
  -- equivalent to equality of the two pairs.
  prodComponentwise
    : {x y : A × B}
    → (x == y)
    → (π₁ x == π₁ y) × (π₂ x == π₂ y)
  prodComponentwise {x = x} idp = refl (π₁ x) , refl (π₂ x)

  prodByComponents
    : {x y : A × B}
    → (π₁ x == π₁ y) × (π₂ x == π₂ y)
    → (x == y)
  prodByComponents {x = a , b} (idp , idp) = refl (a , b)

  -- This is in fact an equivalence.
  prodCompInverse
    : {x y : A × B} (b : ((π₁ x == π₁ y) × (π₂ x == π₂ y)))
    → prodComponentwise (prodByComponents b) == b
  prodCompInverse {x} (idp , idp) = refl (refl (π₁ x) , refl (π₂ x))

  prodByCompInverse
    : {x y : A × B} (b : x == y)
    → prodByComponents (prodComponentwise b) == b
  prodByCompInverse {x = x} idp = refl (refl x)

open CartesianProduct
\end{code}


## Action on dependent paths

More properties and lemmas on equality, transporting and function application.

\begin{code}
apd : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ}  {P : A → Type ℓⱼ} {a b : A}
    → (f : (a : A) → P a) → (p : a == b)
    → transport P p (f a) == f b
apd f idp = idp
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
  h-refl f x = idp

  h-simm : (f g : (x : A) → P x) → f ∼ g → g ∼ f
  h-simm f g u x = inv (u x)

  h-comp : (f g h : (x : A) → P x) → f ∼ g → g ∼ h → f ∼ h
  h-comp f g h u v x = (u x)·(v x)

  _●_ : {f g h : (x : A) → P x} → f ∼ g → g ∼ h → f ∼ h
  α ● β = h-comp _ _ _ α β

open Homotopy public
\end{code}

### Composition

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

### Naturality

Homotopy is natural, meaning that it satisfies the following
square commutative diagram.

\begin{code}

module Naturality {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where
  h-naturality : {f g : A → B} (H : f ∼ g) → {x y : A} → (p : x == y)
               → H x · ap g p == ap f p · H y
  h-naturality H {x = x} idp = inv (·-runit (H x))
open Naturality
\end{code}

A particular case of naturality on the identity function.
\begin{code}
h-naturality-id : ∀ {ℓ} {A : Type ℓ} {f : A → A} (H : f ∼ id) → {x : A}
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
  fib-eq : {f : A → B} → {b : B} → (h : fib f b) → f (π₁ h) == b
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
  isContr : ∀ {ℓ}  (A : Type ℓ) → Type ℓ
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
  _≃_ : ∀ {ℓᵢ ℓⱼ}  (A : Type ℓᵢ) (B : Type ℓⱼ) → Type (ℓᵢ ⊔ ℓⱼ)
  A ≃ B = Σ (A → B) isEquiv

  module EquivalenceMaps {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where

    -- Maps of an equivalence
    lemap : A ≃ B → (A → B)
    lemap = π₁

    ≃-to-→ = lemap
    fun≃   = lemap

    remap : A ≃ B → (B → A)
    remap (f , contrf) b = π₁ (π₁ (contrf b))

    -- The maps of an equivalence are inverses in particular
    lrmap-inverse : (eq : A ≃ B) → {b : B} → (lemap eq) ((remap eq) b) == b
    lrmap-inverse (f , eqf) {b} = fib-eq (π₁ (eqf b))

    rlmap-inverse : (eq : A ≃ B) → {a : A} → (remap eq) ((lemap eq) a) == a
    rlmap-inverse (f , eqf) {a} = ap π₁ ((π₂ (eqf (f a))) fib-image)

    lrmap-inverse-h : (eq : A ≃ B) → ((lemap eq) ∘ (remap eq)) ∼ id
    lrmap-inverse-h eq = λ x → lrmap-inverse eq {x}

    rlmap-inverse-h : (eq : A ≃ B) → ((remap eq) ∘ (lemap eq)) ∼ id
    rlmap-inverse-h eq = λ x → rlmap-inverse eq {x}
  open EquivalenceMaps public

open Equivalence public
\end{code}

## Function extensionality

\begin{code}

module FunExt {ℓᵢ ℓⱼ} {A : Type ℓᵢ}
  {B : A → Type ℓⱼ} {f g : (a : A) → B a} where

  -- Application of an homotopy
  happly : f == g → ((x : A) → f x == g x)
  happly idp x = refl (f x)

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

open FunExt public
\end{code}

- Function extensionality in the transport case

\begin{code}
module FunExt-Transport
  {ℓᵢ ℓⱼ} {X : Type ℓᵢ} {A B : X → Type ℓⱼ} {x y : X} where

  funext-transport
    : (p : x == y) → (f : A x → B x) → (g : A y → B y)
    → ((p ✶) f == g) ≃ ((a : A(x)) → (p ✶) (f a) == g ((p ✶) a))
  funext-transport idp f g = eqFunExt

  funext-transport-l
    : (p : x == y) → (f : A x → B x) → (g : A y → B y)
    → ((p ✶) f == g) → ((a : A(x)) → (p ✶) (f a) == g ((p ✶) a))
  funext-transport-l p f g = lemap (funext-transport p _ _)

  funext-transport-r
    : (p : x == y) → (f : A x → B x) → (g : A y → B y)
    → ((a : A(x)) → (p ✶) (f a) == g ((p ✶) a)) → ((p ✶) f == g)
  funext-transport-r p f g = remap (funext-transport p _ _)
open FunExt-Transport public
\end{code}

\begin{code}
module FunExt-Transport-DFun
  {ℓᵢ ℓⱼ} {X : Type ℓᵢ} {A : X → Type ℓⱼ}{B : (x : X) → A x → Type ℓⱼ}{x y : X}
  where

  -- Lemma 2.9.7
  funext-transport-dfun
    : (p : x == y) → (f : (a : A x) → B x a) → (g : (a : A y) → B y a)
    -------------------------------------------------------------------------------------------
    → ((p ✶) f == g) ≃ ((a : A x) → tr (λ w → B (π₁ w) (π₂ w)) (lift a p) (f a) == g ((p ✶) a))
  funext-transport-dfun idp f g = eqFunExt

  funext-transport-dfun-l
    : (p : x == y) → (f : (a : A x) → B x a) → (g : (a : A y) → B y a)
    → ((p ✶) f == g)
    ---------------------------------------------------------------------------
     → ((a : A x) → tr (λ w → B (π₁ w) (π₂ w)) (lift a p) (f a) == g ((p ✶) a))
  funext-transport-dfun-l p f g = lemap (funext-transport-dfun p _ _)
  --
  funext-transport-dfun-r
    : (p : x == y) → (f : (a : A x) → B x a) → (g : (a : A y) → B y a)
    → ((a : A x) → tr (λ w → B (π₁ w) (π₂ w)) (lift a p) (f a) == g ((p ✶) a))
    --------------------------------------------------------------------------
    → ((p ✶) f == g)
  funext-transport-dfun-r p f g = remap (funext-transport-dfun p _ _)
open FunExt-Transport-DFun public
\end{code}

## Decidable equality

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
  decEqProd da db (a1 , b1) (a2 , b2) | inl aeq | inr bnq = inr λ b → bnq (ap π₂ b)
  decEqProd da db (a1 , b1) (a2 , b2) | inr anq | u       = inr λ b → anq (ap π₁ b)

open DecidableEquality
\end{code}

## Hlevels

### Propositions

Propositions as described on the main text. A type
is a proposition if we can create a function making any two of its
elements equal. We create a type of propositions.

\begin{code}

module Propositions where

  -- A type is a mere proposition if any two inhabitants of the type
  -- are equal
  isProp : ∀ {ℓ}  (A : Type ℓ) → Type ℓ
  isProp A = ((x y : A) → x == y)

  -- The type of mere propositions
  hProp : ∀ {ℓ} → Type (lsuc ℓ)
  hProp {ℓ} = Σ (Type ℓ) isProp


  -- The dependent function type to proposition types is itself a
  -- proposition.
  piProp : ∀ {ℓᵢ ℓⱼ} → {A : Type ℓᵢ} → {B : A → Type ℓⱼ}
         → ((a : A) → isProp (B a)) → isProp ((a : A) → B a)
  piProp props f g = funext λ a → props a (f a) (g a)

  -- The product of propositions is itself a proposition.
  isProp-prod : ∀ {ℓᵢ ℓⱼ} → {A : Type ℓᵢ} → {B : Type ℓⱼ}
              → isProp A → isProp B → isProp (A × B)
  isProp-prod p q x y = prodByComponents ((p _ _) , (q _ _))

open Propositions
\end{code}

### Sets

Sets are types without any higher dimensional structure, all
parallel paths are homotopic and the homotopy is given by a
continuous function on the two paths.

\begin{code}
module Sets where

  -- A type is a "set" by definition if any two equalities on the type
  -- are equal.
  isSet : ∀ {ℓ}  (A : Type ℓ) → Type ℓ
  isSet A = (x y : A) → isProp (x == y)

  -- The type of sets.
  hSet : ∀ {ℓ} → Type (lsuc ℓ)
  hSet {ℓ} = Σ (Type ℓ) isSet

  -- Product of sets is a set.
  isSet-prod : ∀ {ℓᵢ ℓⱼ}  {A : Type ℓᵢ} → {B : Type ℓⱼ}
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

### Lemmas

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
  propIsSet : ∀ {ℓ} {A : Type ℓ} → isProp A → isSet A
  propIsSet {A = A} f a _ p q = lemma p · inv (lemma q)
    where
      triang : {y z : A} {p : y == z} → (f a y) · p == f a z
      triang {y}{p = idp} = inv (·-runit (f a y))

      lemma : {y z : A} (p : y == z) → p == inv (f a y) · (f a z)
      lemma {y} {z} p =
        begin
          p                         ==⟨ ap (_· p) (inv (·-linv (f a y))) ⟩
          inv (f a y) · f a y · p   ==⟨ ·-assoc (inv (f a y)) (f a y) p ⟩
          inv (f a y) · (f a y · p) ==⟨ ap (inv (f a y) ·_) triang ⟩
          inv (f a y) · (f a z)
        ∎

  -- Contractible types are Propositions.
  contrIsProp : ∀ {ℓ}  {A : Type ℓ} → isContr A → isProp A
  contrIsProp (a , p) x y = inv (p x) · p y

  -- To be contractible is itself a proposition.
  isContrIsProp : ∀ {ℓ}  {A : Type ℓ} → isProp (isContr A)
  isContrIsProp {_} {A} (a , p) (b , q) = Σ-bycomponents (inv (q a) , piProp (AisSet b) _ q)
    where
      AisSet : isSet A
      AisSet = propIsSet (contrIsProp (a , p))

open HLevels
\end{code}


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
  sameEqv : {α β : A ≃ B} → π₁ α == π₁ β → α == β
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


### Half-adjoints

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
      τ : (a : A) → ap f (η a) == ε (f a)

  -- Half adjoint equivalences give contractible fibers.
  ishae-contr : (f : A → B) → ishae f → isContrMap f
  ishae-contr f (hae g η ε τ) y = ((g y) , (ε y)) , contra
    where
      lemma : (c c' : fib f y) → Σ (π₁ c == π₁ c') (λ γ → (ap f γ) · π₂ c' == π₂ c) → c == c'
      lemma c c' (p , q) = Σ-bycomponents (p , lemma2)
        where
          lemma2 : transport (λ z → f z == y) p (π₂ c) == π₂ c'
          lemma2 =
            begin
              transport (λ z → f z == y) p (π₂ c)
                ==⟨ transport-eq-fun-l f p (π₂ c) ⟩
              inv (ap f p) · (π₂ c)
                ==⟨ ap (inv (ap f p) ·_) (inv q) ⟩
              inv (ap f p) · ((ap f p) · (π₂ c'))
                ==⟨ inv (·-assoc (inv (ap f p)) (ap f p) (π₂ c')) ⟩
              inv (ap f p) · (ap f p) · (π₂ c')
                ==⟨ ap (_· (π₂ c')) (·-linv (ap f p)) ⟩
              π₂ c'
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

open Halfadjoints public
\end{code}

### Quasiinverses

Two functions are quasi-inverses if we can construct a function providing
`(g ∘ f) x = x` and `(f ∘ g) y = y` for any given `x` and `y`.

\begin{code}
module Quasiinverses {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where

  -- Definitions for quasi-inverses, left-inverses, right-inverses and
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
      γ2 x = idp

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
      aux-lemma : (a : A) → ap f (η (g (f a))) · ε (f a) == ε (f (g (f a))) · ap f (η a)
      aux-lemma a =
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
            ==⟨ ap (inv (ε (f (g (f a)))) ·_) (inv (aux-lemma a)) ⟩
          inv (ε (f (g (f a)))) · (ap f (η (g (f a))) · ε (f a))
            ==⟨ inv (·-assoc (inv (ε (f (g (f a))))) _ (ε (f a))) ⟩
          inv (ε (f (g (f a)))) · ap f (η (g (f a))) · ε (f a)
        ∎

  -- Quasiinverses create equivalences.
  qinv-≃ : (f : A → B) → qinv f → A ≃ B
  qinv-≃ f = ishae-≃ ∘ qinv-ishae

  ≃-qinv : A ≃ B → Σ (A → B) qinv
  ≃-qinv eq =
    lemap eq , (remap eq , (lrmap-inverse-h eq , rlmap-inverse-h eq))

  -- Half-adjoint equivalences are quasiinverses.
  ishae-qinv : {f : A → B} → ishae f → qinv f
  ishae-qinv {f} (hae g η ε τ) = g , (ε , η)

  ≃-ishae : (e : A ≃ B)→ ishae (lemap e)
  ≃-ishae e = qinv-ishae (π₂ (≃-qinv e))

open Quasiinverses public
\end{code}

## Equivalence composition

Composition of equivalences and properties of that composition.

\begin{code}
module EquivalenceComposition where

  -- Composition of quasiinverses
  qinv-comp : ∀ {ℓ} {A B C : Type ℓ} → Σ (A → B) qinv → Σ (B → C) qinv → Σ (A → C) qinv
  qinv-comp (f , (if , (εf , ηf))) (g , (ig , (εg , ηg))) = (g ∘ f) , ((if ∘ ig) ,
     ( (λ x → ap g (εf (ig x)) · εg x)
     ,  λ x → ap if (ηg (f x)) · ηf x))

  qinv-inv : ∀ {ℓ} {A B : Type ℓ} → Σ (A → B) qinv → Σ (B → A) qinv
  qinv-inv (f , (g , (ε , η))) = g , (f , (η , ε))

  -- Composition of equivalences
  idEqv : ∀ {ℓ} {A : Type ℓ} → A ≃ A
  idEqv = id , λ a → (a , refl a) , λ { (_ , idp) → refl (a , refl a) }

  compEqv : ∀ {ℓ} {A B C : Type ℓ} → A ≃ B → B ≃ C → A ≃ C
  compEqv {ℓ} {A} {B} {C} eqf eqg = qinv-≃ (π₁ qcomp) (π₂ qcomp)
   where
     qcomp : Σ (A → C) qinv
     qcomp = qinv-comp (≃-qinv eqf) (≃-qinv eqg)

  invEqv : ∀ {ℓ} {A B : Type ℓ} → A ≃ B → B ≃ A
  invEqv {ℓ} {A} {B} eqf = qinv-≃ (π₁ qcinv) (π₂ qcinv)
   where
     qcinv : Σ (B → A) qinv
     qcinv = qinv-inv (≃-qinv eqf)

  -- Lemmas about composition
  compEqv-inv : ∀ {ℓ} {A B : Type ℓ} → (α : A ≃ B) → compEqv α (invEqv α) == idEqv
  compEqv-inv {_} {A} {B} α = sameEqv (
   begin
     π₁ (compEqv α (invEqv α)) ==⟨ refl _ ⟩
     π₁ (invEqv α) ∘ π₁ α     ==⟨ funext (rlmap-inverse-h α) ⟩
     id
   ∎)

open EquivalenceComposition public
\end{code}


## Equivalence reasoning

\begin{code}
module EquivalenceReasoning where

  infixr 2 _≃⟨⟩_
  _≃⟨⟩_ : ∀ {ℓ} (A {B} : Type ℓ) → A ≃ B → A ≃ B
  _ ≃⟨⟩ e = e

  infixr 2 _≃⟨_⟩_
  _≃⟨_⟩_ : ∀ {ℓ} (A : Type ℓ) {B C : Type ℓ} → A ≃ B → B ≃ C → A ≃ C
  _ ≃⟨ e₁ ⟩ e₂ = compEqv e₁ e₂
  --
  infix  3 _≃∎
  _≃∎ :  ∀ {ℓ} (A : Type ℓ) → A ≃ A
  _≃∎ = λ A → idEqv {A = A}

  infix  1 begin≃_
  begin≃_ : ∀ {ℓ} {A B : Type ℓ} → A ≃ B → A ≃ B
  begin≃_ e = e

open EquivalenceReasoning public
\end{code}

## Equivalence with Sigma type

\begin{code}
module SigmaEquivalence {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {P : A → Type ℓⱼ} where

  pair=Equiv : {v w : Σ A P}
    → Σ (π₁ v == π₁ w) (λ p → (p ✶) (π₂ v) == π₂ w) ≃ v == w
  pair=Equiv = qinv-≃ Σ-bycomponents (Σ-componentwise , HΣ₁ , HΣ₂)
    where
      HΣ₁ : Σ-bycomponents ∘ Σ-componentwise ∼ id
      HΣ₁ idp = idp

      HΣ₂ : Σ-componentwise ∘ Σ-bycomponents ∼ id
      HΣ₂ (idp , idp) = idp

  private
    f : {a₁ a₂ : A} {α : a₁ == a₂}{c₁ : P a₁} {c₂ : P a₂}
      → {β : a₁ == a₂}
      → {γ : transport P β c₁ == c₂}
      → ap π₁ (pair= (β , γ)) == α → β == α
    f {β = idp} {γ = idp} idp = idp

    g : {a₁ a₂ : A} {α : a₁ == a₂}{c₁ : P a₁} {c₂ : P a₂}
      → {β : a₁ == a₂}
      → {γ : transport P β c₁ == c₂}
      → β == α → ap π₁ (pair= (β , γ)) == α
    g {β = idp} {γ = idp} idp = idp

    f-g : {a₁ a₂ : A} {α : a₁ == a₂}{c₁ : P a₁} {c₂ : P a₂}
      → {β : a₁ == a₂}
      → {γ : transport P β c₁ == c₂}
      → f {α = α}{β = β}{γ} ∘ g {α = α}{β = β} ∼ id
    f-g {β = idp} {γ = idp} idp = idp

    g-f : {a₁ a₂ : A} {α : a₁ == a₂}{c₁ : P a₁} {c₂ : P a₂}
      → {β : a₁ == a₂}
      → {γ : transport P β c₁ == c₂}
      → g {α = α}{β = β}{γ} ∘ f {α = α}{β = β}{γ} ∼ id
    g-f {β = idp} {γ = idp} idp = idp

  ap-π₁-pair=Equiv : {a₁ a₂ : A} {c₁ : P a₁} {c₂ : P a₂}
    → (α : a₁ == a₂)
    → (γ : Σ (a₁ == a₂) (λ α' → transport P α' c₁ == c₂))
    → (ap π₁ (pair= γ) == α) ≃ π₁ γ == α
  ap-π₁-pair=Equiv {a₁ = a₁} α (β , γ) = qinv-≃ f (g , f-g , g-f)

open SigmaEquivalence public
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
      (transport (λ X → X) p)
      (transport (λ X → X) (inv p) , (transport-inv-l p , transport-inv-r p))

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
open Univalence public
\end{code}

### Univalence lemmas

\begin{code}
module UnivalenceLemmas {ℓ} where
\end{code}

- The identity equivalence creates the trivial path.
{: .foldable}
\begin{code}
  postulate
    ua-id : {A : Type ℓ} → ua idEqv == refl A
    -- ua-id {A} =
    --   begin
    --     ua idEqv              ==⟨ ap ua (sameEqv (refl id)) ⟩
    --     ua (idtoeqv (refl A)) ==⟨ ua-η (refl A) ⟩
    --     refl A
    --   ∎

    -- The composition of equivalences is preserved into composition
    -- of equalities.
\end{code}
-
{: .foldable}
\begin{code}
  postulate
    ua-comp : {A B C : Type ℓ} → (α : A ≃ B) → (β : B ≃ C) → ua (compEqv α β) == ua α · ua β
    -- ua-comp α β =
    --   begin
    --     ua (compEqv α β)                               ==⟨ ap (λ x → ua (compEqv x β)) (inv (ua-β α)) ⟩
    --     ua (compEqv (idtoeqv (ua α)) β)                ==⟨ ap (λ x → ua (compEqv (idtoeqv (ua α)) x))
    --                                                        (inv (ua-β β)) ⟩
    --     ua (compEqv (idtoeqv (ua α)) (idtoeqv (ua β))) ==⟨ ap ua lemma ⟩
    --     ua (idtoeqv (ua α · ua β))                     ==⟨ ua-η (ua α · ua β) ⟩
    --     ua α · ua β
    --   ∎
    --   where
    --     lemma : compEqv (idtoeqv (ua α)) (idtoeqv (ua β)) == idtoeqv (ua α · ua β)
    --     lemma = sameEqv (
    --       begin
    --         π₁ (idtoeqv (ua β)) ∘ π₁ (idtoeqv (ua α))                 ==⟨ refl _ ⟩
    --         (transport (λ x → x) (ua β)) ∘ (transport (λ x → x) (ua α)) ==⟨ transport-comp (ua α) (ua β) ⟩
    --         transport (λ x → x) (ua α · ua β)                           ==⟨ refl _ ⟩
    --         π₁ (idtoeqv (ua α · ua β))
    --       ∎)
\end{code}

- Inverses are preserved
{: .foldable}
\begin{code}
  postulate
    ua-inv-r : {A B : Type ℓ} → (α : A ≃ B) → ua α · ua (invEqv α) == refl A
    -- ua-inv-r α =
    --   begin
    --     ua α · ua (invEqv α)      ==⟨ inv (ua-comp α (invEqv α)) ⟩
    --     ua (compEqv α (invEqv α)) ==⟨ ap ua (compEqv-inv α) ⟩
    --     ua idEqv                  ==⟨ ua-id ⟩
    --     refl _
    --   ∎
\end{code}

- Missing description
{: .foldable}
\begin{code}
  postulate
    ua-inv : {A B : Type ℓ} → (α : A ≃ B) → ua (invEqv α) == inv (ua α)
    -- ua-inv α =
    --   begin
    --     ua (invEqv α)                       ==⟨ ap (_· ua (invEqv α)) (inv (·-linv (ua α))) ⟩
    --     inv (ua α) · ua α · ua (invEqv α)   ==⟨ ·-assoc (inv (ua α)) _ _ ⟩
    --     inv (ua α) · (ua α · ua (invEqv α)) ==⟨ ap (inv (ua α) ·_) (ua-inv-r α) ⟩
    --     inv (ua α) · refl _                 ==⟨ inv (·-runit (inv ((ua α)))) ⟩
    --     inv (ua α)
    --   ∎
open UnivalenceLemmas public
\end{code}

### Transport and Univalence

\begin{code}
module TransportUA where

  transport-family-ap
    : ∀ {ℓ} {A : Type ℓ}
    → (B : A → Type ℓ)
    → {x y : A}
    → (p : x == y)
    → (u : B x)
    ---------------------------------------------------
    → transport B p u == transport (λ X → X) (ap B p) u
  transport-family-ap B idp u = idp

  transport-family-idtoeqv
    : ∀ {ℓ} {A : Type ℓ}
    → (B : A → Type ℓ)
    → {x y : A}
    → (p : x == y)
    → (u : B x)
    ---------------------------------------------------
    → transport B p u == fun≃ (idtoeqv (ap B p)) u
  transport-family-idtoeqv B idp u = idp

  transport-ua
    : ∀ {ℓ} {A : Type ℓ}
    → (B : A → Type ℓ)
    → {x y : A}
    → (p : x == y)
    → (e : B x ≃ B y)
    → ap B p == ua e
    -----------------
    → (u : B x) → transport B p u == (fun≃ e) u
  transport-ua B idp e q u =
    begin
      transport B idp u
        ==⟨ transport-family-idtoeqv B idp u ⟩
      fun≃ (idtoeqv (ap B idp)) u
        ==⟨ ap (λ r → fun≃ (idtoeqv r) u) q ⟩
      fun≃ (idtoeqv (ua e)) u
        ==⟨ ap (λ r → fun≃ r u) (ua-β e) ⟩
      fun≃ e u
    ∎


  funext-transport-ua
    : ∀ {ℓ} {A : Type ℓ}
    → (B : A → Type ℓ)
    → {x y : A}
    → (p : x == y)
    → (e : B x ≃ B y)
    → ap B p == ua e
    -----------------
    → transport B p == (fun≃ e)
  funext-transport-ua B p e x₁ = funext (transport-ua B p e x₁)
open TransportUA public
\end{code}

## Truncation

\begin{code}
module Truncation where

  private
    -- Higher inductive type, defined with equalities between any two
    -- members.
    data !∥_∥ {ℓ} (A : Type ℓ) : Type ℓ where
      !∣_∣ : A → !∥ A ∥

  ∥_∥ : ∀ {ℓ} (A : Type ℓ) → Type ℓ
  ∥ A ∥ = !∥ A ∥

  ∣_∣ : ∀ {ℓ} {X : Type ℓ} → X → ∥ X ∥
  ∣ x ∣ = !∣ x ∣

  -- Any two elements of the truncated type are equal
  postulate trunc : ∀{ℓ} {A : Type ℓ} → isProp ∥ A ∥

  -- Recursion principle
  trunc-rec : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {P : Type ℓⱼ} → isProp P → (A → P) → ∥ A ∥ → P
  trunc-rec _ f !∣ x ∣ = f x
\end{code}

## Set truncation

An analogous form of truncation for Sets instead of
Propositions. It truncates any higher-dimensional homothopical
structure.

\begin{code}
module SetTruncation where

  private
    -- Higher inductive type
    data !∥_∥₀ {ℓ} (A : Type ℓ) : Type ℓ where
      !∣_∣₀ : A → !∥ A ∥₀

  ∥_∥₀ : ∀ {ℓ} (A : Type ℓ) → Type ℓ
  ∥ A ∥₀ = !∥ A ∥₀

  ∣_∣₀ : ∀{ℓ} {X : Type ℓ} → X → ∥ X ∥₀
  ∣ x ∣₀ = !∣ x ∣₀

  -- Any two equalities on the truncated type are equal
  postulate strunc : ∀{ℓ} {A : Type ℓ} → isSet ∥ A ∥₀

  -- Recursion principle
  strunc-rec : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {P : Type ℓⱼ} → isSet P → (A → P) → ∥ A ∥₀ → P
  strunc-rec _ f !∣ x ∣₀ = f x

  -- Induction principle
  strunc-ind : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : ∥ A ∥₀ → Type ℓⱼ} → ((a : ∥ A ∥₀) → isSet (B a))
             → (g : (a : A) → B ∣ a ∣₀) → (a : ∥ A ∥₀) → B a
  strunc-ind _ g !∣ x ∣₀ = g x
\end{code}

## Quotients

\begin{code}
module Quotients where

  record QRel {ℓ} (A : Type ℓ) : Type (lsuc ℓ) where
    field
      R : A → A → Type ℓ
      Aset : isSet A
      Rprop : (a b : A) → isProp (R a b)
  open QRel {{...}} public

  private
    -- Higher inductive type
    data _!/_ {ℓ} (A : Type ℓ) (r : QRel A) : Type (lsuc ℓ) where
      ![_] : A → (A !/ r)

  _/_ : ∀{ℓ} (A : Type ℓ) (r : QRel A) → Type (lsuc ℓ)
  A / r = (A !/ r)

  [_] : ∀{ℓ} {A : Type ℓ} → A → {r : QRel A} → (A / r)
  [ a ] = ![ a ]

  -- Equalities induced by the relation
  postulate Req : ∀{ℓ} {A : Type ℓ} {r : QRel A}
                 → {a b : A} → R {{r}} a b → [ a ] {r} == [ b ]

  -- The quotient of a set is again a set
  postulate Rtrunc : ∀{ℓ} {A : Type ℓ} {r : QRel A} → isSet (A / r)

  -- Recursion principle
  QRel-rec : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {r : QRel A} {B : Type ℓⱼ}
            → (f : A → B) → ((x y : A) → R {{r}} x y → f x == f y) → A / r → B
  QRel-rec f p ![ x ] = f x

  -- Induction principle
  QRel-ind : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {r : QRel A} {B : A / r → Type ℓⱼ}
            → (f : ((a : A) → B [ a ]))
            → ((x y : A) → (o : R {{r}} x y) → (transport B (Req o) (f x)) == f y)
            → (z : A / r) → B z
  QRel-ind f p ![ x ] = f x

  -- Recursion in two arguments
  QRel-rec-bi : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {r : QRel A} {B : Type ℓⱼ}
              → (f : A → A → B) → ((x y z t : A) → R {{r}} x y → R {{r}} z t → f x z == f y t)
              → A / r → A / r → B
  QRel-rec-bi f p ![ x ] ![ y ] = f x y


  Qrel-prod : ∀{ℓᵢ}{A : Type ℓᵢ} (r : QRel A) → QRel (A × A)
  Qrel-prod r = record { R = λ { (a , b) (c , d) → (R {{r}} a c) × (R {{r}} b d) }
                       ; Aset = isSet-prod (Aset {{r}}) (Aset {{r}})
                       ; Rprop = λ { (x , y) (z , w) → isProp-prod (Rprop {{r}} x z) (Rprop {{r}} y w)} }
\end{code}

## Relation

\begin{code}
module Relation where

  record Rel {ℓ} (A : Type ℓ) : Type (lsuc ℓ) where
    field
      R     : A → A → Type ℓ
      Rprop : (a b : A) → isProp (R a b)
  open Rel {{...}} public

open Relation public
\end{code}


## Hedberg

\begin{code}
module Hedberg {ℓ} where

  module HedbergLemmas (A : Type ℓ) where

    -- A set is a type satisfiying axiom K.
    axiomKisSet : ((a : A) → (p : a == a) → p == refl a) → isSet A
    axiomKisSet k x _ p idp = k x p

    -- Lemma: a reflexive relation on X implying the identity proves
    -- that X is a set.
    reflRelIsSet :  (r : Rel A) →
      ((x y : A) → R {{r}} x y → x == y) →
      (ρ : (a : A) → R {{r}} a a) →
      isSet A
    reflRelIsSet r f ρ x .x p idp = lemma p
      where
        lemma2 : {a : A} (p : a == a) → (o : R {{r}} a a) →
          transport (λ x → a == x) p (f a a o) == f a a (transport (R {{r}} a) p o)
        lemma2 {a} p = funext-transport-l p (f a a) (f a a) (apd (f a) p)

        lemma3 : {a : A} (p : a == a) →
          (f a a (ρ a)) · p == (f a a (ρ a))
        lemma3 {a} p = inv (transport-concat-r p _) · lemma2 p (ρ a) ·
                       ap (f a a) (Rprop {{r}} a a _ (ρ a))

        lemma : {a : A} (p : a == a) → p == refl a
        lemma {a} p = ·-cancellation ((f a a (ρ a))) p (lemma3 p)

    -- Lemma: if a type is decidable, then ¬¬A is actually A.
    lemDoubleNeg : (A + ¬ A) → (¬ (¬ A) → A)
    lemDoubleNeg (inl x) _ = x
    lemDoubleNeg (inr f) n = exfalso (n f)

  open HedbergLemmas public

  -- Hedberg's theorem. A type with decidable equality is a set.
  hedberg : {A : Type ℓ} → ((a b : A) → (a == b) + ¬ (a == b)) → isSet A
  hedberg {A} f = reflRelIsSet A
                (record { R = λ a b → ¬ (¬ (a == b)) ; Rprop = isPropNeg })
                doubleNegEq (λ a z → z (refl a))
    where
      doubleNegEq : (a b : A) → ¬ (¬ (a == b)) → (a == b)
      doubleNegEq a b = lemDoubleNeg (a == b) (f a b)

      isPropNeg : (a b : A) → isProp (¬ (¬ (a == b)))
      isPropNeg a b x y = funext λ u → exfalso (x u)

open Hedberg public
\end{code}


## Algebra

### Monoid

Definition of the algebraic structure of a monoid.

\begin{code}
module Monoids {ℓ} where

  record Monoid : Type (lsuc ℓ) where
    field
      -- Operations of a monoid
      G : Type ℓ
      GisSet : isSet G
      _<>_ : G → G → G  -- Multiplication function
      e : G             -- Unit element

      -- Axioms of a monoid
      lunit : (x : G) → (e <> x) == x
      runit : (x : G) → (x <> e) == x
      assoc : (x y z : G) → (x <> (y <> z)) == ((x <> y) <> z)
open Monoids
\end{code}

### Groups

\begin{code}
module Groups where
  record GroupStructure {ℓ} (M : Type ℓ) : Type ℓ where
    constructor group-structure
    field
      -- A group is a monoid
      _*_   : M → M → M
      e     : M
      lunit : ∀ x → (e * x) == x
      runit : ∀ x → (x * e) == x
      assoc : ∀ x y z → (x * (y * z)) == ((x * y) * z)

      -- With inverses
      ginv : M → M
      glinv : ∀ g → (g * ginv g) == e
      grinv : ∀ g → (ginv g * g) == e

  record Group {ℓ} : Type (lsuc ℓ) where
    constructor group
    field
      M : Type ℓ
      str : GroupStructure M
  open Group {{...}} public
open Groups
\end{code}

### Naturals

\begin{code}
module Naturals where

  -- Addition of natural numbers
  plus : ℕ → ℕ → ℕ
  plus zero y = y
  plus (succ x) y = succ (plus x y)

  infixl 60 _+ₙ_
  _+ₙ_ : ℕ → ℕ → ℕ
  _+ₙ_ = plus

  -- Lemmas about addition
  plus-lunit : (n : ℕ) → zero +ₙ n == n
  plus-lunit n = refl n

  plus-runit : (n : ℕ) → n +ₙ zero == n
  plus-runit zero = refl zero
  plus-runit (succ n) = ap succ (plus-runit n)

  plus-succ : (n m : ℕ) → succ (n +ₙ m) == (n +ₙ (succ m))
  plus-succ zero     m = refl (succ m)
  plus-succ (succ n) m = ap succ (plus-succ n m)

  plus-succ-rs : (n m o p : ℕ) → n +ₙ m == o +ₙ p → n +ₙ (succ m) == o +ₙ (succ p)
  plus-succ-rs n m o p α = inv (plus-succ n m) · ap succ α · (plus-succ o p)

  -- Commutativity
  plus-comm : (n m : ℕ) → n +ₙ m == m +ₙ n
  plus-comm zero     m = inv (plus-runit m)
  plus-comm (succ n) m = ap succ (plus-comm n m) · plus-succ m n

  -- Associativity
  plus-assoc : (n m p : ℕ) → n +ₙ (m +ₙ p) == (n +ₙ m) +ₙ p
  plus-assoc zero     m p = refl (m +ₙ p)
  plus-assoc (succ n) m p = ap succ (plus-assoc n m p)


  -- Decidable equality
  -- Encode-decode technique for natural numbers
  private
    code : ℕ → ℕ → Type₀
    code 0        0        = ⊤
    code 0        (succ m) = ⊥
    code (succ n) 0        = ⊥
    code (succ n) (succ m) = code n m

  crefl : (n : ℕ) → code n n
  crefl zero     = ★
  crefl (succ n) = crefl n

  private
    encode : (n m : ℕ) → (n == m) → code n m
    encode n m p = transport (code n) p (crefl n)

    decode : (n m : ℕ) → code n m → n == m
    decode zero zero c = refl zero
    decode zero (succ m) ()
    decode (succ n) zero ()
    decode (succ n) (succ m) c = ap succ (decode n m c)

  zero-not-succ : (n : ℕ) → ¬ (succ n == zero)
  zero-not-succ n = encode (succ n) 0

  -- The successor function is injective
  succ-inj : {n m : ℕ} → (succ n == succ m) → n == m
  succ-inj {n} {m} p = decode n m (encode (succ n) (succ m) p)

  +-inj : (k : ℕ) {n m : ℕ} → (k +ₙ n == k +ₙ m) → n == m
  +-inj zero   p = p
  +-inj (succ k) p = +-inj k (succ-inj p)

  nat-decEq : decEq ℕ
  nat-decEq zero zero = inl (refl zero)
  nat-decEq zero (succ m) = inr (λ ())
  nat-decEq (succ n) zero = inr (λ ())
  nat-decEq (succ n) (succ m) with (nat-decEq n m)
  nat-decEq (succ n) (succ m) | inl p = inl (ap succ p)
  nat-decEq (succ n) (succ m) | inr f = inr λ p → f (succ-inj p)

  nat-isSet : isSet ℕ
  nat-isSet = hedberg nat-decEq

  -- Naturals form a monoid with addition
  ℕ-plus-monoid : Monoid
  ℕ-plus-monoid = record
    { G = ℕ
    ; GisSet = nat-isSet
    ; _<>_ = plus
    ; e = zero
    ; lunit = plus-lunit
    ; runit = plus-runit
    ; assoc = plus-assoc
    }

  -- Ordering
  _<ₙ_ : ℕ → ℕ → Type₀
  n <ₙ m = Σ ℕ (λ k → n +ₙ succ k == m)

  <-isProp : (n m : ℕ) → isProp (n <ₙ m)
  <-isProp n m (k1 , p1) (k2 , p2) = Σ-bycomponents (succ-inj (+-inj n (p1 · inv p2)) , nat-isSet _ _ _ _)

open Naturals public
\end{code}

#### Integers

\begin{code}
module Integers where

  data ℤ : Type₀ where
    zer : ℤ
    pos : ℕ → ℤ
    neg : ℕ → ℤ

  -- Inclusion of the natural numbers into the integers
  NtoZ : ℕ → ℤ
  NtoZ zero     = zer
  NtoZ (succ n) = pos n

  -- Successor function
  zsucc : ℤ → ℤ
  zsucc zer            = pos 0
  zsucc (pos x)        = pos (succ x)
  zsucc (neg zero)     = zer
  zsucc (neg (succ x)) = neg x

  -- Predecessor function
  zpred : ℤ → ℤ
  zpred zer            = neg 0
  zpred (pos zero)     = zer
  zpred (pos (succ x)) = pos x
  zpred (neg x)        = neg (succ x)

  -- Successor and predecessor
  zsuccpred-id : (n : ℤ) → zsucc (zpred n) == n
  zsuccpred-id zer            = refl _
  zsuccpred-id (pos zero)     = refl _
  zsuccpred-id (pos (succ n)) = refl _
  zsuccpred-id (neg n)        = refl _

  zpredsucc-id : (n : ℤ) → zpred (zsucc n) == n
  zpredsucc-id zer            = refl _
  zpredsucc-id (pos n)        = refl _
  zpredsucc-id (neg zero)     = refl _
  zpredsucc-id (neg (succ n)) = refl _

  zpredsucc-succpred : (n : ℤ) → zpred (zsucc n) == zsucc (zpred n)
  zpredsucc-succpred zer = refl zer
  zpredsucc-succpred (pos zero) = refl (pos zero)
  zpredsucc-succpred (pos (succ x)) = refl (pos (succ x))
  zpredsucc-succpred (neg zero) = refl (neg zero)
  zpredsucc-succpred (neg (succ x)) = refl (neg (succ x))

  zsuccpred-predsucc : (n : ℤ) → zsucc (zpred n) == zpred (zsucc n)
  zsuccpred-predsucc n = inv (zpredsucc-succpred n)

  -- Equivalence given by successor and predecessor
  zequiv-succ : ℤ ≃ ℤ
  zequiv-succ = qinv-≃ zsucc (zpred , (zsuccpred-id , zpredsucc-id))

  -- Negation
  - : ℤ → ℤ
  - zer     = zer
  - (pos x) = neg x
  - (neg x) = pos x

  double- : (z : ℤ) → - (- z) == z
  double- zer = refl _
  double- (pos x) = refl _
  double- (neg x) = refl _

  zequiv- : ℤ ≃ ℤ
  zequiv- = qinv-≃ - (- , (double- , double-))

  -- Addition on integers
  infixl 60 _+ᶻ_
  _+ᶻ_ : ℤ → ℤ → ℤ
  zer +ᶻ m = m
  pos zero +ᶻ m = zsucc m
  pos (succ x) +ᶻ m = zsucc (pos x +ᶻ m)
  neg zero +ᶻ m = zpred m
  neg (succ x) +ᶻ m = zpred (neg x +ᶻ m)

  -- Lemmas on addition
  +ᶻ-lunit : (n : ℤ) → n == n +ᶻ zer
  +ᶻ-lunit zer            = refl _
  +ᶻ-lunit (pos zero)     = refl _
  +ᶻ-lunit (pos (succ x)) = ap zsucc (+ᶻ-lunit (pos x))
  +ᶻ-lunit (neg zero)     = refl _
  +ᶻ-lunit (neg (succ x)) = ap zpred (+ᶻ-lunit (neg x))


  +ᶻ-unit-zsucc : (n : ℤ) → zsucc n == (n +ᶻ pos zero)
  +ᶻ-unit-zsucc zer = refl _
  +ᶻ-unit-zsucc (pos zero) = refl _
  +ᶻ-unit-zsucc (pos (succ x)) = ap zsucc (+ᶻ-unit-zsucc (pos x))
  +ᶻ-unit-zsucc (neg zero) = refl _
  +ᶻ-unit-zsucc (neg (succ x)) = inv (zpredsucc-id (neg x)) · ap zpred (+ᶻ-unit-zsucc (neg x))

  +ᶻ-unit-zpred : (n : ℤ) → zpred n == (n +ᶻ neg zero)
  +ᶻ-unit-zpred zer = refl _
  +ᶻ-unit-zpred (pos zero) = refl zer
  +ᶻ-unit-zpred (pos (succ x)) = inv (zsuccpred-id (pos x)) · ap zsucc (+ᶻ-unit-zpred (pos x))
  +ᶻ-unit-zpred (neg zero) = refl _
  +ᶻ-unit-zpred (neg (succ x)) = ap zpred (+ᶻ-unit-zpred (neg x))


  +ᶻ-pos-zsucc : (n : ℤ) → (x : ℕ) → zsucc (n +ᶻ pos x) == n +ᶻ pos (succ x)
  +ᶻ-pos-zsucc zer x = refl _
  +ᶻ-pos-zsucc (pos zero) x = refl _
  +ᶻ-pos-zsucc (pos (succ n)) x = ap zsucc (+ᶻ-pos-zsucc (pos n) x)
  +ᶻ-pos-zsucc (neg zero) x = zsuccpred-id (pos x)
  +ᶻ-pos-zsucc (neg (succ n)) x = zsuccpred-predsucc (neg n +ᶻ pos x) · ap zpred (+ᶻ-pos-zsucc (neg n) x)

  +ᶻ-neg-zpred : (n : ℤ) → (x : ℕ) → zpred (n +ᶻ neg x) == n +ᶻ neg (succ x)
  +ᶻ-neg-zpred zer x = refl _
  +ᶻ-neg-zpred (pos zero) x = zpredsucc-id (neg x)
  +ᶻ-neg-zpred (pos (succ n)) x = zpredsucc-succpred (pos n +ᶻ neg x) · ap zsucc (+ᶻ-neg-zpred (pos n) x)
  +ᶻ-neg-zpred (neg zero) x = refl _
  +ᶻ-neg-zpred (neg (succ n)) x = ap zpred (+ᶻ-neg-zpred (neg n) x)

  +ᶻ-comm : (n m : ℤ) → n +ᶻ m == m +ᶻ n
  +ᶻ-comm zer m = +ᶻ-lunit m
  +ᶻ-comm (pos zero) m = +ᶻ-unit-zsucc m
  +ᶻ-comm (pos (succ x)) m = ap zsucc (+ᶻ-comm (pos x) m) · +ᶻ-pos-zsucc m x
  +ᶻ-comm (neg zero) m = +ᶻ-unit-zpred m
  +ᶻ-comm (neg (succ x)) m = ap zpred (+ᶻ-comm (neg x) m) · +ᶻ-neg-zpred m x



  -- Decidable equality
  pos-inj : {n m : ℕ} → pos n == pos m → n == m
  pos-inj {n} {.n} idp = refl n

  neg-inj : {n m : ℕ} → neg n == neg m → n == m
  neg-inj {n} {.n} idp = refl n

  z-decEq : decEq ℤ
  z-decEq zer zer = inl (refl zer)
  z-decEq zer (pos x) = inr (λ ())
  z-decEq zer (neg x) = inr (λ ())
  z-decEq (pos x) zer = inr (λ ())
  z-decEq (pos n) (pos m) with (nat-decEq n m)
  z-decEq (pos n) (pos m) | inl p = inl (ap pos p)
  z-decEq (pos n) (pos m) | inr f = inr (f ∘ pos-inj)
  z-decEq (pos n) (neg m) = inr (λ ())
  z-decEq (neg n) zer = inr (λ ())
  z-decEq (neg n) (pos x₁) = inr (λ ())
  z-decEq (neg n) (neg m) with (nat-decEq n m)
  z-decEq (neg n) (neg m) | inl p = inl (ap neg p)
  z-decEq (neg n) (neg m) | inr f = inr (f ∘ neg-inj)

  z-isSet : isSet ℤ
  z-isSet = hedberg z-decEq


  -- Multiplication
  infixl 60 _*ᶻ_
  _*ᶻ_ : ℤ → ℤ → ℤ
  zer *ᶻ m = zer
  pos zero *ᶻ m = m
  pos (succ x) *ᶻ m = (pos x *ᶻ m) +ᶻ m
  neg zero *ᶻ m = - m
  neg (succ x) *ᶻ m = (neg x *ᶻ m) +ᶻ (- m)


  -- Ordering
  _<ᶻ_ : ℤ → ℤ → Type₀
  zer <ᶻ zer = ⊥
  zer <ᶻ pos x = ⊤
  zer <ᶻ neg x = ⊥
  pos x <ᶻ zer = ⊥
  pos x <ᶻ pos y = x <ₙ y
  pos x <ᶻ neg y = ⊥
  neg x <ᶻ zer = ⊤
  neg x <ᶻ pos y = ⊤
  neg x <ᶻ neg y = y <ₙ x

open Integers
\end{code}

### Integer action

\begin{code}
module IntegerAction {ℓ} {M : Type ℓ} (grpst : GroupStructure M) where

  open GroupStructure grpst

    -- Integers acting on a group structure M.
  z-act : ℤ → M → M
  z-act zer            m = e
  z-act (pos zero)     m = m
  z-act (pos (succ x)) m = z-act (pos x) m * m
  z-act (neg zero)     m = ginv m
  z-act (neg (succ x)) m = (z-act (neg x) m) * ginv m


  -- Lemmas on how integers act on a group.
  zsucc-act : ∀ n a → z-act (zsucc n) a == (z-act n a * a)
  zsucc-act zer a = inv (lunit a)
  zsucc-act (pos x) a = refl _
  zsucc-act (neg zero) a = inv (grinv a)
  zsucc-act (neg (succ n)) a =
    begin
      z-act (neg n) a                   ==⟨ inv (runit (z-act (neg n) a)) ⟩
      z-act (neg n) a * e               ==⟨ ap (λ section → _*_ (z-act (neg n) a) section) (inv (grinv a)) ⟩
      z-act (neg n) a * (ginv a * a)    ==⟨ assoc (z-act (neg n) a) (ginv a) a ⟩
      ((z-act (neg n) a * ginv a) * a)
    ∎

  zpred-act : ∀ n a → z-act (zpred n) a == (z-act n a * ginv a)
  zpred-act zer a = inv (lunit (ginv a))
  zpred-act (pos zero) a = inv (glinv a)
  zpred-act (pos (succ x)) a =
    begin
      z-act (zpred (pos (succ x))) a   ==⟨ refl _ ⟩
      z-act (pos x) a                  ==⟨ inv (runit _) ⟩
      z-act (pos x) a * e              ==⟨ ap (λ section → _*_ (z-act (pos x) a) section) (inv (glinv a)) ⟩
      z-act (pos x) a * (a * ginv a)   ==⟨ assoc (z-act (pos x) a) a (ginv a) ⟩
      (z-act (pos x) a * a) * ginv a   ==⟨ refl _ ⟩
      z-act (pos (succ x)) a * ginv a
    ∎
  zpred-act (neg x) a = refl _


  act-zsucc : ∀ n a → z-act (zsucc n) a == (a * z-act n a)
  act-zsucc zer a = inv (runit a)
  act-zsucc (pos zero) a = refl _
  act-zsucc (pos (succ x)) a =
    begin
       ((z-act (pos x) a * a) * a) ==⟨ ap (λ u → u * a) (act-zsucc (pos x) a) ⟩
       ((a * z-act (pos x) a) * a) ==⟨ inv (assoc a (z-act (pos x) a) a) ⟩
       (a * (z-act (pos x) a * a))
    ∎
  act-zsucc (neg zero) a = inv (glinv a)
  act-zsucc (neg (succ x)) a =
    begin
       z-act (neg x) a                    ==⟨ inv (runit (z-act (neg x) a)) ⟩
       (z-act (neg x) a) * e              ==⟨ ap (λ section → _*_ (z-act (neg x) a) section) (inv (glinv a)) ⟩
       (z-act (neg x) a) * (a * ginv a)   ==⟨ assoc (z-act (neg x) a) a (ginv a) ⟩
       ((z-act (neg x) a) * a) * ginv a   ==⟨ ap (λ s → s * (ginv a)) (inv (zsucc-act (neg x) a)) ⟩
       (z-act (zsucc (neg x)) a) * ginv a ==⟨ ap (λ s → s * (ginv a)) (act-zsucc (neg x) a) ⟩
       (a * (z-act (neg x) a)) * ginv a   ==⟨ inv (assoc a (z-act (neg x) a) (ginv a)) ⟩
       (a * (z-act (neg x) a * ginv a))
    ∎

  act-zpred : ∀ n a → z-act (zpred n) a == (ginv a * z-act n a)
  act-zpred n a =
    begin
      z-act (zpred n) a  ==⟨ inv (lunit (z-act (zpred n) a)) ⟩
      e * z-act (zpred n) a  ==⟨ ap (λ section → _*_ section (z-act (zpred n) a)) (inv (grinv a)) ⟩
      (ginv a * a) * z-act (zpred n) a  ==⟨ inv (assoc _ a _) ⟩
      ginv a * (a * z-act (zpred n) a)  ==⟨ ap (λ section → _*_ (ginv a) section) (inv (act-zsucc (zpred n) a)) ⟩
      ginv a * z-act (zsucc (zpred n)) a ==⟨ ap (λ u → (ginv a * (z-act u a))) (zsuccpred-id n) ⟩
      ginv a * z-act n a
    ∎

  z-act+ : ∀ n m a → z-act (n +ᶻ m) a == (z-act n a * z-act m a)
  z-act+ zer m a = inv (lunit (z-act m a))
  z-act+ (pos zero) m a = act-zsucc m a
  z-act+ (pos (succ x)) m a =
    begin
      z-act (zsucc (pos x +ᶻ m)) a        ==⟨ act-zsucc (pos x +ᶻ m) a ⟩
      a * z-act (pos x +ᶻ m) a            ==⟨ ap (λ s → a * s) (z-act+ (pos x) m a) ⟩
      a * (z-act (pos x) a * z-act m a)   ==⟨ assoc a (z-act (pos x) a) (z-act m a) ⟩
      (a * z-act (pos x) a) * z-act m a   ==⟨ ap (_* z-act m a) (inv (act-zsucc (pos x) a)) ⟩
      (z-act (pos (succ x)) a) * z-act m a
    ∎
  z-act+ (neg zero) m a = act-zpred m a
  z-act+ (neg (succ x)) m a =
    begin
      z-act (zpred (neg x +ᶻ m)) a             ==⟨ act-zpred (neg x +ᶻ m) a ⟩
      ginv a * z-act (neg x +ᶻ m) a            ==⟨ ap (λ section → _*_ (ginv a) section) (z-act+ (neg x) m a) ⟩
      ginv a * (z-act (neg x) a * z-act m a)  ==⟨ assoc (ginv a) (z-act (neg x) a) (z-act m a) ⟩
      (ginv a * z-act (neg x) a) * z-act m a  ==⟨ inv (ap (λ s → s * (z-act m a)) (act-zpred (neg x) a)) ⟩
      z-act (neg (succ x)) a * z-act m a
    ∎

open IntegerAction public
\end{code}

## Higher inductive types

### Interval

Interval. An interval is defined by taking two points (two elements) and a path
between them (an element of the equality type). The path is nontrivial.

\begin{code}
module Interval where

  private
    -- The interval is defined as a type with a nontrivial equality
    -- between its two elements.
    data !I : Type₀ where
      !Izero : !I
      !Ione : !I

  I : Type₀
  I = !I

  Izero : I
  Izero = !Izero

  Ione : I
  Ione = !Ione

  postulate
    seg : Izero == Ione

  -- Recursion principle on points.
  I-rec : ∀ {ℓ} {A : Type ℓ}
        → (a b : A)
        → (p : a == b)
        --------------
        → (I → A)
  I-rec a _ _ !Izero = a
  I-rec _ b _ !Ione  = b

  -- Recursion principle on paths.
  postulate
    I-βrec : ∀ {ℓ}
      → (A : Type ℓ)
      → (a b : A)
      → (p : a == b)
      ---------------------------
      → ap (I-rec a b p) seg == p

open Interval public
\end{code}

### Circle

The circle type is constructed by postulating a type with
a single element (base) and a nontrivial path (loop).

\begin{code}
module Circle where

  private
    data !S¹ : Type₀ where
      !base : !S¹

  S¹ : Type₀
  S¹ = !S¹

  base : S¹
  base = !base

  -- Nontrivial path on the circle.
  postulate
    loop : base == base

  -- Recursion principle on points
  S¹-rec : ∀ {ℓ}
         → (A : Type ℓ)
         → (a : A)
         → (p : a == a)
         --------------
         → (S¹ → A)
  S¹-rec A a p !base = a

  -- Recursion principle on paths
  postulate
    S¹-βrec : ∀ {ℓ} (A : Type ℓ)
            → (a : A)
            → (p : a == a)
            ------------------------------
            → ap (S¹-rec A a p) loop == p

  -- Induction principle on points
  S¹-ind : ∀ {ℓ} (P : S¹ → Type ℓ)
         → (x : P base)
         → (x == x [ P ↓ loop ])
         --------------------------
         → ((t : S¹) → P t)
  S¹-ind P x p !base = x

  -- Induction principle on paths
  postulate
    S¹-βind : ∀{ℓ} (P : S¹ → Type ℓ)
            → (x : P base)
            → (p : x == x [ P ↓ loop ])
            -------------------------------
            → apd (S¹-ind P x p) loop == p

\end{code}


### Suspension

\begin{code}
module Suspension where

  module S where

  private
    data Suspₚ {ℓ} (A : Type ℓ) : Type ℓ where
      Nₚ : Suspₚ A
      Sₚ : Suspₚ A

    data Suspₓ {ℓ} (A : Type ℓ) : Type ℓ where
      mkSusp : Suspₚ A → (𝟙 → 𝟙) → Suspₓ A

  Susp = Suspₓ

  -- point-constructors
  North : ∀ {ℓ} {A : Type ℓ} → Susp A
  North = mkSusp Nₚ _

  South : ∀ {ℓ} {A : Type ℓ} → Susp A
  South = mkSusp Sₚ _

  -- path-constructors
  postulate
    merid : ∀ {ℓ} {A : Type ℓ}
          → A
          → Path {ℓ}{Susp A} North South

  -- Recursion principle on points
  Susp-rec : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ}{C : Type ℓⱼ}
           → (cₙ cₛ  : C)
           → (merid' : A → cₙ == cₛ)
           ------------------------
           → (Susp A → C)
  Susp-rec cₙ _ _ (mkSusp Nₚ _) = cₙ
  Susp-rec _ cₛ _ (mkSusp Sₚ _) = cₛ

  -- Recursion principle on paths
  postulate
    Susp-βrec : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ}{C : Type ℓⱼ}
              → {cₙ cₛ : C} {mer : A → cₙ == cₛ}
              → {a : A}
              -------------------------------------------
              → ap (Susp-rec cₙ cₛ mer) (merid a) == mer a

  -- Induction principle on points
  Susp-ind : ∀ {ℓ} {A : Type ℓ} (C : Susp A → Type ℓ)
              → (N' : C North)
              → (S' : C South)
              → (merid' : (x : A) → N' == S' [ C ↓ (merid x) ])
              --------------------------------------------------
              → ((x : Susp A) → C x)

  Susp-ind _ N' S' _ (mkSusp Nₚ _) = N'
  Susp-ind _ N' S' _ (mkSusp Sₚ _) = S'

  -- Induction principle on paths
  postulate
    Susp-βind : ∀ {ℓ} {A : Type ℓ} (C : Susp A → Type ℓ)
              → (N' : C North)
              → (S' : C South)
              → (merid' : (x : A) → N' == S' [ C ↓ (merid x)]) {x : A}
              --------------------------------------------------------
              → apd (Susp-ind C N' S' merid') (merid x) == merid' x

open Suspension
\end{code}

## Fundamental group

Definition of the fundamental group of a type.
Let a:A be one point of the type. The fundamental group on a is the
group given by proofs of the equality (a=a).

\begin{code}
module FundamentalGroup where

  -- Definition of the fundamental group.
  Ω : ∀{ℓ} (A : Type ℓ) → (a : A) → Type ℓ
  Ω A a = (a == a)

  -- Its group structure.
  Ω-st : ∀{ℓ} (A : Type ℓ) → (a : A) → GroupStructure (Ω A a)
  Ω-st A a = group-structure _·_ (refl a)
    (λ a → inv (·-lunit a)) (λ a → inv (·-runit a))
    (λ x y z → inv (·-assoc x y z))
    inv ·-rinv ·-linv

  Ω-gr : ∀{ℓ} (A : Type ℓ) → (a : A) → Group {ℓ}
  Ω-gr A a = group (a == a) (Ω-st A a)

  Ω-st-r : ∀{ℓ} (A : Type ℓ) → (a : A) → GroupStructure (Ω A a)
  Ω-st-r A a = group-structure (λ x y → y · x) (refl a)
    (λ a → inv (·-runit a)) (λ a → inv (·-lunit a))
    (λ x y z → ·-assoc z y x)
    inv ·-linv ·-rinv
open FundamentalGroup public
\end{code}

### Circle fundamental group

\begin{code}
module FundGroupCircle where
  open Circle
  -- Winds a loop n times on the circle.
  loops : ℤ → Ω S¹ base
  loops n = z-act (Ω-st S¹ base) n loop

  private
  -- Uses univalence to unwind a path over the integers.
    code : S¹ → Type₀
    code = S¹-rec Type₀ ℤ (ua zequiv-succ)

  tcode-succ : (n : ℤ) → transport code loop n == zsucc n
  tcode-succ n =
    begin
      transport code loop n ==⟨ refl _ ⟩
      transport ((λ a → a) ∘ code) loop n ==⟨ transport-family loop n ⟩
      transport (λ a → a) (ap code loop) n ==⟨ ap (λ u → transport (λ a → a) u n) (S¹-βrec _ ℤ (ua zequiv-succ)) ⟩
      transport (λ a → a) (ua zequiv-succ) n ==⟨ ap (λ e → (lemap e) n) (ua-β zequiv-succ) ⟩
      zsucc n
    ∎

  tcode-pred : (n : ℤ) → transport code (inv loop) n == zpred n
  tcode-pred n =
    begin
      transport code (inv loop) n
        ==⟨ refl _ ⟩
      transport ((λ a → a) ∘ code) (inv loop) n
        ==⟨ transport-family (inv loop) n ⟩
      transport (λ a → a) (ap code (inv loop)) n
        ==⟨ ap (λ u → transport (λ a → a) u n) (ap-inv code loop) ⟩
      transport (λ a → a) (inv (ap code loop)) n
        ==⟨ ap (λ u → transport (λ a → a) (inv u) n) (S¹-βrec _ ℤ (ua zequiv-succ)) ⟩
      transport (λ a → a) (inv (ua zequiv-succ)) n
        ==⟨ ap (λ u → transport (λ a → a) u n) (inv (ua-inv zequiv-succ)) ⟩
      transport (λ a → a) (ua (invEqv zequiv-succ)) n
        ==⟨ ap (λ e → (lemap e) n) ((ua-β (invEqv zequiv-succ))) ⟩
      zpred n
    ∎

  private
    encode : (x : S¹) → (base == x) → code x
    encode x p = transport code p zer

    decode : (x : S¹) → code x → (base == x)
    decode = S¹-ind (λ x → (code x → (base == x))) loops (
      begin
        transport (λ x → code x → base == x) loop loops
          ==⟨ transport-fun loop loops ⟩
        transport (λ x → base == x) loop ∘ (loops ∘ transport code (inv loop))
          ==⟨ ap (λ u → u ∘ (loops ∘ transport code (inv loop))) (funext λ p → transport-concat-r loop p) ⟩
        (_· loop) ∘ (loops ∘ transport code (inv loop))
          ==⟨ ap (λ u → (_· loop) ∘ (loops ∘ u)) (funext tcode-pred) ⟩
        (_· loop) ∘ (loops ∘ zpred)
          ==⟨ funext lemma ⟩
        loops
      ∎)
      where
        lemma : (n : ℤ) → ((_· loop) ∘ (loops ∘ zpred)) n == loops n
        lemma zer            = ·-linv loop
        lemma (pos zero)     = refl _
        lemma (pos (succ x)) = refl _
        lemma (neg zero) =
          ·-assoc (inv loop) (inv loop) loop ·
          ap (inv loop ·_) (·-linv loop) ·
          inv (·-runit (inv _))
        lemma (neg (succ x)) =
          ·-assoc (loops (neg x) · inv loop) _ loop ·
          ap ((loops (neg x) · (inv loop)) ·_) (·-linv loop) ·
          inv (·-runit _)

    decode-encode : (x : S¹) → (p : base == x) → decode x (encode x p) == p
    decode-encode .base idp = refl (refl base)

    encode-decode : (x : S¹) → (c : code x) → encode x (decode x c) == c
    encode-decode x = S¹-ind
        ((λ y → (c : code y) → encode y (decode y c) == c))
        lemma (funext λ _ → z-isSet _ _ _ _) x
      where
        lemma : (n : ℤ) → encode base (loops n) == n
        lemma zer = refl zer
        lemma (pos 0) = tcode-succ zer
        lemma (pos (succ n)) =
          inv (transport-comp-h (loops (pos n)) loop zer) ·
          ap (transport code loop) (lemma (pos n)) ·
          tcode-succ _
        lemma (neg zero) = tcode-pred zer
        lemma (neg (succ n)) =
          inv (transport-comp-h (loops (neg n)) (inv loop) zer) ·
          ap (transport code (inv loop)) (lemma (neg n)) ·
          tcode-pred _

  -- Creates an equivalence between paths and encodings.
  equiv-family : (x : S¹) → (base == x) ≃ code x
  equiv-family x = qinv-≃ (encode x) (decode x , (encode-decode x , decode-encode x))


  -- The fundamental group of the circle is the integers.  In this
  -- proof, univalence is crucial. The next lemma will prove that the
  -- equivalence in fact preserves the group structure.
  fundamental-group-of-the-circle : Ω S¹ base ≃ ℤ
  fundamental-group-of-the-circle = equiv-family base

  preserves-composition : ∀ n m → loops (n +ᶻ m) == loops n · loops m
  preserves-composition n m = z-act+ (Ω-st S¹ base) n m loop
\end{code}

## Agda references

We based on the following Agda libraries.

{: .links}

  - (Mostly all code from) basic homotopy type theory in Agda: [agda-hott](https://mroman42.github.io/ctlc/agda-hott/Total.html).
  - Higher Inductive types in `hott-agda` from https://github.com/dlicata335/hott-agda/
