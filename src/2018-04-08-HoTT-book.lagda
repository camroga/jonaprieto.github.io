---
layout: "post"
title: "HoTT-Book Exercises"
date: "2018-04-08"
categories: type-theory
---

This is a self-contained version of some solutions for HoTT-Book's exercises.
The idea is to unpackage all as long as possible to get a better understanding.
Many changes can be appear running this experiment. The solutions are
type-checked as a whole using Agda v2.5.3.


## Requirements

-------------------------------------------------------------------------------

An Agda pragma for consistency with HoTT:

\begin{code}
{-# OPTIONS --without-K #-}
\end{code}

-------------------------------------------------------------------------------


Equality type defintion also called Identity type:

\begin{code}
infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
  \end{code}

Some functions to work with this type:

\begin{code}
sym : ∀ {i} {A : Set i} {x y : A}
    → x ≡ y → y ≡ x
sym refl = refl

_·_ : ∀ {i}{X : Set i}{x y z : X}
    → x ≡ y → y ≡ z → x ≡ z
refl · p = p
infixl 9 _·_

ap : ∀ {i j}{A : Set i}{B : Set j}{x y : A}
   → (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

subst : ∀ {i j} {A : Set i}{x y : A}
      → (B : A → Set j) → x ≡ y
      → B x → B y
subst B refl = (λ z → z)
\end{code}

Path induction:

\begin{code}
J' : ∀ {i j}{X : Set i}{x : X}
   → (P : (y : X) → x ≡ y → Set j)
   → P x refl
   → (y : X)
   → (p : x ≡ y)
   → P y p
J' P u y refl = u

J : ∀ {i j}{X : Set i}
  → (P : (x y : X) → x ≡ y → Set j)
  → ((x : X) → P x x refl)
  → (x y : X)
  → (p : x ≡ y)
  → P x y p
J P u x y p = J' (P x) (u x) y p
\end{code}

## Chapter 1

### Exercise 1.1

<div class="exercise">
Given functions $$f : A \to B$$ and $$g:B\to C$$, define
their composite $$ g\circ f:A\to C$$.
</div>

\begin{code}
_∘_ : ∀ {i j k} {A : Set i}{B : Set j}{C : Set k}
    → (B → C)
    → (A → B)
    → A → C
g ∘ f = λ x → g (f x)
\end{code}
<div class="exercise">
Show that we have $$h \circ (g\circ f) \equiv (h\circ g)\circ f$$.
</div>
\begin{code}
∘-assoc : ∀ {i j k l} {A : Set i}{B : Set j}{C : Set k}{D : Set l}
        → (h : C → D)(g : B → C)(f : A → B)
        → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
∘-assoc f g h = refl
\end{code}

### Exercise 1.2

<div class="exercise">
Derive the recursion principle for products $$\mathsf{rec}_{A\times B}$$
using only the projections, and verify that the definitional equalities
are valid. Do the same for $$\Sigma$$-types.
</div>

Let's add some machinery to handle levels of the universe needed for
the following exercises including this one:

\begin{code}
open import Agda.Primitive public
  using    (Level; _⊔_; lzero; lsuc)
\end{code}

To solve this problem we need:

  - Σ-type definition

  - Product type definition

  - Review the recursion principle, what exactly it consists of.
    Maybe this refresh our minds (see Pp. 42 HoTT-Book).

    <p class="equation">
    $$ \mathsf{rec}_{\sum\limits_{(x : A) } B(x)} : \prod\limits_{(C : U)} (\Pi_{(x : A)} B(x) \rightarrow C) \rightarrow \sum_{(x : A)} B(x) \rightarrow C $$
    </p>

-------------------------------------------------------------------------------

Σ-type (sigma type) definition (see the definition without projections
[here](https://github.com/jonaprieto/hott-book/blob/master/other/prelim.agda#L20)):

\begin{code}
module Σ-def₁ where

  record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B proj₁
  open Σ public
-- _,_ : (proj₁ : A) → B proj₁ → Σ A B.
\end{code}

Its recursor with a function $$g : \prod_{(x : A)} B(x)\rightarrow C$$
that we provide.

\begin{code}
module Σ-Rec {i j k}{A : Set i}{B : A → Set j}{C : Set k}
             (g : (x : A) → B x → C) where
  open Σ-def₁ using (Σ ; proj₁; proj₂; _,_ )

  Σ-rec : Σ A B → C
  Σ-rec p = g (proj₁ p) (proj₂ p)

  Σ-rec-β : (x : A)(y : B x) → Σ-rec (x , y) ≡ g x y
  Σ-rec-β x y = refl
\end{code}

-------------------------------------------------------------------------------

On the other hand, the product type is just a particular case of the sigma type
when the codomain is not dependent, as we can see next by omitting the argument
in `(λ _ → B)`.

\begin{code}
module ×-def₁ where
  open Σ-def₁ public

  _×_ : {l k : Level} (A : Set l) (B : Set k) → Set (l ⊔ k)
  A × B = Σ A (λ _ → B)
\end{code}

Its recursor with a function $$g : A \rightarrow B \rightarrow C$$ that we provide.

\begin{code}
module ×-Rec {i j k}{A : Set i}{B : Set j}{C : Set k}
           (g : A → B → C) where
  open ×-def₁ using (_×_; proj₁; proj₂; _,_)

  ×-rec : A × B → C
  ×-rec p = g (proj₁ p) (proj₂ p)

  ×-rec-β : (x : A)(y : B) → ×-rec (x , y) ≡ g x y
  ×-rec-β x y = refl
\end{code}

### Exercise 1.3

<p class="exercise">
Derive the induction principle for products $$\mathsf{ind}_{A\times B}$$,
using only the projections and the propositional uniqueness principle
$$\mathsf{uniq}_{A\times B}$$.
Verify that the definitional equalities are valid.
</p>

To solve this problem, recall the uniqueness principle (Pp. 29. HoTT-Book)

- The **propositional uniqueness principle** says that
every element of $$A\times B$$ is equal to a pair.

<p class="equation">
$$\mathsf{uniq}_{A\times B} : \prod_{(x : A \times B)} ((pr_{1}(x) , pr_{2}(x)) \equiv_{A\times B} x).$$
</p>

Product type definition using `data`:

\begin{code}
-- this would be trivial in agda due to definitional η for records
-- so Capriotti defined a product type without η:
module ×-def₂ where

  data _×_ {i j}(A : Set i)(B : Set j) : Set (i ⊔ j) where
    _,_ : A → B → A × B

  proj₁ : ∀ {i j}{A : Set i}{B : Set j}
        → A × B → A
  proj₁ (a , b) = a

  proj₂ : ∀ {i j}{A : Set i}{B : Set j}
        → A × B → B
  proj₂ (a , b) = b
\end{code}

Projections and $$\mathsf{uniq}_{A\times B}$$:

\begin{code}
module ×-fun₂ {i j}{A : Set i}{B : Set j} where
  open ×-def₂
  -- unique principle *propositional uniqueness principle*
  uppt : (x : A × B) → (proj₁ x , proj₂ x) ≡ x
  uppt (a , b) = refl
\end{code}

Its induction principle:

<p class="equation">
$$\mathsf{ind}_{A\times B} : \prod\limits_{C : A \times B \to \mathcal{U}}
\left( \prod\limits_{x:A}\ \prod\limits_{y:B}\ \,C( (x,y) ) \right) \to \prod\limits_{x:A \times B}\ \,C(x)$$
</p>

\begin{code}
module ×-Ind {i j}{A : Set i}{B : Set j} where
  open ×-def₂ using (_×_; _,_;proj₁;proj₂)
  open ×-fun₂ using (uppt)

  ×-ind : ∀ {k}(C : A × B → Set k)
        → ((x : A)(y : B) → C (x , y))
        → (x : A × B) → C x
  ×-ind C g x = subst C (uppt x) (g (proj₁ x) (proj₂ x))

  ×-ind-β : ∀ {k} (C : A × B → Set k)
          → (g : (x : A)(y : B) → C (x , y))
          → (x : A)(y : B)
          → ×-ind C g (x , y) ≡ g x y
  ×-ind-β C g x y = refl
\end{code}

<p class="exercise">
Generalize $$\mathsf{uniq}_{A\times B}$$ to Σ-types, and do the same for
$$\Sigma$$-types, i.e. show induction and verify the definitional equality
is valid.
</p>

Σ-type definition using `data`:


\begin{code}
module Σ-def₂ where

  data Σ {i j}(A : Set i)(B : A → Set j) : Set (i ⊔ j) where
    _,_ : (x : A) → B x → Σ A B
\end{code}

\begin{code}
module Σ-fun₂ {i j } {A : Set i}{B : A → Set j} where
  open Σ-def₂ using (Σ; _,_ )

  proj₁ : Σ A B → A
  proj₁ (a , b) = a

  proj₂ : (x : Σ A B) → B (proj₁ x)
  proj₂ (a , b) = b

  uppt : (x : Σ A B) → (proj₁ x , proj₂ x) ≡ x
  uppt (a , b) = refl
\end{code}

Its induction principle:

\begin{code}
module Σ-Ind {i j}{A : Set i}{B : A → Set j} where
  open Σ-def₂ public
  open Σ-fun₂ public

  Σ-ind : (C : Σ A B → Set (i ⊔ j))
        → ((x : A)(y : B x) → C (x , y))
        → (x : Σ A B) → C x
  Σ-ind C g (a , b) = g a b

  Σ-ind-β : (C : Σ A B → Set (i ⊔ j))
          → (g : (x : A)(y : B x) → C (x , y))
          → (x : A) (y : B x)
          → (Σ-ind C g (x , y)) ≡ g x y
  Σ-ind-β C g x y = refl
\end{code}

### Exercise 1.4

<div class="exercise">
Assuming as given only the <em>iterator</em> for natural numbers
<p class="equation">
$$\mathsf{ite} : \prod\limits_{C:\mathcal{U}} C \to (C \to C) \to \mathbb{N} \to C $$
</p>
with the defining equations
<p class="equation">
$$
\begin{align*}
\mathsf{ite}(C,c_0,c_s,0)               &\equiv c_0, \\
\mathsf{ite}(C,c_0,c_s,\mathsf{suc}(n)) &\equiv c_s(\mathsf{ite}(C,c_0,c_s,n)),
\end{align*}
$$
</p>
derive a function having the type of the recursor $$\mathsf{rec}{\mathbb{N}}$$.
Show that the defining equations of the recursor hold propositionally for this
function, using the induction principle for $$\mathbb{N}$$.
</div>

To solve this problem, let us define the recursor and also the induction principle
for natural numbers. (See more details in
[Induction on Natural Numbers]({% post_url 2018-02-12-induction-on-natural-numbers %})).

\begin{code}
module ℕ-def where

  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

  recℕ : ∀ (C : Set) → C → (ℕ → C → C) → ℕ → C
  recℕ C c₀ cₛ zero    = c₀
  recℕ C c₀ cₛ (suc n) = cₛ n (recℕ C c₀ cₛ n)

  indℕ : ∀ (C : ℕ → Set)
       → (C zero)
       → (∀ (n : ℕ) → C n → C (suc n))
       → (∀ (n : ℕ) → C n)
  indℕ C c₀ cₛ zero    = c₀
  indℕ C c₀ cₛ (suc n) = cₛ n (indℕ C c₀ cₛ n)
\end{code}

Now, we define the iterator function:

\begin{code}
module ℕ-fun where
  open ℕ-def using ( ℕ; recℕ; zero; suc)

  ite : ∀ (C : Set) → C → (C → C) → ℕ → C
  ite C c₀ cₛ zero    = c₀
  ite C c₀ cₛ (suc n) = cₛ (ite C c₀ cₛ n)
\end{code}

Then, we now can define the recursor using this iterator function `ite`
as follows:

\begin{code}
-- recursor
  open ×-def₂ using (_×_; proj₁; proj₂; _,_)

  rec₂ℕ : ∀ (C : Set) → C → (ℕ → C → C) → ℕ → (ℕ × C)
  rec₂ℕ C c₀ cₛ n =
      (ite (ℕ × C)
           (zero , c₀)
           (λ (p : ℕ × C) → (suc (proj₁ p) , cₛ (proj₁ p) (proj₂ p)))
           n)
\end{code}

Now, we need to establish the propositional equality between these two
definitions for the recursor, i.e, `recℕ` and `rec₂ℕ`. This can be proved by
induction.

\begin{code}
open ℕ-def public
open ℕ-fun public
postulate
  C : Set
  c₀ : C
  m : ℕ
  cₛ : ℕ → C → C

n = suc m
module exC1n4  where
  open ℕ-def using (ℕ; zero; suc; recℕ; indℕ)
  open ℕ-fun using (ite; rec₂ℕ)
  open ×-def₂ using (_×_; proj₁; proj₂; _,_)

  up : ∀ {A B : Set} → (u : A × B) → (proj₁ u , proj₂ u) ≡ u
  up (a , b ) = refl

  lem : (C : Set)(c₀ : C)(cₛ : ℕ → C → C)
      → ∀ (n : ℕ) → rec₂ℕ C c₀ cₛ (suc n) ≡ (suc n , cₛ n (proj₂ (rec₂ℕ C c₀ cₛ n)))
  lem C c₀ cₛ n = {!   !}

  proof : (C : Set)(c₀ : C)(cₛ : ℕ → C → C)
        → ∀ (n : ℕ) → rec₂ℕ C c₀ cₛ n ≡ (n , recℕ C c₀ cₛ n)
  proof C c₀ cₛ zero    = refl
  proof C c₀ cₛ (suc n) = {!   !} -- ap (cₛ n) (proof C c₀ cₛ n) · helper




\end{code}


## Chapter 3

### Exercise 3.1

<div class="exercise">
Prove that if $$A\simeq B$$ and $$A$$ is a set, then so is $$B$$.
</div>
To solve this problem, let us recall a few things:

- The *set* definition in HoTT:

A type $$A$$ is a **set** if for all $$x, y : A$$ and
all $$p, q : x ≡ y$$, we have $$ p \equiv q$$. In a proposition
we have

$$
\mathsf{isSet}(A) :\equiv \prod\limits_{(x,y : A)}\prod\limits_{(p,q : x \equiv y)} (p \equiv q).
$$

- The type for equivalence from $$A$$ to $$B$$

$$
  (A \simeq B) :\equiv \sum\limits_{f : A \to B} \mathsf{isequiv}(f),
$$

where

$$
\mathsf{isequiv(f)} :\equiv
  \left (\sum\limits_{g : B \to A} (f \circ g \sim \mathsf{id}_{B})\right) \times
  \left (\sum\limits_{h : B \to A} (h \circ f \sim \mathsf{id}_{A})\right)
$$

- The homotopy concept:

Let $$f , g : \prod\limits_{(x:A)} P(x)$$ be two sections of a
type family $$P : A \to \mathcal{U}$$. A **homotopy** from $$f$$ to $$g$$
is a dependent function of type

$$
(f \sim g) :\equiv \prod\limits_{x : A} (f(x) \equiv g(x)).
$$

### Exercise 3.2

<div class="exercise">
Prove that if $$A$$ and $$B$$ are sets, then so is $$A+B$$.
</div>

### Exercise 3.3

<div class="exercise">
Prove that if $$ A $$ is a set and $$B : A \to \mathcal{U}$$
is a type family such that $$B(x)$$ is a set for all
$$x : A$$, then $$\Sigma\limits_{(x:A)}\ B(x)$$ is a set.
</div>

### Exercise 3.4

<div class="exercise">
Show that $$A$$ is a mere proposition if and only
if $$A\to A$$ is contractible.
</div>

### References

* Univalent Foundations Program, T. (2013). Homotopy Type Theory: Univalent Foundations of Mathematics. Institute for Advanced Study.

* [Capriotti's hott-exercises](https://github.com/pcapriotti/hott-exercises).

* [Capriotti's agda-base](https://github.com/pcapriotti/agda-base/)
