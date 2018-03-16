---
layout: "post"
title: "Path Algebra"
date: "2018-02-16 21:57"
categories: type-theory
---

In univalence we have a different interpreation of type theory. We replace the
set-theoretical notion of sets for types and we use instead of it the *topological
space*. In this interpretation we also replace the notion of an element of `a =
b`, that is, the proof of such a equality and instead of it we use a new
concept, *path*, for this element, where `a` is the start of the path, and `b` is
the endpoint. Then, the identity type, `a = b`, is all paths that start in `a` and
end in `b`. We call this type *path space*.

To help with our intintuion of what happen with certain types, we can draw some
pictures. Let's see.  For instance, if `p : a = b`, we write `p⁻¹ : b = a` for
the reversed path. We can join two paths that share the endpoint and the start
point by what we call _concatenation_ and its symbol (`_·_`). We have what we
call path algebra for the basic operations like `p · p⁻¹ : a = a` and
`p⁻¹ · p : b = b`.

### Lemma

![path](/assets/images/path-algebra.png)

#### Proofs

Let's using identity type from the Agda standard library.

\begin{code}
{-# OPTIONS --without-K #-}
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
\end{code}

As happen often in HoTT our proofs are by induction therefore let's define
our path induction.

\begin{code}
pi
  : ∀ {i j} {A : Set i}
  → (C : (x y : A) → x ≡ y → Set j)
  → (∀ (x : A) → C x x refl)
  → ∀ (x y : A) (p : x ≡ y) → C x y p
pi {A} C c x .x refl = c x
\end{code}

-------------------------------------------------------------------------------

To prove our identities we define the concatenation operator and inverse
operation as follows.

\begin{code}
infixr 20 _·_
_·_ : ∀ {A : Set}
    → {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → x ≡ z
_·_  {A} {x} {y} {z} p q = D₁ x y p z q
  where
    D₂ : (x z : A) (q : x ≡ z) → x ≡ z
    D₂ = pi (λ x z q → x ≡ z) (λ x → refl)

    D₁ : (x y : A) → (x ≡ y) → ((z : A) → (q : y ≡ z) → x ≡ z)
    D₁ = pi (λ x y p → ((z : A) → (q : y ≡ z) → x ≡ z)) (λ x → D₂ x)
\end{code}

Surely just using pattern-matching we've could do this proof in just one-line.
What is the point?, we are walking by the hard way, learning path induction.
See the same proof in Chapter 2 in the HoTT Book.

\begin{code}
infixl 20 _⁻¹
_⁻¹ : ∀ {A : Set} {x y : A} → (p : x ≡ y) → y ≡ x
_⁻¹ {A}{x}{y} p = pi (λ x y p → y ≡ x) (λ x → refl) x y p
\end{code}

+ `(refl x) ⁻¹ ≡ refl x`
\begin{code}
l1 : ∀ {A : Set} {x : A} → (refl ⁻¹) ≡ refl {x = x}
l1 {A}{x} = pi (λ x y p → (refl ⁻¹) ≡ refl {x = x}) (λ x → refl) x x refl
\end{code}

+ `p · p ⁻¹ ≡ refl x`

\begin{code}

l2 : ∀ {A : Set} (x y : A) → (p : x ≡ y) → (p · (p ⁻¹))  ≡ refl
l2 = {!   !}

\end{code}

+ `refl x · p ≡ p`

+ `p · refl y ≡ p`

+ ` (p  ⁻¹) ⁻¹ ≡ p`


-------------------------------------------------------------------------------

+ A function `f : (x =A y) → 𝟙` where 𝟙 is the unit type with only one constructor.

\begin{code}
data 𝟙 : Set where
  * : 𝟙

f₁ : ∀ {A : Set} (x y : A) → x ≡ y → 𝟙
f₁ = pi (λ x y _ → 𝟙) (λ x → *)

_~_ : ∀ {A : Set}{P : A → Set} → ((x : A) → P x) → ((x : A) → P x) → Set
_~_ {A} f g = (x : A) → f x ≡ g x

infixr 4 _~_

open import Data.Product
open import Function hiding (id)

id : ∀ {A : Set} → A → A
id = λ z → z

is-equiv : ∀ {A : Set}{B : Set}
  → (f : A → B)
  → (g : B → A)
  → (h : B → A)
  → (Σ (B → A) (λ _ → B)) × (Σ (B → A) (λ _ → A))
is-equiv {A}{B} f g h = ((g , {!   !})) , (h , {!   !})

-- _≃_ : ∀ {i j} (A : Set i) (B : Set j) → ?
-- A ≃ B = Σ (A → B) is-equiv

-- thm : ∀ (x y : 𝟙) → Equiv (x ≡ y) 𝟙
-- thm = {!   !}
\end{code}
