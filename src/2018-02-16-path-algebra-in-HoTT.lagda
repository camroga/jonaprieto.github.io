---
layout: "post"
title: "Path Algebra in HoTT"
date: "2018-02-16 21:57"
categories: type-theory
---

In Univalence we have a different interpreation of type theory. We replace the
set-theoretical notion of sets for types and we use the *topological space*
notion instead. And the judment `a : A` for a type A, it reads as the point `a` in
the topological space `A`. We also include the identity type but instead of thinking
about it as the proof of equality for `a = b`, we refer us to this type as
the *path* between `a` and `b` where `a` is the starting point and `b` the end
of the path. We also could have different paths for that path, and its set
we call it *path space*.

To help streghten our intintuion of what really happens with this type, we
will see some pictures next.

### Prerequisites

To work with the identity type let's use the type `(_≡_)` from
the Agda standard library.

\begin{code}
{-# OPTIONS --without-K #-}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl; _≡_)
\end{code}

+ *Path Induction*

This is the elimination principle for the identity type and
this also called `J` eliminator with some variations.

\begin{code}
pi
  : ∀ {i j} {A : Set i}
  → (C : (x y : A) → x ≡ y → Set j)
  → (∀ (x : A) → C x x refl)
  → ∀ (x y : A) (p : x ≡ y) → C x y p
pi {A} C c x .x refl = c x
\end{code}

+ *Path Concatenation*

We can join two paths when one ends where the other starts.
We use the _concatenation_ operator for such purposes with its symbol (`_·_`)
--\centerdot in Latex--. Let's see its picture.

![path](/assets/images/path-concatenation.png)

\begin{code}
infixr 20 _·_
_·_ : ∀ {A : Set}
    → {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → x ≡ z
_·_ {A} {x} {y} {z} p q = D₁ x y p z q
  where
    D₂ : (x z : A) (q : x ≡ z) → x ≡ z
    D₂ = pi (λ x z q → x ≡ z) (λ x → refl)

    D₁ : (x y : A) → (x ≡ y) → ((z : A) → (q : y ≡ z) → x ≡ z)
    D₁ = pi (λ x y p → ((z : A) → (q : y ≡ z) → x ≡ z)) (λ x → D₂ x)
\end{code}

*We've could define the same using Agda pattern-matching in just one-line.*

+ *Path Inverse*

If `p : a = b`, we write `p⁻¹ : b = a` for the path in the opposite direction.

\begin{code}
infixl 20 _⁻¹
_⁻¹ : ∀ {A : Set} {x y : A} → (p : x ≡ y) → y ≡ x
_⁻¹ {A}{x}{y} p =
  pi (λ x y p → y ≡ x)
     (λ x → refl {x = x})
     x y p
\end{code}

-- dante
-----------------------------------------------------------------------------

### Lemma

![path](/assets/images/path-algebra.png)

#### Proofs

+ `(refl x) ⁻¹ ≡ refl x`
\begin{code}
l1 : ∀ {A : Set} {x : A} → (refl ⁻¹) ≡ refl
l1 {A}{x} =
  pi (λ x y p → (refl ⁻¹) ≡ refl {x = x})
     (λ x → refl {x = refl {x = x}})
     x x refl
\end{code}

+ `p · p ⁻¹ ≡ refl x`

\begin{code}
l2 : ∀ {A : Set} (x y : A) → (p : x ≡ y) → (p · (p ⁻¹))  ≡ refl
l2 =
  pi (λ x y p → (p · (p ⁻¹))  ≡ refl)
     (λ x → refl { x = refl {x = x}})
\end{code}

+ `refl x · p ≡ p`

\begin{code}
l3 : ∀ {A : Set} (x y : A) → (p : x ≡ y) → refl · p ≡ p
l3 =
  pi (λ x y p → refl · p ≡ p)
     (λ x → refl { x = refl {x = x}})
\end{code}

+ `p · refl y ≡ p`

\begin{code}
l4 : ∀ {A : Set} (x y : A) → (p : x ≡ y) → refl · p ≡ p
l4 = pi (λ x y p → refl · p ≡ p)
        (λ x → refl {x = refl {x = x}})
\end{code}

+ ` (p  ⁻¹) ⁻¹ ≡ p`

\begin{code}
l5 : ∀ {A : Set} (x y : A) → (p : x ≡ y) → (p  ⁻¹) ⁻¹ ≡ p
l5 = pi (λ x y p → (p  ⁻¹) ⁻¹ ≡ p)
        (λ x → refl {x = refl {x = x}})
\end{code}

### Transport

![path](/assets/images/transport-fiber.png)
