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
end in `b` that's why we call this type *path space* for `a : A` and `b : A`.

Besides traditional type theory, recall HoTT comes from geometry and the beauty
of this is we can draw some of its concepts and for sure that will help us to
strengthen our intuition about paths. For instance, if `p : a = b`, we
write `p⁻¹ : b = a` for the reversed path. We can join two path that share
the endpoint of one to the start point of the other, we call this operation,
concatenation and we use the symbol (`_·_`). For instance we have the path
`p · p⁻¹ : a = a` and `p⁻¹ · p : b = b`.

### Path Algebra

As always:

\begin{code}
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
\end{code}

\begin{code}
pi
  : ∀ {i} {A : Set}
  → (C : (x y : A) → x ≡ y → Set i)
  → (∀ (x : A) → C x x refl)
  → ∀ (x y : A) (p : x ≡ y) → C x y p
\end{code}

defined by the equation

\begin{code}
pi {A} C c x .x refl = c x
\end{code}

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
