---
layout: "post"
title: "Equivalences"
date: "2018-02-20"
categories: type-theory
---

<div class="todo">
  Equivalence Definitions and intuitions...
</div>

+ Show that for all x, y : 𝟙, (x ≡ y  ≃ 𝟙 ).

To prove that, we must to exhibit a function `f : (x =A y) → 𝟙`
to provide an inhabitant of the equivalence type `x ≡ y  ≃ 𝟙`.

Imports:

\begin{code}
{-# OPTIONS --without-K #-}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl; _≡_)
\end{code}

Definitions:

* Unit type

\begin{code}
data 𝟙 : Set where
  * : 𝟙
\end{code}

* Path Induction *

\begin{code}
pi
  : ∀ {i j} {A : Set i}
  → (C : (x y : A) → x ≡ y → Set j)
  → (∀ (x : A) → C x x refl)
  → ∀ (x y : A) (p : x ≡ y) → C x y p
pi {A} C c x .x refl = c x
\end{code}

Proof :

\begin{code}
f₁ : ∀ {A : Set} (x y : A) → x ≡ y → 𝟙
f₁ = pi (λ x y _ → 𝟙) (λ x → *)

infixr 4 _~_
_~_ : ∀ {A : Set}{P : A → Set}
    → ((x : A) → P x) → ((x : A) → P x) → Set
_~_ {A} f g = (x : A) → f x ≡ g x

open import Data.Product
open import Function hiding (id)

id : ∀ {A : Set} → A → A
id = λ z → z

-- is-equiv : ∀ {A : Set}{B : Set}
--   → (f : A → B)
--   → (g : B → A)
--   → (h : B → A)
--   → (Σ (B → A) (λ x → ((f (g x)))) × (Σ (B → A) (λ _ → A))
-- is-equiv {A}{B} f g h = ((g , {!   !})) , (h , {!   !})

-- _≃_ : ∀ {i j} (A : Set i) (B : Set j) → ?
-- A ≃ B = Σ (A → B) is-equiv

-- thm : ∀ (x y : 𝟙) → Equiv (x ≡ y) 𝟙
-- thm = {!   !}
\end{code}
