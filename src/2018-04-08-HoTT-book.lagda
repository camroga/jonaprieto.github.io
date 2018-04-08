---
layout: "post"
title: "HoTT Book Solutions"
date: "2018-03-17"
categories: type-theory
---

This is a version self-contained of the [Capriotti's solutions](https://github.com/pcapriotti/hott-exercises).
The idea is to unpackage all his work to get a better understanding.
Many changes can be appear running this experiment, do not expect the same
code structure as the original.

TODO:

- problem text for each problem
- remove the requirements: `agda-base`
- add a table of contents

-------------------------------------------------------------------------------

An Agda pragma for consistency:

\begin{code}
{-# OPTIONS --without-K #-}
\end{code}

-------------------------------------------------------------------------------

## Chapter 1

Equality type defintion also called Identity type:

\begin{code}
infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
  \end{code}

### Exercise 1

\begin{code}
_∘_ : ∀ {i j k} {A : Set i}{B : Set j}{C : Set k}
    → (B → C)
    → (A → B)
    → A → C
g ∘ f = λ x → g (f x)

∘-assoc : ∀ {i j k l} {A : Set i}{B : Set j}{C : Set k}{D : Set l}
        → (h : C → D)(g : B → C)(f : A → B)
        → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
∘-assoc f g h = refl
\end{code}

### Exercise 2

Some machinery to handle levels of the universe needed for
the following exercises including this one:

\begin{code}
open import Agda.Primitive public
  using    (Level; _⊔_; lzero; lsuc)
\end{code}

To solve this problem we need:

  - Σ-type definition

  - Product type definition

  - Review the recursion principle, what exactly it consists of. Maybe this refresh our minds:
    ```
      rec-T : (C : 𝒰) → ...constructor cases... → (T → C)
    ```

-------------------------------------------------------------------------------

+ Σ-type definition:

\begin{code}
infixr 2 _×_

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

-- _,_ : (proj₁ : A) → B proj₁ → Σ A B.
open Σ public
\end{code}

\begin{code}
module Σ-Rec {i j k}{A : Set i}{B : A → Set j}{C : Set k}
             (d : (x : A) → B x → C) where

  Σ-rec : Σ A B → C
  Σ-rec p = d (proj₁ p) (proj₂ p)

  Σ-rec-β : (x : A)(y : B x) → Σ-rec (x , y) ≡ d x y
  Σ-rec-β x y = refl
\end{code}

+ Product type is just a particular case of the sigma type when
the codomain is not dependent:

\begin{code}
_×_ : {l k : Level} (A : Set l) (B : Set k) → Set (l ⊔ k)
A × B = Σ A λ _ → B
\end{code}

\begin{code}
module ×-Rec {i j k}{A : Set i}{B : Set j}{C : Set k}
           (d : A → B → C) where

  ×-rec : A × B → C
  ×-rec p = d (proj₁ p) (proj₂ p)

  ×-rec-β : (x : A)(y : B) → ×-rec (x , y) ≡ d x y
  ×-rec-β x y = refl
\end{code}

## Chapter 2

### Exercise 1

## Chapter 3

### Exercise 1
