---
layout: "post"
title: "PathOvers in HoTT"
date: "2018-06-30"
categories: type-theory
published: true
toc: true
---

We want to formilise the intuition behind the correspondance between
PathOvers and their total space.

![](/assets/png-images/2018-07-05-geometry-intution-of-pathovers-7f9fb342.png)


## Heterogeneous equality

The path type Path {A} a0 a1 (an inductive family with one constructor id : Path
a0 a0) is sometimes called homogeneous equality, because it relates two elements
a0 and a1 whose

## Path over a path

> While we have motivated PathOver as a factored heteroge- neous equality, there
> is also a geometric intuition. Dependent types correspond to fibrations, so a
> type C : A ? Type can be pictured as its total space Σ a:A. C a projecting down
> to A by first projection. A path-over γ : PathOver C α c1 c2 represents a path σ
> in Σ a:A. C a between (a1,c1) and (a2,c2), such that ap fst σ is exactly α. That
> is, it is a path in the total space that projects down to, or lies over, α (path
> pairing pair= αγ will be made precise below)

\begin{code}
{-# OPTIONS --without-K #-}

open import HoTT

module _ {i j}{A : Type i}{B : A → Type j}{x y : A} where

  f : {p : x == y}{u : B x}{v : B y}
    → Σ ((x , u) == (y , v)) (λ q → (ap fst q) == p)
    → u == v [ B ↓ p ] -- PathOver B p u v
  f (idp , idp) = idp

  g : {p : x == y}{u : B x}{v : B y}
    → (r : PathOver B p u v)
    → Σ ((x , u) == (y , v)) (λ q → (ap fst q) == p)
  g {p = p} r = (pair= p r , ap-fst-pair= p r)
    where
    ap-fst-pair=
      : (p : x == y)
      → {u : B x}{v : B y} (q : PathOver B p u v)
      → ap fst (pair= p q) == p
    ap-fst-pair= idp idp = idp

  f-g : {p : x == y}{u : B x}{v : B y}
    → (r : PathOver B p u v)
    → f (g r) == r
  f-g {p = idp} idp = idp

  g-f : {p : x == y}{u : B x}{v : B y}
    → (pair : Σ ((x , u) == (y , v)) (λ q → (ap fst q) == p))
    → g (f pair) == pair
  g-f (idp , idp) = idp

  e : {p : x == y}{u : B x}{v : B y}
    → (Σ ((x , u) == (y , v)) (λ q → (ap fst q) == p)) ≃ PathOver B p u v
  e = equiv f g f-g g-f

\end{code}


\begin{code}
-- Heterogeneous equality

  infix 4 _≅_

  data _≅_ {ℓ} {A : Set ℓ} (x : A) : {B : Set ℓ} → B → Set ℓ where
     refl : x ≅ x

  ------------------------------------------------------------------------
  -- Conversion

  ≅-to-≡ : ∀ {a} {A : Set a} {x y : A} → x ≅ y → x == y
  ≅-to-≡ = {!   !}
\end{code}
