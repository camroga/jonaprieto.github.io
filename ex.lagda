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


-- Heterogenous equality

--  data HE (A : _) (B : _) : (α : A == B) (a : A) (b : B) → Set where
--    hidp : HE A A idp a a
\end{code}
