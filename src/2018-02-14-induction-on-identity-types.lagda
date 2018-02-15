---
layout: "post"
title: "Induction on Identity Types"
date: "2018-02-14 17:41"
---

## Identity type

\begin{code}
𝒰 = Set
-- data Id (A : 𝒰) (x y : A) : 𝒰 where
--   refl : Id A x y
\end{code}
We can use another notation:

\begin{code}
-- _≡_ : ∀ {A : 𝒰} → (x y : A) → Id A x y
-- x ≡ y = refl
\end{code}

With a low precedence:

\begin{code}
-- infix 3 _≡_
\end{code}

### Elimination rules

#### Path induction

\begin{code}
-- test : ∀ {A : 𝒰} → (x y : A) → Id A x y → 𝒰
-- test = {!   !}
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
pi : ∀ {A : 𝒰}
    → (C : (x y : A) → x ≡ y → 𝒰)
    → ((x : A) → C x x (refl))
    → ∀ (x y : A) (p : x ≡ y) → C x y p
pi {A} C c x .x refl = c x
\end{code}

#### Path based induction

\begin{code}
bpi : ∀ {A : 𝒰}
    → (a : A)
    → (C : (y : A) → a ≡ y → 𝒰)
    → C a refl
    → ∀ (y : A) (p : a ≡ y) → C y p
bpi a C c .a refl = c
\end{code}


\begin{code}
bpi-pi
    : ∀ {A : 𝒰}
    → (C : (x y : A) → x ≡ y → 𝒰)
    → (c : (x : A) → C x x refl)
    → (x y : A) (p : x ≡ y) → C x y p
bpi-pi {A} C c x = g
  where
    C′ : (y : A) → x ≡ y → 𝒰
    C′ = C x

    c′ : C x x refl
    c′  = c x
    --
    g : ∀ (y : A) (p : x ≡ y) → C′ y p
    g = bpi x C′ c′
\end{code}

## References

* Univalent Foundations Program, T. (2013). Homotopy Type Theory: Univalent
Foundations of Mathematics. Institute for Advanced Study:
https://homotopytypetheory.org/book.
