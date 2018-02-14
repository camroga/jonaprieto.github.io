---
layout: "post"
title: "Induction on Identity Types"
date: "2018-02-14 17:41"
---

## Identity type

\begin{code}
𝒰 = Set
data Id (A : 𝒰) (x y : A) : Set where
  refl : Id A x y
\end{code}
We can use another notation:

\begin{code}
_≡_ : ∀ {A : 𝒰} → (x y : A) → Id A x y
x ≡ y = refl
\end{code}

With a low precedence:

\begin{code}
infix 3 _≡_
\end{code}

### Elimination rules

#### Path induction

#### Path based induction

## References

* Univalent Foundations Program, T. (2013). Homotopy Type Theory: Univalent
Foundations of Mathematics. Institute for Advanced Study:
https://homotopytypetheory.org/book.
