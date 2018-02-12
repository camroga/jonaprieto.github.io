---
layout: "post"
title: "Leibniz's Equality"
date: "2018-02-09 21:58"
---

  > Leibniz characterised the notion of equality as follows:
  Given any x and y, x = y if and only if, given any
  predicate P, P(x) if and only if P(y).

  ```
  ∀x ∀y (x = y → ∀P (P x ↔ P y))
  ```

\begin{code}
Eq : ∀ {A : Set} → (x y : A) → Set₁
Eq {A} x y = (P : A → Set) → (P x → P y)
\end{code}

We can think about this equality definition saying that
x is equal to y if and only if every property (unary predicate variable P)
that x satisfies, y satisfies as well.

* Reflexivity

\begin{code}
refl : ∀ {A : Set} → (x : A) → Eq x x
refl {A} x = λ P Px₁ → Px₁
\end{code}

* Transitivity

\begin{code}
trans : ∀ {A : Set} → (x y z : A) → Eq x y → Eq y z → Eq x z
trans {A} x y z x≡y P₁ y≡z P₂ = P₁ y≡z (x≡y y≡z P₂)
\end{code}

* Symmetry

\begin{code}
sym : ∀ {A : Set} → (x y : A) → Eq x y → Eq y x
sym {A} x y x≡y P = x≡y p₁ (λ z → z)
  where
    p₁ : A → Set
    p₁ = λ z → P z → P x
\end{code}

## Related

  > The principle of identity of indiscernibles states that two objects
  are identical if they have all the same properties.
  This is also known as “Leibniz’s Law”
  + [https://ncatlab.org/nlab/show/identity+of+indiscernibles](https://ncatlab.org/nlab/show/identity+of+indiscernibles)
