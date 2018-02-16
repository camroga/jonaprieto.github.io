---
layout: "post"
title: "Induction on Identity Types"
date: "2018-02-14 17:41"
---

We present here a new type former to introduce identities.
The identity or equality type is defined as follows:

```
data Id (A : Set) (x y : A) : Set where
  refl : Id A x y
```

The only rule/constructor is `refl` that represents the reflexivity property of
the inductive types.

To use another notation for Id,
we can use the equality symbol (_≡_):

```
infix 3 _≡_
_≡_ : ∀ {A : Set} → (x y : A) → Id A x y
x ≡ y = refl
```

However, there are many things already proved about this type
in the Agda, so let use the common import for such a purpose:

\begin{code}
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
\end{code}

### Path induction

Before continue, remember that since we are using Agda, there are universes and
its levels to handle the
[hierarchie](https://pigworker.wordpress.com/2015/01/09/universe-hierarchies/).
We mention that because in the following we use these levels for the first time
in these notes.

\begin{code}
pi
  : ∀ {i} {A : Set}
  → (C : (x y : A) → x ≡ y → Set i)
  → ((x : A) → C x x refl)
  → ∀ (x y : A) (p : x ≡ y) → C x y p
\end{code}
Defined by the equation:
\begin{code}
pi {A} C c x .x refl = c x
\end{code}

### Path based induction

\begin{code}
bpi
  : ∀ {i} {A : Set} → (a : A)
  → (C : (y : A) → a ≡ y → Set i)
  → C a refl
  → (y : A) (p : a ≡ y) → C y p
\end{code}
Defined by the equation:
\begin{code}
bpi a C c .a refl = c
\end{code}

### Equivalence between pi and bpi

Path-induction follows from path based induction.

\begin{code}
bpi⇒pi
  : ∀ {A : Set}
  → (C : (x y : A) → x ≡ y → Set)
  → (c : (x : A) → C x x refl)
  → (x y : A) (p : x ≡ y) → C x y p

bpi⇒pi {A} C c x = g
  where
    C′ : (y : A) → x ≡ y → Set
    C′ = C x

    c′ : C x x refl
    c′  = c x

    g : ∀ (y : A) (p : x ≡ y) → C′ y p
    g = bpi x C′ c′
\end{code}

The other direction:

\begin{code}
pi⇒bpi
  : ∀ {A : Set}
  → (a : A)
  → (C : (y : A) → a ≡ y → Set)
  → (c : C a refl)
  → ∀ (y : A) (p : a ≡ y) → C y p

pi⇒bpi {A} a C c y p = f a y p C c
  where
    D : ∀ (x y : A) → x ≡ y → Set₁
    D x y p = (K : (z : A) → x ≡ z → Set) → K x refl → K y p

    d : ∀ (x : A) → D x x refl
    d = λ x C c → c

    f : ∀ (x y : A) (p : x ≡ y) → D x y p
    f = pi D d
\end{code}


## References

* Univalent Foundations Program, T. (2013). Homotopy Type Theory: Univalent
Foundations of Mathematics. Institute for Advanced Study:
https://homotopytypetheory.org/book.
