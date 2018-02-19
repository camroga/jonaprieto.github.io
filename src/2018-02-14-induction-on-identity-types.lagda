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
the inductive types. Sometimes we can another definition for refl, that is
similar as the presented above but using the equality symbol (_≡_) and Π-type.

```
refl: Π x:A. x ≡ x
```

where

```
infix 3 _≡_
_≡_ : ∀ {A : Set} → (x y : A) → Id A x y
x ≡ y = refl
```

However, since this an important type many things are already proved for this type
in the Agda standard library, so let use that:

\begin{code}
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
\end{code}

Before continue, remember that since we are using Agda, there are *universes* of types and
there are some [levels](https://pigworker.wordpress.com/2015/01/09/universe-hierarchies/) associated to them.
We mention this because in the following we have to use these levels for the first time
in these notes to define in an appropriate way some types.

### Path induction

We call *path* to the inhabitant of the identity type, that is, p : x ≡ y for
some x and y of type A. We can probably think that there is only one p, but
there are many identifications between x and y from the HoTT perspective. That's
the reason we talk about one path and one set of paths, the *path space*.

![path](/assets/images/path.png)

Now, we introduce the induction principle for the identity type with `pi`,
abbreviation of path induction.

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

Let us unpackage this:

To contruct something of the type (∀ (x y : A) (p : x ≡ y) → C x y p) we need that:

+ [1] C can construct types from three arguments: two endpoints and one path.

+ [2] C holds in the *diagonal*, that is, there is a proof for C x x refl for all x.

Then, as result, the property C holds for all paths! (all identifications of x with y).

We can think in the diagonal requeriment as the base case on an ordinary
induction.

### Path based induction

A differente or more customized version of path induction is the based
path induction abbreviated as `bpi`.

\begin{code}
bpi
  : ∀ {i} {A : Set}
  → (a : A)
  → (C : (y : A) → a ≡ y → Set i)
  → C a refl
  → (y : A) (p : a ≡ y) → C y p
\end{code}

defined by the equation
\begin{code}
bpi a C c .a refl = c
\end{code}

Let us unpackage this:

+ With a fixed endpoint a

+ if we consider all paths whiches start with a

+ to have the property for all y:A and for all paths a ≡ y the only
necessary is to have C a refl, that is, holds C for the *base case*.


### Equivalence between path induction and base path induction

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
