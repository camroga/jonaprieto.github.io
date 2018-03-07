---
layout: "post"
title: "Induction on Identity Types"
date: "2018-02-14 17:41"
categories: type-theory
---

We present here a new type former to introduce identities.
The identity or equality type is defined as follows:

```agda
data Id (A : Set) (x y : A) : Set where
  refl : Id A x y
```

The only rule/constructor is `refl` that represents the reflexivity property of
the inductive types. Sometimes we can another definition for refl, that is
similar as the presented above but using the equality symbol (`_≡_`) and Π-type.

```
refl: Π x:A. x ≡ x
```

In Agda we will write this

```agda
infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x
```

instead of

```agda
infix 3 _≡_
_≡_ : ∀ {A : Set} → (x y : A) → Id A x y
x ≡ y = refl
```

However, this type is already present in the Agda standard library, so let's use it

\begin{code}
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
\end{code}

### Martin-Löf's rules about identity type

- ML1. For any type `X`, for each `a` and `b` of it, there is a type `a = b`

- ML2. There is an element `refl x : x = x` for each `x : X`

- ML3. Induction for equality:

    > For any type $$X$$ and for any element $$a$$ of it, given a family of types $$P(b,e)$$
    depending on parameters $$b$$ of type $$X$$ and $$e$$ of type $$a=b$$, in order to
    define elements $$f(b,e) : P(b,e)$$ of all of them it suffices to provide an
    element $$p$$ of $$P(a, refl\ a)$$.  The resulting function $$f$$ may be regarded as
    having been completely defined by the single definition $$f(a, refl\ a) := p$$.


    > Intuitively, the induction principle for equality amounts to saying that the
    element $$refl a$$ ``generates'' the system of types $$a=b$$, as $$b$$ ranges
    over elements of $$A$$.
    <cite>[Daniel Grayson](http://arxiv.org/abs/1711.01477)</cite>

We will show in a moment more about ML3 rule from the univalance perspective,
that is, the homotopy type theory perspective. The main diference up to now, we
give another meaning of `a = b`, insteaf of thinking about it as a proof of such
a equality, we are going to think as a `path space` in a topological space
associated to `A`


In the following, we may encounter with [levels](https://pigworker.wordpress.com/2015/01/09/universe-hierarchies/) in Agda.
The small types are those that belongs to the first level 0, types of level 1 are
those formed by using small types, and so on. The small types in Agda has `Set` type ,
types formed by these small types have `Set 1` type, and so on with `Set i` type.

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

+ C can construct types from three arguments: two endpoints and one path.

+ C holds in the *diagonal*, that is, we need to prove or find an
inhabitant of C x x refl for all x.

Then, as result, the property C holds for all paths in general.

### Based path induction

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

*Remark*: we can not repeat in Agda a name variable in an equation. But using
the dot accompanying as a prefix of a variable, it tells the typechecker that
there is only one possible value and it corresponds to that variable.

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

* [Univalent Foundations Program, T. (2013). Homotopy Type Theory: Univalent Foundations of Mathematics. Institute for Advanced Study][HoTT]
* [Grayson, D. R. (2017). An introduction to univalent foundations for mathematicians.][Grayson]


[HoTT]:https://homotopytypetheory.org/book.
[Grayson]:http://arxiv.org/abs/1711.01477
