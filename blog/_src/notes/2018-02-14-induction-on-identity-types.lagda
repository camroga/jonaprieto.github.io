---
layout: "post"
title: "Induction on Identity Types"
date: "2018-02-14"
categories: learning
latex: true
references: true
agda: true
toc: true
---

In this entry, we work with the Identity type, sometimes also called Equality type.
This type only has one constructor, the constructor denoted by `refl` which represents
the reflexivity property. Its definition in Agda is as follows:

```agda
data Id (A : Set) (x y : A) : Set where
  refl : Id A x y
```

Nonetheless, its more common to find the definition in Agda as it follows,

\begin{code}
infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x
\end{code}

instead of

```agda
infix 3 _≡_
_≡_ : ∀ {A : Set} → (x y : A) → Id A x y
x ≡ y = refl
```

In the Agda standard library, we find this type in the `Relation.Binary.PropositionalEquality` module.

### Martin-Löf rules about the Identity type

- **ML1**. For any type `X`, for each `a` and `b` of it, there is a type `a = b`

- **ML2**. There is an element `refl x : x = x` for each `x : X`

- **ML3**. Induction for equality:

    > For any type $$X$$ and for any element $$a$$ of it, given a family of types $$P(b,e)$$
    depending on parameters $$b$$ of type $$X$$ and $$e$$ of type $$a=b$$, in order to
    define elements $$f(b,e) : P(b,e)$$ of all of them it suffices to provide an
    element $$p$$ of $$P(a, refl\ a)$$.  The resulting function $$f$$ may be regarded as
    having been completely defined by the single definition $$f(a, refl\ a) := p$$.

    > Intuitively, the induction principle for equality amounts to saying that the
    element $$refl a$$ *generates* the system of types $$a=b$$, as $$b$$ ranges
    over elements of $$A$$. Read more in {% cite Grayson2017 %}.

In HoTT, the ML3 rule is interpreted in a different way. The identity type `a =
b` is not longer the type that stands for proofs of the equality between `a` and
`b`. Instead of it, an identity type becomes in the *path space* where each of
inhabitants are just *paths* between points in the topological space associated
to `A`. Read the full discussion in {% cite hott-book %}.

Before to jump to the next section, one comment before about the type theory of
Agda. In `Agda`, the types follow a hierarchy by using what they call
[*levels*](https://goo.gl/7TcwuL). For instance, in the first level, level `0`,
we find the **small types** which are of the `Set` type. Types of the level `1`
are those formed by using some small types which means they have `Set 1` type
and so on with `Set i` type.

### Path induction

We call *path* to the inhabitant `p` of the identity type, that is, `x ≡ y` for
some `x` and `y` of type `A`. We can probably think that there is only one `p`,
but there could be many identifications between `x` and `y` from the HoTT
perspective, proof-relevant!, yeah.

![path](/assets/ipe-images/path.png)

As any other type, we have the elimination principle also called induction. We
denote this rule by `pi` because it is the abbreviation of *path induction*.
Other references call this `pi` as the `J` eliminator but please refer to [`J`
rule](https://goo.gl/Sm4ZAs) for a more detailed description.

\begin{code}
pi
  : ∀ {i} {A : Set}
  → (C : (x y : A) → x ≡ y → Set i)
  → (∀ (x : A) → C x x refl)
  -----------------------------------
  → ∀ (x y : A) (p : x ≡ y) → C x y p
\end{code}

The computation rule using this rule is:

\begin{code}
pi {A} C c x .x refl = c x
\end{code}

To understand this basic principle, let's unpackage its definition.

What `pi` is telling us is to construct something of the type `C`
using information about the path `x ≡ y`, we need to provide that:

+ `C` is able to construct new types from just three arguments: two points and
one path.

+ `C` must hold the *diagonal*, which it means that, we need to prove that
`C x x refl` holds for all `x`.

Then, as result, the property `C` holds *for all paths* in general.

### Based path induction

Another approach for the same principle is the *based path induction* that we
abbreviate as `bpi`. The major difference is that we *fixed* the induction with
one parameter, the variable `a` in the following definition.

{: .foldable until="7" }
\begin{code}
bpi
  : ∀ {i} {A : Set}
  → (a : A)   -- Fixed
  → (C : (y : A) → a ≡ y → Set i)
  → C a refl
  -----------------------------
  → (y : A) (p : a ≡ y) → C y p

bpi a C c .a refl = c
\end{code}

*Remark*: The dot accompanying the variable `a` in the equation above is
because in `Agda` we can tell to the type-checker that there is only one
possible value that corresponds to that variable, which in this case, only can
be the same `a`.

Let us unpackage the `bpi` definition:

+ With the fixed endpoint `a`,

+ if we consider all paths which start with this `a`,

+ to have the property that for all `y:A` and for all paths `a ≡ y`. We only
need to have `C a refl`, which it means, `C` always holds for the *base case*.

### Equivalence between path induction and base path induction

Path-induction and based path induction are *equivalent*.
Let's see a proof in Agda. Please click on each proof to expand it.

Using `bpi` we prove the same as `pi` under the same assumptions.

{: .foldable until="5" }
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

Similarly, the other direction from `pi` to `bpi`.

{: .foldable until="6" }
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
    D x y p = (L : (z : A) → x ≡ z → Set) → L x refl → L y p

    d : ∀ (x : A) → D x x refl
    d = λ x C c → c

    f : ∀ (x y : A) (p : x ≡ y) → D x y p
    f = pi D d
\end{code}
