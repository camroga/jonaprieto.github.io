---
layout: "post"
title: "Univalence From Scratch"
date: "2018-03-17"
categories: type-theory
---

This is my reading of the paper:

> M.H. Escardo. [*A self-contained, brief and complete formulation of Voevodsky's
Univalence Axiom*](https://arxiv.org/abs/1803.02294), March 2018, arXiv:1803.02294.

For the original version of the Agda code, review the link of the paper.
The following type-checks in Agda 2.5.3.

\begin{code}
{-# OPTIONS --without-K #-}
\end{code}

Basic imports:

\begin{code}
open import Agda.Primitive
  using    ( _⊔_; lsuc )
  renaming ( lzero to U₀ ; Level to Universe )
\end{code}

### Σ-type and Identity type

\begin{code}
data Σ {U V : Universe}
       {X : Set U}
       (Y : X → Set V)
      : Set (U ⊔ V) where
  _,_ : (x : X) (y : Y x) → Σ Y

data Id {U : Universe} {X : Set U} : X → X → Set U  where
  refl : (x : X) → Id x x
\end{code}

### J eliminator

\begin{code}
J : {U V : Universe} {X : Set U}
  → (A : (x y : X) → Id x y → Set V)  -- type former
  → ((x : X) → A x x (refl x))        -- diagonal proof
  → (x y : X) (p : Id x y) → A x y p
J A f x .x (refl .x) = f x
\end{code}

### Singleton

We say that a type `X` is a *singleton* (also called *contractable* type)
if we have an element `c : X` with `Id c x` for all `x : X`.

\begin{code}
singletonType : {U : Universe} {X : Set U} → X → Set U
singletonType x = Σ \y → Id y x
\end{code}

![path](/assets/images/issinglenton.png)

\begin{code}
isSingleton : {U : Universe} → Set U → Set U
isSingleton X = Σ \(c : X) → (x : X) → Id c x
\end{code}

### Fiber

\begin{code}
fiber
  : {U V : Universe} {X : Set U} {Y : Set V}
  → (X → Y)
  → Y
  → Set (U ⊔ V)
fiber f y = Σ \x → Id (f x) y
\end{code}

### Equivalence

\begin{code}
isEquiv
  : {U V : Universe} {X : Set U} {Y : Set V}
  → (X → Y)
  → Set (U ⊔ V)
isEquiv f = (y : _) → isSingleton(fiber f y)

Eq : {U V : Universe} → Set U → Set V → Set (U ⊔ V)
Eq X Y = Σ \(f : X → Y) → isEquiv f


η : {U : Universe} {X : Set U} (x : X) → singletonType x
η x = (x , refl x)

singletonTypesAreSingletons : {U : Universe} {X : Set U} (x : X) → isSingleton(singletonType x)
singletonTypesAreSingletons {U} {X} = h
 where
  A : (y x : X) → Id y x → Set U
  A y x p = Id (η x) (y , p)

  f : (x : X) → A x x (refl x)
  f x = refl (η x)

  φ : (y x : X) (p : Id y x) → Id (η x) (y , p)
  φ = J A f

  g : (x : X) (σ : singletonType x) → Id (η x) σ
  g x (y , p) = φ y x p

  h : (x : X) → Σ \(c : singletonType x) → (σ : singletonType x) → Id c σ
  h x = (η x , g x)

id : {U : Universe} (X : Set U) → X → X
id X x = x

idIsEquiv : {U : Universe} (X : Set U) → isEquiv(id X)
idIsEquiv X = g
 where
  g : (x : X) → isSingleton (fiber (id X) x)
  g = singletonTypesAreSingletons

IdToEq : {U : Universe} (X Y : Set U) → Id X Y → Eq X Y
IdToEq {U} = J A f
 where
  A : (X Y : Set U) → Id X Y → Set U
  A X Y p = Eq X Y

  f : (X : Set U) → A X X (refl X)
  f X = (id X , idIsEquiv X)

isUnivalent : (U : Universe) → Set (lsuc (U))
isUnivalent U = (X Y : Set U) → isEquiv(IdToEq X Y)

\end{code}
