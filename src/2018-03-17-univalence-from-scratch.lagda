---
layout: "post"
title: "Univalence From Scratch"
date: "2018-03-17"
categories: type-theory
---

M.H. Escardo. [*A self-contained, brief and complete formulation of Voevodsky's
Univalence Axiom*](https://arxiv.org/abs/1803.02294), March 2018, arXiv:1803.02294.

The author of the following code is the same author's paper, Martín Hötzel
Escardó. I put the code here for me but I modified it a little for my own
convenience. For the original version, review the link of the paper.

Basic imports:

\begin{code}
{-# OPTIONS --without-K #-}

open import Agda.Primitive
  using    (_⊔_)
  renaming (lzero to U₀ ; lsuc to _′ ; Level to Universe)
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

A type X is a *singleton* if we have
an element c : X with Id(c,x) for all x : X.

![path](/assets/images/issinglenton.png)

\begin{code}
isSingleton : {U : Universe} → Set U → Set U
isSingleton X = Σ \(c : X) → (x : X) → Id c x
\end{code}

### Fiber

\begin{code}
fiber : {U V : Universe} {X : Set U} {Y : Set V} → (X → Y) → Y → Set (U ⊔ V)
fiber f y = Σ \x → Id (f x) y
\end{code}

### Equivalence

\begin{code}
isEquiv : {U V : Universe} {X : Set U} {Y : Set V} → (X → Y) → Set (U ⊔ V)
isEquiv f = (y : _) → isSingleton(fiber f y)

-- Eq : {U V : Universe} → U ̇ → V ̇ → U ⊔ V ̇
-- Eq X Y = Σ \(f : X → Y) → isEquiv f
--
-- singletonType : {U : Universe} {X : U ̇} → X → U ̇
-- singletonType x = Σ \y → Id y x
--
-- η : {U : Universe} {X : U ̇} (x : X) → singletonType x
-- η x = (x , refl x)
--
-- singletonTypesAreSingletons : {U : Universe} {X : U ̇} (x : X) → isSingleton(singletonType x)
-- singletonTypesAreSingletons {U} {X} = h
--  where
--   A : (y x : X) → Id y x → U ̇
--   A y x p = Id (η x) (y , p)
--   f : (x : X) → A x x (refl x)
--   f x = refl (η x)
--   φ : (y x : X) (p : Id y x) → Id (η x) (y , p)
--   φ = J A f
--   g : (x : X) (σ : singletonType x) → Id (η x) σ
--   g x (y , p) = φ y x p
--   h : (x : X) → Σ \(c : singletonType x) → (σ : singletonType x) → Id c σ
--   h x = (η x , g x)
--
-- id : {U : Universe} (X : U ̇) → X → X
-- id X x = x
--
-- idIsEquiv : {U : Universe} (X : U ̇) → isEquiv(id X)
-- idIsEquiv X = g
--  where
--   g : (x : X) → isSingleton (fiber (id X) x)
--   g = singletonTypesAreSingletons
--
-- IdToEq : {U : Universe} (X Y : U ̇) → Id X Y → Eq X Y
-- IdToEq {U} = J A f
--  where
--   A : (X Y : U ̇) → Id X Y → U ̇
--   A X Y p = Eq X Y
--   f : (X : U ̇) → A X X (refl X)
--   f X = (id X , idIsEquiv X)
--
-- isUnivalent : (U : Universe) → U ′ ̇
-- isUnivalent U = (X Y : U ̇) → isEquiv(IdToEq X Y)

\end{code}

Using projections pr₁ and pr₂ rather than pattern matching on Σ types
(by defining Σ as a record type), Agda calculates the following normal
form for the term isUnivalent:

λ U → (X Y : Set U) (y : Σ (λ f → (y₁ : Y) → Σ (λ c →
(x : Σ (λ x₁ → Id (f x₁) y₁)) → Id c x))) →
Σ (λ c → (x : Σ (λ x₁ → Id (J (λ X₁ Y₁ p → Σ (λ f →
(y₁ : Y₁) → Σ (λ c₁ → (x₂ : Σ (λ x₃ → Id (f x₃) y₁)) → Id c₁ x₂)))
(λ X₁ → (λ x₂ → x₂) , (λ x₂ → (x₂ , refl x₂) , (λ yp → J (λ y₁ x₃ p →
Id (x₃ , refl x₃) (y₁ , p)) (λ x₃ → refl (x₃ , refl x₃))
(pr₁ yp) x₂ (pr₂ yp)))) X Y x₁) y)) → Id c x)

This is with lots of subterms elided. With all of them explicitly
given, the normal form of isUnivalent is

λ U → (X Y : U ̇) (y : Σ {U} {U} {X → Y} (λ f → (y₁ : Y) → Σ {U} {U}
{Σ {U} {U} {X} (λ x → Id {U} {Y} (f x) y₁)} (λ c → (x : Σ {U} {U} {X}
(λ x₁ → Id {U} {Y} (f x₁) y₁)) → Id {U} {Σ {U} {U} {X} (λ x₁ → Id {U} {Y}
(f x₁) y₁)} c x))) → Σ {U ′} {U ′} {Σ {U ′} {U} {Id {U ′} {U ̇} X Y}
(λ x → Id {U} {Σ {U} {U} {X → Y} (λ f → (y₁ : Y) → Σ {U} {U}
{Σ {U} {U} {X} (λ x₁ → Id {U} {Y} (f x₁) y₁)} (λ c → (x₁ : Σ {U} {U} {X}
(λ x₂ → Id {U} {Y} (f x₂) y₁)) → Id {U} {Σ {U} {U} {X} (λ x₂ → Id {U} {Y}
(f x₂) y₁)} c x₁))} (J {U ′} {U} {U ̇} (λ X₁ Y₁ p → Σ {U} {U} {X₁ → Y₁}
(λ f → (y₁ : Y₁) → Σ {U} {U} {Σ {U} {U} {X₁} (λ x₁ → Id {U} {Y₁} (f x₁) y₁)}
(λ c → (x₁ : Σ {U} {U} {X₁} (λ x₂ → Id {U} {Y₁} (f x₂) y₁)) → Id {U}
{Σ {U} {U} {X₁} (λ x₂ → Id {U} {Y₁} (f x₂) y₁)} c x₁))) (λ X₁ → (λ x₁ → x₁)
, (λ x₁ → (x₁ , refl x₁) , (λ yp → J {U} {U} {X₁} (λ y₁ x₂ p → Id {U}
{Σ {U} {U} {X₁} (λ y₂ → Id {U} {X₁} y₂ x₂)} (x₂ , refl x₂) (y₁ , p))
(λ x₂ → refl (x₂ , refl x₂)) (pr₁ yp) x₁ (pr₂ yp)))) X Y x) y)} (λ c →
(x : Σ {U ′} {U} {Id {U ′} {U ̇} X Y} (λ x₁ → Id {U} {Σ {U} {U} {X → Y}
(λ f → (y₁ : Y) → Σ {U} {U} {Σ {U} {U} {X} (λ x₂ → Id {U} {Y} (f x₂) y₁)}
(λ c₁ → (x₂ : Σ {U} {U} {X} (λ x₃ → Id {U} {Y} (f x₃) y₁)) → Id {U}
{Σ {U} {U} {X} (λ x₃ → Id {U} {Y} (f x₃) y₁)} c₁ x₂))} (J {U ′} {U} {U ̇}
(λ X₁ Y₁ p → Σ {U} {U} {X₁ → Y₁} (λ f → (y₁ : Y₁) → Σ {U} {U} {Σ {U} {U}
{X₁} (λ x₂ → Id {U} {Y₁} (f x₂) y₁)} (λ c₁ → (x₂ : Σ {U} {U} {X₁} (λ x₃ →
Id {U} {Y₁} (f x₃) y₁)) → Id {U} {Σ {U} {U} {X₁} (λ x₃ → Id {U} {Y₁} (f x₃)
y₁)} c₁ x₂))) (λ X₁ → (λ x₂ → x₂) , (λ x₂ → (x₂ , refl x₂) , (λ yp → J {U}
{U} {X₁} (λ y₁ x₃ p → Id {U} {Σ {U} {U} {X₁} (λ y₂ → Id {U} {X₁} y₂ x₃)}
(x₃ , refl x₃) (y₁ , p)) (λ x₃ → refl (x₃ , refl x₃)) (pr₁ yp) x₂ (pr₂ yp))))
X Y x₁) y)) → Id {U ′} {Σ {U ′} {U} {Id {U ′} {U ̇} X Y} (λ x₁ → Id {U}
{Σ {U} {U} {X → Y} (λ f → (y₁ : Y) → Σ {U} {U} {Σ {U} {U} {X} (λ x₂ →
Id {U} {Y} (f x₂) y₁)} (λ c₁ → (x₂ : Σ {U} {U} {X} (λ x₃ → Id {U} {Y} (f x₃)
y₁)) → Id {U} {Σ {U} {U} {X} (λ x₃ → Id {U} {Y} (f x₃) y₁)} c₁ x₂))}
(J {U ′} {U} {U ̇} (λ X₁ Y₁ p → Σ {U} {U} {X₁ → Y₁} (λ f → (y₁ : Y₁) →
Σ {U} {U} {Σ {U} {U} {X₁} (λ x₂ → Id {U} {Y₁} (f x₂) y₁)} (λ c₁ →
(x₂ : Σ {U} {U} {X₁} (λ x₃ → Id {U} {Y₁} (f x₃) y₁)) → Id {U} {Σ {U} {U} {X₁}
(λ x₃ → Id {U} {Y₁} (f x₃) y₁)} c₁ x₂))) (λ X₁ → (λ x₂ → x₂) , (λ x₂ → (x₂ ,
refl x₂) , (λ yp → J {U} {U} {X₁} (λ y₁ x₃ p → Id {U} {Σ {U} {U} {X₁}
(λ y₂ → Id {U} {X₁} y₂ x₃)} (x₃ , refl x₃) (y₁ , p)) (λ x₃ → refl (x₃ ,
refl x₃)) (pr₁ yp) x₂ (pr₂ yp)))) X Y x₁) y)} c x)
