---
layout: "post"
title: "The circle and one type equivalent"
date: "2018-05-01"
agda: true
categories: type-theory
---

{: .hidden }
  Moebius type family:

  {: .equation}
    $$
    \mathsf{rec}_{\mathbb{S}^1}\, \mathcal{U}\, 2\, (\mathsf{ua}(\mathsf{rec}_{2}\,2\,1_{2}\,0_{2})):
    \mathbb{S}^1 \to \mathcal{U}.
    $$

{% comment %}

{: . equation }

  $$\sum\,{\mathbb{S}^1}\,(\mathsf{rec}_{\mathbb{S}^1}\, \mathcal{U}\,  2\,
  (\mathsf{ua}(\mathsf{rec}_{2}2 1_{2} 0_{2}))) \simeq \mathbb{S}^1.$$

I gave a talk giving one solution using the flattening lemma:

- [**Direct link PDF**](https://github.com/jonaprieto/flattenlem/files/2045561/Jonathan-Prieto-Cubides-The-Flattening-Lemma.pdf)

{% endcomment %}

Let us define the circle and the hit $$S^{2/2}$$.

{: .hidden}
\begin{code}
open import 2018-07-05-hott-lib
\end{code}

##  S¹ type

The circle is an higher inductive type with one point
and one no trivial path called path as we show in the following
picture.

![path](/assets/ipe-images/circle.png)
*Figure 1. The circle type `S¹`.*

\begin{code}
private
  data !S¹ : Type₀ where
    !base : !S¹

S¹ : Type₀
S¹ = !S¹

base : S¹
base = !base

-- Nontrivial path on the circle.
postulate
  loop : base == base

-- Recursion principle on points
-- Recursion principle on points
S¹-rec : ∀ {ℓ}
       → (A : Type ℓ)
       → (a : A)
       → (p : a == a)
       --------------
       → (S¹ → A)
S¹-rec A a p !base = a

-- Recursion principle on paths
postulate
  S¹-βrec : ∀ {ℓ} (A : Type ℓ)
          → (a : A) (p : a == a)
          ------------------------------
          → ap (S¹-rec A a p) loop == p

-- Induction principle on points
S¹-ind : ∀ {ℓ} (P : S¹ → Type ℓ)
       → (x : P base)
       → (x == x [ P ↓ loop ])
       --------------------------
       → ((t : S¹) → P t)
S¹-ind P x p !base = x

-- Induction principle on paths
postulate
  S¹-βind : ∀ {ℓ} (P : S¹ → Type ℓ)
          → (x : P base)
          → (p : x == x [ P ↓ loop ])
          -------------------------------
          → apd (S¹-ind P x p) loop == p
\end{code}

## `pS` type

![path](/assets/ipe-images/tour-type.png)
*Figure 2. `pS` Type.*

\begin{code}
private
  data !pS : Type₀ where
    !pS₀ : !pS
    !pS₁ : !pS

pS : Type₀
pS = !pS

pS₀ : pS
pS₀ = !pS₀

pS₁ : pS
pS₁ = !pS₁

postulate
   p₀₁ : pS₀ == pS₁
   p₁₀ : pS₁ == pS₀

-- Recursion principle
module pS-Rec (C : Type₀)
              (c₀ c₁ : C)
              (p₀₁'  : c₀ == c₁)
              (p₁₀'  : c₁ == c₀) where

  -- Recursion principle on points
  rec : pS → C
  rec !pS₀ = c₀
  rec !pS₁ = c₁

-- -- Recursion principle on paths
  postulate
    βrec₀₁ : ap rec p₀₁ == p₀₁'
    βrec₁₀ : ap rec p₁₀ == p₁₀'

\end{code}

## Equivalence

{: .equation}
  $$
    \Sigma~S^{1}~P~\simeq~pS
  $$

  where $$P (\mathsf{base}) :≡ Bool$$ and $$\mathsf{ap~P~loop~=~ua~(neg)}$$

\begin{code}
-- Def.
neg : Bool → Bool
neg true  = false
neg false = true

neg-eq : Bool ≃ Bool
neg-eq = qinv-≃ neg (neg , h , h)
  where
    h : neg ∘ neg ∼ id
    h true  = idp
    h false = idp

P : S¹ → Type₀
P = S¹-rec Type₀ Bool (ua neg-eq)

f :  Σ S¹ (λ b → P b) → pS
f (s , pₛ) = {!   !}

open module gdef =
    pS-Rec
      (Σ S¹ (λ b → P b))
      (base , false)
      (base , true)
      (pair= (loop , transport-ua P loop neg-eq (S¹-βrec Type₀ Bool (ua neg-eq)) false))
      (pair= (loop , transport-ua P loop neg-eq (S¹-βrec Type₀ Bool (ua neg-eq)) true))

ΣSP-≃-pS : Σ S¹ (λ b → P b) ≃ pS
ΣSP-≃-pS = qinv-≃ f (g , f-g , g-f)
  where
    g : pS → Σ S¹ (λ b → P b)
    g = gdef.rec

    f-g : f ∘ g ∼ id
    f-g !pS₀ = {!   !}
    f-g !pS₁ = {!   !}

    g-f : g ∘ f ∼ id
    g-f (s , pₛ) = {!   !}
\end{code}
{: references }

  - {% reference hottbook %}
