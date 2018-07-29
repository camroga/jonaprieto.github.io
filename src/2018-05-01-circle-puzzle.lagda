---
layout: "post"
title: "The circle"
date: "2018-05-01"
agda: true
categories: type-theory
---

{% comment %}
  Moebius type family:

    $$
    \mathsf{rec}_{\mathbb{S}^1}\, \mathcal{U}\, 2\, (\mathsf{ua}(\mathsf{rec}_{2}\,2\,1_{2}\,0_{2})):
    \mathbb{S}^1 \to \mathcal{U}.
    $$


{: . equation }

  $$\sum\,{\mathbb{S}^1}\,(\mathsf{rec}_{\mathbb{S}^1}\, \mathcal{U}\,  2\,
  (\mathsf{ua}(\mathsf{rec}_{2}2 1_{2} 0_{2}))) \simeq \mathbb{S}^1.$$

I gave a talk giving one solution using the flattening lemma:

- [**Direct link PDF**](https://github.com/jonaprieto/flattenlem/files/2045561/Jonathan-Prieto-Cubides-The-Flattening-Lemma.pdf)

{% endcomment %}

\begin{code}
open import 2018-07-05-mini-hott
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

  where $$P (\mathsf{base}) :≡ \mathsf{Bool}$$ and $$\mathsf{ap~P~loop~=~ua~(neg)}$$.


\begin{code}
module _ {ℓ} {A : Type ℓ}(C : A → Type ℓ)
    {Z : Type ℓ}
    (d : (a : A) → C a → Z) where

  f : Σ A (λ a → C a) → Z
  f (a , b) = (d a) b


  ap-f=pair= :
      {a₁ a₂ : A}
      (α : a₁ == a₂)
      (c₁ : C a₁) (c₂ : C a₂)
      (γ : c₁ == c₂ [ C ↓ α ])
      → ap f (pair= (α , γ))
        == (begin
            f (a₁ , c₁)
              ==⟨⟩
            d a₁ c₁
              ==⟨ inv (transport-const {A = A} {P = λ _ → Z} α (d a₁ c₁)) ⟩
            tr (λ X → Z) α (d a₁ c₁)
              ==⟨ ap (λ k → tr (λ X → Z) α (d a₁ k)) idp ⟩
            tr (λ X → Z) α (d a₁ (tr C (refl a₁) c₁))
              ==⟨ ap {a = idp} {b = α · inv α} (λ k → tr (λ X → Z) α (d a₁ (tr C k c₁))) (inv (·-rinv α)) ⟩
            tr (λ X → Z) α (d a₁ (tr C (α · inv α) c₁))
              ==⟨ ap (λ k → tr (λ X → Z) α (d a₁ k)) (inv (transport-comp-h α (inv α) c₁)) ⟩
            tr (λ X → Z) α (d a₁ (tr C (inv α) (tr C α c₁)))
              ==⟨ inv (transport-fun-h α (d a₁) (tr C α c₁)) ⟩
            (tr (λ x → (C x → Z)) α (d a₁)) (tr C α c₁)
              ==⟨ happly (apd d α) (tr C α c₁) ⟩
            d a₂ (tr C α c₁)
              ==⟨ ap (d a₂) γ ⟩
            d a₂ c₂
              ==⟨⟩
            f (a₂ , c₂)
          ∎)
  ap-f=pair= idp c₁ .c₁ idp = idp

\end{code}

\begin{code}
-- -- Def.
-- neg : Bool → Bool
-- neg true  = false
-- neg false = true
--
-- neg-eq : Bool ≃ Bool
-- neg-eq = qinv-≃ neg (neg , h , h)
--   where
--     h : neg ∘ neg ∼ id
--     h true  = idp
--     h false = idp
--
-- P : S¹ → Type₀
-- P = S¹-rec Type₀ Bool (ua neg-eq)
--
-- f :  Σ S¹ (λ b → P b) → pS
-- f (s , pₛ) = {!   !}
--
-- open module gdef =
--     pS-Rec
--       (Σ S¹ (λ b → P b))
--       (base , false)
--       (base , true)
--       (pair= (loop , transport-ua P loop neg-eq (S¹-βrec Type₀ Bool (ua neg-eq)) false))
--       (pair= (loop , transport-ua P loop neg-eq (S¹-βrec Type₀ Bool (ua neg-eq)) true))
--
-- ΣSP-≃-pS : Σ S¹ (λ b → P b) ≃ pS
-- ΣSP-≃-pS = qinv-≃ f (g , f-g , g-f)
--   where
--     g : pS → Σ S¹ (λ b → P b)
--     g = gdef.rec
--
--     f-g : f ∘ g ∼ id
--     f-g !pS₀ = {!  g !pS₀ !}
--     f-g !pS₁ = {!   !}
--
--     g-f : g ∘ f ∼ id
--     g-f (s , pₛ) = {!   !}
\end{code}

{: .references }

  - {% reference hottbook %}
