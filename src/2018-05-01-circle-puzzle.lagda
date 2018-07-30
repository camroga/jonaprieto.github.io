---
layout: "post"
title: "The circle"
date: "2018-05-01"
agda: true
categories: type-theory
---

In this entry, we want to show some equivalences
between the circle and other higher inductive types.

{% comment %}

{: . equation }

  $$\sum\,{\mathbb{S}^1}\,(\mathsf{rec}_{\mathbb{S}^1}\, \mathcal{U}\,  2\,
  (\mathsf{ua}(\mathsf{rec}_{2}2 1_{2} 0_{2}))) \simeq \mathbb{S}^1.$$

I gave a talk giving one solution using the flattening lemma:

- [**Direct link PDF**](https://github.com/jonaprieto/flattenlem/files/2045561/Jonathan-Prieto-Cubides-The-Flattening-Lemma.pdf)

{% endcomment %}

\begin{code}
open import 2018-07-06-mini-hott
\end{code}

##  S¹ type

The circle is the higher inductive type with one point
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
S¹-rec : ∀ {ℓ}
       → (A : Type ℓ)
       → (a : A)
       → (p : a == a)
       --------------
       → (S¹ → A)
S¹-rec A a p !base = a

-- Recursion principle on paths
postulate
  S¹-βrec : ∀ {ℓ}
          → (A : Type ℓ)
          → (a : A)
          → (p : a == a)
          -----------------------------
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
  data !pS : Type lzero where
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

-- Recursion principle on points
pS-rec : (C : Type₀)
       → (c₀ c₁ : C)
       → (p₀₁'  : c₀ == c₁)
       → (p₁₀'  : c₁ == c₀)
       --------------------
       → (pS → C)
pS-rec _ c₀ _  _ _ !pS₀ = c₀
pS-rec _ _  c₁ _ _ !pS₁ = c₁

-- Recursion principle on paths
postulate
  pS-βrec₀₁ : (C : Type₀)
            → (c₀ c₁ : C)
            → (p₀₁'  : c₀ == c₁)
            → (p₁₀'  : c₁ == c₀)
            -----------------------
            → ap (pS-rec C c₀ c₁ p₀₁' p₁₀') p₀₁ == p₀₁'

  pS-βrec₁₀ : (C : Type₀)
            → (c₀ c₁ : C)
            → (p₀₁'  : c₀ == c₁)
            → (p₁₀'  : c₁ == c₀)
            -----------------------
            →  ap (pS-rec C c₀ c₁ p₀₁' p₁₀') p₁₀ == p₁₀'

\end{code}


\begin{code}
private
  f' : S¹ → pS
  f' = S¹-rec pS
              pS₀
              (transport (λ p → pS₀ == pS₀) loop (p₀₁ · p₁₀))

  g' : pS → S¹
  g' = pS-rec S¹ base base (loop ²) (loop ⁻¹)

  aux-path : (loop ²) · (loop ⁻¹) == loop
  aux-path = begin
                (loop ²) · (loop ⁻¹)
                  ==⟨ ·-assoc loop loop (! loop) ⟩
                loop · (loop · ! loop)
                  ==⟨ ap (λ r → loop · r) (·-rinv loop) ⟩
                loop · idp
                  ==⟨ ! (·-runit loop)    ⟩
                loop
              ∎

  -- H₁ : f' ∘ g' ∼ id
  -- H₁ x = pS-rec _ {!   !} {!   !} {!   !} {!   !} x

  H₂ : g' ∘ f' ∼ id
  H₂ = S¹-ind _ idp q
    where
      q : refl !base == refl !base [ (λ z → (g' ∘ f') z == id z) ↓ loop ]
      q =
        begin
          transport (λ z → (g' ∘ f') z == id z) loop idp
            ==⟨ transport-eq-fun (g' ∘ f') id loop idp ⟩
          ! (ap (g' ∘ f') loop) · idp · ap id loop
            ==⟨ ap (λ r → ! (ap (g' ∘ f') loop) · idp · r) (ap-id loop) ⟩
          ! (ap (g' ∘ f') loop) · idp · loop
            ==⟨ ·-assoc _ idp loop ⟩
          ! (ap (g' ∘ f') loop) · (idp · loop)
            ==⟨ ap (λ r → ! (ap (g' ∘ f') loop) · r) (·-lunit loop) ⟩
          ! (ap (g' ∘ f') loop) · loop
            ==⟨ ap  (λ r → ! r · loop) (! (ap-comp f' g' loop)) ⟩
          ! ap g' (ap f' loop) · loop
            ==⟨ ap {A = pS₀ == pS₀} (λ r → ( ! (ap g' r)) · loop) (S¹-βrec !pS !pS₀ _) ⟩
          ! ap g' (transport (λ p → pS₀ == pS₀) loop (p₀₁ · p₁₀)) · loop
            ==⟨ ap {A = pS₀ == pS₀} (λ r → ! ap g' r · loop)
                    (transport-const {P = λ _ → S¹} loop (p₀₁ · p₁₀)) ⟩
          ! ap g' (p₀₁ · p₁₀) · loop
            ==⟨ ap (λ r → ! r · loop)  (ap-· g' p₀₁ p₁₀) ⟩
          ! (ap g' p₀₁ · ap g' p₁₀) · loop
            ==⟨ ap {A = !base == !base} (λ r → ! (r · ap g' p₁₀) · loop)
                   (pS-βrec₀₁ !S¹ !base !base (loop · loop) idp) ⟩ 
          ! ((loop ²) · ap g' p₁₀) · loop
            ==⟨ ap {A = !base == !base} (λ r → ! ( loop · loop · r) · loop)
                   (pS-βrec₁₀ !S¹ !base !base idp (inv loop)) ⟩
          ! ((loop ²) · ! loop) · loop
            ==⟨ ap (λ r →  ! r · loop) aux-path ⟩
          ! loop · loop
            ==⟨ ·-linv loop ⟩
           idp
        ∎


\end{code}
## Equivalence

{: .equation}
  $$
    \Sigma~S^{1}~P~\simeq~pS
  $$

  where $$P (\mathsf{base}) :≡ \mathsf{Bool}$$ and $$\mathsf{ap~P~loop~=~ua~(neg)}$$.

### Lemmas

- Action on paths of pairs

\begin{code}
module _ {ℓ} {A : Type ℓ}(C : A → Type ℓ)
    {Z : Type ℓ}
    (d : (a : A) → C a → Z) where

  private
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
            ==⟨ ap {b = α · ! α} (λ k → tr (λ X → Z) α (d a₁ (tr C k c₁))) (! ·-rinv α) ⟩
          tr (λ X → Z) α (d a₁ (tr C (α · ! α) c₁))
            ==⟨ ap (λ k → tr (λ X → Z) α (d a₁ k)) (! transport-comp-h α (! α) c₁) ⟩
          tr (λ X → Z) α (d a₁ (tr C (! α) (tr C α c₁)))
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

Pbase=Bool : P base == Bool
Pbase=Bool = idp


-- ΣSP-≃-pS : Σ S¹ (λ b → P b) ≃ pS
-- ΣSP-≃-pS = qinv-≃ f (g , f-g , g-f)
--   where
--     d : (b : S¹) → P b → pS
--     d = S¹-ind (λ z → P z → pS) d̰ p̰
--       where
--         d̰ : P base → pS
--         d̰ x with Pbase=Bool
--         d̰ true  | idp = pS₀
--         d̰ false | idp = pS₁
--
--         p̰ : d̰ == d̰ [ (λ z → P z → pS) ↓ loop ]
--         p̰ = {!   !}
--
--     -- d b x with Pbase=Bool
--     -- d !base true  | idp = pS₀
--     -- d !base false | idp = pS₁
--
--     f :  Σ S¹ (λ b → P b) → pS
--     f (b , x) = d b x
--
--     g : pS → Σ S¹ (λ b → P b)
--     g = -- 0   ↦ (base, 0)
--         -- 1   ↦ (base, 1)
--         -- p₀₁ ↦ (base, 0) == (base, 1)
--         -- p₁₀ ↦ (base, 1) == (base, 0)
--         pS-rec
--             (Σ S¹ (λ b → P b))
--             (base , false)
--             (base , true)
--             (pair= (loop , transport-ua P loop neg-eq (S¹-βrec Type₀ Bool (ua neg-eq)) false))
--             (pair= (loop , transport-ua P loop neg-eq (S¹-βrec Type₀ Bool (ua neg-eq)) true))
--


    -- f-g : f ∘ g ∼ id
    -- f-g !pS₀ = {! def  !}
    -- f-g !pS₁ = {!   !}
    --
    -- g-f : g ∘ f ∼ id
    -- g-f (s , pₛ) = {!   !}
\end{code}

{: .references }

  - {% reference hottbook %}
