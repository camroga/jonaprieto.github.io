---
layout: "post"
title: "The circle"
date: "2018-05-01"
agda: true
toc: true
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

-- Induction principle on points
pS-ind : ∀ {ℓ} (C : pS → Type ℓ)
       → (c₀ : C pS₀)
       → (c₁ : C pS₁)
       → (q₁ : c₀ == c₁ [ C ↓ p₀₁ ] )
       → (q₂ : c₁ == c₀ [ C ↓ p₁₀ ] )
       -------------------------------
       → ((t : pS) → C t)
pS-ind C c₀ c₁ q₁ q₂ !pS₀ = c₀
pS-ind C c₀ c₁ q₁ q₂ !pS₁ = c₁

postulate
  pS-βind₀₁ : ∀ {ℓ} (C : pS → Type ℓ)
            → (c₀   : C pS₀)
            → (c₁   : C pS₁)
            → (p₀₁' : c₀ == c₁ [ C ↓ p₀₁ ] )
            → (p₁₀' : c₁ == c₀ [ C ↓ p₁₀ ] )
            → ((t : pS) → C t)
            -------------------------------
            → apd (pS-ind C c₀ c₁ p₀₁' p₁₀') p₀₁ == p₀₁'

  pS-βind₁₀ : ∀ {ℓ} (C : pS → Type ℓ)
            → (c₀   : C pS₀)
            → (c₁   : C pS₁)
            → (p₀₁' : c₀ == c₁ [ C ↓ p₀₁ ] )
            → (p₁₀' : c₁ == c₀ [ C ↓ p₁₀ ] )
            → ((t : pS) → C t)
            -------------------------------
            → apd (pS-ind C c₀ c₁ p₀₁' p₁₀') p₁₀ == p₁₀'
\end{code}


## Equivalences

### Lemma 1

{: .equation }

  $$ \mathsf{S}^{1} \simeq \mathsf{pS}. $$

**Proof**.

Let us define the outgoing functions:

\begin{code}
-- Defs.
private
  p₀₀ : pS₀ == pS₀
  p₀₀ = p₀₁ · p₁₀

  f' : S¹ → pS
  f' = S¹-rec pS
              pS₀
              (transport (λ p → pS₀ == pS₀) loop p₀₀)

  g' : pS → S¹
  g' = pS-rec S¹ base base (loop ²) (loop ⁻¹)
\end{code}

In the following, we will need the following term:
\begin{code}
-- Def.
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
\end{code}

The proof of the homotopy $$ f' ∘ g' \sim \mathsf{id}$$.

\begin{code}
-- Homotopy.
  H₁ : f' ∘ g' ∼ id
  H₁ = pS-ind _ (refl pS₀) q₁ dpath₀ dpath₁
    where
      q₁ : f' (g' pS₁) == pS₁
      q₁ = ! p₀₀ · ! p₀₀ · p₀₁

      dpath₀ :  refl pS₀ == q₁ [ (λ z → (f' ∘ g') z == id z) ↓ p₀₁ ]
      dpath₀ =
        begin
          transport (λ z → (f' ∘ g') z == id z) p₀₁ idp
            ==⟨ transport-eq-fun (f' ∘ g') id p₀₁ idp ⟩
          ! ap (f' ∘ g') p₀₁ · idp · ap id p₀₁
            ==⟨ ·-assoc _ idp (ap id p₀₁) ⟩
          ! ap (f' ∘ g') p₀₁ · (idp · ap id p₀₁)
            ==⟨ ap (λ r → ! ap (f' ∘ g') p₀₁ · r) (·-lunit (ap id p₀₁)) ⟩
          ! ap (f' ∘ g') p₀₁  · (ap id p₀₁)
            ==⟨ ap (λ r → ! ap (f' ∘ g') p₀₁ · r) (ap-id p₀₁) ⟩
          ! ap (f' ∘ g') p₀₁ · p₀₁
            ==⟨ ap (λ r → ! r · p₀₁) (! (ap-comp g' f' p₀₁)) ⟩
          ! ap f' (ap g' p₀₁) · p₀₁
            ==⟨ ap (λ r → ! ap f' r · p₀₁) (pS-βrec₀₁ !S¹ !base !base (loop · loop) idp) ⟩
          ! ap f' (loop ²) · p₀₁
            ==⟨ ap (λ r → ! r · p₀₁) (ap-· f' loop loop) ⟩
          ! (ap f' loop · ap f' loop) · p₀₁
            ==⟨ ap (λ r → ! (r · ap f' loop) · p₀₁)
              (S¹-βrec !pS !pS₀ (transport (λ _ → !pS₀ == !pS₀) loop p₀₀)) ⟩
          ! (transport (λ p → !pS₀ == !pS₀) loop p₀₀ · ap f' loop) · p₀₁
            ==⟨ ap (λ r → ! (r · ap f' loop) · p₀₁)
                   (transport-const {A = S¹}{P = λ _ → !pS₀ == !pS₀} loop p₀₀) ⟩
          ! (p₀₀ · ap f' loop) · p₀₁
            ==⟨ ap (λ r → ! (p₀₀ · r) · p₀₁)
                   (S¹-βrec !pS !pS₀ (transport (λ _ → !pS₀ == !pS₀) loop p₀₀)) ⟩
          ! (p₀₀ · transport (λ p → !pS₀ == !pS₀) loop p₀₀) · p₀₁
            ==⟨ ap (λ r → ! (p₀₀ · r) · p₀₁)
                   (transport-const  {A = S¹}{P = λ _ → !pS₀ == !pS₀} loop p₀₀) ⟩
          ! (p₀₀ · p₀₀) · p₀₁
            ==⟨ ap (_· p₀₁) (!-· p₀₀ p₀₀) ⟩
          q₁ -- this choice was a posteriori :S
        ∎


      dpath₁ : q₁ == refl pS₀ [ (λ z → (f' ∘ g') z == id z) ↓ p₁₀ ]
      dpath₁ =
        begin
          transport  (λ z → (f' ∘ g') z == id z) p₁₀ q₁
            ==⟨ transport-eq-fun (f' ∘ g') id p₁₀ q₁ ⟩
          ! ap (f' ∘ g') p₁₀ · q₁ · ap id p₁₀
            ==⟨ ap (λ r → ! ap (f' ∘ g') p₁₀ · q₁ · r) (ap-id p₁₀) ⟩
          ! ap (f' ∘ g') p₁₀ · q₁ · p₁₀
            ==⟨ ap (λ r → ! r · q₁ · p₁₀) (! (ap-comp g' f' p₁₀)) ⟩
          ! ap f' (ap g' p₁₀) · q₁ · p₁₀
            ==⟨ ap (λ r → ! ap f' r · q₁ · p₁₀) (pS-βrec₁₀ !S¹ !base !base idp (! loop)) ⟩
          ! ap f' (! loop) · q₁ · p₁₀
            ==⟨ ap (λ r → ! r · q₁ · p₁₀) (ap-inv f' loop) ⟩
          (! ! ap f' loop) · q₁ · p₁₀
            ==⟨ ap (λ r → r · q₁ · p₁₀) (involution {p = ap f' loop}) ⟩
          ap f' loop · q₁ · p₁₀
            ==⟨ ap (λ r → r · q₁ · p₁₀)
                   (S¹-βrec !pS !pS₀ (transport (λ _ → !pS₀ == !pS₀) loop (p₀₁ · p₁₀))) ⟩
          (transport (λ p → !pS₀ == !pS₀) loop p₀₀) · q₁ · p₁₀
            ==⟨ ap (λ r → r · q₁ · p₁₀) (transport-const {P = λ _ → !pS₀ == !pS₀} loop p₀₀) ⟩
          p₀₀ · q₁ · p₁₀
            ==⟨ idp ⟩
          p₀₀ · (! p₀₀ · ! p₀₀ · p₀₁) · p₁₀
            ==⟨ ap (λ r → p₀₀ · r · p₁₀) (·-assoc (! p₀₀) (! p₀₀) p₀₁) ⟩
          p₀₀ · (! p₀₀ · (! p₀₀ · p₀₁)) · p₁₀
            ==⟨ ap (λ r → r · p₁₀) (! (·-assoc p₀₀ (! p₀₀) (! p₀₀ · p₀₁))) ⟩
          (p₀₀ · ! p₀₀ ) · (! p₀₀ · p₀₁) · p₁₀
            ==⟨ ap (λ r → r · (! p₀₀ · p₀₁) · p₁₀)  (·-rinv p₀₀) ⟩
          idp · (! p₀₀ · p₀₁) · p₁₀
            ==⟨ ap (_· p₁₀) ( ! ·-lunit ((! p₀₀ · p₀₁))) ⟩
          (! p₀₀ · p₀₁) · p₁₀
            ==⟨ ·-assoc (! p₀₀) p₀₁ p₁₀ ⟩
          ! p₀₀ · (p₀₁ · p₁₀)
            ==⟨⟩
          ! p₀₀ · p₀₀
            ==⟨ ·-linv p₀₀ ⟩
          idp
            ==⟨⟩
          refl pS₀
        ∎
\end{code}

The proof of the homotopy $$g' ∘ f' \sim \mathsf{id}$$:

\begin{code}
-- Homotopy
  H₂ : g' ∘ f' ∼ id
  H₂ = S¹-ind _ (refl !base) q
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
          ! ap g' (transport (λ p → pS₀ == pS₀) loop p₀₀) · loop
            ==⟨ ap {A = pS₀ == pS₀} (λ r → ! ap g' r · loop)
                    (transport-const {P = λ _ → S¹} loop p₀₀) ⟩
          ! ap g' p₀₀ · loop
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

Finally,

\begin{code}
-- The equivalence by quasi-inverse:
  S¹-≃-pS : S¹ ≃ pS
  S¹-≃-pS = qinv-≃ f' (g' , H₁ , H₂)
\end{code}


### Lemma 2

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

### Lemma 3

{: .equation}
  $$
    \Sigma~S^{1}~P~\simeq~pS
  $$

  where $$P (\mathsf{base}) :≡ \mathsf{Bool}$$ and $$\mathsf{ap~P~loop~=~ua~(neg)}$$.


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


ΣSP-≃-pS : Σ S¹ (λ b → P b) ≃ pS
ΣSP-≃-pS = qinv-≃ {!   !} {!   !}
  where
    d : (b : S¹) → P b → pS
    d = S¹-ind (λ z → P z → pS) d̰ p̰
      where
        d̰ : P base → pS
        d̰ x with Pbase=Bool
        d̰ true  | idp = pS₀
        d̰ false | idp = pS₁

        p̰ : d̰ == d̰ [ (λ z → P z → pS) ↓ loop ]
        p̰ = begin
              transport (λ z → P z → pS) loop d̰
                ==⟨ transport-fun loop d̰ ⟩
              (λ (x : Bool) → transport (λ z → pS) loop (d̰ (transport (λ z → P z) (! loop) x)))
                ==⟨ ap {!   !}  (happly {!   !} {!  !}) ⟩
              (λ (x : Bool) → transport (λ z → pS) loop (d̰ x))
                ==⟨ {!   !} ⟩
              (λ (x : Bool) → d̰ x)
                ==⟨⟩
              d̰
            ∎

    f :  Σ S¹ (λ b → P b) → pS
    f (b , x) = d b x

    γ₀₁   = transport-ua P loop neg-eq (S¹-βrec Type₀ Bool (ua neg-eq)) false
    g-p₀₁ = pair= (loop , γ₀₁)

    γ₁₀   = transport-ua P loop neg-eq (S¹-βrec Type₀ Bool (ua neg-eq)) true
    g-p₁₀ = pair= (loop , γ₁₀)

    g : pS → Σ S¹ (λ b → P b)
    g = -- 0   ↦ (base, 0)
        -- 1   ↦ (base, 1)
        -- p₀₁ ↦ (base, 0) == (base, 1)
        -- p₁₀ ↦ (base, 1) == (base, 0)
        pS-rec
            (Σ S¹ (λ b → P b))
            (base , false)
            (base , true)
            g-p₀₁
            g-p₁₀
\end{code}

\begin{code}
    postulate
      lemma-ap-f-γ₀₁ : ap f (pair= (loop , γ₀₁)) == p₁₀
      lemma-ap-f-γ₁₀ : ap f (pair= (loop , γ₁₀)) == p₀₁

\end{code}

Let us prove the homotopies:
\begin{code}
-- Homotopy
    f-g : f ∘ g ∼ id
    f-g = pS-ind (λ ps → (f ∘ g) ps == id ps) q₀ q₁ dpath₁ dpath₂
      where

        q₀ : (f ∘ g) pS₀ == id pS₀
        q₀ = p₁₀

        q₁ : (f ∘ g) pS₁ == id pS₁
        q₁ = p₀₁

        dpath₁ :  q₀ == q₁ [ (λ z → (f ∘ g) z == id z) ↓ p₀₁ ]
        dpath₁ =
          begin
            transport (λ z → (f ∘ g) z == id z) p₀₁ q₀
              ==⟨ transport-eq-fun (f ∘ g) id p₀₁ q₀ ⟩
            ! ap (f ∘ g) p₀₁ · q₀ · ap id p₀₁
              ==⟨ ap (! ap (f ∘ g) p₀₁ · q₀ ·_) (ap-id p₀₁) ⟩
            ! ap (f ∘ g) p₀₁ · q₀ · p₀₁
              ==⟨ ap (λ r → ! r · q₀ · p₀₁) (! ap-comp g f p₀₁) ⟩
            ! ap f (ap g p₀₁) · q₀ · p₀₁
              ==⟨ ap (λ r → ! ap f r · q₀ · p₀₁) (pS-βrec₀₁ ((Σ S¹ (λ b → P b))) (base , false) (base , true) g-p₀₁ g-p₁₀) ⟩
            ! ap f g-p₀₁ · q₀ · p₀₁
              ==⟨ ap (λ r → ! r · q₀ · p₀₁) lemma-ap-f-γ₀₁ ⟩
            ! p₁₀ · q₀ · p₀₁
              ==⟨⟩
            ! p₁₀ · p₁₀ · p₀₁
              ==⟨ ap (_· p₀₁) (·-linv p₁₀) ⟩
            idp · p₀₁
              ==⟨ ·-lunit p₀₁ ⟩
            q₁
          ∎

        dpath₂ : q₁ == q₀ [ (λ z → (f ∘ g) z == id z) ↓ p₁₀ ]
        dpath₂ =
          begin
            transport (λ z → (f ∘ g) z == id z) p₁₀ q₁
              ==⟨ transport-eq-fun (f ∘ g) id p₁₀ q₁ ⟩
            ! ap (f ∘ g) p₁₀ · q₁ · ap id p₁₀
              ==⟨ ap (! ap (f ∘ g) p₁₀ · q₁ ·_) (ap-id p₁₀) ⟩
            ! ap (f ∘ g) p₁₀ · q₁ · p₁₀
              ==⟨ ap (λ r → ! r · q₁ · p₁₀) (! ap-comp g f p₁₀) ⟩
            ! ap f (ap g p₁₀) · q₁ · p₁₀
              ==⟨ ap (λ r → ! ap f r · q₁ · p₁₀) (pS-βrec₁₀ ((Σ S¹ (λ b → P b))) (base , false) (base , true) g-p₀₁ g-p₁₀) ⟩
            ! ap f g-p₁₀ · q₁ · p₁₀
              ==⟨ ap (λ r → ! r · q₁ · p₁₀) lemma-ap-f-γ₁₀ ⟩
            ! p₀₁ · q₁ · p₁₀
              ==⟨⟩
            ! p₀₁ · p₀₁ · p₁₀
              ==⟨ ap (_· p₁₀) (·-linv p₀₁) ⟩
            idp · p₁₀
              ==⟨ ·-lunit p₁₀ ⟩
            q₀
          ∎
\end{code}

\begin{code}
-- Homotopy
    -- g-f : g ∘ f ∼ id
    -- g-f (s , pₛ) = g-f' s pₛ
    --   where
    --     g-f' : (s : S¹) → (pₛ : P s) → (g ∘ f) (s , pₛ) == id (s , pₛ)
    --     g-f' = S¹-ind {! r₀  !} {!   !} {!   !}
    -- begin
    --   {!   !}
    --     ==⟨ {!   !} ⟩
    --   {!   !}
    --     ==⟨ {!   !} ⟩
    --   {!   !}
    -- ∎
\end{code}

{: .references }

  - {% reference hottbook %}
