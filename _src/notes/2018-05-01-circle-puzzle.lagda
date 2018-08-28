---
layout: "post"
title: "Circle Equivalences"
date: "2018-05-01"
author: "Jonathan Prieto-Cubides"
author_affiliation: "University of Bergen"
coauthor: "Marc Bezem"
coauthor_affiliation: "University of Bergen"
bibtexauthors: "Prieto-Cubides, Jonathan and Bezem, Marc"
bibtextag: "prietobezem:circle"
categories: type-theory
references: true
toc: true
agda: true
gallery: true
latex: true
showcitation: true
---

{: .only-website }
  *This is a work in progress jointly with Marc Bezem. Some of
  the following proofs are collapsed or hidden to reduce the size of the document.
  Nevertheless, the reader can click on them to open the full description.
  Pictures are also clickable.*

In this entry, we want to show some equivalences
between the circle and other higher inductive types.

{% comment %}

{: .equation }

  $$\sum\,{\mathbb{S}^1}\,(\mathsf{rec}_{\mathbb{S}^1}\, \mathcal{U}\,  2\,
  (\mathsf{ua}(\mathsf{rec}_{2}2 1_{2} 0_{2}))) \simeq \mathbb{S}^1.$$

Using the flattening lemma we can prove this equivalence:

- [**Direct link PDF**](https://github.com/jonaprieto/flattenlem/files/2045561/Jonathan-Prieto-Cubides-The-Flattening-Lemma.pdf)

{% endcomment %}


\begin{code}
{-# OPTIONS --without-K #-}

open import 2018-07-06-mini-hott
module _ where
\end{code}

##  `S¹` type

The circle is the higher inductive type with one point and one no trivial path
called *path* as we can see in the following picture.

![path](/assets/ipe-images/circle.png){: width="%30" }
*Figure 1. The circle type `S¹`.*

### Definition

\begin{code}
-- Definition of the Circle S¹ using an Agda hack.
module _ where
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
\end{code}

{: .foldable until="0" }
\begin{code}
  -- Def. loop^2
  _²
    : ∀ {ℓ} {A : Type ℓ} {a : A}
    → a == a
    --------
    → a == a

  p ² = p · p
\end{code}

### Recursion principle

Recursion principle on points:

\begin{code}
  -- Def.
  S¹-rec
    : ∀ {ℓ}
    → (A : Type ℓ)
    → (a : A)
    → (p : a == a)
    --------------
    → (S¹ → A)

  S¹-rec A a p !base = a
\end{code}

Recursion on paths:

\begin{code}
  -- Postulate.
  postulate
    S¹-βrec
      : ∀ {ℓ}
      → (A : Type ℓ)
      → (a : A)
      → (p : a == a)
      -----------------------------
      → ap (S¹-rec A a p) loop == p
\end{code}

### Induction principle

Induction principle on points:

\begin{code}
  -- Def.
  S¹-ind
    : ∀ {ℓ} (P : S¹ → Type ℓ)
    → (x : P base)
    → (x == x [ P ↓ loop ])
    ------------------------
    → ((t : S¹) → P t)

  S¹-ind P x p !base = x
\end{code}

Induction principle on paths:

\begin{code}
  -- Postulate.
  postulate
    S¹-βind
      : ∀ {ℓ} (P : S¹ → Type ℓ)
      → (x : P base)
      → (p : x == x [ P ↓ loop ])
      -------------------------------
      → apd (S¹-ind P x p) loop == p
\end{code}

## `pS` type

The `pS` type as the figure below shows, it is a circle with two edges
in opposite direction between two points. Notice this HIT is just different
form the suspension of booleans (Σ 2) by reversing one arrow.

![path](/assets/ipe-images/tour-type.png){: width="%40" }
*Figure 2. `pS` Type.*

\begin{code}
-- Definition of pS type using an Agda hack.
module _ where
  private
    data #!pS : Type lzero where
      #!pS₀ : #!pS
      #!pS₁ : #!pS

    data !pS : Type lzero where
      !ps : #!pS → (Unit → Unit) → !pS

  pS : Type₀
  pS = !pS

  pS₀ : pS
  pS₀ = !ps #!pS₀ _

  pS₁ : pS
  pS₁ = !ps #!pS₁ _

  postulate
    p₀₁ : pS₀ == pS₁
    p₁₀ : pS₁ == pS₀
\end{code}

### Recursion principle

Recursion principle on points:

\begin{code}
  -- Def.
  pS-rec
    : (C : Type₀)
    → (c₀ c₁ : C)
    → (p₀₁'  : c₀ == c₁)
    → (p₁₀'  : c₁ == c₀)
    --------------------
    → (pS → C)

  pS-rec C c₀ c₁ p₀₁' p₁₀' (!ps #!pS₀ x₁) = c₀
  pS-rec C c₀ c₁ p₀₁' p₁₀' (!ps #!pS₁ x₁) = c₁
\end{code}

Recursion principle on paths:

\begin{code}
  -- Postulate.
  postulate
    pS-βrec₀₁
      : (C : Type₀)
      → (c₀ c₁ : C)
      → (p₀₁'  : c₀ == c₁)
      → (p₁₀'  : c₁ == c₀)
      -------------------------------------------
      → ap (pS-rec C c₀ c₁ p₀₁' p₁₀') p₀₁ == p₀₁'

    pS-βrec₁₀
      : (C : Type₀)
      → (c₀ c₁ : C)
      → (p₀₁'  : c₀ == c₁)
      → (p₁₀'  : c₁ == c₀)
      --------------------------------------------
      →  ap (pS-rec C c₀ c₁ p₀₁' p₁₀') p₁₀ == p₁₀'
\end{code}

### Induction principle

Induction principle on points:

\begin{code}
  -- Def.
  pS-ind
    : ∀ {ℓ} (C : pS → Type ℓ)
    → (c₀ : C pS₀)
    → (c₁ : C pS₁)
    → (q₁ : c₀ == c₁ [ C ↓ p₀₁ ])
    → (q₂ : c₁ == c₀ [ C ↓ p₁₀ ])
    -----------------------------
    → ((t : pS) → C t)

  pS-ind C c₀ c₁ q₁ q₂ (!ps #!pS₀ x₁) = c₀
  pS-ind C c₀ c₁ q₁ q₂ (!ps #!pS₁ x₁) = c₁
\end{code}

Induction principle on paths:

\begin{code}
  -- Postulate.
  postulate
    pS-βind₀₁
      : ∀ {ℓ} (C : pS → Type ℓ)
      → (c₀   : C pS₀)
      → (c₁   : C pS₁)
      → (p₀₁' : c₀ == c₁ [ C ↓ p₀₁ ])
      → (p₁₀' : c₁ == c₀ [ C ↓ p₁₀ ])
      → ((t : pS) → C t)
      --------------------------------------------
      → apd (pS-ind C c₀ c₁ p₀₁' p₁₀') p₀₁ == p₀₁'

    pS-βind₁₀
      : ∀ {ℓ} (C : pS → Type ℓ)
      → (c₀   : C pS₀)
      → (c₁   : C pS₁)
      → (p₀₁' : c₀ == c₁ [ C ↓ p₀₁ ])
      → (p₁₀' : c₁ == c₀ [ C ↓ p₁₀ ])
      → ((t : pS) → C t)
      -------------------------------------------
      → apd (pS-ind C c₀ c₁ p₀₁' p₁₀') p₁₀ == p₁₀'
\end{code}


## `S¹ ≃ pS`

**Lemma 1** . $$ \mathsf{S}^{1} \simeq \mathsf{pS}. $$

**Proof**. We proceed as usual. Defining the outgoing functions and proving
the homotopies. We prove the equivalence by quasiinverse equivalence.

Let `p₀₀` be the path defined as follows. We want to correspond this path with
the `loop` path in order to show the equivalence.

\begin{code}
p₀₀ : pS₀ == pS₀
p₀₀ = p₀₁ · p₁₀
\end{code}

#### Outgoing functions

\begin{code}
module Lemma₁ where

  private
    f : S¹ → pS
    f = S¹-rec pS pS₀ (transport (λ p → pS₀ == pS₀) loop p₀₀)

    g : pS → S¹
    g = pS-rec S¹ base base (loop ²) (loop ⁻¹)
\end{code}

####  `f ∘ g ~ id`

To prove the homotopy $$ f ∘ g \sim \mathsf{id}$$,
we prove for the pS₁ case and the case for paths.

- Case on `pS₁`:

\begin{code}
  -- Def.
  q₁ : f (g pS₁) == pS₁
  q₁ = ! p₀₀ · ! p₀₀ · p₀₁
\end{code}

Case on paths:

{: .foldable until="2" }
\begin{code}
  -- Def.
  dpath₀ :  refl pS₀ == q₁ [ (λ z → (f ∘ g) z == id z) ↓ p₀₁ ]
  dpath₀ =
    begin
      transport (λ z → (f ∘ g) z == id z) p₀₁ idp
        ==⟨ transport-eq-fun (f ∘ g) id p₀₁ idp ⟩
      ! ap (f ∘ g) p₀₁ · idp · ap id p₀₁
        ==⟨ ·-assoc _ idp (ap id p₀₁) ⟩
      ! ap (f ∘ g) p₀₁ · (idp · ap id p₀₁)
        ==⟨ ap (λ r → ! ap (f ∘ g) p₀₁ · r) (·-lunit (ap id p₀₁)) ⟩
      ! ap (f ∘ g) p₀₁  · (ap id p₀₁)
        ==⟨ ap (λ r → ! ap (f ∘ g) p₀₁ · r) (ap-id p₀₁) ⟩
      ! ap (f ∘ g) p₀₁ · p₀₁
        ==⟨ ap (λ r → ! r · p₀₁) (! (ap-comp g f p₀₁)) ⟩
      ! ap f (ap g p₀₁) · p₀₁
        ==⟨ ap (λ r → ! ap f r · p₀₁) (pS-βrec₀₁ S¹ base base (loop · loop) idp) ⟩
      ! ap f (loop ²) · p₀₁
        ==⟨ ap (λ r → ! r · p₀₁) (ap-· f loop loop) ⟩
      ! (ap f loop · ap f loop) · p₀₁
        ==⟨ ap (λ r → ! (r · ap f loop) · p₀₁)
          (S¹-βrec pS pS₀ (transport (λ _ → pS₀ == pS₀) loop p₀₀)) ⟩
      ! (transport (λ p → pS₀ == pS₀) loop p₀₀ · ap f loop) · p₀₁
        ==⟨ ap (λ r → ! (r · ap f loop) · p₀₁) (transport-const loop p₀₀) ⟩
      ! (p₀₀ · ap f loop) · p₀₁
        ==⟨ ap (λ r → ! (p₀₀ · r) · p₀₁)
               (S¹-βrec pS pS₀ (transport (λ _ → pS₀ == pS₀) loop p₀₀)) ⟩
      ! (p₀₀ · transport (λ p → pS₀ == pS₀) loop p₀₀) · p₀₁
        ==⟨ ap (λ r → ! (p₀₀ · r) · p₀₁)(transport-const loop p₀₀) ⟩
      ! (p₀₀ · p₀₀) · p₀₁
        ==⟨ ap (_· p₀₁) (!-· p₀₀ p₀₀) ⟩
      q₁
    ∎
\end{code}

{: .foldable until="2" }
\begin{code}
  -- Def.
  dpath₁ : q₁ == refl pS₀ [ (λ z → (f ∘ g) z == id z) ↓ p₁₀ ]
  dpath₁ =
    begin
      transport  (λ z → (f ∘ g) z == id z) p₁₀ q₁
        ==⟨ transport-eq-fun (f ∘ g) id p₁₀ q₁ ⟩
      ! ap (f ∘ g) p₁₀ · q₁ · ap id p₁₀
        ==⟨ ap (λ r → ! ap (f ∘ g) p₁₀ · q₁ · r) (ap-id p₁₀) ⟩
      ! ap (f ∘ g) p₁₀ · q₁ · p₁₀
        ==⟨ ap (λ r → ! r · q₁ · p₁₀) (! (ap-comp g f p₁₀)) ⟩
      ! ap f (ap g p₁₀) · q₁ · p₁₀
        ==⟨ ap (λ r → ! ap f r · q₁ · p₁₀) (pS-βrec₁₀ S¹ base base idp (! loop)) ⟩
      ! ap f (! loop) · q₁ · p₁₀
        ==⟨ ap (λ r → ! r · q₁ · p₁₀) (ap-inv f loop) ⟩
      (! ! ap f loop) · q₁ · p₁₀
        ==⟨ ap (λ r → r · q₁ · p₁₀) (involution {p = ap f loop}) ⟩
      ap f loop · q₁ · p₁₀
        ==⟨ ap (λ r → r · q₁ · p₁₀)
               (S¹-βrec pS pS₀
               (transport (λ _ → pS₀ == pS₀) loop (p₀₁ · p₁₀))) ⟩
      (transport (λ p → pS₀ == pS₀) loop p₀₀) · q₁ · p₁₀
        ==⟨ ap (λ r → r · q₁ · p₁₀) (transport-const loop p₀₀) ⟩
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

Finally, by path induction on `pS` type, we got the homotopy.

\begin{code}
  -- Homotopy.
  H₁ : f ∘ g ∼ id
  H₁ = pS-ind _ (refl pS₀) q₁ dpath₀ dpath₁
\end{code}

####  g ∘ f ~ id

To prove this homotopy $$g ∘ f \sim \mathsf{id}$$, we proceed by induction on
the circle. For the `base` case, `refl base` works since `g (f base)` is
definitionally equal to `base`.

\begin{code}
  -- Def.
  H₂-base : base == base
  H₂-base = refl base
\end{code}

The rest is how we prove the case for action on `loop`.

We will need the term `aux-path` which is:

{: .foldable until="2"}
\begin{code}
  -- Def.
  aux-path : (loop ²) · (loop ⁻¹) == loop
  aux-path =
    begin
      (loop ²) · (loop ⁻¹)
        ==⟨ ·-assoc loop loop (! loop) ⟩
      loop · (loop · ! loop)
        ==⟨ ap (loop ·_) (·-rinv loop) ⟩
      loop · idp
        ==⟨ ! (·-runit loop) ⟩
      loop
    ∎
\end{code}

{: .foldable until="2" }
\begin{code}
  -- Def.
  H₂-loop : refl base == refl base [ (λ z → (g ∘ f) z == id z) ↓ loop ]
  H₂-loop =
    begin
      transport (λ z → (g ∘ f) z == id z) loop idp
        ==⟨ transport-eq-fun (g ∘ f) id loop idp ⟩
      ! (ap (g ∘ f) loop) · idp · ap id loop
        ==⟨ ap (λ r → ! (ap (g ∘ f) loop) · idp · r) (ap-id loop) ⟩
      ! (ap (g ∘ f) loop) · idp · loop
        ==⟨ ·-assoc _ idp loop ⟩
      ! (ap (g ∘ f) loop) · (idp · loop)
        ==⟨ ap (λ r → ! (ap (g ∘ f) loop) · r) (·-lunit loop) ⟩
      ! (ap (g ∘ f) loop) · loop
        ==⟨ ap  (λ r → ! r · loop) (! (ap-comp f g loop)) ⟩
      ! ap g (ap f loop) · loop
        ==⟨ ap {A = pS₀ == pS₀} (λ r → ( ! (ap g r)) · loop)
                                (S¹-βrec pS pS₀ _) ⟩
      ! ap g (transport (λ p → pS₀ == pS₀) loop p₀₀) · loop
        ==⟨ ap {A = pS₀ == pS₀} (λ r → ! ap g r · loop)
                (transport-const loop p₀₀) ⟩
      ! ap g p₀₀ · loop
        ==⟨ ap (λ r → ! r · loop)  (ap-· g p₀₁ p₁₀) ⟩
      ! (ap g p₀₁ · ap g p₁₀) · loop
        ==⟨ ap {A = base == base} (λ r → ! (r · ap g p₁₀) · loop)
               (pS-βrec₀₁ S¹ base base (loop · loop) idp) ⟩
      ! ((loop ²) · ap g p₁₀) · loop
        ==⟨ ap {A = base == base} (λ r → ! ( loop · loop · r) · loop)
               (pS-βrec₁₀ S¹ base base idp (inv loop)) ⟩
      ! ((loop ²) · ! loop) · loop
        ==⟨ ap (λ r →  ! r · loop) aux-path ⟩
      ! loop · loop
        ==⟨ ·-linv loop ⟩
       idp
    ∎
\end{code}

\begin{code}
  -- Homotopy
  H₂ : g ∘ f ∼ id
  H₂ = S¹-ind _ H₂-base H₂-loop
\end{code}

Finally, we complete the proof of the equivalence.

\begin{code}
  -- Equivalence.
  S¹-≃-pS : S¹ ≃ pS
  S¹-≃-pS = qinv-≃ f (g , H₁ , H₂)
\end{code}

## Action on paths of pairs

We need to understand how is the action on paths of pairs which appears as Lemma
6.12.7 in {% cite hottbook %}.

Let's define out context for this lemma:

\begin{code}
module Lemma₂ {ℓ}
  {A : Type ℓ}
  (C : A → Type ℓ)
  {Z : Type ℓ}
  (d : (a : A) → C a → Z) where

  private
    f : Σ A (λ a → C a) → Z
    f (a , b) = (d a) b
\end{code}

And this lemma says:

\begin{code}
  -- Lemma.
  ap-f-pair=
    : {a₁ a₂ : A}
    → (α : a₁ == a₂)
    → (c₁ : C a₁) (c₂ : C a₂)
    → (γ : c₁ == c₂ [ C ↓ α ])
    ---------------------------
    → ap f (pair= (α , γ))
        ==
     (begin
        f (a₁ , c₁)
          ==⟨⟩
        d a₁ c₁
          ==⟨ ! (transport-const  α (d a₁ c₁)) ⟩
        tr (λ X → Z) α (d a₁ c₁)
          ==⟨ ap (λ k → tr (λ X → Z) α (d a₁ k)) idp ⟩
        tr (λ X → Z) α (d a₁ (tr C (refl a₁) c₁))
          ==⟨ (! ·-rinv α) |in-ctx (λ k → tr (λ X → Z) α (d a₁ (tr C k c₁)))  ⟩
        tr (λ X → Z) α (d a₁ (tr C (α · ! α) c₁))
          ==⟨ (! transport-comp-h α (! α) c₁) |in-ctx (λ k → tr (λ X → Z) α (d a₁ k))⟩
        tr (λ X → Z) α (d a₁ (tr C (! α) (tr C α c₁)))
          ==⟨ ! (transport-fun-h α (d a₁) (tr C α c₁)) ⟩
        (tr (λ x → (C x → Z)) α (d a₁)) (tr C α c₁)
          ==⟨ happly (apd d α) (tr C α c₁) ⟩
        d a₂ (tr C α c₁)
          ==⟨ ap (d a₂) γ ⟩
        d a₂ c₂
          ==⟨⟩
        f (a₂ , c₂)
      ∎)

  ap-f-pair= idp c₁ .c₁ idp = idp
open Lemma₂
\end{code}

##  Σ S¹ P ≃ pS

**Lemma 3.** $$ \Sigma~S^{1}~P~\simeq~pS $$ where
$$P (\mathsf{base}) :≡ \mathsf{Bool}$$ and $$\mathsf{ap~P~loop~=~ua~(neg)}$$.

\begin{code}
module Lemma₃ where

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
\end{code}

Now, using the negation function as an equivalence, we define the family of types `P`
over the circle S¹.

\begin{code}
P : S¹ → Type₀
P = S¹-rec Type₀ Bool (ua neg-eq)
\end{code}

Two auxiliar lemmas for the latter:

{: .foldable until="1" }
\begin{code}
aux-lemma₀ : (x : P base) → neg x == x [ P ↓ loop ]

aux-lemma₀ x =
  (begin
    transport P loop (neg x)
      ==⟨ transport-ua P loop neg-eq (S¹-βrec Type₀ Bool (ua neg-eq)) (neg x) ⟩
    neg (neg x)
      ==⟨ neg-neg x ⟩
    refl x)
  where
    neg-neg : (x : P base) → neg (neg x) == x
    neg-neg true  = idp
    neg-neg false = idp
\end{code}

{: .foldable until="1" }
\begin{code}
aux-lemma₁ : (x : P base) → x == neg x [ P ↓ ! loop ]

aux-lemma₁ x =
  let
    apP!loop :  ap P (! loop) == ua (invEqv neg-eq)
    apP!loop =
      begin
        ap P (! loop)
          ==⟨ ap-inv P loop ⟩
        ! ap P loop
          ==⟨ ap (!_) (S¹-βrec Type₀ Bool (ua (neg-eq))) ⟩
        ! ua (neg-eq)
          ==⟨ ! (ua-inv neg-eq) ⟩
        ua (invEqv neg-eq)
      ∎
  in
  begin
    transport P (! loop) x
      ==⟨ transport-ua P (! loop) (invEqv neg-eq) apP!loop x ⟩
    fun≃ (invEqv (neg-eq)) x
      ==⟨⟩
    fun≃ (neg-eq) x
      ==⟨⟩
    neg x
  ∎
\end{code}

### f : Σ S¹ P → pS

{: .foldable until="11" }
\begin{code}
f :  Σ S¹ P → pS
f (b , x) = f̰ b x
  where
  f̰ : (b : S¹) → P b → pS
  f̰ = S¹-ind (λ z → P z → pS) d̰ p̰
    where
      d̰ : P base → pS
      d̰ true  = pS₁
      d̰ false = pS₀

      p̰ : d̰ == d̰ [ (λ z → P z → pS) ↓ loop ]
      p̰  =
        (begin
          transport (λ z → P z → pS) loop d̰
            ==⟨ transport-fun loop d̰ ⟩
          (λ (x : P base) → transport (λ z → pS) loop
                              (d̰ (transport (λ z → P z) (! loop) x)))
            ==⟨ funext (λ (pb : P base) → transport-const loop
                              (d̰ (transport (λ z → P z) (! loop) pb))) ⟩
          (λ (x : P base) → (d̰ (transport (λ z → P z) (! loop) x)))
            ==⟨ funext (λ (pb : P base) → ap d̰ (aux-lemma₁ pb)) ⟩
          (λ (x : P base) → d̰ (neg x) )
            ==⟨ funext aux-lemma₂ ⟩
          d̰
         ∎)
       where
         aux-lemma₂ : (x : P base) → d̰ (neg x) == d̰ x
         aux-lemma₂ true  = p₀₁
         aux-lemma₂ false = p₁₀
\end{code}

\begin{code}
-- Defs.
γ₀₁   : tr P loop false == true
γ₀₁   = transport-ua P loop neg-eq (S¹-βrec Type₀ Bool (ua neg-eq)) false

g-p₀₁ : (base , false ) == (base , true)
g-p₀₁ = pair= (loop , γ₀₁)

γ₁₀   : tr P loop true == false
γ₁₀   = transport-ua P loop neg-eq (S¹-βrec Type₀ Bool (ua neg-eq)) true

g-p₁₀ : (base , true ) == ( base , false)
g-p₁₀ = pair= (loop , γ₁₀)
\end{code}

### g : pS → Σ S¹ P

\begin{code}
g : pS → Σ S¹ P
g = -- 0   ↦ (base, 0)
    -- 1   ↦ (base, 1)
    -- p₀₁ ↦ (base, 0) == (base, 1)
    -- p₁₀ ↦ (base, 1) == (base, 0)
    pS-rec
        (Σ S¹ P)
        (base , false)
        (base , true)
        g-p₀₁
        g-p₁₀
\end{code}

\begin{code}
ct : P base → pS
ct true  = pS₁
ct false = pS₀
\end{code}

\begin{code}
ctp : P base → Σ S¹ P
ctp b = base , b
\end{code}

\begin{code}
ptp : (y : P base) → ctp y == ctp (neg y)
ptp true  = pair= (loop , γ₁₀)
ptp false = pair= (loop , γ₀₁)
\end{code}

\begin{code}
c : (b : P base) → (g ∘ f) (base , b) == id (base , b)
c true  = refl (base , true)
c false = refl (base , false)
\end{code}

\begin{code}
Q : (s : S¹) → Type _
Q = (λ z → (b : P z) → (g ∘ f) (z , b) == id (z , b))
\end{code}

\begin{code}

d : (a : S¹) → (c : P a) → pS
d a c = f (a , c)

module L2 = Lemma₂ {_} {S¹} P {pS} d
\end{code}

\begin{code}
postulate -- Lemma 6.12.8
  lemma-ap-f-γ₀₁ : ap f (pair= (loop , γ₀₁)) == p₀₁
  lemma-ap-f-γ₁₀ : ap f (pair= (loop , γ₁₀)) == p₁₀
\end{code}

\begin{code}
p : (b : P base) → tr (λ w → (g ∘ f) w == id w) (ptp b) (c b) == c (neg b)
p true  =
  begin
    tr (λ w → (g ∘ f) w == id w) (ptp true) (c true)
      ==⟨ idp ⟩
    tr (λ w → (g ∘ f) w == id w) (pair= (loop , γ₁₀)) idp
      ==⟨ transport-eq-fun (g ∘ f) id (pair= (loop , γ₁₀)) idp ⟩
    ! ap (g ∘ f) (pair= (loop , γ₁₀)) · idp · ap id (pair= (loop , γ₁₀))
      ==⟨ ap (λ r → ! (ap (g ∘ f) (pair= (loop , γ₁₀))) · idp · r) (ap-id (pair= (loop , γ₁₀))) ⟩
    ! ap (g ∘ f) (pair= (loop , γ₁₀)) · idp · (pair= (loop , γ₁₀))
      ==⟨ ap (λ r → r · pair= (loop , γ₁₀)) (! (·-runit (! ap (g ∘ f) (pair= (loop , γ₁₀))))) ⟩
    ! ap (g ∘ f) (pair= (loop , γ₁₀)) · (pair= (loop , γ₁₀))
      ==⟨ ap (λ r → ! r · pair= (loop , γ₁₀)) (! ap-comp f g (pair= (loop , γ₁₀))) ⟩
    ! ap g (ap f (pair= (loop , γ₁₀))) · (pair= (loop , γ₁₀))
      ==⟨ ap (λ r → ! ap g r · pair= (loop , γ₁₀)) lemma-ap-f-γ₁₀ ⟩
    ! ap g p₁₀ · (pair= (loop , γ₁₀))
      ==⟨ ap (λ r → ! r · pair= (loop , γ₁₀)) (pS-βrec₁₀ (Σ S¹ P) (base , false) (base , true) g-p₀₁ g-p₁₀) ⟩
    ! g-p₁₀ · (pair= (loop , γ₁₀))
      ==⟨ idp ⟩
    ! (pair= (loop , γ₁₀)) · (pair= (loop , γ₁₀))
      ==⟨ ·-linv (pair= (loop , γ₁₀)) ⟩
    idp
  ∎

p false =
  begin
    tr (λ w → (g ∘ f) w == id w) (ptp false) (c false)
      ==⟨ idp ⟩
    tr (λ w → (g ∘ f) w == id w) (pair= (loop , γ₀₁)) idp
      ==⟨ transport-eq-fun (g ∘ f) id (pair= (loop , γ₀₁)) idp ⟩
    ! ap (g ∘ f) (pair= (loop , γ₀₁)) · idp · ap id (pair= (loop , γ₀₁))
      ==⟨ ap (λ r → ! (ap (g ∘ f) (pair= (loop , γ₀₁))) · idp · r) (ap-id (pair= (loop , γ₀₁))) ⟩
    ! ap (g ∘ f) (pair= (loop , γ₀₁)) · idp · (pair= (loop , γ₀₁))
      ==⟨ ap (λ r → r · pair= (loop , γ₀₁)) (! (·-runit (! ap (g ∘ f) (pair= (loop , γ₀₁))))) ⟩
    ! ap (g ∘ f) (pair= (loop , γ₀₁)) · (pair= (loop , γ₀₁))
      ==⟨ ap (λ r → ! r · pair= (loop , γ₀₁)) (! ap-comp f g (pair= (loop , γ₀₁))) ⟩
    ! ap g (ap f (pair= (loop , γ₀₁))) · (pair= (loop , γ₀₁))
      ==⟨ ap (λ r → ! ap g r · pair= (loop , γ₀₁)) lemma-ap-f-γ₀₁ ⟩
    ! ap g p₀₁ · (pair= (loop , γ₀₁))
      ==⟨ ap (λ r → ! r · pair= (loop , γ₀₁)) (pS-βrec₀₁ (Σ S¹ P) (base , false) (base , true) g-p₀₁ g-p₁₀) ⟩
    ! g-p₀₁ · (pair= (loop , γ₀₁))
      ==⟨ idp ⟩
    ! (pair= (loop , γ₀₁)) · (pair= (loop , γ₀₁))
      ==⟨ ·-linv (pair= (loop , γ₀₁)) ⟩
    idp
  ∎

-- {! ap-f-pair= {A = S¹}(P){Z = P base} ? loop true false γ₁₀  !}
\end{code}

### f ∘ g ∼ id

\begin{code}
-- Homotopy
f-g : f ∘ g ∼ id
f-g = pS-ind (λ ps → (f ∘ g) ps == id ps) q₀ q₁ dpath₁ dpath₂
  where

    q₀ : (f ∘ g) pS₀ == id pS₀
    q₀ = p₀₁ · p₁₀

    q₁ : (f ∘ g) pS₁ == id pS₁
    q₁ = p₁₀ · p₀₁

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
          ==⟨ ap (λ r → ! ap f r · q₀ · p₀₁)
                 (pS-βrec₀₁ ((Σ S¹ (λ b → P b))) (base , false) (base , true) g-p₀₁ g-p₁₀) ⟩
        ! ap f g-p₀₁ · q₀ · p₀₁
          ==⟨ ap (λ r → ! r · q₀ · p₀₁) lemma-ap-f-γ₀₁ ⟩
        ! p₀₁  · q₀ · p₀₁
          ==⟨⟩
        ! p₀₁  · (p₀₁ · p₁₀) · p₀₁
          ==⟨ ! (·-assoc (! p₀₁) p₀₁ p₁₀) |in-ctx (_· p₀₁) ⟩
        (! p₀₁  · p₀₁) · p₁₀ · p₀₁
          ==⟨ ·-linv p₀₁ |in-ctx (λ r → r · p₁₀ · p₀₁) ⟩
        idp · p₁₀ · p₀₁
          ==⟨⟩
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
          ==⟨ ap (λ r → ! ap f r · q₁ · p₁₀)
                 (pS-βrec₁₀ ((Σ S¹ (λ b → P b))) (base , false) (base , true) g-p₀₁ g-p₁₀) ⟩
        ! ap f g-p₁₀ · q₁ · p₁₀
          ==⟨ ap (λ r → ! r · q₁ · p₁₀) lemma-ap-f-γ₁₀ ⟩
        ! p₁₀ · q₁ · p₁₀
          ==⟨⟩
        ! p₁₀ · (p₁₀ · p₀₁) · p₁₀
          ==⟨ ! (·-assoc (! p₁₀) p₁₀ p₀₁) |in-ctx (_· p₁₀) ⟩
        (! p₁₀ · p₁₀) · p₀₁ · p₁₀
          ==⟨ ·-linv p₁₀ |in-ctx (λ r → r · p₀₁ · p₁₀) ⟩
        idp ·  p₀₁ · p₁₀
          ==⟨⟩
        q₀
      ∎
\end{code}

### g ∘ f ∼ id

Taking inspiration from Flattening lemma's proof in Section 6
in {% cite hottbook %}, we got the following proof.

\begin{code}
g-f : g ∘ f ∼ id
g-f (s , b) = g-f' s b
  where
    g-f' : (s : S¹) → (b : P s) → (g ∘ f) (s , b) == id (s , b)
    g-f' = S¹-ind (λ s → (b : P s) → (g ∘ f) (s , b) == id (s , b)) c cpath
      where

      cpath : transport Q loop c == c
      cpath = funext-transport-dfun-r loop c c helper

        where
          auxAP : ∀ {x y : P base}{p : base == base}
              → (q : tr (λ x → P x) p x == y)
              →  ap (λ w → ctp w ) q ==  pair= (refl base , q)
          auxAP idp = idp

          auxCfalse1 : ∀ {x y : P base}
              → (q : tr (λ x → P x) loop x == y)
              → pair= (loop , refl (tr (λ z → P z) loop x)) · pair= (refl base , q) == pair= (loop , q)

          auxCfalse1 {x = x} idp =
            begin
                pair= (loop , refl (tr (λ z → P z) loop x)) · pair= (refl base , idp)
            ==⟨ idp ⟩
                pair= (loop , refl (tr (λ z → P z) loop x)) · idp
            ==⟨ ! ·-runit (pair= (loop , refl (tr P loop x))) ⟩
                pair= (loop , refl (tr (λ z → P z) loop x))
            ==⟨ idp ⟩
                pair= (loop , idp)
            ∎

          auxCfalse2 :
               c (tr (λ x → P x) loop false)
            == tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₀₁)) (c (neg false))

          auxCfalse2 = begin
            c (tr (λ x → P x) loop false)
              ==⟨ ! (apd (λ x → c x) (! γ₀₁)) ⟩
            tr (λ b → (g ∘ f) (base , b) == id (base , b)) (! γ₀₁) (c (neg false))
              ==⟨ transport-family (! γ₀₁) (c (neg false)) ⟩
            tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₀₁)) (c (neg false))
            ∎

          auxCfalse3 : tr (λ w → (g ∘ f) w == id w)
                    ( (pair= (loop , refl (tr (λ z → P z) loop false)))
                    · ap  (λ x → ctp x) γ₀₁
                    )
                    (c false) == c (neg false)
          auxCfalse3  =
            begin
                tr (λ w → (g ∘ f) w == id w)
                          ( (pair= (loop , refl (tr (λ z → P z) loop false)))
                          · ap (λ x → ctp x) γ₀₁
                          )
                          (c false)
            ==⟨ ap (λ r → tr (λ w → (g ∘ f) w == id w) ((pair= (loop , refl (tr (λ z → P z) loop false))) · r ) (c false)) (auxAP {p = loop} γ₀₁) ⟩
             tr (λ w → (g ∘ f) w == id w)
                          ((pair= (loop , refl (tr (λ z → P z) loop false)))
                          ·  pair= (refl base , γ₀₁))
                          (c false)
            ==⟨ ap (λ r → tr (λ w → (g ∘ f) w == id w) r (c false)) (auxCfalse1 γ₀₁) ⟩
                tr (λ w → (g ∘ f) w == id w)
                          (pair= (loop , γ₀₁))
                          (c false)
            ==⟨ p false ⟩
              c (neg false)
            ∎

          auxCfalse4 :
            tr (λ w → (g ∘ f) w == id w)
              (pair= (loop , refl (tr (λ z → P z) loop false)) · (ap (λ x → ctp x) (γ₀₁)) ) (c false)
              ==  c (neg false)
            →
            tr (λ w → (g ∘ f) w == id w)
              (pair= (loop , refl (tr (λ z → P z) loop false))) (c false)
            == tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₀₁)) (c (neg false))
          auxCfalse4 p =
            begin
              tr (λ w → (g ∘ f) w == id w) (pair= (loop , refl (tr (λ z → P z) loop false))) (c false)
                ==⟨ ap (λ r → tr (λ w → (g ∘ f) w == id w) r (c false)) (·-runit (pair= (loop , refl (tr (λ z → P z) loop false)))) ⟩
              tr (λ w → (g ∘ f) w == id w) (pair= (loop , refl (tr (λ z → P z) loop false)) · idp) (c false)
                ==⟨ ap (λ r → tr (λ w → (g ∘ f) w == id w) (pair= (loop , refl (tr (λ z → P z) loop false)) · r) (c false)) (! (·-rinv (ap (λ x → ctp x) (γ₀₁)))) ⟩
              tr (λ w → (g ∘ f) w == id w) (pair= (loop , refl (tr (λ z → P z) loop false)) · ((ap (λ x → ctp x) (γ₀₁)) · ! (ap (λ x → ctp x) (γ₀₁)))) (c false)
                ==⟨ ap (λ r → tr (λ w → (g ∘ f) w == id w) r (c false)) (! ·-assoc (pair= (loop , refl (tr (λ z → P z) loop false))) ((ap (λ x → ctp x) (γ₀₁))) (! (ap (λ x → ctp x) (γ₀₁)))) ⟩
              tr (λ w → (g ∘ f) w == id w) ( (pair= (loop , refl (tr (λ z → P z) loop false)) · ((ap (λ x → ctp x) (γ₀₁))) · ! (ap (λ x → ctp x) (γ₀₁)))) (c false)
                ==⟨ ! (transport-comp-h (pair= (loop , refl (tr (λ z → P z) loop false)) · ap (λ x → ctp x) γ₀₁) (! (ap (λ x → ctp x) (γ₀₁))) (c false)) ⟩
              tr (λ w → (g ∘ f) w == id w) (! (ap (λ x → ctp x) (γ₀₁))) (tr (λ w → (g ∘ f) w == id w) (pair= (loop , refl (tr (λ z → P z) loop false)) · ((ap (λ x → ctp x) (γ₀₁)))) (c false))
                ==⟨ ap (λ r → tr (λ w → (g ∘ f) w == id w) (! (ap (λ x → ctp x) (γ₀₁))) r) p ⟩
              tr (λ w → (g ∘ f) w == id w) (! (ap (λ x → ctp x) (γ₀₁))) (c (neg false))
                ==⟨ ap (λ r → tr (λ w → (g ∘ f) w == id w) r (c (neg false))) (! ap-inv (λ x → ctp x) γ₀₁) ⟩
              tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₀₁)) (c (neg false))
            ∎

          auxCfalse5 :
            tr (λ w → (g ∘ f) w == id w) (pair= (loop , refl (tr (λ z → P z) loop false))) (c false)
            == tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₀₁)) (c (neg false))
          auxCfalse5 =
            auxCfalse4 auxCfalse3

    -------

          auxCtrue1 : ∀ {x y : P base}
              → (q : tr P loop x == y)
              → pair= (loop , refl (tr P loop x)) · pair= (refl base , q) == pair= (loop , q)

          auxCtrue1 {x = x} idp =
            begin
                pair= (loop , refl (tr P loop x)) · pair= (refl base , idp)
            ==⟨ idp ⟩
                pair= (loop , refl (tr P loop x)) · idp
            ==⟨ ! ·-runit (pair= (loop , refl (tr P loop x))) ⟩
                pair= (loop , refl (tr P loop x))
            ==⟨ idp ⟩
                pair= (loop , idp)
            ∎

          auxCtrue2 :
               c (tr (λ x → P x) loop true)
            == tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₁₀)) (c (neg true))

          auxCtrue2 = begin
            c (tr (λ x → P x) loop true)
              ==⟨ ! (apd (λ x → c x) (! γ₁₀)) ⟩
            tr (λ b → (g ∘ f) (base , b) == id (base , b)) (! γ₁₀) (c (neg true))
              ==⟨ transport-family (! γ₁₀) (c (neg true)) ⟩
            tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₁₀)) (c (neg true))
            ∎

          auxCtrue3 : tr (λ w → (g ∘ f) w == id w)
                    ( (pair= (loop , refl (tr (λ z → P z) loop true)))
                    · ap  (λ x → ctp x) γ₁₀
                    )
                    (c true) == c (neg true)
          auxCtrue3  =
            begin
                tr (λ w → (g ∘ f) w == id w)
                          ( (pair= (loop , refl (tr (λ z → P z) loop true)))
                          · ap (λ x → ctp x) γ₁₀
                          )
                          (c true)
            ==⟨ ap (λ r → tr (λ w → (g ∘ f) w == id w) ( (pair= (loop , refl (tr (λ z → P z) loop true))) · r ) (c true)) (auxAP {p = loop}  γ₁₀) ⟩
             tr (λ w → (g ∘ f) w == id w)
                          ((pair= (loop , refl (tr (λ z → P z) loop true)))
                          ·  pair= (refl base , γ₁₀))
                          (c true)
            ==⟨ ap (λ r → tr (λ w → (g ∘ f) w == id w) r (c true)) (auxCtrue1 γ₁₀) ⟩
                tr (λ w → (g ∘ f) w == id w)
                          (pair= (loop , γ₁₀))
                          (c true)
            ==⟨ p true ⟩
              c (neg true)
            ∎

          auxCtrue4 :
            tr (λ w → (g ∘ f) w == id w)
              (pair= (loop , refl (tr (λ z → P z) loop true)) · (ap (λ x → ctp x) (γ₁₀)) ) (c true)
              ==  c (neg true)
            →
            tr (λ w → (g ∘ f) w == id w)
              (pair= (loop , refl (tr (λ z → P z) loop true))) (c true)
            == tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₁₀)) (c (neg true))
          auxCtrue4 p =
            begin
              tr (λ w → (g ∘ f) w == id w) (pair= (loop , refl (tr (λ z → P z) loop true))) (c true)
                ==⟨ ap (λ r → tr (λ w → (g ∘ f) w == id w) r (c true)) (·-runit (pair= (loop , refl (tr (λ z → P z) loop true)))) ⟩
              tr (λ w → (g ∘ f) w == id w) (pair= (loop , refl (tr (λ z → P z) loop true)) · idp) (c true)
                ==⟨ ap (λ r → tr (λ w → (g ∘ f) w == id w) (pair= (loop , refl (tr (λ z → P z) loop true)) · r) (c true)) (! (·-rinv (ap (λ x → ctp x) (γ₁₀)))) ⟩
              tr (λ w → (g ∘ f) w == id w) (pair= (loop , refl (tr (λ z → P z) loop true)) · ((ap (λ x → ctp x) (γ₁₀)) · ! (ap (λ x → ctp x) (γ₁₀)))) (c true)
                ==⟨ ap (λ r → tr (λ w → (g ∘ f) w == id w) r (c true)) (! ·-assoc (pair= (loop , refl (tr (λ z → P z) loop true))) ((ap (λ x → ctp x) (γ₁₀))) (! (ap (λ x → ctp x) (γ₁₀)))) ⟩
              tr (λ w → (g ∘ f) w == id w) ( (pair= (loop , refl (tr (λ z → P z) loop true)) · ((ap (λ x → ctp x) (γ₁₀))) · ! (ap (λ x → ctp x) (γ₁₀)))) (c true)
                ==⟨ ! (transport-comp-h (pair= (loop , refl (tr (λ z → P z) loop true)) · ap (λ x → ctp x) γ₁₀) (! (ap (λ x → ctp x) (γ₁₀))) (c true)) ⟩
              tr (λ w → (g ∘ f) w == id w) (! (ap (λ x → ctp x) (γ₁₀))) (tr (λ w → (g ∘ f) w == id w) (pair= (loop , refl (tr (λ z → P z) loop true)) · ((ap (λ x → ctp x) (γ₁₀)))) (c true))
                ==⟨ ap (λ r → tr (λ w → (g ∘ f) w == id w) (! (ap (λ x → ctp x) (γ₁₀))) r) p ⟩
              tr (λ w → (g ∘ f) w == id w) (! (ap (λ x → ctp x) (γ₁₀))) (c (neg true))
                ==⟨ ap (λ r → tr (λ w → (g ∘ f) w == id w) r (c (neg true))) (! ap-inv (λ x → ctp x) γ₁₀) ⟩
              tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₁₀)) (c (neg true))
            ∎

          auxCtrue5 :
            tr (λ w → (g ∘ f) w == id w) (pair= (loop , refl (tr (λ z → P z) loop true))) (c true)
            == tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₁₀)) (c (neg true))
          auxCtrue5 =
            auxCtrue4 auxCtrue3

          helper : (b : P base)
                 → tr (λ w → (g ∘ f) w == id w) (pair= (loop , refl (tr (λ z → P z) loop b)))
                  (c b) == c (tr (λ x → P x) loop b)

          helper false =
              begin
                  tr (λ w → (g ∘ f) w == id w) (pair= (loop , refl (tr (λ z → P z) loop false))) (c false)
              ==⟨ auxCfalse5 ⟩
                  tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₀₁)) (c (neg false))
              ==⟨ ! auxCfalse2 ⟩
                 c (tr (λ x → P x) loop false)
              ∎

          helper true =
              begin
                  tr (λ w → (g ∘ f) w == id w) (pair= (loop , refl (tr (λ z → P z) loop true))) (c true)
              ==⟨ auxCtrue5 ⟩
                  tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₁₀)) (c (neg true))
              ==⟨ ! auxCtrue2 ⟩
                 c (tr (λ x → P x) loop true)
              ∎
\end{code}

Finally, the equivalence:

\begin{code}
ΣS¹P-≃-pS : Σ S¹ P ≃ pS
ΣS¹P-≃-pS = qinv-≃ f (g , f-g , g-f)
\end{code}
