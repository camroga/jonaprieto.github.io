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

For this equivalence, we need to find a proper candidate to correspond
with the `loop` path of `S¹`. Our propose is `p₀₀`, the path `p₀₁ · p₁₀`.
This choice makes sense because
`p₀₀` suggests a loop, closing the circuit with the arrows.

\begin{code}
p₀₀ : pS₀ == pS₀
p₀₀ = p₀₁ · p₁₀
\end{code}

#### Outgoing functions

We define the function `f` that goes from `S¹` to `pS` type.
Which it means we need to use the recursion principle of the circle.
We map `base` to `pS₀` and the action on `loop` to
`(tr (λ p → pS₀ == pS₀) loop p₀₀)`.

\begin{code}
module Lemma₁ where

  private
    f : S¹ → pS
    f = S¹-rec pS pS₀ (tr (λ p → pS₀ == pS₀) loop p₀₀)
\end{code}

For the inverse function of `f` we have `g` which goes from `pS` to `S¹`. `g` is
defined by the recursion principle of `pS` type. The correspondence in this case
maps all the points to `base` in S¹, and the arrows `p₀₁` and `p₁₀` to `loop ²`
and `loop ⁻¹` respectively. The reason for these last choices is because their
concatenation gives a `loop` which is exactly the correspondence that we want to
have. Another possible choices would be if we take instead `loop` and `refl
base` but that would give us a different proof and `p₀₀` could be something
else.

\begin{code}
  -- Inverse
    g : pS → S¹
    g = pS-rec S¹ base base (loop ²) (loop ⁻¹)
\end{code}

Now, let's prove the respective homotopies to show the equivalence.

####  `f ∘ g ~ id`

To prove the homotopy $$f ∘ g \sim \mathsf{id}$$, we also need recursion
principle of `pS` type as it follows.

- Case `pS₁`:

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

To prove the homotopy $$g ∘ f \sim \mathsf{id}$$, we proceed by induction on
the circle. For the `base` case, `refl base` works since `g (f base)` is
definitionally equal to `base`.


\begin{code}
  -- Def.
  H₂-base : g (f base) == base
  H₂-base = refl base
\end{code}

Action on `loop` case:

{: .foldable until="2" }
\begin{code}
  -- Def.
  H₂-loop : refl base == refl base [ (λ z → (g ∘ f) z == id z) ↓ loop ]
  H₂-loop =
    (begin
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
    ∎)
    where
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

\begin{code}
  -- Homotopy
  H₂ : g ∘ f ∼ id
  H₂ = S¹-ind _ H₂-base H₂-loop
\end{code}

Now, everything we needed to prove the equivalence is
and the equivalence is by quasiinverse equivalence.

\begin{code}
  -- Equivalence.
  S¹-≃-pS : S¹ ≃ pS
  S¹-≃-pS = qinv-≃ f (g , H₁ , H₂)
\end{code}

{% comment %}
## Action on paths of pairs

For the following equivalence, `Σ S¹ P ≃ pS`, we need first to
understand how is the action on paths of pairs, which appears as Lemma
6.12.7 in {% cite hottbook %}.

In context:

\begin{code}
module Lemma₂ {ℓ}
  {A : Type ℓ}
  (C : A → Type ℓ)
  {Z : Type ℓ}
  (d : (a : A) → C a → Z) where
\end{code}

The function `f` is curried version of the function `d`,
we made its definition private since it can interfere with other
definitions of the same symbol `f`.

\begin{code}
-- Def.
  private
    f : Σ A (λ a → C a) → Z
    f (a , b) = (d a) b
\end{code}

What we want to prove is that action on pairs is identified with a no trivial
composition as it follows. Once we do path induction on `α` we have `a₂ ≡ a₁`
and `α = idp`. We proceed doing path induction on the pathover `γ` which is now
a path in the same fiber `C c₁` transporting along the reflexivity path and
`c₁ = c₂`, `γ = idp`. All this gives us trivial paths in the composition.
Therefore, we inhabit the lemma with a proof of reflexivity.

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
          ==⟨ (! ·-rinv α)
            |in-ctx (λ k → tr (λ X → Z) α (d a₁ (tr C k c₁))) ⟩
        tr (λ X → Z) α (d a₁ (tr C (α · ! α) c₁))
          ==⟨ (! transport-comp-h α (! α) c₁)
          |in-ctx (λ k → tr (λ X → Z) α (d a₁ k))⟩
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
  L6-12-8 = ap-f-pair=

open Lemma₂
\end{code}

{% endcomment %}

## `Σ S¹ P ≃ pS`

**Lemma 3.** $$ \Sigma~S^{1}~P~\simeq~pS $$ where
$$P (\mathsf{base}) :≡ \mathsf{Bool}$$ and $$\mathsf{ap~P~loop~=~ua~(neg)}$$.

`P` is a type family defined by the recursion principle of the circle.
When it is the `base` case, `P base` is definitionally equal to the booleans `Bool`.
When `P` is acting on `loop`, a path of type `Bool == Bool` is given
by Univalence Axiom and the equivalence `neg`, the negation function for booleans.

![path](/assets/ipe-images/Bid.png){: width="%40" }
*Figure 3. `P` type family.*

Let's define this type family formally.

\begin{code}
module Lemma₃ where

  -- Def.
  neg : Bool → Bool
  neg true  = false
  neg false = true

  -- Equiv.
  neg-eq : Bool ≃ Bool
  neg-eq = qinv-≃ neg (neg , h , h)
    where
      h : neg ∘ neg ∼ id
      h true  = idp
      h false = idp
\end{code}

The type family `P : S¹ → Type₀`.

\begin{code}
  -- Def
  P : S¹ → Type₀
  P = S¹-rec Type₀ Bool (ua neg-eq)
\end{code}

As we saw in the Fig. 3, the paths `γ₀₁` and `γ₁₀` are defined as pathovers.

\begin{code}
  -- Defs.
  γ₀₁ : tr P loop false == true
  γ₀₁ = transport-ua P loop neg-eq (S¹-βrec Type₀ Bool (ua neg-eq)) false

  γ₁₀ : tr P loop true == false
  γ₁₀ = transport-ua P loop neg-eq (S¹-βrec Type₀ Bool (ua neg-eq)) true
\end{code}

**Proof.** We proceed as usual to show the equivalence.
We define the outgoing functions `f : Σ S¹ P → pS`, `g : pS → Σ S¹ P`
and the homotopies `f ∘ g ~ id` and `g ∘ f ∼ id`. Let's start defining
the function `f`.

### `f : Σ S¹ P → pS`

To define `f` we need to use the recursor principle of Sigma types which gives a
pair `(b , x)` in order to provide a definition for the uncurried version of
`f`, `f̰ : (b : S¹) → P b → pS`. Since `f̰` is a dependent function, we define
it using induction principle on the circle. In this case, we maps `base` to `ct`
and `p̰` as evidence of the pathover of `ct` and `ct` along the `loop` in the
family `(λ z → P z → pS)`.

\begin{code}
  -- Def.
  ct : P base → pS
  ct true  = pS₁
  ct false = pS₀
\end{code}

{: .foldable until="2" }
\begin{code}
  -- Def.
  p̰ : ct == ct [ (λ z → P z → pS) ↓ loop ]
  p̰ =
    (begin
      transport (λ z → P z → pS) loop ct
        ==⟨ transport-fun loop ct ⟩
      (λ (x : P base) → transport (λ z → pS) loop
                          (ct (transport (λ z → P z) (! loop) x)))
        ==⟨ funext (λ (pb : P base) → transport-const loop
                          (ct (transport (λ z → P z) (! loop) pb))) ⟩
      (λ (x : P base) → (ct (transport (λ z → P z) (! loop) x)))
        ==⟨ funext (λ (pb : P base) → ap ct (helper₁ pb)) ⟩
      (λ (x : P base) → ct (neg x) )
        ==⟨ funext helper₂ ⟩
      ct
     ∎)
     where
       helper₁ : (x : P base) → x == neg x [ P ↓ ! loop ]
       helper₁ x =
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

       helper₂ : (x : P base) → ct (neg x) == ct x
       helper₂ true  = p₀₁
       helper₂ false = p₁₀
\end{code}

\begin{code}
  -- Def.
  f̰ : (b : S¹) → P b → pS
  f̰ = S¹-ind (λ z → P z → pS) ct p̰
\end{code}

\begin{code}
  -- Def.
  f :  Σ S¹ P → pS
  f (b , x) = f̰ b x
\end{code}

### `g : pS → Σ S¹ P`

We define `g` as the inverse function of `f` by recursion on `pS` type. Since
`pS` and `Σ S¹ P` both have two points, two arrows and their graphs are actually
isomorphic, `g` entitled such a correspond as it is expected. `false` maps to
`(base , false)`, `true` maps to `(base, true)`. For the paths, the subindexes
will suggest the correspondence: `p₀₁` maps to `(base , false) == (base , true
)`, and `p₁₀` maps to `(base , true) == (base, false)`. For these last paths, we
use Theorem 2.9.7 in {% cite hottbook %} to get the respective dependent pair
equalities, this is by using the `pair=` function.

\begin{code}
-- Def.
  ctp : P base → Σ S¹ P
  ctp b = base , b

  ptp : (y : P base) → ctp y == ctp (neg y)
  ptp false = pair= (loop , γ₀₁)
  ptp true  = pair= (loop , γ₁₀)

  g : pS → Σ S¹ P
  g = pS-rec (Σ S¹ P)
            (ctp false)  -- false ↦ (base , false)
            (ctp true)   -- true ↦ (base , true)
            (ptp false)  -- p₀₁ ↦ (base , false) = (base , true)
            (ptp true)   -- p₁₀ ↦ (base , true ) = (base , false)
\end{code}


### `f ∘ g ∼ id`

To show that this homotopy holds, we proceed by induction principle of `pS`
type. This means we need to show the identity types `(f ∘ g) pS₀ == id pS₀` and
`(f ∘ g) pS₁ == id pS₁` are inhabited but also the pathovers along `p₀₁` and
`p₁₀` respectively. These are the terms `q₀`, `q₁`, `pover₁`, and `pover₂` in
the following. To define `pover₁` and `pover₂` we need the following lemmas
based on Lemma 6.12.8 in {% cite hott-book %}. We postulated for now, we are working
on the proof terms. Let's see.

\begin{code}
  -- Lemma 6.12.8
  postulate
    lemma-ap-f-γ₀₁ : ap f (ptp false) == p₀₁
    lemma-ap-f-γ₁₀ : ap f (ptp true)  == p₁₀
\end{code}

-------------------------------------------------------------------------------
*(Working in Progress to remove the above lemmas)*:

\begin{code}
  -- Def.
  G : (b : P base) → (tr P loop (neg b) == b)
  G true  = γ₀₁
  G false = γ₁₀

  H : (b : P base) → {!  !}
  H true  = ap (f̰ base) (G true)  · p₁₀
  H false = ap (f̰ base) (G false) · p₀₁

  H' : {!   !}
  H' = {!   !}

  O : apd f̰ loop == funext H'
  O = {!   !}

  module app = Lemma₂ {A = S¹} P {Z = pS} f̰
  t = app.L6-12-8 loop false true γ₀₁

\end{code}
-------------------------------------------------------------------------------
