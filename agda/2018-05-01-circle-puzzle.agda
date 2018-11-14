{-# OPTIONS --without-K #-}
open import Agda.Primitive using ( Level ; lsuc; lzero; _⊔_ )

open import 2018-07-06-mini-hott
module _ where
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
  -- Def. loop^2
  _²
    : ∀ {ℓ} {A : Type ℓ} {a : A}
    → a == a
    --------
    → a == a

  p ² = p · p
  -- Def.
  S¹-rec
    : ∀ {ℓ}
    → (A : Type ℓ)
    → (a : A)
    → (p : a == a)
    --------------
    → (S¹ → A)

  S¹-rec A a p !base = a
  -- Postulate.
  postulate
    S¹-βrec
      : ∀ {ℓ}
      → (A : Type ℓ)
      → (a : A)
      → (p : a == a)
      -----------------------------
      → ap (S¹-rec A a p) loop == p
  -- Def.
  S¹-ind
    : ∀ {ℓ} (P : S¹ → Type ℓ)
    → (x : P base)
    → (x == x [ P ↓ loop ])
    ------------------------
    → ((t : S¹) → P t)

  S¹-ind P x p !base = x
  -- Postulate.
  postulate
    S¹-βind
      : ∀ {ℓ} (P : S¹ → Type ℓ)
      → (x : P base)
      → (p : x == x [ P ↓ loop ])
      -------------------------------
      → apd (S¹-ind P x p) loop == p
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
p₀₀ : pS₀ == pS₀
p₀₀ = p₀₁ · p₁₀
module Lemma₁ where

  private
    f : S¹ → pS
    f = S¹-rec pS pS₀ (tr (λ p → pS₀ == pS₀) loop p₀₀)
  -- Inverse
    g : pS → S¹
    g = pS-rec S¹ base base (loop ²) (loop ⁻¹)
  -- Def.
  q₁ : f (g pS₁) == pS₁
  q₁ = ! p₀₀ · ! p₀₀ · p₀₁
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
  -- Homotopy.
  H₁ : f ∘ g ∼ id
  H₁ = pS-ind _ (refl pS₀) q₁ dpath₀ dpath₁
  -- Def.
  H₂-base : g (f base) == base
  H₂-base = refl base
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
  -- Homotopy
  H₂ : g ∘ f ∼ id
  H₂ = S¹-ind _ H₂-base H₂-loop
  -- Equivalence.
  S¹-≃-pS : S¹ ≃ pS
  S¹-≃-pS = qinv-≃ f (g , H₁ , H₂)
-- module Lemma₂ {ℓ}
--   {A : Type ℓ}
--   (C : A → Type ℓ)
--   {Z : Type ℓ}
--   (d : (a : A) → C a → Z) where
-- -- Def.
--   private
--     f : Σ A (λ a → C a) → Z
--     f (a , b) = (d a) b
--   -- Lemma.
--   ap-f-pair=
--     : {a₁ a₂ : A}
--     → (α : a₁ == a₂)
--     → (c₁ : C a₁) (c₂ : C a₂)
--     → (γ : c₁ == c₂ [ C ↓ α ])
--     ---------------------------
--     → ap f (pair= (α , γ))
--         ==
--      (begin
--         f (a₁ , c₁)
--           ==⟨⟩
--         d a₁ c₁
--           ==⟨ ! (transport-const  α (d a₁ c₁)) ⟩
--         tr (λ X → Z) α (d a₁ c₁)
--           ==⟨ ap (λ k → tr (λ X → Z) α (d a₁ k)) idp ⟩
--         tr (λ X → Z) α (d a₁ (tr C (refl a₁) c₁))
--           ==⟨ (! ·-rinv α)
--             |in-ctx (λ k → tr (λ X → Z) α (d a₁ (tr C k c₁))) ⟩
--         tr (λ X → Z) α (d a₁ (tr C (α · ! α) c₁))
--           ==⟨ (! transport-comp-h α (! α) c₁)
--           |in-ctx (λ k → tr (λ X → Z) α (d a₁ k))⟩
--         tr (λ X → Z) α (d a₁ (tr C (! α) (tr C α c₁)))
--           ==⟨ ! (transport-fun-h α (d a₁) (tr C α c₁)) ⟩
--         (tr (λ x → (C x → Z)) α (d a₁)) (tr C α c₁)
--           ==⟨ happly (apd d α) (tr C α c₁) ⟩
--         d a₂ (tr C α c₁)
--           ==⟨ ap (d a₂) γ ⟩
--         d a₂ c₂
--           ==⟨⟩
--         f (a₂ , c₂)
--       ∎)
--
--   ap-f-pair= idp c₁ .c₁ idp = idp
--
-- open Lemma₂
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
  -- Def
  P : S¹ → Type₀
  P = S¹-rec Type₀ Bool (ua neg-eq)
  -- Defs.
  γ₀₁ : tr P loop false == true
  γ₀₁ = transport-ua P loop neg-eq (S¹-βrec Type₀ Bool (ua neg-eq)) false

  γ₁₀ : tr P loop true == false
  γ₁₀ = transport-ua P loop neg-eq (S¹-βrec Type₀ Bool (ua neg-eq)) true
  -- Def.
  ct : P base → pS
  ct true  = pS₁
  ct false = pS₀
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
  -- Def.
  f̰ : (b : S¹) → P b → pS
  f̰ = S¹-ind (λ z → P z → pS) ct p̰
  -- Def.
  f :  Σ S¹ P → pS
  f (b , x) = f̰ b x
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
  -- Lemma 6.12.8
  postulate
    lemma-ap-f-γ₀₁ : ap f (ptp false) == p₀₁
    lemma-ap-f-γ₁₀ : ap f (ptp true) == p₁₀
  -- Def.
  q₀ : (f ∘ g) pS₀ == id pS₀
  q₀ = p₀₁ · p₁₀
  -- Def.
  q₁ : (f ∘ g) pS₁ == id pS₁
  q₁ = p₁₀ · p₀₁
  -- Def.
  pover₁ : q₀ == q₁ [ (λ z → (f ∘ g) z == id z) ↓ p₀₁ ]
  pover₁ =
    (begin
      transport (λ z → (f ∘ g) z == id z) p₀₁ q₀
        ==⟨ transport-eq-fun (f ∘ g) id p₀₁ q₀ ⟩
      ! ap (f ∘ g) p₀₁ · q₀ · ap id p₀₁
        ==⟨ ap (! ap (f ∘ g) p₀₁ · q₀ ·_) (ap-id p₀₁) ⟩
      ! ap (f ∘ g) p₀₁ · q₀ · p₀₁
        ==⟨ ap (λ r → ! r · q₀ · p₀₁) (! ap-comp g f p₀₁) ⟩
      ! ap f (ap g p₀₁) · q₀ · p₀₁
        ==⟨ ap (λ r → ! ap f r · q₀ · p₀₁) (pS-βrec₀₁ (Σ S¹ (λ b → P b)) (ctp false) (ctp true) (ptp false) (ptp true)) ⟩
      ! ap f (ptp false) · q₀ · p₀₁
        ==⟨ ap (λ r → ! r · q₀ · p₀₁) lemma-ap-f-γ₀₁ ⟩
      ! p₀₁ · q₀ · p₀₁
        ==⟨ idp ⟩
      ! p₀₁ · (p₀₁ · p₁₀) · p₀₁
        ==⟨ ! (·-assoc (! p₀₁) p₀₁ p₁₀) |in-ctx (_· p₀₁) ⟩
      (! p₀₁ · p₀₁) · p₁₀ · p₀₁
        ==⟨ ·-linv p₀₁ |in-ctx (λ r → r · p₁₀ · p₀₁) ⟩
      idp · p₁₀ · p₀₁
        ==⟨⟩
      q₁
    ∎)
  -- Def.
  pover₂ : q₁ == q₀ [ (λ z → (f ∘ g) z == id z) ↓ p₁₀ ]

  pover₂ =
    (begin
      transport (λ z → (f ∘ g) z == id z) p₁₀ q₁
        ==⟨ transport-eq-fun (f ∘ g) id p₁₀ q₁ ⟩
      ! ap (f ∘ g) p₁₀ · q₁ · ap id p₁₀
        ==⟨ ap (! ap (f ∘ g) p₁₀ · q₁ ·_) (ap-id p₁₀) ⟩
      ! ap (f ∘ g) p₁₀ · q₁ · p₁₀
        ==⟨ ap (λ r → ! r · q₁ · p₁₀) (! ap-comp g f p₁₀) ⟩
      ! ap f (ap g p₁₀) · q₁ · p₁₀
        ==⟨ ap (λ r → ! ap f r · q₁ · p₁₀)
               (pS-βrec₁₀ (Σ S¹ (λ b → P b)) (ctp false) (ctp true) (ptp false) (ptp true)) ⟩
      ! ap f (ptp true) · q₁ · p₁₀
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
    ∎)
  -- Homotopy
  f-g : f ∘ g ∼ id
  f-g = pS-ind (λ ps → (f ∘ g) ps == id ps) q₀ q₁ pover₁ pover₂
  -- Def.
  c : (b : P base) → (g ∘ f) (base , b) == id (base , b)
  c true  = refl (base , true)
  c false = refl (base , false)
  -- Def.
  Q : (s : S¹) → Type lzero
  Q = λ z → (b : P z) → (g ∘ f) (z , b) == id (z , b)
  -- Helpers and auxiliar lemmas

  -- Def.
  auxAP : ∀ {x y : P base}{p : base == base}
      → (q : tr (λ x → P x) p x == y)
      →  ap (λ w → ctp w ) q == pair= (refl base , q)

  auxAP idp = idp

  stepFalse1
    : ∀ {x y : P base}
    → (q : tr (λ x → P x) loop x == y)
    → pair= (loop , refl (tr (λ z → P z) loop x)) · pair= (refl base , q) == pair= (loop , q)

  stepFalse1 {x = x} idp =
    begin
        pair= (loop , refl (tr (λ z → P z) loop x)) · pair= (refl base , idp)
    ==⟨ idp ⟩
        pair= (loop , refl (tr (λ z → P z) loop x)) · idp
    ==⟨ ! ·-runit (pair= (loop , refl (tr P loop x))) ⟩
        pair= (loop , refl (tr (λ z → P z) loop x))
    ==⟨ idp ⟩
        pair= (loop , idp)
    ∎

  stepFalse2
    : c (tr (λ x → P x) loop false)
      == tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₀₁)) (c (neg false))

  stepFalse2 = begin
    c (tr (λ x → P x) loop false)
      ==⟨ ! (apd (λ x → c x) (! γ₀₁)) ⟩
    tr (λ b → (g ∘ f) (base , b) == id (base , b)) (! γ₀₁) (c (neg false))
      ==⟨ transport-family (! γ₀₁) (c (neg false)) ⟩
    tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₀₁)) (c (neg false))
    ∎


  -- Def.
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
        ==⟨ ap (λ r → ! r · pair= (loop , γ₁₀)) (pS-βrec₁₀ (Σ S¹ P) (base , false) (base , true) (ptp false) (ptp true)) ⟩
      ! (ptp true) · (pair= (loop , γ₁₀))
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
        ==⟨ ap (λ r → ! r · pair= (loop , γ₀₁)) (pS-βrec₀₁ (Σ S¹ P) (base , false) (base , true) (ptp false) (ptp true)) ⟩
      ! (ptp false) · (pair= (loop , γ₀₁))
        ==⟨ idp ⟩
      ! (pair= (loop , γ₀₁)) · (pair= (loop , γ₀₁))
        ==⟨ ·-linv (pair= (loop , γ₀₁)) ⟩
      idp
    ∎
  ------------------------------------------------------------------------------

  -- Def.
  stepFalse3 :
    tr (λ w → (g ∘ f) w == id w)
       ((pair= (loop , refl (tr (λ z → P z) loop false))) · ap  (λ x → ctp x) γ₀₁ )
       (c false) == c (neg false)

  stepFalse3  =
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
    ==⟨ ap (λ r → tr (λ w → (g ∘ f) w == id w) r (c false)) (stepFalse1 γ₀₁) ⟩
        tr (λ w → (g ∘ f) w == id w)
                  (pair= (loop , γ₀₁))
                  (c false)
    ==⟨ p false ⟩
      c (neg false)
    ∎

  -- Def.
  stepFalse4 :
    tr (λ w → (g ∘ f) w == id w)
      (pair= (loop , refl (tr (λ z → P z) loop false)) · (ap (λ x → ctp x) (γ₀₁)) ) (c false)
      ==  c (neg false)
    →
    tr (λ w → (g ∘ f) w == id w)
      (pair= (loop , refl (tr (λ z → P z) loop false))) (c false)
    == tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₀₁)) (c (neg false))

  stepFalse4 p =
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

  -- Def.
  stepFalse5 :
    tr (λ w → (g ∘ f) w == id w) (pair= (loop , refl (tr (λ z → P z) loop false))) (c false)
    == tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₀₁)) (c (neg false))

  stepFalse5 = stepFalse4 stepFalse3

  -- Def.
  stepTrue1
    : ∀ {x y : P base}
    → (q : tr P loop x == y)
    → pair= (loop , refl (tr P loop x)) · pair= (refl base , q) == pair= (loop , q)

  stepTrue1 {x = x} idp =
    begin
        pair= (loop , refl (tr P loop x)) · pair= (refl base , idp)
    ==⟨ idp ⟩
        pair= (loop , refl (tr P loop x)) · idp
    ==⟨ ! ·-runit (pair= (loop , refl (tr P loop x))) ⟩
        pair= (loop , refl (tr P loop x))
    ==⟨ idp ⟩
        pair= (loop , idp)
    ∎

  -- Def.
  stepTrue2
    : c (tr (λ x → P x) loop true)
      == tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₁₀)) (c (neg true))

  stepTrue2 = begin
    c (tr (λ x → P x) loop true)
      ==⟨ ! (apd (λ x → c x) (! γ₁₀)) ⟩
    tr (λ b → (g ∘ f) (base , b) == id (base , b)) (! γ₁₀) (c (neg true))
      ==⟨ transport-family (! γ₁₀) (c (neg true)) ⟩
    tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₁₀)) (c (neg true))
    ∎

  -- Def.
  stepTrue3
    : tr (λ w → (g ∘ f) w == id w)
         ((pair= (loop , refl (tr (λ z → P z) loop true))) · ap  (λ x → ctp x) γ₁₀ )
         (c true) == c (neg true)

  stepTrue3  =
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
    ==⟨ ap (λ r → tr (λ w → (g ∘ f) w == id w) r (c true)) (stepTrue1 γ₁₀) ⟩
        tr (λ w → (g ∘ f) w == id w)
                  (pair= (loop , γ₁₀))
                  (c true)
    ==⟨ p true ⟩
      c (neg true)
    ∎

  -- Def.
  stepTrue4 :
    tr (λ w → (g ∘ f) w == id w)
      (pair= (loop , refl (tr (λ z → P z) loop true)) · (ap (λ x → ctp x) (γ₁₀)) ) (c true)
      ==  c (neg true)
    →
    tr (λ w → (g ∘ f) w == id w)
      (pair= (loop , refl (tr (λ z → P z) loop true))) (c true)
    == tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₁₀)) (c (neg true))

  stepTrue4 p =
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

  -- Def.
  stepTrue5
    : tr (λ w → (g ∘ f) w == id w) (pair= (loop , refl (tr (λ z → P z) loop true))) (c true)
      == tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₁₀)) (c (neg true))

  stepTrue5 = stepTrue4 stepTrue3

  -- Def.
  helper
    : (b : P base)
    → tr (λ w → (g ∘ f) w == id w) (pair= (loop , refl (tr (λ z → P z) loop b)))
      (c b) == c (tr (λ x → P x) loop b)

  helper false =
      begin
        tr (λ w → (g ∘ f) w == id w) (pair= (loop , refl (tr (λ z → P z) loop false))) (c false)
          ==⟨ stepFalse5 ⟩
        tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₀₁)) (c (neg false))
          ==⟨ ! stepFalse2 ⟩
        c (tr (λ x → P x) loop false)
      ∎

  helper true =
      begin
          tr (λ w → (g ∘ f) w == id w) (pair= (loop , refl (tr (λ z → P z) loop true))) (c true)
      ==⟨ stepTrue5 ⟩
          tr (λ w → (g ∘ f) w == id w) (ap (λ x → ctp x) (! γ₁₀)) (c (neg true))
      ==⟨ ! stepTrue2 ⟩
         c (tr (λ x → P x) loop true)
      ∎
  -- Def.
  cpath : PathOver (λ s → (b : P s) → g (f (s , b)) == s , b) loop c c
  cpath = funext-transport-dfun-r loop c c helper
-- Homotopy
  -- Def. by Sigma induction. Step 1.
  g-f : g ∘ f ∼ id
  g-f (s , b) = g-f' s b
    where
      -- Def. by S¹ induction. Step 2.
      g-f' : (s : S¹) → (b : P s) → (g ∘ f) (s , b) == id (s , b)
      g-f' = S¹-ind (λ s → (b : P s) → (g ∘ f) (s , b) == id (s , b)) c cpath
  -- Equiv.
  ΣS¹P-≃-pS : Σ S¹ P ≃ pS
  ΣS¹P-≃-pS = qinv-≃ f (g , f-g , g-f)
