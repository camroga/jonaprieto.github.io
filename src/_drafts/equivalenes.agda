<!-- <div class="proof" id="proof=3.1b"> -->
<!-- Proof 2.<br/> -->
<!-- Exhibit an equivalence. -->
<!-- </div> -->

% In Agda, we can define the predicate `isSet` as follows:

% \begin{code}
% module sets where
%
%   isSet : ∀ {i} (A : Set i) → Set _
%   isSet A = (x y : A) → (p : x ≡ y) → (q : x ≡ y) → p ≡ q
%   -- TODO
% \end{code}

In Agda.

\begin{code}
module 𝟘-Def where
  data 𝟘 : Set where

module 𝟘-Rec where
  open 𝟘-Def
  rec : {A : Set} → 𝟘 → A
  rec = λ ()
\end{code}

\begin{code}
module +-Def₂ where

  data _+_ : Set → Set → Set₁ where
    inl : ∀ {B : Set} → (A : Set) → A + B
    inr : ∀ {A : Set} → (B : Set) → A + B

module +-Fun₂ where

  open +-Def₂
  open 𝟘-Def
  open 𝟘-Rec

  code : {A B : Set}
       → A + B → Set _
  code {A}{B} (inl a) = a ≡ a
  code {A}{B} (inr b) = {! !}

module +-Rec₂ where
  open +-Def₂

  rec : {A B : Set}
      → (C : Set)
      → (A → C)
      → (B → C)
      → A + B → C
  rec C f g (inl A) = f {! a  !}
  rec C f g (inr B) = g {!   !}

module +-Ind₂ where
  open +-Def₂

  -- ind : {A B : Set}
  --     → (C : A + B → Set)
  --     → ((x : A) → C (inl x))
  --     → ((x : B) → C (inr x))
  --     → (x : A + B) → C x
  -- ind C f g c x = {!   !}

-- module +-Fun₂ where
\end{code}


\begin{code}
module ex3-2 where
  open +-Def₂
  open sets using (isSet)

  p : {A B : Set}
    → isSet A → isSet B → isSet (A + B)
  p {.A} {B} setA setB (inl A) (inl .A) refl refl = refl
  p {A} {.B} setA setB (inr B) (inr .B) refl refl = refl
  p {.A} {.B} setA setB (inl A) (inr B) p q = {!   !}
  p {.A} {.B} setA setB (inr B) (inl A) p q = {!   !}
\end{code}
