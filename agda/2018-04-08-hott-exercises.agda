{-# OPTIONS --without-K #-}
infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
sym : ∀ {i} {A : Set i} {x y : A}
    → x ≡ y → y ≡ x
sym refl = refl

_·_ : ∀ {i}{X : Set i}{x y z : X}
    → x ≡ y → y ≡ z → x ≡ z
refl · p = p
trans = _·_

infixl 9 _·_

ap : ∀ {i j}{A : Set i}{B : Set j}{x y : A}
   → (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

ap₂ : ∀ {i j} {A B : Set i}{C : Set j}
      {x₀ x₁ : A}{y₀ y₁ : B}
    → (f : A → B → C) → (x₀ ≡ x₁) → (y₀ ≡ y₁)
    → f x₀ y₀ ≡ f x₁ y₁
ap₂ f refl refl = refl

subst : ∀ {i j} {A : Set i}{x y : A}
      → (B : A → Set j) → x ≡ y
      → B x → B y
subst B refl = (λ z → z)

J' : ∀ {i j}{X : Set i}{x : X}
   → (P : (y : X) → x ≡ y → Set j)
   → P x refl
   → (y : X)
   → (p : x ≡ y)
   → P y p
J' P u y refl = u

J : ∀ {i j}{X : Set i}
  → (P : (x y : X) → x ≡ y → Set j)
  → ((x : X) → P x x refl)
  → (x y : X)
  → (p : x ≡ y)
  → P x y p
J P u x y p = J' (P x) (u x) y p
_∘_ : ∀ {i j k} {A : Set i}{B : Set j}{C : Set k}
    → (B → C)
    → (A → B)
    → A → C
g ∘ f = λ x → g (f x)
∘-assoc : ∀ {i j k l} {A : Set i}{B : Set j}{C : Set k}{D : Set l}
        → (h : C → D)(g : B → C)(f : A → B)
        → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
∘-assoc f g h = refl
\begin{align*}
&\rec_1 : \prod\limits_{C : \U} (A \to B \to C) \to A \times B \to C\\
&\rec_1~C~g~c~:\equiv~g~(\proj_1 c,~\proj_2 c).
\end{align*}
\begin{align*}
&\rec_2 : \prod\limits_{C : \U}  (\prod_{x : A} Bx \to C) \to \sum\limits_{x : A} B x \to C\\
&\rec_2~C~g~c~=~g~(\proj_1 c)~(\proj_2 c)
\end{align*}
open import Agda.Primitive
  using (Level; _⊔_; lzero; lsuc)
module Σ-Def₁ where

  record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B proj₁

  open Σ public
-- _,_ : (proj₁ : A) → B proj₁ → Σ A B.
module Σ-Rec₁ {i j k}{A : Set i}{B : A → Set j}{C : Set k}
             (g : (x : A) → B x → C) where

  open Σ-Def₁ using (Σ ; proj₁; proj₂; _,_ )

  rec : Σ A B → C
  rec p = g (proj₁ p) (proj₂ p)

  rec-β : (x : A)(y : B x) → rec (x , y) ≡ g x y
  rec-β x y = refl
module ×-Def₁ where
  open Σ-Def₁ public

  _×_ : {l k : Level} (A : Set l) (B : Set k) → Set (l ⊔ k)
  A × B = Σ A (λ _ → B)
module ×-Rec₁ {i j k}{A : Set i}{B : Set j}{C : Set k} (g : A → B → C) where

  open ×-Def₁ using (_×_; proj₁; proj₂; _,_)

  rec : A × B → C
  rec p = g (proj₁ p) (proj₂ p)

  rec-β : (x : A)(y : B) → rec (x , y) ≡ g x y
  rec-β x y = refl
-- this would be trivial in agda due to definitional η for records
-- so Capriotti defined a product type without η:
module ×-Def₂ where

  data _×_ {i j}(A : Set i)(B : Set j) : Set (i ⊔ j) where
    _,_ : A → B → A × B

  proj₁ : ∀ {i j}{A : Set i}{B : Set j}
        → A × B → A
  proj₁ (a , b) = a

  proj₂ : ∀ {i j}{A : Set i}{B : Set j}
        → A × B → B
  proj₂ (a , b) = b
module ×-Fun₂ {i j}{A : Set i}{B : Set j} where
  open ×-Def₂ using ( _×_;_,_; proj₁; proj₂)

  -- propositional uniqueness principle:
  uppt : (x : A × B) → (proj₁ x , proj₂ x) ≡ x
  uppt (a , b) = refl

  -- (ap functions): (a)ction over a (p)ath
  ap-proj₁ : {A B : Set}{x y : A × B}
           → (x ≡ y) → proj₁ x ≡ proj₁ y
  ap-proj₁ refl = refl

  ap-proj₂ : {A B : Set}{x y : A × B}
           → (x ≡ y) → proj₂ x ≡ proj₂ y
  ap-proj₂ refl = refl

  pair= : ∀ {A B : Set} {x w : A} {y z : B}
        → x ≡ w → y ≡ z → (x , y) ≡ (w , z)
  pair= refl refl = refl
module ×-Ind₂ {i j}{A : Set i}{B : Set j} where
  open ×-Def₂ using (_×_; _,_;proj₁;proj₂)
  open ×-Fun₂ using (uppt)

  ind : ∀ {k}(C : A × B → Set k)
        → ((x : A)(y : B) → C (x , y))
        → (x : A × B) → C x
  ind C g x = subst C (uppt x) (g (proj₁ x) (proj₂ x))

  ind-β : ∀ {k} (C : A × B → Set k)
          → (g : (x : A)(y : B) → C (x , y))
          → (x : A)(y : B)
          → ind C g (x , y) ≡ g x y
  ind-β C g x y = refl
module Σ-Def₂ where

  data Σ {i j}(A : Set i)(B : A → Set j) : Set (i ⊔ j) where
    _,_ : (x : A) → B x → Σ A B
module Σ-Fun₂ {i j } {A : Set i}{B : A → Set j} where
  open Σ-Def₂ using (Σ; _,_ )

  proj₁ : Σ A B → A
  proj₁ (a , b) = a

  proj₂ : (x : Σ A B) → B (proj₁ x)
  proj₂ (a , b) = b

  uppt : (x : Σ A B) → (proj₁ x , proj₂ x) ≡ x
  uppt (a , b) = refl
module Σ-Ind₂ {i j}{A : Set i}{B : A → Set j} where
  open Σ-Def₂ public
  open Σ-Fun₂ public

  ind : (C : Σ A B → Set (i ⊔ j))
        → ((x : A)(y : B x) → C (x , y))
        → (x : Σ A B) → C x
  ind C g (a , b) = g a b

  ind-β : (C : Σ A B → Set (i ⊔ j))
          → (g : (x : A)(y : B x) → C (x , y))
          → (x : A) (y : B x)
          → (ind C g (x , y)) ≡ g x y
  ind-β C g x y = refl
\begin{align*}
\mathsf{ite}(C,c_0,c_s,0)               &\equiv c_0, \\
\mathsf{ite}(C,c_0,c_s,\mathsf{suc}(n)) &\equiv c_s(\mathsf{ite}(C,c_0,c_s,n)),
\end{align*}
module ℕ-Def where

  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

module ℕ-Rec where
  open ℕ-Def
  rec : ∀ (C : Set) → C → (ℕ → C → C) → ℕ → C
  rec C c₀ cₛ zero    = c₀
  rec C c₀ cₛ (suc n) = cₛ n (rec C c₀ cₛ n)

module ℕ-Ind where
  open ℕ-Def
  ind : ∀ (C : ℕ → Set)
       → (C zero)
       → (∀ (n : ℕ) → C n → C (suc n))
       → (∀ (n : ℕ) → C n)
  ind C c₀ cₛ zero    = c₀
  ind C c₀ cₛ (suc n) = cₛ n (ind C c₀ cₛ n)
module ℕ-Fun where
  open ℕ-Def using (ℕ; zero; suc)
  open ℕ-Rec using (rec)

  ite : ∀ (C : Set) → C → (C → C) → ℕ → C
  ite C c₀ cₛ zero    = c₀
  ite C c₀ cₛ (suc n) = cₛ (ite C c₀ cₛ n)
-- recursor
  open ×-Def₂ using (_×_; proj₁; proj₂; _,_)

  rec₂ : ∀ (C : Set) → C → (ℕ → C → C) → ℕ → (ℕ × C)
  rec₂ C c₀ cₛ n =
      (ite (ℕ × C)
           (zero , c₀)
           (λ (p : ℕ × C) → (suc (proj₁ p) , cₛ (proj₁ p) (proj₂ p)))
           n)
module ex1-4 where

  open ℕ-Def using (ℕ; zero; suc)
  open ℕ-Rec using (rec)
  open ℕ-Ind using (ind)
  open ℕ-Fun using (ite; rec₂)

  open ×-Def₂ using (_×_; proj₁; proj₂; _,_)
  open ×-Fun₂

  proof : (C : Set)(c₀ : C)(cₛ : ℕ → C → C)
        → ∀ (n : ℕ) → rec₂ C c₀ cₛ n ≡ (n , rec C c₀ cₛ n)

  proof C c₀ cₛ zero    = refl
  proof C c₀ cₛ (suc n) = pair= {A = ℕ}{B = C} (ap suc v) (ap₂ cₛ v u)
    where
      v : proj₁ {A = ℕ}{B = C}
        (ite
            (ℕ × C)
            (zero , c₀)
            (λ p → suc (proj₁ p) , cₛ (proj₁ p) (proj₂ p)) n)
         ≡ n
      v = (ap-proj₁ {A = ℕ}{B = C} (proof C c₀ cₛ n))

      u : proj₂ {A = ℕ}{B = C} (rec₂ C c₀ cₛ n) ≡ rec C c₀ cₛ n
      u = ap-proj₂  {A = ℕ}{B = C} (proof C c₀ cₛ n)
module 𝟚-Def₁ where

  data 𝟚 : Set where
    𝟘 : 𝟚
    𝟙 : 𝟚
module 𝟚-Rec₁ where

  open 𝟚-Def₁  using (𝟘;𝟙;𝟚)

  rec : ∀ {i} {C : Set i} (a : C) (b : C ) → 𝟚 → C
  rec a b 𝟘 = a
  rec a b 𝟙 = b
  -- rec is the same if_then_else
module 𝟚-Ind₁ where

  open 𝟚-Def₁ using (𝟘;𝟙;𝟚)

  ind : ∀ {i} {C : 𝟚 → Set i} → C 𝟘 → C 𝟙 → (c : 𝟚) → C c
  ind c₀ c₁ 𝟘 = c₀
  ind c₀ c₁ 𝟙 = c₁
module +-Def₁ where

  open Σ-Def₁ using (Σ;_,_;proj₁; proj₂) public

  open 𝟚-Def₁ using (𝟘;𝟙;𝟚)
  open 𝟚-Rec₁ using (rec)

  _+_ : ∀ {i} (A B : Set i) → Set _
  A + B = Σ 𝟚 (rec A B) -- if it's 𝟘 return A otherwise returns B

  -- the tradional constructors
  inl : ∀ {i}{A B : Set i} → A → A + B
  inl a = (𝟘 , a)

  inr : ∀ {i}{A B : Set i} → B → A + B
  inr b = (𝟙 , b)
module +-Rec₁ where

  open +-Def₁ using (_+_; inl;inr;_,_)
  open 𝟚-Def₁ using (𝟘;𝟙;𝟚)

  rec : ∀ {i j} {A B : Set i} {C : Set j}
      → (A → C)
      → (B → C)
      → A + B → C
  rec f g (𝟘 , a) = f a
  rec f g (𝟙 , b) = g b
module +-Ind₁ where

  open +-Def₁ using (_+_; inl;inr; _,_)
  open 𝟚-Def₁ using (𝟘;𝟙;𝟚)

  ind : ∀ {i j} {A B : Set i} {C : A + B → Set j}
      → ((a : A) → C (inl a))
      → ((b : B) → C (inr b))
      → (p : A + B) → C p
  ind f g (𝟘 , a) = f a
  ind f g (𝟙 , b) = g b

  ind-β₁ : ∀ {i j} {A B : Set i} {C : A + B → Set j}
      → (f : (a : A) → C (inl a))
      → (g : (b : B) → C (inr b))
      → (x : A) → ind {C = C} f g (inl x) ≡ f x
  ind-β₁ f g x = refl

  ind-β₂ : ∀ {i j} {A B : Set i} {C : A + B → Set j}
      → (f : (a : A) → C (inl a))
      → (g : (b : B) → C (inr b))
      → (x : B) → ind {C = C} f g (inr x) ≡ g x
  ind-β₂ f g x = refl
module ×-Def₃ where
  open 𝟚-Def₁ using (𝟘;𝟙;𝟚) public
  open 𝟚-Rec₁ using (rec)

  _×_ : (A B : Set) → Set
  A × B = (x : 𝟚) → rec A B x

  _,_ : ∀ {A B} → A → B → A × B
  (a , b) 𝟘 = a
  (a , b) 𝟙 = b

  proj₁ : ∀ {A B : Set} → A × B → A
  proj₁ x = x 𝟘

  proj₂ : ∀ {A B : Set} → A × B → B
  proj₂ x = x 𝟙

module ×-Fun₃ where
  open ×-Def₃

  pair= : ∀  {A}{B} {x y : A}{a b : B}
        → x ≡ y → a ≡ b → (x , a) ≡ (y , b)
  pair= = ap₂ _,_

  postulate
    Extensionality
      : {A : Set} {B : A → Set} {f g : (x : A) → B x}
      → (∀ x → f x ≡ g x) → f ≡ g

  uniq : ∀ {A B} → (c : A × B) → (proj₁ c , proj₂ c) ≡ c
  uniq {A}{B} c = Extensionality helper
    where
      helper : ∀ (x : 𝟚) → (proj₁ c , proj₂ c) x ≡ c x
      helper 𝟘 = refl
      helper 𝟙 = refl

module ×-Ind₃ where
  open ×-Def₃
  open ×-Fun₃

  ind : ∀ {A B} (C : A × B → Set)
      → ((a : A)(b : B) → C (a , b))
      → (c : A × B) → C c
  ind {A}{B} C f c = subst C (uniq c) (f (c 𝟘) (c 𝟙))

  ind-β : ∀ {A B} (C : A × B → Set)
        → (g : (a : A)(b : B) → C (a , b))
        → ((a : A)(b : B) → ind C g (a , b) ≡ g a b)
  ind-β {A}{B} C g a b = {! !}
    where
      helper :  (u : A × B) → (proj₁ u , proj₂ u) ≡ u
      helper u =  sym (uniq (proj₁ u , proj₂ u)) · uniq u

      uniq-compute : (x : A)(y : B) → helper (x , y) ≡ refl
      uniq-compute x y = right-inverse (uniq (x , y))
        where
          right-inverse : ∀ {i}{X : Set i}{x y : X}
                        → (p : x ≡ y)
                        → (sym p) · p ≡ refl
          right-inverse refl = refl
module Ex1-8 where
  open ℕ-Def
  open ℕ-Rec

  _+_ : ℕ → ℕ → ℕ
  zero    + n = n
  (suc n) + m = suc (n + m)

  multi : ∀ (n m : ℕ) → ℕ
  multi = rec ((m : ℕ) → ℕ) (λ n → zero) (λ n f m →  m + f m)

  exp : ∀ (n m : ℕ) → ℕ
  exp = rec ((m : ℕ) → ℕ) (λ n → suc zero) (λ n g m → multi m (g m))
module Ex1-9 where

  open ℕ-Def
  open Ex1-8 using (_+_)

  data _<_ : ℕ → ℕ → Set where
    z<n : (n : ℕ) → zero < n
    s<s : (n : ℕ) (m : ℕ) → n < m → suc n < suc m

  data _≤_ : ℕ → ℕ → Set where
    z≤n : (n : ℕ) → zero ≤ n
    s≤s : (n : ℕ) (m : ℕ) → n ≤ m → suc n ≤ suc m

  open Σ-Def₁

  Fin : ℕ → Set
  Fin = λ (n : ℕ) → (Σ ℕ (λ m → (suc m ≤ n)))

  fmax : (n : ℕ) → Fin (suc n)
  fmax zero    = (zero , s≤s zero zero (z≤n zero))
  fmax (suc n) = (suc n , s≤s (suc n) (suc n) (s≤s n n (helper n)))
    where
      helper : ∀ (n : ℕ) → n ≤ n
      helper zero    = z≤n zero
      helper (suc n) = s≤s n n (helper n)

  fmax-well : ∀ (n : ℕ)
            → (m : Fin (suc n))
            → proj₁ m ≤ proj₁ (fmax n)
  fmax-well zero    (zero  , p)                    = z≤n zero
  fmax-well zero    (suc n , s≤s .(suc n) .zero p) = p
  fmax-well (suc n) (m     , s≤s .m .(suc n) p)    = p
module Ex1-11 where
  open import Data.PropFormula 1

  proof : ∀ {Γ} {A}
        → Γ ⊢ ¬ ¬ ¬ A ⊃ ¬ A
  proof {Γ}{A} =
    ⊃-intro
      (¬-intro
          (¬-elim
              (weaken A (assume {Γ = Γ} (¬ (¬ (¬ A)))))
              (¬-intro
                (¬-elim
                  (assume {Γ = Γ , ¬ ¬ ¬ A , A} (¬ A))
                  (weaken (¬ A) (assume {Γ = Γ , ¬ ¬ ¬ A} A))))))
module Ex1-16 where
  open ℕ-Def
  open ℕ-Ind
  open Ex1-8 using (_+_)

  proof : (i : ℕ) → ((j : ℕ) → i + j ≡ j + i)
  proof =
    ind (λ (i : ℕ) → ((j : ℕ) → i + j ≡ j + i))
      sproof₁
      sproof₂
    where
      sproof₁ : (j : ℕ) → j ≡ (j + zero)
      sproof₁ =
        ind (λ (j : ℕ) → j ≡ (j + zero))
            refl
            (λ n n≡n+zero → ap suc n≡n+zero)

      sproof₂ : (n : ℕ)
              → ((j : ℕ) → (n + j) ≡ (j + n))
              → ((j : ℕ) → suc (n + j) ≡ (j + suc n))
      sproof₂ n hyp₁ =
          ind (λ (j : ℕ) → suc (n + j) ≡ (j + suc n))
            (ap suc (sym (sproof₁ n)))
            (λ m hyp₂ →
                ap suc
                  (trans
                      (hyp₁ (suc m))
                  (trans
                      (ap suc (sym (hyp₁ m)))
                      hyp₂)))
\begin{align*}
&g : x ≡ z → y ≡ z\\
&g~m~=~\trans~(\sym~p)~m
\end{align*}
\begin{align*}
(p \cdot -) \circ g (m) &= (p \cdot -)~(g~m)\\
                        &= (p \cdot -)~(\trans~(\sym~p)~m)\\
                        &= \trans~p~(\trans~(\sym~p)~m)\\
                        &= \trans~(\trans~p~(\sym~p))~m\\
                        &= \trans~\refl_{x≡z}~m\\
                        &= m
\end{align*}
\begin{align*}
g \circ (p \cdot -) n &= g (\trans~p~n)\\
                      &= (\trans~(\sym~p)~(\trans~p~n)\\
                      &= \trans~(\trans~(\sym~p)~p)~n\\
                      &= \trans~\refl_{y ≡ z}~n\\
                      &= n.
\end{align*}
\begin{align*}
(f \circ g) (z, c) &:\equiv f (g (z,c))\\
&:\equiv f\,(\proj_1 z,\proj_{2} z, c)\\
&:\equiv ((\proj_1 z,\proj_{2} z), c)
\end{align*}
module Σ-Fun₁ where
  open Σ-Def₁ using (proj₁; proj₂; _,_;Σ)

  f : ∀ {A : Set} {B : A → Set} {C : Σ A B → Set}
    → Σ A (λ a → Σ (B a) (λ z → C (a , z))) → Σ (Σ A B) C
  f (a , (b , c)) = (a , b) , c

  g : ∀ {A : Set} {B : A → Set} {C : Σ A B → Set}
     → Σ (Σ A B) C → Σ A (λ a → Σ (B a) (λ z → C (a , z)))
  g {A}{B}{C} (z , c) = (proj₁ z , (proj₂ z , c))

  f-g : ∀ {A : Set} {B : A → Set} {C : Σ A B → Set}
        → (x : Σ (Σ A B) C)
        → f {A = A}{B = B}{C = C} (g x) ≡ x
  f-g x = refl

  g-f : ∀ {A : Set} {B : A → Set} {C : Σ A B → Set}
        → (x : Σ A (λ a → Σ (B a) (λ b → C (a , b))))
        → g {A = A}{B = B}{C = C} (f x) ≡ x
  g-f x = refl
$$\begin{align*}
  f(g(\zero_{\two})) &= f(\id_{\two}) = \id_{\two}(\zero_{\two}) = \zero_{\two}
  \\
  f(g(\one_{\two})) &= f(\lnot) = \lnot \zero_{\two} = \one_{\two}
\end{align*}$$
  $$\begin{align*}
  &h : (A\times B) \to (A'\times B')\\
  &h (a , b) = (f\, a, g\, b).
  \end{align*}$$
  $$\begin{align*}
  &h^{-1} : (A'\times B') \to (A\times B)\\
  &h^{-1} (a , b) = (f^{-1}\, a, g^{-1}\, b).
  \end{align*}$$
\begin{align*}
(\mathsf{ap}_{f}) (\mathsf{ap}_{g} p) \equiv (\mathsf{ap}_{f})  (\mathsf{ap}_{g} q) &=
  \mathsf{ap}_{f \circ g} p \equiv \mathsf{ap}_{f \circ g} q\\
  &=(\text{transporting by using} f \sim g)\\
  &=\mathsf{ap}_{\id_{B}} p \equiv \mathsf{ap}_{\id_{B}} q\\
  &=p \equiv q.
\end{align*}
