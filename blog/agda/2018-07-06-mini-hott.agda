{-# OPTIONS --without-K #-}
open import Agda.Primitive using ( Level ; lsuc; lzero; _⊔_ )
Type : (ℓ : Level) → Set (lsuc ℓ)
Type ℓ = Set ℓ
Type₀ : Type (lsuc lzero)
Type₀ = Type lzero
data ⊥ {ℓᵢ} : Type ℓᵢ where
Empty = ⊥
𝟘     = ⊥
exfalso
  : ∀ {ℓ ℓᵢ} {A : Type ℓ}
  → ⊥ {ℓᵢ}
  --------
  → A

exfalso ()
Empty-elim = exfalso
⊥-elim     = exfalso
𝟘-elim     = exfalso
¬ : ∀ {ℓ} → Type ℓ → Type ℓ
¬ A = (A → ⊥ {lzero})
record ⊤ : Type₀ where
  constructor ★

{-# BUILTIN UNIT ⊤ #-}
Unit = ⊤
𝟙    = ⊤
unit = ★
infixr 60 _,_
record Σ {ℓᵢ ℓⱼ} (A : Type ℓᵢ)(C : A → Type ℓⱼ) : Type (ℓᵢ ⊔ ℓⱼ) where
  constructor _,_
  field
    π₁ : A
    π₂ : C π₁

open Σ public
proj₁ = π₁
proj₂ = π₂

pr₁   = π₁
pr₂   = π₂

fst   = π₁
snd   = π₂
Π
  : ∀ {ℓᵢ ℓⱼ}
  → (A : Type ℓᵢ) (P : A → Type ℓⱼ)
  --------------------------------
  → Type (ℓᵢ ⊔ ℓⱼ)

Π A P = (x : A) → P x
_×_
  : ∀ {ℓᵢ ℓⱼ}
  → (A : Type ℓᵢ) (B : Type ℓⱼ)
  ----------------------------
  → Type (ℓᵢ ⊔ ℓⱼ)

A × B = Σ A (λ _ → B)
infixr 80 _+_
data _+_ {ℓᵢ ℓⱼ} (A : Type ℓᵢ) (B : Type ℓⱼ) : Type (ℓᵢ ⊔ ℓⱼ) where
  inl : A → A + B
  inr : B → A + B
-- Implication.
data _⇒_ {ℓ}(A B : Type ℓ) : Type ℓ where
  fun : (A → B) → A ⇒ B
-- Biconditional.
_⇔_ : ∀ {ℓ} → Type ℓ → Type ℓ → Type ℓ
A ⇔ B = (A ⇒ B) × (B ⇒ A)
data Bool : Type₀ where
  true  : Bool
  false : Bool
𝟚  = Bool
𝟘₂ = false
𝟙₂ = true
neg¬ : Bool → Bool
neg¬ true  = false
neg¬ false = true
data ℕ : Type₀ where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- synonyms for natural numbers
Nat = ℕ
id
  : ∀ {ℓ} {A : Type ℓ}
  → A → A

id = λ x → x
idf
  : ∀ {ℓᵢ}
  → (A : Type ℓᵢ)
  ---------------
  → (A → A)

idf A = λ x → x
cst
  : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ}
  → (b : B)
  ---------
  → (A → B)

cst b = λ _ → b
_∘_
  : ∀ {ℓᵢ ℓⱼ ℓₖ}
  → {A : Type ℓᵢ} {B : A → Type ℓⱼ} {C : (a : A) → (B a → Type ℓₖ)}
  → (g : {a : A} → Π (B a) (C a))
  → (f : Π A B)
  -------------------------------
  → Π A (λ a → C a (f a))

g ∘ f = λ x → g (f x)
infixr 80 _∘_
_//_
  : ∀ {ℓᵢ ℓⱼ ℓₖ}
  → {A : Type ℓᵢ} {B : A → Type ℓⱼ} {C : (a : A) → (B a → Type ℓₖ)}
  → (f : Π A B)
  → (g : {a : A} → Π (B a) (C a))
  -------------------------------
  → Π A (λ a → C a (f a))

f // g = g ∘ f
infixr 0 _$_
_$_
  : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : A → Type ℓⱼ}
  → (∀ x → B x)
  -------------
  → (∀ x → B x)

f $ x = f x
curry
  : ∀ {i j k} {A : Type i} {B : A → Type j} {C : Σ A B → Type k}
  → (∀ s → C s)
  ---------------------
  → (∀ x y → C (x , y))

curry f x y = f (x , y)
uncurry
  : ∀ {i j k} {A : Type i} {B : A → Type j} {C : ∀ x → B x → Type k}
  → (∀ x y → C x y)
  -------------------------
  → (∀ s → C (π₁ s) (π₂ s))

uncurry f (x , y) = f x y
⟨⟩
  : ∀ {i} {A : Type i} {{a : A}} → A

⟨⟩ {{a}} = a
data _==_ {ℓᵢ} {A : Type ℓᵢ} (a : A) : A → Type ℓᵢ where
  idp : a == a

infix 30 _==_
{-# BUILTIN EQUALITY _==_ #-}

-- synonyms for identity type
Path = _==_
refl
  : ∀ {ℓᵢ} {A : Type ℓᵢ}
  → (a : A)
  ---------
  → a == a

refl {ℓᵢ}{A} a = idp {ℓᵢ = ℓᵢ}{A = A}
J
  : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {a : A}
  → (B : (a' : A) (p : a == a') → Type ℓⱼ)
  → (d : B a idp)
  ----------------------------------------
  → {a' : A} (p : a == a') → B a' p

J {a = a} B d idp = d
J'
  : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {a : A}
  → (B : (a' : A) (p : a' == a) → Type ℓⱼ)
  → (d : B a idp)
  ----------------------------------------
  → {a' : A} (p : a' == a) → B a' p

J' {a = a} B d idp = d
_·_
  : ∀ {ℓ} {A : Type ℓ} {x y z : A}
  → (p : x == y)
  → (q : y == z)
  --------------
  → x == z

_·_ idp q = q

infixl 50 _·_
inv
  : ∀ {ℓ} {A : Type ℓ} {a b : A}
  → a == b
  --------
  → b == a

inv idp = idp

-- synonyms for inverse path
infixl 60 _⁻¹
_⁻¹ = inv

infixr 60 !_
!_  = inv
∘-lassoc
  : ∀ {ℓ} {A B C D : Type ℓ}
  → (h : C → D) → (g : B → C) → (f : A → B)
  -----------------------------------------
  → (h ∘ (g ∘ f)) == ((h ∘ g) ∘ f)

∘-lassoc h g f = idp {a = (λ x → h (g (f x)))}
∘-rassoc
  : ∀ {ℓ} {A B C D : Type ℓ}
  → (h : C → D) → (g : B → C) → (f : A → B)
  -----------------------------------------
  → ((h ∘ g) ∘ f) == (h ∘ (g ∘ f))

∘-rassoc h g f = (∘-lassoc h g f) ⁻¹
data HEq {ℓ} (A : Type ℓ)
           : (B : Type ℓ)
           → (α : A == B) (a : A) (b : B)
           → Type ℓ where
  idp : ∀ {a : A} → HEq A A idp a a
module EquationalReasoning {ℓᵢ} {A : Type ℓᵢ} where
  -- Reasoning.
  _==⟨⟩_
    : ∀ (x {y} : A)
    → x == y → x == y

  _ ==⟨⟩ p = p

  -- synonyms for _==⟨⟩
  _==⟨idp⟩_  = _==⟨⟩_
  _==⟨refl⟩_ = _==⟨⟩_

  infixr 2 _==⟨⟩_
  -- chain
  _==⟨_⟩_
    : (x : A) {y z : A}
    → x == y
    → y == z
    → x == z

  _ ==⟨ thm ⟩ q = thm · q

  infixr 2 _==⟨_⟩_
  -- Q.E.D
  infix 3 _∎
  _∎
    : (x : A)
    → x == x

  _∎ = λ x → idp
  -- Begin
  infix 1 begin_
  begin_
    : {x y : A}
    → x == y
    → x == y

  begin_ p = p
open EquationalReasoning public
ap
  : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ}
  → (f : A → B) {a₁ a₂ : A}
  → a₁ == a₂
  --------------
  → f a₁ == f a₂

ap f idp = idp
infixl 40 ap
syntax ap f p = p |in-ctx f
ap₂
  : ∀ {ℓᵢ ℓⱼ ℓₖ} {A : Type ℓᵢ} {B : Type ℓⱼ} {C : Type ℓₖ}  {b₁ b₂ : B}
  → (f : A → B → C)
  → {a₁ a₂ : A} → (a₁ == a₂)
  → {b₁ b₂ : B} → (b₁ == b₂)
  --------------------------
  → f a₁ b₁  == f a₂ b₂

ap₂ f idp idp = idp
ap-·
  : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} {a b c : A}
  → (f : A → B) → (p : a == b) → (q : b == c)
  -------------------------------------------
  → ap f (p · q) == ap f p · ap f q

ap-· f idp q = refl (ap f q)
ap-inv
  : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} {a b : A}
  → (f : A → B) → (p : a == b)
  ----------------------------
  → ap f (p ⁻¹) == (ap f p) ⁻¹

ap-inv f idp = idp

-- synonyms
ap-! = ap-inv
ap-comp
  : ∀ {ℓᵢ ℓⱼ ℓₖ} {A : Type ℓᵢ} {B : Type ℓⱼ} {C : Type ℓₖ} {a b : A}
  → (f : A → B)
  → (g : B → C)
  → (p : a == b)
  -------------------------------
  → ap g (ap f p) == ap (g ∘ f) p

ap-comp f g idp = idp
ap-id
  : ∀ {ℓᵢ} {A : Type ℓᵢ} {a b : A}
  → (p : a == b)
  --------------
  → ap id p == p

ap-id idp = idp
ap-const
  : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {C : Type ℓⱼ} {a b : A} {c : C}
  → (p : a == b)
  -----------------------
  → ap (λ _ → c) p == idp

ap-const {c = c} idp = refl (refl c)
·-runit
  : ∀ {ℓ} {A : Type ℓ} {a b : A}
  → (p : a == b)
  --------------
  → p == p · idp

·-runit idp = idp
·-lunit
  : ∀ {ℓ} {A : Type ℓ} {a b : A}
  → (p : a == b)
  --------------
  → p == idp · p

·-lunit idp = idp
·-linv
  : ∀ {ℓ} {A : Type ℓ} {a b : A}
  → (p : a == b)
  ----------------
  → ! p · p == idp

·-linv idp = idp
·-rinv
  : ∀ {ℓ} {A : Type ℓ} {a b : A}
  → (p : a == b)
  ----------------
  → p · ! p == idp

·-rinv idp = idp
involution
  : ∀ {ℓ} {A : Type ℓ} {a b : A}
  → {p : a == b}
  ---------------
  → ! (! p) == p

involution {p = idp} = idp
·-assoc
  : ∀ {ℓ} {A : Type ℓ} {a b c d : A}
  → (p : a == b) → (q : b == c) → (r : c == d)
  --------------------------------------------
  → p · q · r == p · (q · r)

·-assoc idp q r = idp
·-cancellation
  : ∀ {ℓ} {A : Type ℓ} {a : A}
  → (p : a == a) → (q : a == a) → p · q == p
  -----------------------------------------
  → q == refl a

·-cancellation {a = a} p q α =
    begin
      q             ==⟨ ap (_· q) (! (·-linv p)) ⟩
      ! p · p · q   ==⟨ (·-assoc (! p) _ _) ⟩
      ! p · (p · q) ==⟨ (ap (! p ·_) α) ⟩
      ! p · p       ==⟨ ·-linv p ⟩
      refl a
    ∎
·-left-to-right-l
  : ∀ {ℓ} {A : Type ℓ} {a b c : A} {p : a == b} {q : b == c} {r : a == c}
  → p · q == r
  ------------------
  →     q == ! p · r

·-left-to-right-l {a = a}{b = b}{c = c} {p} {q} {r} α =
  begin
    q
      ==⟨ ·-lunit q ⟩
    refl b · q
      ==⟨ ap (_· q) (! (·-linv p)) ⟩
    (! p · p) · q
      ==⟨ ·-assoc (! p) p q ⟩
    ! p · (p · q)
      ==⟨ ap (! p ·_) α ⟩
    ! p · r
  ∎
·-left-to-right-r
  : ∀ {ℓ} {A : Type ℓ} {a b c : A} {p : a == b} {q : b == c} {r : a == c}
  → p · q == r
  -------------------
  →      p == r · ! q

·-left-to-right-r {a = a}{b = b}{c = c} {p} {q} {r} α =
  begin
    p
      ==⟨ ·-runit p ⟩
    p · refl b
      ==⟨ ap (p ·_) (! (·-rinv q)) ⟩
    p · (q · ! q)
      ==⟨ ! (·-assoc p q (! q)) ⟩
    (p · q) · ! q
      ==⟨ ap (_· ! q) α ⟩
    r · ! q
  ∎
·-right-to-left-r
  : ∀ {ℓ} {A : Type ℓ} {a b c : A} {p : a == c} {q : a == b} {r : b == c}
  →       p == q · r
  -------------------
  → p · ! r == q

·-right-to-left-r {a = a}{b = b}{c = c} {p} {q} {r} α =
  begin
    p · ! r
      ==⟨ ap (_· ! r) α ⟩
    (q · r) · ! r
      ==⟨ ·-assoc q r (! r) ⟩
    q · (r · ! r)
      ==⟨ ap (q ·_) (·-rinv r) ⟩
    q · refl b
      ==⟨ ! (·-runit q) ⟩
    q
    ∎
·-right-to-left-l
  : ∀ {ℓ} {A : Type ℓ} {a b c : A} {p : a == c} {q : a == b} {r : b == c}
  →       p == q · r
  ------------------
  → ! q · p == r

·-right-to-left-l {a = a}{b = b}{c = c} {p} {q} {r} α =
  begin
    ! q · p
      ==⟨ ap (! q ·_) α ⟩
    ! q · (q · r)
      ==⟨ ! (·-assoc (! q) q r) ⟩
    ! q · q · r
      ==⟨ ap (_· r) (·-linv q) ⟩
    refl b · r
      ==⟨ ! (·-lunit r) ⟩
    r
  ∎
!-·
  : ∀ {ℓ} {A : Type ℓ} {a b : A}
  → (p : a == b)
  → (q : b == a)
  --------------------------
  → ! (p · q) == ! q · ! p

!-· idp q = ·-runit (! q)
transport
  : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ}
  → (C : A → Type ℓⱼ) {a₁ a₂ : A}
  → (p : a₁ == a₂)
  -------------------------------
  → (C a₁ → C a₂)

transport C idp = (λ x → x)
-- synonyms
tr     = transport
transp = transport
_✶
  : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {C : A → Type ℓⱼ} {a₁ a₂ : A}
  → (p : a₁ == a₂)
  ----------------
  → (C a₁ → C a₂)

_✶ {ℓᵢ}{ℓⱼ}{C = C} = transport {ℓᵢ = ℓᵢ} {ℓⱼ = ℓⱼ} C
coe
  : ∀ {ℓ} {A B : Type ℓ}
  → A == B
  ---------
  → (A → B)

coe p a = transport (λ X → X) p a
tr₂
  : {i j k : Level}
  → (A : Type i)
  → (B : A → Type j)
  → (C : (x : A) → (b : B x) → Type k)
  → ∀ {a₁ a₂ : A}{b₁ : B a₁}{b₂ : B a₂}
  → (p : a₁ == a₂)
  → (q : tr B p b₁ == b₂)
  → C a₁ b₁
  -----------------------
  → C a₂ b₂

tr₂ A B C idp idp = id
PathOver
  : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ}
  → (C : A → Type ℓⱼ) {a₁ a₂ : A}
  → (α : a₁ == a₂)
  → (c₁ : C a₁) → (c₂ : C a₂)
  ------------------------------
  → Type ℓⱼ

PathOver C α c₁ c₂ = tr C α c₁ == c₂
infix 30 PathOver
syntax PathOver B p u v = u == v [ B ↓ p ]
lift
  : ∀ {ℓᵢ} {A : Type ℓᵢ} {a₁ a₂ : A} {ℓⱼ} {C : A → Type ℓⱼ}
  → (u : C a₁)
  → (α : a₁ == a₂)
  -----------------------------
  → (a₁ , u) == (a₂ , tr C α u)

lift {a₁ = a₁} u idp = refl (a₁ , u)
transport-const
  : ∀ {ℓᵢ} {A : Type ℓᵢ} {a₁  a₂ : A} {ℓⱼ} {B : Type ℓⱼ}
  → (p : a₁ == a₂)
  → (b : B)
  -----------------------
  → tr (λ _ → B) p b == b

transport-const idp b = refl b
transport-concat-r
  : ∀ {ℓᵢ} {A : Type ℓᵢ} {a : A} {x y : A}
  → (p : x == y)
  → (q : a == x)
  ---------------------------------
  →  tr (λ x → a == x) p q == q · p

transport-concat-r idp q = ·-runit q
transport-concat-l
  : ∀ {ℓᵢ} {A : Type ℓᵢ} {a : A} {x y : A}
  → (p : x == y)
  → (q : x == a)
  ----------------------------------
  → tr (λ x → x == a) p q == ! p · q

transport-concat-l idp q = idp
transport-concat
  : ∀ {ℓᵢ} {A : Type ℓᵢ} {x y : A}
  → (p : x == y)
  → (q : x == x)
  ---------------------------------------
  → tr (λ x → x == x) p q == ! p · q · p

transport-concat idp q = ·-runit q
transport-eq-fun
  : ∀ {ℓᵢ} {A : Type ℓᵢ} {ℓⱼ} {B : Type ℓⱼ}
  → (f g : A → B) {x y : A}
  → (p : x == y)
  → (q : f x == g x)
  --------------------------------------------------------
  → tr (λ z → f z == g z) p q == ! (ap f p) · q · (ap g p)

transport-eq-fun f g idp q = ·-runit q
transport-comp
  : ∀ {ℓᵢ} {A : Type ℓᵢ}{ℓⱼ} {a b c : A} {P : A → Type ℓⱼ}
  → (p : a == b)
  → (q : b == c)
  ---------------------------------------
  → ((tr P q) ∘ (tr P p)) == tr P (p · q)

transport-comp {P = P} idp q = refl (transport P q)
transport-comp-h
  : ∀ {ℓᵢ} {A : Type ℓᵢ} {ℓⱼ} {a b c : A} {P : A → Type ℓⱼ}
  → (p : a == b)
  → (q : b == c)
  → (x : P a)
  -------------------------------------------
  → ((tr P q) ∘ (tr P p)) x == tr P (p · q) x

transport-comp-h {P = P} idp q x = refl (transport P q x)
transport-eq-fun-l
  : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} {b : B} (f : A → B) {x y : A}
  → (p : x == y)
  → (q : f x == b)
  -------------------------------------------
  → tr (λ z → f z == b) p q == ! (ap f p) · q

transport-eq-fun-l {b = b} f p q =
  begin
    transport (λ z → f z == b) p q   ==⟨ transport-eq-fun f (λ _ → b) p q ⟩
    ! (ap f p) · q · ap (λ _ → b) p  ==⟨ ap (! (ap f p) · q ·_) (ap-const p) ⟩
    ! (ap f p) · q · idp             ==⟨ ! (·-runit _) ⟩
    ! (ap f p) · q
  ∎
transport-eq-fun-r
  : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} {b : B}
  → (g : A → B) {x y : A}
  → (p : x == y)
  → (q : b == g x)
  -----------------------------------------
  → tr (λ z → b == g z) p q == q · (ap g p)

transport-eq-fun-r {b = b} g p q =
  begin
    transport (λ z → b == g z) p q    ==⟨ transport-eq-fun (λ _ → b) g p q ⟩
    ! (ap (λ _ → b) p) · q · ap g p   ==⟨ ·-assoc (! (ap (λ _ → b) p)) q (ap g p) ⟩
    ! (ap (λ _ → b) p) · (q · ap g p) ==⟨ ap (λ u → ! u · (q · ap g p)) (ap-const p) ⟩
    (q · ap g p)
  ∎
transport-inv
  : ∀ {ℓᵢ ℓⱼ} {X : Type ℓᵢ}{A : X → Type ℓⱼ}{x y : X}
  → (p : x == y)
  → {a : A y}
  --------------------------------------
  → tr (λ v → A v) p (tr A (! p) a) == a

transport-inv {A = A}  idp {a = a} =
  begin
    tr (λ v → A v) idp (tr A (! idp) a)
      ==⟨ idp ⟩
    tr A (! idp · idp) a
      ==⟨⟩
    tr A idp a
      ==⟨ idp ⟩
    a
  ∎
coe-inv-l
  : ∀ {ℓ} {A B : Type ℓ}
  → (p : A == B)
  → (b : B)
  --------------------------------------------
  → tr (λ v → v) p (tr (λ v → v) (! p) b) == b

coe-inv-l idp b = idp
coe-inv-r
  : ∀ {ℓ} {A B : Type ℓ}
  → (p : A == B)
  → (a : A)
  ---------------------------------------------
  → tr (λ v → v) (! p) (tr (λ v → v) p a) == a

coe-inv-r idp b = idp
transport-family
  : ∀ {ℓᵢ ℓⱼ ℓₖ} {A : Type ℓᵢ} {B : Type ℓⱼ} {P : B → Type ℓₖ}
  → {f : A → B} → {x y : A}
  → (p : x == y)
  → (u : P (f x))
  -----------------------------------
  → tr (P ∘ f) p u == tr P (ap f p) u

transport-family idp u = idp
transport-family-id
  : ∀ {ℓᵢ ℓₖ} {A : Type ℓᵢ} {P : A → Type ℓₖ} → {x y : A}
  → (p : x == y)
  → (u : P x)
  ----------------------------------------------
  → transport (λ a → P a) p u == transport P p u

transport-family-id idp u = idp
transport-fun
  : ∀ {ℓᵢ ℓⱼ ℓₖ} {X : Type ℓᵢ} {x y : X}
  → {A : X → Type ℓⱼ} {B : X → Type ℓₖ}
  → (p : x == y)
  → (f : A x → B x)
  -----------------------------------------------------------------
  → tr (λ x → (A x → B x)) p f == (λ x → tr B p (f (tr A (! p) x)))

transport-fun idp f = idp
-- synonyms
back-and-forth = transport-fun
transport-fun-h
  : ∀ {ℓᵢ ℓⱼ ℓₖ} {X : Type ℓᵢ} {A : X → Type ℓⱼ} {B : X → Type ℓₖ}
  → {x y : X}
  → (p : x == y) → (f : A x → B x)
  → (b : A y)
  --------------------------------------------------------------
  → (tr (λ x → (A x → B x)) p f) b == tr B p (f (tr A (! p) b))

transport-fun-h idp f b = idp
-- synonyms
back-and-forth-h = transport-fun-h
transport-fun-dependent-h
  : ∀ {ℓᵢ ℓⱼ ℓₖ} {X : Type ℓᵢ} {A : X → Type ℓⱼ}
  → {B : (x : X) → (a : A x) → Type ℓₖ} {x y : X}
  → (p : x == y)
  → (f : (a : A x) → B x a)
  ---------------------------------------------------------------------
  → (a' : A y)
  → (tr (λ x → (a : A x) → B x a) p f) a'
    == tr (λ w → B (π₁ w) (π₂ w)) (! lift a' (! p)) (f (tr A (! p) a'))

transport-fun-dependent-h idp f a' = idp
-- synonyms
dependent-back-and-forth-h = transport-fun-dependent-h
transport-fun-dependent
  : ∀ {ℓᵢ ℓⱼ ℓₖ} {X : Type ℓᵢ} {A : X → Type ℓⱼ}
  → {B : (x : X) → (a : A x) → Type ℓₖ} {x y : X}
  → (p : x == y)
  → (f : (a : A x) → B x a)
  ---------------------------------------------------------------------
  → (tr (λ x → (a : A x) → B x a) p f)
    == λ (a' : A y)
      → tr (λ w → B (π₁ w) (π₂ w)) (! lift a' (! p)) (f (tr A (! p) a'))

transport-fun-dependent idp f = idp
-- synonyms
dependent-back-and-forth = transport-fun-dependent
apOver
  : {A A' : Type₀} {C : A → Type₀} {C' : A' → Type₀}  -- types
  → {a a' : A} {b : C a} {b' : C a'}                  -- points
  → (f : A → A')
  → (g : {x : A} → C x → C' (f x))
  → (p : a == a')
  → b == b' [ C ↓ p ]
  --------------------------------
  → g b == g b' [ C' ↓ ap f p ]

apOver f g idp q = ap g q
module Sigma {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {P : A → Type ℓⱼ} where
  -- Lemma.
  Σ-componentwise
    : ∀ {v w : Σ A P}
    → v == w
    ----------------------------------------------
    → Σ (π₁ v == π₁ w) (λ p → (p ✶) (π₂ v) == π₂ w)

  Σ-componentwise  idp = (idp , idp)
  -- Lemma.
  Σ-bycomponents
    : ∀ {v w : Σ A P}
    → Σ (π₁ v == π₁ w) (λ p → (p ✶) (π₂ v) == π₂ w)
    -----------------------------------------------
    → v == w

  Σ-bycomponents (idp , idp) = idp

  -- synonym of Σ-bycomponents
  pair= = Σ-bycomponents
-- Lemma.
  lift-pair=
    : ∀ {x y : A} {u : P x}
    → (p : x == y)
    --------------------------------------------------------
    → lift {A = A}{C = P} u p == pair= (p , refl (tr P p u))

  lift-pair= idp = idp
-- Uniqueness principle property for products
  uppt : (x : Σ A P) → (π₁ x , π₂ x) == x
  uppt (a , b) = idp
-- Lemma.
  Σ-ap-π₁
    : {a₁ a₂ : A} {b₁ : P a₁} {b₂ : P a₂}
    → (α : a₁ == a₂)
    → (γ : transport P α b₁ == b₂)
    ------------------------------
    → ap π₁ (pair= (α , γ)) == α

  Σ-ap-π₁ idp idp = idp

  -- synonym for this lemma
  ap-π₁-pair= = Σ-ap-π₁
open Sigma public
transport-fun-dependent-bezem
  : ∀ {ℓᵢ ℓⱼ} {X : Type ℓᵢ} {A : X → Type ℓⱼ}
      {B : (x : X) → (a : A x) → Type ℓⱼ} {x y : X}
  → (p : x == y)
  → (f : (a : A x) → B x a)
  → (a' : A y)
  ----------------------------------------------------------
  → (tr (λ x → (a : A x) → B x a) p f) a'
    == tr (λ w → B (π₁ w) (π₂ w))
          (pair= (p , transport-inv p )) (f (tr A (! p) a'))

transport-fun-dependent-bezem idp f a' = idp
module CartesianProduct {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where
  -- Lemma.
  prodComponentwise
    : {x y : A × B}
    → (x == y)
    ---------------------------------
    → (π₁ x == π₁ y) × (π₂ x == π₂ y)

  prodComponentwise {x = x} idp = refl (π₁ x) , refl (π₂ x)
  -- Lemma.
  prodByComponents
    : {x y : A × B}
    → (π₁ x == π₁ y) × (π₂ x == π₂ y)
    ---------------------------------
    → (x == y)

  prodByComponents {x = a , b} (idp , idp) = refl (a , b)
  -- Lemma.
  prodCompInverse
    : {x y : A × B}
    → (b : (π₁ x == π₁ y) × (π₂ x == π₂ y))
    ---------------------------------------------
    → prodComponentwise (prodByComponents b) == b

  prodCompInverse {x} (idp , idp) = refl (refl (π₁ x) , refl (π₂ x))
  -- Lemma.
  prodByCompInverse
    : {x y : A × B}
    → (b : x == y)
    ---------------------------------------------
    → prodByComponents (prodComponentwise b) == b

  prodByCompInverse {x = x} idp = refl (refl x)
open CartesianProduct
apd
  : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ}  {P : A → Type ℓⱼ} {a b : A}
  → (f : (a : A) → P a) → (p : a == b)
  ------------------------------------
  → transport P p (f a) == f b

apd f idp = idp
module Homotopy {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {P : A → Type ℓⱼ} where
  -- Lemma.
  homotopy
    : (f g : Π A P)
    ---------------
    → Type (ℓᵢ ⊔ ℓⱼ)

  homotopy f g = ∀ (x : A) → f x == g x
  -- Usual notation for homotopy
  _∼_ : (f g : ((x : A) → P x)) → Type (ℓᵢ ⊔ ℓⱼ)
  f ∼ g = homotopy f g
  -- Homotopy is an equivalence relation
  h-refl
    : (f : Π A P)
    -------------
    → f ∼ f

  h-refl f x = idp
  -- Lemma.
  h-sym
    : (f g : Π A P)
    → f ∼ g
    -------
    → g ∼ f

  h-sym _ _ e x = ! (e x)
  -- Lemma.
  h-comp
    : {f g h : Π A P}
    → f ∼ g
    → g ∼ h
    -------
    → f ∼ h

  h-comp u v x = (u x) · (v x)
  -- synonym for h-comp
  _●_
    : {f g h : Π A P}
    → f ∼ g
    → g ∼ h
    -------
    → f ∼ h

  α ● β = h-comp α β
open Homotopy public
module HomotopyComposition {ℓᵢ ℓⱼ ℓₖ}
  {A : Type ℓᵢ} {B : Type ℓⱼ} {C : Type ℓₖ} where
  -- Lemma.
  hl-comp
    : {f g : A → B}
    → {j k : B → C}
    → f ∼ g
    → j ∼ k
    -------------------
    → (j ∘ f) ∼ (k ∘ g)

  hl-comp {g = g}{j = j} f-g j-k = λ x → ap j (f-g x) · j-k (g x)
  -- Lemma.
  rcomp-∼
    : (f : A → B)
    → {j k : B → C}
    → j ∼ k
    -------------------
    → (j ∘ f) ∼ (k ∘ f)

  rcomp-∼ f j-k = hl-comp (h-refl f) j-k
  -- Lemma.
  lcomp-∼
    : {f g : A → B}
    → (j : B → C)
    → f ∼ g
    -------------------
    → (j ∘ f) ∼ (j ∘ g)

  lcomp-∼ j α = hl-comp α (h-refl j)
open HomotopyComposition
module Naturality {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where
  -- Lemma.
  h-naturality
    : {f g : A → B} → {x y : A}
    → (H : f ∼ g)
    → (p : x == y)
    ------------------------------
    → H x · ap g p == ap f p · H y

  h-naturality {x = x} H idp = ! (·-runit (H x))
open Naturality public
-- Lemma.
h-naturality-id
  : ∀ {ℓ} {A : Type ℓ} {f : A → A} → {x : A}
  → (H : f ∼ id)
  -----------------------
  → H (f x) == ap f (H x)

h-naturality-id {f = f} {x = x} H =
  begin
    H (f x)
      ==⟨ ·-runit (H (f x)) ⟩
    H (f x) · refl (f x)
      ==⟨ ap (H (f x) ·_) (! (·-rinv (H x))) ⟩
    H (f x) · ((H x) · (! (H x)))
      ==⟨ ap (H (f x) ·_) (ap (_· (! (H x))) (! ap-id (H x))) ⟩
    H (f x) · (ap id (H x) · ! (H x))
      ==⟨ ! (·-assoc (H (f x)) (ap id (H x)) (! (H x))) ⟩
    (H (f x) · ap id (H x)) · ! (H x)
      ==⟨ ·-right-to-left-r (h-naturality H (H x)) ⟩
    ap f (H x)
  ∎
module Fibers {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ}  where
  -- Fiber
  fib
    : (f : A → B)
    → (b : B)
    ---------------
    → Type (ℓᵢ ⊔ ℓⱼ)

  fib f b = Σ A (λ a → f a == b)
  -- Lemma.
  fib-eq
    : ∀ {f : A → B} {b : B}
    → (h : fib f b)
    ---------------
    → f (π₁ h) == b

  fib-eq (a , α) = α
  -- Lemma.
  fib-image
    :  ∀ {f : A → B} → {a : A}
    → fib f (f a)

  fib-image {f} {a} = a , refl (f a)
open Fibers public
module Contractible where
  -- Def.
  isContr
    : ∀ {ℓ}
    → (A : Type ℓ)
    --------------
    → Type ℓ

  isContr A = Σ A (λ a → ((x : A) → a == x))

  -- Lemma.
  allAreCenter
    : ∀ {ℓ} {A : Type ℓ}
    → (c₁ : A) → (f : (x : A) → c₁ == x)
    → (∀ (c₂ : A) → (∀ (x : A) → c₂ == x))
  allAreCenter c₁ f c₂ x = ! (f c₂) · (f x)

open Contractible public
isContrMap
  : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ}
  → (f : A → B)
  → Type (ℓᵢ ⊔ ℓⱼ)

isContrMap {B = B} f = (b : B) → isContr (fib f b)
module Equivalence where

  module DefinitionOfEquivalence  {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where
    -- There exists an equivalence between two types if there exists a
    -- contractible function between them.
    isEquiv : (f : A → B) → Type (ℓᵢ ⊔ ℓⱼ)
    isEquiv = isContrMap
  open DefinitionOfEquivalence public
  -- Equivalence of types.
  _≃_ : ∀ {ℓᵢ ℓⱼ}  (A : Type ℓᵢ) (B : Type ℓⱼ) → Type (ℓᵢ ⊔ ℓⱼ)
  A ≃ B = Σ (A → B) isEquiv
  module EquivalenceMaps {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where

    -- Maps of an equivalence
    lemap : A ≃ B → (A → B)
    lemap = π₁

    ≃-to-→ = lemap
    fun≃   = lemap

    infixl 70 _∙
    _∙ = lemap

    remap : A ≃ B → (B → A)
    remap (f , contrf) b = π₁ (π₁ (contrf b))

    -- The maps of an equivalence are inverses in particular
    lrmap-inverse : (eq : A ≃ B) → {b : B} → (lemap eq) ((remap eq) b) == b
    lrmap-inverse (f , eqf) {b} = fib-eq (π₁ (eqf b))

    rlmap-inverse : (eq : A ≃ B) → {a : A} → (remap eq) ((lemap eq) a) == a
    rlmap-inverse (f , eqf) {a} = ap π₁ ((π₂ (eqf (f a))) fib-image)

    lrmap-inverse-h : (eq : A ≃ B) → ((lemap eq) ∘ (remap eq)) ∼ id
    lrmap-inverse-h eq = λ x → lrmap-inverse eq {x}

    rlmap-inverse-h : (eq : A ≃ B) → ((remap eq) ∘ (lemap eq)) ∼ id
    rlmap-inverse-h eq = λ x → rlmap-inverse eq {x}
  open EquivalenceMaps public
open Equivalence public

module FunExt {ℓᵢ ℓⱼ} {A : Type ℓᵢ}
  {B : A → Type ℓⱼ} {f g : (a : A) → B a} where
  -- Application of an homotopy
  happly : f == g → ((x : A) → f x == g x)
  happly idp x = refl (f x)
  -- The axiom of function extensionality postulates that the
  -- application of homotopies is an equivalence.
  postulate
    axiomFunExt : isEquiv happly
  eqFunExt : (f == g) ≃ ((x : A) → f x == g x)
  eqFunExt = happly , axiomFunExt
  -- From this, the usual notion of function extensionality follows.
  funext : ((x : A) → f x == g x) → f == g
  funext = remap eqFunExt
  -- Beta and eta rules for function extensionality
  funext-β : (h : ((x : A) → f x == g x)) → happly (funext h) == h
  funext-β h = lrmap-inverse eqFunExt
  funext-η : (p : f == g) → funext (happly p) == p
  funext-η p = rlmap-inverse eqFunExt
open FunExt public
module FunExt-Transport
  {ℓᵢ ℓⱼ} {X : Type ℓᵢ} {A B : X → Type ℓⱼ} {x y : X} where
  funext-transport
    : (p : x == y) → (f : A x → B x) → (g : A y → B y)
    ------------------------------------------------------------
    → ((p ✶) f == g) ≃ ((a : A(x)) → (p ✶) (f a) == g ((p ✶) a))

  funext-transport idp f g = eqFunExt
  funext-transport-l
    : (p : x == y)
    → (f : A x → B x)
    → (g : A y → B y)
    → ((p ✶) f == g)
    -------------------------------------------
    → ((a : A(x)) → (p ✶) (f a) == g ((p ✶) a))

  funext-transport-l p f g = lemap (funext-transport p _ _)
  funext-transport-r
    : (p : x == y)
    → (f : A x → B x)
    → (g : A y → B y)
    → ((a : A(x)) → (p ✶) (f a) == g ((p ✶) a))
    -------------------------------------------
    → ((p ✶) f == g)

  funext-transport-r p f g = remap (funext-transport p _ _)
open FunExt-Transport public
module FunExt-Transport-DFun
  {ℓᵢ ℓⱼ} {X : Type ℓᵢ} {A : X → Type ℓⱼ}{B : (x : X) → A x → Type ℓⱼ}{x y : X}
  where

  -- Lemma 2.9.7
  funext-transport-dfun
    : (p : x == y)
    → (f : (a : A x) → B x a)
    → (g : (a : A y) → B y a)
    ----------------------------------------------------------------------------
    → ((p ✶) f == g)
      ≃ ((a : A x) → tr (λ w → B (π₁ w) (π₂ w)) (pair= (p , refl (tr A p a))) (f a) == g ((p ✶) a))

  funext-transport-dfun idp f g = eqFunExt

  funext-transport-dfun-l
    : (p : x == y) → (f : (a : A x) → B x a) → (g : (a : A y) → B y a)
    → ((p ✶) f == g)
    ---------------------------------------------------------------------------
    → ((a : A x) → tr (λ w → B (π₁ w) (π₂ w)) (pair= (p , refl (tr A p a))) (f a) == g ((p ✶) a))

  funext-transport-dfun-l p f g = lemap (funext-transport-dfun p _ _)

  funext-transport-dfun-r
    : (p : x == y)
    → (f : (a : A x) → B x a)
    → (g : (a : A y) → B y a)
    → ((a : A x) → tr (λ w → B (π₁ w) (π₂ w)) (pair= (p , refl (tr A p a))) (f a) == g ((p ✶) a))
    --------------------------------------------------------------------------
    → ((p ✶) f == g)

  funext-transport-dfun-r p f g = remap (funext-transport-dfun p _ _)
open FunExt-Transport-DFun public
module DecidableEquality {ℓ} where

  -- A type has decidable equality if we can prove that any two of its
  -- elements are equal or different.
  decEq : (A : Type ℓ) → Type ℓ
  decEq A = (a b : A) → (a == b) + ¬ (a == b)

  -- The product of types with decidable equality is a type with
  -- decidable equality.
  decEqProd : {A B : Type ℓ} → decEq A → decEq B → decEq (A × B)
  decEqProd da db (a1 , b1) (a2 , b2) with (da a1 a2) | (db b1 b2)
  decEqProd da db (a1 , b1) (a2 , b2) | inl aeq | inl beq = inl (prodByComponents (aeq , beq))
  decEqProd da db (a1 , b1) (a2 , b2) | inl aeq | inr bnq = inr λ b → bnq (ap π₂ b)
  decEqProd da db (a1 , b1) (a2 , b2) | inr anq | u       = inr λ b → anq (ap π₁ b)

open DecidableEquality
module Halfadjoints {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where

  -- Half adjoint equivalence.
  record ishae (f : A → B) : Type (ℓᵢ ⊔ ℓⱼ) where
    constructor hae
    field
      g : B → A
      η : (g ∘ f) ∼ id
      ε : (f ∘ g) ∼ id
      τ : (a : A) → ap f (η a) == ε (f a)

  -- Half adjoint equivalences give contractible fibers.
  ishae-contr : (f : A → B) → ishae f → isContrMap f
  ishae-contr f (hae g η ε τ) y = ((g y) , (ε y)) , contra
    where
      lemma : (c c' : fib f y) → Σ (π₁ c == π₁ c') (λ γ → (ap f γ) · π₂ c' == π₂ c) → c == c'
      lemma c c' (p , q) = Σ-bycomponents (p , lemma2)
        where
          lemma2 : transport (λ z → f z == y) p (π₂ c) == π₂ c'
          lemma2 =
            begin
              transport (λ z → f z == y) p (π₂ c)
                ==⟨ transport-eq-fun-l f p (π₂ c) ⟩
              inv (ap f p) · (π₂ c)
                ==⟨ ap (inv (ap f p) ·_) (inv q) ⟩
              inv (ap f p) · ((ap f p) · (π₂ c'))
                ==⟨ inv (·-assoc (inv (ap f p)) (ap f p) (π₂ c')) ⟩
              inv (ap f p) · (ap f p) · (π₂ c')
                ==⟨ ap (_· (π₂ c')) (·-linv (ap f p)) ⟩
              π₂ c'
            ∎

      contra : (x : fib f y) → (g y , ε y) == x
      contra (x , p) = lemma (g y , ε y) (x , p) (γ , lemma3)
        where
          γ : g y == x
          γ = inv (ap g p) · η x

          lemma3 : (ap f γ · p) == ε y
          lemma3 =
            begin
              ap f γ · p
                ==⟨ ap (_· p) (ap-· f (inv (ap g p)) (η x)) ⟩
              ap f (inv (ap g p)) · ap f (η x) · p
                ==⟨ ·-assoc (ap f (inv (ap g p))) _ p ⟩
              ap f (inv (ap g p)) · (ap f (η x) · p)
                ==⟨ ap (_· (ap f (η x) · p)) (ap-inv f (ap g p)) ⟩
              inv (ap f (ap g p)) · (ap f (η x) · p)
                ==⟨ ap (λ u → inv (ap f (ap g p)) · (u · p)) (τ x) ⟩
              inv (ap f (ap g p)) · (ε (f x) · p)
                ==⟨ ap (λ u → inv (ap f (ap g p)) · (ε (f x) · u)) (inv (ap-id p)) ⟩
              inv (ap f (ap g p)) · (ε (f x) · ap id p)
                ==⟨ ap (inv (ap f (ap g p)) ·_) (h-naturality ε p) ⟩
              inv (ap f (ap g p)) · (ap (f ∘ g) p · ε y)
                ==⟨ ap (λ u → inv u · (ap (f ∘ g) p · ε y)) (ap-comp g f p) ⟩
              inv (ap (f ∘ g) p) · (ap (f ∘ g) p · ε y)
                ==⟨ inv (·-assoc (inv (ap (f ∘ g) p)) _ (ε y)) ⟩
              (inv (ap (f ∘ g) p) · ap (f ∘ g) p) · ε y
                ==⟨ ap (_· ε y) (·-linv (ap (λ z → f (g z)) p)) ⟩
              ε y
            ∎

  -- Half-adjointness implies equivalence.
  ishae-≃ : {f : A → B} → ishae f → A ≃ B
  ishae-≃ ishaef = _ , (ishae-contr _ ishaef)

open Halfadjoints public
module Quasiinverses {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where

  -- Definitions for quasi-inverses, left-inverses, right-inverses and
  -- biinverses.
  qinv : (A → B) → Type (ℓᵢ ⊔ ℓⱼ)
  qinv f = Σ (B → A) (λ g → ((f ∘ g) ∼ id) × ((g ∘ f) ∼ id))

  linv : (A → B) → Type (ℓᵢ ⊔ ℓⱼ)
  linv f = Σ (B → A) (λ g → (g ∘ f) ∼ id)

  rinv : (A → B) → Type (ℓᵢ ⊔ ℓⱼ)
  rinv f = Σ (B → A) λ g → (f ∘ g) ∼ id

  biinv : (A → B) → Type (ℓᵢ ⊔ ℓⱼ)
  biinv f = linv f × rinv f

  qinv-biinv : (f : A → B) → qinv f → biinv f
  qinv-biinv f (g , (u1 , u2)) = (g , u2) , (g , u1)

  biinv-qinv : (f : A → B) → biinv f → qinv f
  biinv-qinv f ((h , α) , (g , β)) = g , (β , δ)
    where
      γ1 : g ∼ ((h ∘ f) ∘ g)
      γ1 = rcomp-∼ g (h-sym (h ∘ f) id α)

      γ2 : ((h ∘ f) ∘ g) ∼ (h ∘ (f ∘ g))
      γ2 x = idp

      γ : g ∼ h
      γ = γ1 ● (γ2 ● (lcomp-∼ h β))

      δ : (g ∘ f) ∼ id
      δ = (rcomp-∼ f γ) ● α

  equiv-biinv : (f : A → B) → isContrMap f → biinv f
  equiv-biinv f contrf =
    (remap eq , rlmap-inverse-h eq) , (remap eq , lrmap-inverse-h eq)
    where
      eq : A ≃ B
      eq = f , contrf

  -- Quasiinverses are halfadjoint equivalences.
  qinv-ishae : {f : A → B} → qinv f → ishae f
  qinv-ishae {f} (g , (ε , η)) = record {
      g = g ;
      η = η ;
      ε = λ b → inv (ε (f (g b))) · ap f (η (g b)) · ε b ;
      τ = τ
    }
    where
      aux-lemma : (a : A) → ap f (η (g (f a))) · ε (f a) == ε (f (g (f a))) · ap f (η a)
      aux-lemma a =
        begin
          ap f (η ((g ∘ f) a)) · ε (f a)
            ==⟨ ap (λ u → ap f u · ε (f a)) (h-naturality-id η) ⟩
          ap f (ap (g ∘ f) (η a)) · ε (f a)
            ==⟨ ap (_· ε (f a)) (ap-comp (g ∘ f) f (η a)) ⟩
          ap (f ∘ (g ∘ f)) (η a) · ε (f a)
            ==⟨ inv (h-naturality (λ x → ε (f x)) (η a)) ⟩
          ε (f (g (f a))) · ap f (η a)
        ∎

      τ : (a : A) → ap f (η a) == (inv (ε (f (g (f a)))) · ap f (η (g (f a))) · ε (f a))
      τ a =
        begin
          ap f (η a)
            ==⟨ ap (_· ap f (η a)) (inv (·-linv (ε (f (g (f a)))))) ⟩
          inv (ε (f (g (f a)))) · ε (f (g (f a))) · ap f (η a)
            ==⟨ ·-assoc (inv (ε (f (g (f a))))) _ (ap f (η a)) ⟩
          inv (ε (f (g (f a)))) · (ε (f (g (f a))) · ap f (η a))
            ==⟨ ap (inv (ε (f (g (f a)))) ·_) (inv (aux-lemma a)) ⟩
          inv (ε (f (g (f a)))) · (ap f (η (g (f a))) · ε (f a))
            ==⟨ inv (·-assoc (inv (ε (f (g (f a))))) _ (ε (f a))) ⟩
          inv (ε (f (g (f a)))) · ap f (η (g (f a))) · ε (f a)
        ∎

  -- Quasiinverses create equivalences.
  qinv-≃ : (f : A → B) → qinv f → A ≃ B
  qinv-≃ f = ishae-≃ ∘ qinv-ishae

  ≃-qinv : A ≃ B → Σ (A → B) qinv
  ≃-qinv eq =
    lemap eq , (remap eq , (lrmap-inverse-h eq , rlmap-inverse-h eq))

  -- Half-adjoint equivalences are quasiinverses.
  ishae-qinv : {f : A → B} → ishae f → qinv f
  ishae-qinv {f} (hae g η ε τ) = g , (ε , η)

  ≃-ishae : (e : A ≃ B)→ ishae (lemap e)
  ≃-ishae e = qinv-ishae (π₂ (≃-qinv e))

open Quasiinverses public
module EquivalenceProperties where
  -- Composition of quasiinverses
  qinv-comp
    : ∀ {ℓ} {A B C : Type ℓ}
    → Σ (A → B) qinv
    → Σ (B → C) qinv
    ----------------
    → Σ (A → C) qinv

  qinv-comp (f , (if , (εf , ηf))) (g , (ig , (εg , ηg))) = (g ∘ f) , ((if ∘ ig) ,
     ( (λ x → ap g (εf (ig x)) · εg x)
     ,  λ x → ap if (ηg (f x)) · ηf x))
  -- Lemma.
  qinv-inv
    : ∀ {ℓ} {A B : Type ℓ}
    → Σ (A → B) qinv
    ----------------
    → Σ (B → A) qinv

  qinv-inv (f , (g , (ε , η))) = g , (f , (η , ε))
  idEqv
    : ∀ {ℓ} {A : Type ℓ}
    -------
    → A ≃ A

  idEqv = id , λ a → (a , refl a) , λ { (_ , idp) → refl (a , refl a) }

  -- Synonyms
  ≃-refl = idEqv
  A≃A    = idEqv
  -- Lemma.
  ≃-trans
    : ∀ {ℓ} {A B C : Type ℓ}
    → A ≃ B
    → B ≃ C
    -------
    → A ≃ C

  ≃-trans {A = A} {C = C} eq-f eq-g = qinv-≃ (π₁ qcomp) (π₂ qcomp)
   where
     qcomp : Σ (A → C) qinv
     qcomp = qinv-comp (≃-qinv eq-f) (≃-qinv eq-g)

  -- Synonyms
  compEqv = ≃-trans
  ≃-sym
    : ∀ {ℓ} {A B : Type ℓ}
    → A ≃ B
    -------
    → B ≃ A

  ≃-sym {ℓ} {A} {B} eq-f = qinv-≃ (π₁ qcinv) (π₂ qcinv)
   where
     qcinv : Σ (B → A) qinv
     qcinv = qinv-inv (≃-qinv eq-f)

  -- Synonyms
  invEqv = ≃-sym
  ≃-flip = ≃-sym
open EquivalenceProperties public
module SigmaEquivalence {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {P : A → Type ℓⱼ} where
  -- Lemma.
  pair=Equiv
    : {v w : Σ A P}
    → Σ (π₁ v == π₁ w) (λ p → tr (λ a → P a) p (π₂ v) == π₂ w) ≃ v == w

  pair=Equiv = qinv-≃ Σ-bycomponents (Σ-componentwise , HΣ₁ , HΣ₂)
    where
      HΣ₁ : Σ-bycomponents ∘ Σ-componentwise ∼ id
      HΣ₁ idp = idp

      HΣ₂ : Σ-componentwise ∘ Σ-bycomponents ∼ id
      HΣ₂ (idp , idp) = idp

  private
    f : {a₁ a₂ : A} {α : a₁ == a₂}{c₁ : P a₁} {c₂ : P a₂}
      → {β : a₁ == a₂}
      → {γ : transport P β c₁ == c₂}
      → ap π₁ (pair= (β , γ)) == α → β == α
    f {β = idp} {γ = idp} idp = idp

    g : {a₁ a₂ : A} {α : a₁ == a₂}{c₁ : P a₁} {c₂ : P a₂}
      → {β : a₁ == a₂}
      → {γ : transport P β c₁ == c₂}
      → β == α → ap π₁ (pair= (β , γ)) == α
    g {β = idp} {γ = idp} idp = idp

    f-g : {a₁ a₂ : A} {α : a₁ == a₂}{c₁ : P a₁} {c₂ : P a₂}
      → {β : a₁ == a₂}
      → {γ : transport P β c₁ == c₂}
      → f {α = α}{β = β}{γ} ∘ g {α = α}{β = β} ∼ id
    f-g {β = idp} {γ = idp} idp = idp

    g-f : {a₁ a₂ : A} {α : a₁ == a₂}{c₁ : P a₁} {c₂ : P a₂}
      → {β : a₁ == a₂}
      → {γ : transport P β c₁ == c₂}
      → g {α = α}{β = β}{γ} ∘ f {α = α}{β = β}{γ} ∼ id
    g-f {β = idp} {γ = idp} idp = idp
  -- Lemma
  ap-π₁-pair=Equiv
    : {a₁ a₂ : A} {c₁ : P a₁} {c₂ : P a₂}
    → (α : a₁ == a₂)
    → (γ : Σ (a₁ == a₂) (λ α' → transport P α' c₁ == c₂))
    → (ap π₁ (pair= γ) == α) ≃ (π₁ γ == α)

  ap-π₁-pair=Equiv {a₁ = a₁} α (β , γ) = qinv-≃ f (g , f-g , g-f)
open SigmaEquivalence public
module UnivalenceAxiom {ℓ} {A B : Type ℓ} where
  -- Fun.
  idtoeqv
    : A == B
    --------
    → A ≃ B

  idtoeqv p = qinv-≃
    (transport (λ X → X) p)
    (transport (λ X → X) (inv p) , (coe-inv-l p , coe-inv-r p))

  -- Synonyms
  ==-to-≃ = idtoeqv
  -- Axiom.
  postulate
    axiomUnivalence : isEquiv idtoeqv
  -- Lema.
  eqvUnivalence
    : (A == B) ≃ (A ≃ B)

  eqvUnivalence = idtoeqv , axiomUnivalence

  -- Synonyms
  ==-equiv-≃ = eqvUnivalence
  ==-≃-≃     = eqvUnivalence
  -- Fun.
  ua : A ≃ B → A == B
  ua = remap eqvUnivalence

  -- Synonyms
  ≃-to-== = ua
  -- Beta rule.
  ua-β
    : (α : A ≃ B)
    ----------------------
    → idtoeqv (ua α) == α

  ua-β eqv = lrmap-inverse eqvUnivalence
  -- Eta rule.
  ua-η
    : (p : A == B)
    ---------------------
    → ua (idtoeqv p) == p

  ua-η p = rlmap-inverse eqvUnivalence
open UnivalenceAxiom public
module Propositions where
  -- Def.
  isProp
    : ∀ {ℓ} (A : Type ℓ) → Type ℓ

  isProp A = ((x y : A) → x == y)
  -- The type of mere propositions
  hProp : ∀ {ℓ} → Type (lsuc ℓ)
  hProp {ℓ} = Σ (Type ℓ) isProp
open Propositions public
module Sets where

  isSet : ∀ {ℓ}  (A : Type ℓ) → Type ℓ
  isSet A = (x y : A) → isProp (x == y)

  -- The type of sets.
  hSet : ∀ {ℓ} → Type (lsuc ℓ)
  hSet {ℓ} = Σ (Type ℓ) isSet

open Sets public
module hLevelLemmas where
  -- Lemma. Propositions are Sets.
  propIsSet
    : ∀ {ℓ} {A : Type ℓ}
    → isProp A
    ----------
    → isSet A

  propIsSet {A = A} f a _ p q = lemma p · inv (lemma q)
    where
      triang : {y z : A} {p : y == z} → (f a y) · p == f a z
      triang {y}{p = idp} = inv (·-runit (f a y))

      lemma : {y z : A} (p : y == z) → p == ! (f a y) · (f a z)
      lemma {y} {z} p =
        begin
          p                       ==⟨ ap (_· p) (inv (·-linv (f a y))) ⟩
          ! (f a y) · f a y · p   ==⟨ ·-assoc (! (f a y)) (f a y) p ⟩
          ! (f a y) · (f a y · p) ==⟨ ap (! (f a y) ·_) triang ⟩
          ! (f a y) · (f a z)
        ∎

  -- Synonyms
  prop-is-set  = propIsSet
  prop→set     = propIsSet
  isProp-isSet = propIsSet
  -- Lemma. Propositions are propositions.
  propIsProp
    :  ∀ {ℓ}{A : Type ℓ}
    --------------------
    → isProp (isProp A)

  propIsProp {_}{A} =
    λ x y → funext (λ a →
              funext (λ b
                → propIsSet x a b (x a b) (y a b)))

  prop-is-prop-always = propIsProp
  prop-is-prop        = propIsProp
  prop→prop           = propIsProp
  isProp-isProp       = propIsProp
  -- Lemma.
  isProp-pi
    : ∀ {ℓᵢ ℓⱼ} → {A : Type ℓᵢ} → {B : A → Type ℓⱼ}
    → ((a : A) → isProp (B a))
    --------------------------
    → isProp ((a : A) → B a)

  isProp-pi props f g = funext λ a → props a (f a) (g a)

  pi-is-prop = isProp-pi
  Π-isProp   = isProp-pi
  piIsProp   = isProp-pi
  -- Lemma.
  ispropA-B
    : ∀ {ℓ} {A B : Type ℓ}
    →  isProp A → isProp B → (A ⇔ B)
    -------------------------------
    → A == B

  ispropA-B propA propB (fun f , fun g) =
    ua (qinv-≃ f (g , (λ x → propB _ _) , (λ x → propA _ _)))

  -- Synonyms
  props-⇔-to-== = ispropA-B
  -- Lemma.
  -- propEqvIsprop
  --   : ∀ {ℓ} {A B : Type ℓ}
  --   → isProp A → isProp B
  --   ---------------------
  --   → isProp (A == B)
  --
  -- propEqvIsprop {ℓ} {A} {B} x x₁ x₂ y = {!   !}
  -- Lemma.
  setIsProp
    : ∀ {ℓ} {A : Type ℓ}
    → isProp (isSet A)

  setIsProp {ℓ} {A} p₁ p₂ =
    funext (λ x →
      funext (λ y →
        funext (λ p →
          funext (λ q → propIsSet (p₂ x y) p q (p₁ x y p q) (p₂ x y p q)))))

  set→prop           = setIsProp
  set-is-prop-always = setIsProp
  -- Lemma.
  isProp-prod
    : ∀ {ℓᵢ ℓⱼ} → {A : Type ℓᵢ} → {B : Type ℓⱼ}
    → isProp A → isProp B
    ---------------------
    → isProp (A × B)

  isProp-prod p q x y = prodByComponents ((p _ _) , (q _ _))

  ispropA×B      = isProp-prod
  ×-isProp       = isProp-prod
  prop×prop→prop = isProp-prod
  -- Lemma.
  isSet-prod
    : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} → {B : Type ℓⱼ}
    → isSet A → isSet B
    -------------------
    → isSet (A × B)

  isSet-prod sa sb (a , b) (c , d) p q = begin
     p
      ==⟨ inv (prodByCompInverse p) ⟩
     prodByComponents (prodComponentwise p)
      ==⟨ ap prodByComponents (prodByComponents (sa a c _ _ , sb b d _ _)) ⟩
     prodByComponents (prodComponentwise q)
      ==⟨ prodByCompInverse q ⟩
     q
    ∎

  isSetA×B      = isSet-prod
  ×-isSet       = isSet-prod
  set×set→set   = isSet-prod
  -- Contractible types are Propositions.
  contrIsProp
    : ∀ {ℓ}  {A : Type ℓ}
    → isContr A
    -----------
    → isProp A

  contrIsProp (a , p) x y = ! (p x) · p y

  -- Synonyms
  isContr→isProp = contrIsProp
  -- Lemma 3.11.3 in HoTT-Book.
  isContrIsProp
    : ∀ {ℓ} {A : Type ℓ}
    --------------------
    → isProp (isContr A)

  isContrIsProp {_} {A} (a , p) (b , q) =
    Σ-bycomponents (inv (q a) , isProp-pi (AisSet b) _ q)
      where
        AisSet : isSet A
        AisSet = propIsSet (contrIsProp (a , p))

open hLevelLemmas public

module EquivalenceProp {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where

  -- Contractible maps are propositions
  isContrMapIsProp : (f : A → B) → isProp (isContrMap f)
  isContrMapIsProp f = isProp-pi λ a → isContrIsProp

  isEquivIsProp : (f : A → B) → isProp (isEquiv f)
  isEquivIsProp = isContrMapIsProp

  -- Equality of same-morphism equivalences
  sameEqv : {α β : A ≃ B} → π₁ α == π₁ β → α == β
  sameEqv {(f , σ)} {(g , τ)} p = Σ-bycomponents (p , (isEquivIsProp g _ τ))

  -- Equivalences preserve propositions
  isProp-≃ : (A ≃ B) → isProp A → isProp B
  isProp-≃ eq prop x y =
    begin
      x                       ==⟨ inv (lrmap-inverse eq) ⟩
      lemap eq ((remap eq) x) ==⟨ ap (λ u → lemap eq u) (prop _ _) ⟩
      lemap eq ((remap eq) y) ==⟨ lrmap-inverse eq ⟩
      y
    ∎
open EquivalenceProp public
-- Lemma.
≃-trans-inv
  : ∀ {ℓ} {A B : Type ℓ}
  → (α : A ≃ B)
  -----------------------------
  → ≃-trans α (≃-flip α) == A≃A

≃-trans-inv α = sameEqv (
 begin
   π₁ (≃-trans α (≃-sym α)) ==⟨ refl _ ⟩
   π₁ (≃-sym α) ∘ π₁ α     ==⟨ funext (rlmap-inverse-h α) ⟩
   id
 ∎)
module EquivalenceReasoning where

  infixr 2 _≃⟨⟩_
  _≃⟨⟩_ : ∀ {ℓ} (A {B} : Type ℓ) → A ≃ B → A ≃ B
  _ ≃⟨⟩ e = e

  infixr 2 _≃⟨_⟩_
  _≃⟨_⟩_ : ∀ {ℓ} (A : Type ℓ) {B C : Type ℓ} → A ≃ B → B ≃ C → A ≃ C
  _ ≃⟨ e₁ ⟩ e₂ = ≃-trans e₁ e₂
  --
  infix  3 _≃∎
  _≃∎ :  ∀ {ℓ} (A : Type ℓ) → A ≃ A
  _≃∎ = λ A → idEqv {A = A}

  infix  1 begin≃_
  begin≃_ : ∀ {ℓ} {A B : Type ℓ} → A ≃ B → A ≃ B
  begin≃_ e = e

open EquivalenceReasoning public
module UnivalenceLemmas {ℓ} where
  ua-id : {A : Type ℓ} → ua idEqv == refl A
  ua-id {A} =
    begin
      ua idEqv              ==⟨ ap ua (sameEqv (refl id)) ⟩
      ua (idtoeqv (refl A)) ==⟨ ua-η (refl A) ⟩
      refl A
    ∎

    -- The composition of equivalences is preserved into composition
    -- of equalities.
  postulate
    ua-comp
      : {A B C : Type ℓ}
      → (α : A ≃ B)
      → (β : B ≃ C)
      ---------------------------------
      → ua (≃-trans α β) == ua α · ua β

    -- ua-comp α β =
    --   begin
    --     ua (≃-trans α β)                               ==⟨ ap (λ x → ua (≃-trans x β)) (inv (ua-β α)) ⟩
    --     ua (≃-trans (idtoeqv (ua α)) β)                ==⟨ ap (λ x → ua (≃-trans (idtoeqv (ua α)) x))
    --                                                        (inv (ua-β β)) ⟩
    --     ua (≃-trans (idtoeqv (ua α)) (idtoeqv (ua β))) ==⟨ ap ua lemma ⟩
    --     ua (idtoeqv (ua α · ua β))                     ==⟨ ua-η (ua α · ua β) ⟩
    --     ua α · ua β
    --   ∎
    --   where
    --     lemma : ≃-trans (idtoeqv (ua α)) (idtoeqv (ua β)) == idtoeqv (ua α · ua β)
    --     lemma = sameEqv (
    --       begin
    --         π₁ (idtoeqv (ua β)) ∘ π₁ (idtoeqv (ua α))                 ==⟨ refl _ ⟩
    --         (transport (λ x → x) (ua β)) ∘ (transport (λ x → x) (ua α)) ==⟨ transport-comp (ua α) (ua β) ⟩
    --         transport (λ x → x) (ua α · ua β)                           ==⟨ refl _ ⟩
    --         π₁ (idtoeqv (ua α · ua β))
    --       ∎)
  ua-inv-r
    : {A B : Type ℓ}
    → (α : A ≃ B)
    → ua α · ua (≃-sym α) == refl A
  ua-inv-r α =
    begin
      ua α · ua (≃-sym α)      ==⟨ inv (ua-comp α (≃-sym α)) ⟩
      ua (≃-trans α (≃-sym α)) ==⟨ ap ua (≃-trans-inv α) ⟩
      ua idEqv                  ==⟨ ua-id ⟩
      refl _
    ∎
  postulate
    ua-inv : {A B : Type ℓ} → (α : A ≃ B) → ua (≃-sym α) == inv (ua α)
    -- ua-inv α =
    --   begin
    --     ua (≃-sym α)                       ==⟨ ap (_· ua (≃-sym α)) (inv (·-linv (ua α))) ⟩
    --     inv (ua α) · ua α · ua (≃-sym α)   ==⟨ ·-assoc (inv (ua α)) _ _ ⟩
    --     inv (ua α) · (ua α · ua (≃-sym α)) ==⟨ ap (inv (ua α) ·_) (ua-inv-r α) ⟩
    --     inv (ua α) · refl _                 ==⟨ inv (·-runit (inv ((ua α)))) ⟩
    --     inv (ua α)
    --   ∎
open UnivalenceLemmas public
module TransportUA where

  transport-family-ap
    : ∀ {ℓ} {A : Type ℓ}
    → (B : A → Type ℓ)
    → {x y : A}
    → (p : x == y)
    → (u : B x)
    ---------------------------------------------------
    → transport B p u == transport (λ X → X) (ap B p) u
  transport-family-ap B idp u = idp

  transport-family-idtoeqv
    : ∀ {ℓ} {A : Type ℓ}
    → (B : A → Type ℓ)
    → {x y : A}
    → (p : x == y)
    → (u : B x)
    ---------------------------------------------------
    → transport B p u == fun≃ (idtoeqv (ap B p)) u
  transport-family-idtoeqv B idp u = idp

  transport-ua
    : ∀ {ℓ} {A : Type ℓ}
    → (B : A → Type ℓ)
    → {x y : A}
    → (p : x == y)
    → (e : B x ≃ B y)
    → ap B p == ua e
    -----------------
    → (u : B x) → transport B p u == (fun≃ e) u
  transport-ua B idp e q u =
    begin
      transport B idp u
        ==⟨ transport-family-idtoeqv B idp u ⟩
      fun≃ (idtoeqv (ap B idp)) u
        ==⟨ ap (λ r → fun≃ (idtoeqv r) u) q ⟩
      fun≃ (idtoeqv (ua e)) u
        ==⟨ ap (λ r → fun≃ r u) (ua-β e) ⟩
      fun≃ e u
    ∎


  funext-transport-ua
    : ∀ {ℓ} {A : Type ℓ}
    → (B : A → Type ℓ)
    → {x y : A}
    → (p : x == y)
    → (e : B x ≃ B y)
    → ap B p == ua e
    -----------------
    → transport B p == (fun≃ e)
  funext-transport-ua B p e x₁ = funext (transport-ua B p e x₁)

  postulate
    ua-coe
      : ∀ {ℓ} {A B : Type ℓ}
      → (α : A ≃ B)
      → (∀ x → (coe (ua α) x) == ((α ∙) x))
  -- ua-coe α x =
  --   begin
  --     (coe (ua α) x)
  --       ==⟨ idp ⟩
  --     transport (λ X → X) (ua α) x
  --       ==⟨ {!   !} ⟩
  --     {!   !}
  --       ==⟨ {!   !} ⟩
  --     {!   !}
open TransportUA public
funext-transport-dfun-bezem
  : ∀ {ℓᵢ ℓⱼ}{X : Type ℓᵢ}{A : X → Type ℓⱼ}{B : (x : X) → A x → Type ℓⱼ} {x y : X}
  → (p : x == y)
  → (f : (a : A x) → B x a)
  → (g : (a : A y) → B y a)
  → (a : A y)
  ------------------------------------------------------------------------------------
  → (tr (λ x → (a : A x) → B x a) p f) a == g a
  ≃  tr (λ w → B (π₁ w) (π₂ w)) (pair= (p , transport-inv p)) (f (((! p) ✶) a)) == g a

funext-transport-dfun-bezem idp f g a = idEqv
funext-transport-dfun-bezem-l
  : ∀ {ℓᵢ ℓⱼ}{X : Type ℓᵢ}{A : X → Type ℓⱼ}{B : (x : X) → A x → Type ℓⱼ} {x y : X}
  → (p : x == y)
  → (f : (a : A x) → B x a)
  → (g : (a : A y) → B y a)
  → (a : A y)
  → (tr (λ x → (a : A x) → B x a) p f) a == g a
  ------------------------------------------------------------------------------------
  →  tr (λ w → B (π₁ w) (π₂ w)) (pair= (p , transport-inv p)) (f (((! p) ✶) a)) == g a

funext-transport-dfun-bezem-l p f g a x₁ = lemap (funext-transport-dfun-bezem p f g a) x₁
funext-transport-dfun-bezem-r
  : ∀ {ℓᵢ ℓⱼ}{X : Type ℓᵢ}{A : X → Type ℓⱼ}{B : (x : X) → A x → Type ℓⱼ} {x y : X}
  → (p : x == y)
  → (f : (a : A x) → B x a)
  → (g : (a : A y) → B y a)
  → (a : A y)
  →  tr (λ w → B (π₁ w) (π₂ w)) (pair= (p , transport-inv p)) (f (((! p) ✶) a)) == g a
  ------------------------------------------------------------------------------------
  → (tr (λ x → (a : A x) → B x a) p f) a == g a

funext-transport-dfun-bezem-r p f g a x₁ = remap (funext-transport-dfun-bezem p f g a) x₁
module Truncation where

  private
    -- Higher inductive type, defined with equalities between any two
    -- members.
    data !∥_∥ {ℓ} (A : Type ℓ) : Type ℓ where
      !∣_∣ : A → !∥ A ∥

  ∥_∥ : ∀ {ℓ} (A : Type ℓ) → Type ℓ
  ∥ A ∥ = !∥ A ∥

  ∣_∣ : ∀ {ℓ} {X : Type ℓ} → X → ∥ X ∥
  ∣ x ∣ = !∣ x ∣

  -- Any two elements of the truncated type are equal
  postulate
    trunc : ∀ {ℓ} {A : Type ℓ} → isProp ∥ A ∥

  -- Recursion principle
  trunc-rec : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {P : Type ℓⱼ}
            → isProp P
            → (A → P)
            ---------
            → ∥ A ∥ → P
  trunc-rec _ f !∣ x ∣ = f x
open Truncation public
module SetTruncation where

  private
    -- Higher inductive type
    data !∥_∥₀ {ℓ} (A : Type ℓ) : Type ℓ where
      !∣_∣₀ : A → !∥ A ∥₀

  ∥_∥₀ : ∀ {ℓ} (A : Type ℓ) → Type ℓ
  ∥ A ∥₀ = !∥ A ∥₀

  ∣_∣₀ : ∀ {ℓ} {X : Type ℓ} → X → ∥ X ∥₀
  ∣ x ∣₀ = !∣ x ∣₀

  -- Any two equalities on the truncated type are equal
  postulate
    strunc : ∀ {ℓ} {A : Type ℓ} → isSet ∥ A ∥₀

  -- Recursion principle
  strunc-rec : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {P : Type ℓⱼ} → isSet P → (A → P) → ∥ A ∥₀ → P
  strunc-rec _ f !∣ x ∣₀ = f x

  -- Induction principle
  strunc-ind : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : ∥ A ∥₀ → Type ℓⱼ} → ((a : ∥ A ∥₀) → isSet (B a))
             → (g : (a : A) → B ∣ a ∣₀) → (a : ∥ A ∥₀) → B a
  strunc-ind _ g !∣ x ∣₀ = g x
module Quotients where

  record QRel {ℓ} (A : Type ℓ) : Type (lsuc ℓ) where
    field
      R : A → A → Type ℓ
      Aset : isSet A
      Rprop : (a b : A) → isProp (R a b)
  open QRel {{...}} public

  private
    -- Higher inductive type
    data _!/_ {ℓ} (A : Type ℓ) (r : QRel A) : Type (lsuc ℓ) where
      ![_] : A → (A !/ r)

  _/_ : ∀ {ℓ} (A : Type ℓ) (r : QRel A) → Type (lsuc ℓ)
  A / r = (A !/ r)

  [_] : ∀ {ℓ} {A : Type ℓ} → A → {r : QRel A} → (A / r)
  [ a ] = ![ a ]

  -- Equalities induced by the relation
  postulate
    Req
      : ∀ {ℓ} {A : Type ℓ} {r : QRel A}
      → {a b : A}
      → R {{r}} a b
      --------------------
      → [ a ] {r} == [ b ]

  -- The quotient of a set is again a set
  postulate
    Rtrunc
      : ∀ {ℓ} {A : Type ℓ} {r : QRel A}
      ---------------
      → isSet (A / r)

  -- Recursion principle
  QRel-rec : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {r : QRel A} {B : Type ℓⱼ}
            → (f : A → B) → ((x y : A) → R {{r}} x y → f x == f y) → A / r → B
  QRel-rec f p ![ x ] = f x

  -- Induction principle
  QRel-ind : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {r : QRel A} {B : A / r → Type ℓⱼ}
            → (f : ((a : A) → B [ a ]))
            → ((x y : A) → (o : R {{r}} x y) → (transport B (Req o) (f x)) == f y)
            → (z : A / r) → B z
  QRel-ind f p ![ x ] = f x

  -- Recursion in two arguments
  QRel-rec-bi : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {r : QRel A} {B : Type ℓⱼ}
              → (f : A → A → B) → ((x y z t : A) → R {{r}} x y → R {{r}} z t → f x z == f y t)
              → A / r → A / r → B
  QRel-rec-bi f p ![ x ] ![ y ] = f x y


  Qrel-prod : ∀ {ℓᵢ}{A : Type ℓᵢ} (r : QRel A) → QRel (A × A)
  Qrel-prod r = record { R = λ { (a , b) (c , d) → (R {{r}} a c) × (R {{r}} b d) }
                       ; Aset = isSet-prod (Aset {{r}}) (Aset {{r}})
                       ; Rprop = λ { (x , y) (z , w) → isProp-prod (Rprop {{r}} x z) (Rprop {{r}} y w)} }
module Relation where

  record Rel {ℓ} (A : Type ℓ) : Type (lsuc ℓ) where
    field
      R     : A → A → Type ℓ
      Rprop : (a b : A) → isProp (R a b)
  open Rel {{...}} public

open Relation public
module Hedberg {ℓ} where

  module HedbergLemmas (A : Type ℓ) where

    -- A set is a type satisfiying axiom K.
    axiomKisSet : ((a : A) → (p : a == a) → p == refl a) → isSet A
    axiomKisSet k x _ p idp = k x p

    -- Lemma: a reflexive relation on X implying the identity proves
    -- that X is a set.
    reflRelIsSet :  (r : Rel A) →
      ((x y : A) → R {{r}} x y → x == y) →
      (ρ : (a : A) → R {{r}} a a) →
      isSet A
    reflRelIsSet r f ρ x .x p idp = lemma p
      where
        lemma2 : {a : A} (p : a == a) → (o : R {{r}} a a) →
          transport (λ x → a == x) p (f a a o) == f a a (transport (R {{r}} a) p o)
        lemma2 {a} p = funext-transport-l p (f a a) (f a a) (apd (f a) p)

        lemma3 : {a : A} (p : a == a) →
          (f a a (ρ a)) · p == (f a a (ρ a))
        lemma3 {a} p = inv (transport-concat-r p _) · lemma2 p (ρ a) ·
                       ap (f a a) (Rprop {{r}} a a _ (ρ a))

        lemma : {a : A} (p : a == a) → p == refl a
        lemma {a} p = ·-cancellation ((f a a (ρ a))) p (lemma3 p)

    -- Lemma: if a type is decidable, then ¬¬A is actually A.
    lemDoubleNeg : (A + ¬ A) → (¬ (¬ A) → A)
    lemDoubleNeg (inl x) _ = x
    lemDoubleNeg (inr f) n = exfalso (n f)

  open HedbergLemmas public

  -- Hedberg's theorem. A type with decidable equality is a set.
  hedberg : {A : Type ℓ} → ((a b : A) → (a == b) + ¬ (a == b)) → isSet A
  hedberg {A} f = reflRelIsSet A
                (record { R = λ a b → ¬ (¬ (a == b)) ; Rprop = isPropNeg })
                doubleNegEq (λ a z → z (refl a))
    where
      doubleNegEq : (a b : A) → ¬ (¬ (a == b)) → (a == b)
      doubleNegEq a b = lemDoubleNeg (a == b) (f a b)

      isPropNeg : (a b : A) → isProp (¬ (¬ (a == b)))
      isPropNeg a b x y = funext λ u → exfalso (x u)

open Hedberg public
module Monoids {ℓ} where

  record Monoid : Type (lsuc ℓ) where
    field
      -- Operations of a monoid
      G : Type ℓ
      GisSet : isSet G
      _<>_ : G → G → G  -- Multiplication function
      e : G             -- Unit element

      -- Axioms of a monoid
      lunit : (x : G) → (e <> x) == x
      runit : (x : G) → (x <> e) == x
      assoc : (x y z : G) → (x <> (y <> z)) == ((x <> y) <> z)
open Monoids
module Groups where
  record GroupStructure {ℓ} (M : Type ℓ) : Type ℓ where
    constructor group-structure
    field
      -- A group is a monoid
      _*_   : M → M → M
      e     : M
      lunit : ∀ x → (e * x) == x
      runit : ∀ x → (x * e) == x
      assoc : ∀ x y z → (x * (y * z)) == ((x * y) * z)

      -- With inverses
      ginv : M → M
      glinv : ∀ g → (g * ginv g) == e
      grinv : ∀ g → (ginv g * g) == e

  record Group {ℓ} : Type (lsuc ℓ) where
    constructor group
    field
      M : Type ℓ
      str : GroupStructure M
  open Group {{...}} public
open Groups
module Naturals where

  -- Addition of natural numbers
  plus : ℕ → ℕ → ℕ
  plus zero y = y
  plus (succ x) y = succ (plus x y)

  infixl 60 _+ₙ_
  _+ₙ_ : ℕ → ℕ → ℕ
  _+ₙ_ = plus

  -- Lemmas about addition
  plus-lunit : (n : ℕ) → zero +ₙ n == n
  plus-lunit n = refl n

  plus-runit : (n : ℕ) → n +ₙ zero == n
  plus-runit zero = refl zero
  plus-runit (succ n) = ap succ (plus-runit n)

  plus-succ : (n m : ℕ) → succ (n +ₙ m) == (n +ₙ (succ m))
  plus-succ zero     m = refl (succ m)
  plus-succ (succ n) m = ap succ (plus-succ n m)

  plus-succ-rs : (n m o p : ℕ) → n +ₙ m == o +ₙ p → n +ₙ (succ m) == o +ₙ (succ p)
  plus-succ-rs n m o p α = inv (plus-succ n m) · ap succ α · (plus-succ o p)

  -- Commutativity
  plus-comm : (n m : ℕ) → n +ₙ m == m +ₙ n
  plus-comm zero     m = inv (plus-runit m)
  plus-comm (succ n) m = ap succ (plus-comm n m) · plus-succ m n

  -- Associativity
  plus-assoc : (n m p : ℕ) → n +ₙ (m +ₙ p) == (n +ₙ m) +ₙ p
  plus-assoc zero     m p = refl (m +ₙ p)
  plus-assoc (succ n) m p = ap succ (plus-assoc n m p)


  -- Decidable equality
  -- Encode-decode technique for natural numbers
  private
    code : ℕ → ℕ → Type₀
    code 0        0        = ⊤
    code 0        (succ m) = ⊥
    code (succ n) 0        = ⊥
    code (succ n) (succ m) = code n m

  crefl : (n : ℕ) → code n n
  crefl zero     = ★
  crefl (succ n) = crefl n

  private
    encode : (n m : ℕ) → (n == m) → code n m
    encode n m p = transport (code n) p (crefl n)

    decode : (n m : ℕ) → code n m → n == m
    decode zero zero c = refl zero
    decode zero (succ m) ()
    decode (succ n) zero ()
    decode (succ n) (succ m) c = ap succ (decode n m c)

  zero-not-succ : (n : ℕ) → ¬ (succ n == zero)
  zero-not-succ n = encode (succ n) 0

  -- The successor function is injective
  succ-inj : {n m : ℕ} → (succ n == succ m) → n == m
  succ-inj {n} {m} p = decode n m (encode (succ n) (succ m) p)

  +-inj : (k : ℕ) {n m : ℕ} → (k +ₙ n == k +ₙ m) → n == m
  +-inj zero   p = p
  +-inj (succ k) p = +-inj k (succ-inj p)

  nat-decEq : decEq ℕ
  nat-decEq zero zero = inl (refl zero)
  nat-decEq zero (succ m) = inr (λ ())
  nat-decEq (succ n) zero = inr (λ ())
  nat-decEq (succ n) (succ m) with (nat-decEq n m)
  nat-decEq (succ n) (succ m) | inl p = inl (ap succ p)
  nat-decEq (succ n) (succ m) | inr f = inr λ p → f (succ-inj p)

  nat-isSet : isSet ℕ
  nat-isSet = hedberg nat-decEq

  -- Naturals form a monoid with addition
  ℕ-plus-monoid : Monoid
  ℕ-plus-monoid = record
    { G = ℕ
    ; GisSet = nat-isSet
    ; _<>_ = plus
    ; e = zero
    ; lunit = plus-lunit
    ; runit = plus-runit
    ; assoc = plus-assoc
    }

  -- Ordering
  _<ₙ_ : ℕ → ℕ → Type₀
  n <ₙ m = Σ ℕ (λ k → n +ₙ succ k == m)

  <-isProp : (n m : ℕ) → isProp (n <ₙ m)
  <-isProp n m (k1 , p1) (k2 , p2) = Σ-bycomponents (succ-inj (+-inj n (p1 · inv p2)) , nat-isSet _ _ _ _)

open Naturals public
module Integers where

  data ℤ : Type₀ where
    zer : ℤ
    pos : ℕ → ℤ
    neg : ℕ → ℤ

  -- Inclusion of the natural numbers into the integers
  NtoZ : ℕ → ℤ
  NtoZ zero     = zer
  NtoZ (succ n) = pos n

  -- Successor function
  zsucc : ℤ → ℤ
  zsucc zer            = pos 0
  zsucc (pos x)        = pos (succ x)
  zsucc (neg zero)     = zer
  zsucc (neg (succ x)) = neg x

  -- Predecessor function
  zpred : ℤ → ℤ
  zpred zer            = neg 0
  zpred (pos zero)     = zer
  zpred (pos (succ x)) = pos x
  zpred (neg x)        = neg (succ x)

  -- Successor and predecessor
  zsuccpred-id : (n : ℤ) → zsucc (zpred n) == n
  zsuccpred-id zer            = refl _
  zsuccpred-id (pos zero)     = refl _
  zsuccpred-id (pos (succ n)) = refl _
  zsuccpred-id (neg n)        = refl _

  zpredsucc-id : (n : ℤ) → zpred (zsucc n) == n
  zpredsucc-id zer            = refl _
  zpredsucc-id (pos n)        = refl _
  zpredsucc-id (neg zero)     = refl _
  zpredsucc-id (neg (succ n)) = refl _

  zpredsucc-succpred : (n : ℤ) → zpred (zsucc n) == zsucc (zpred n)
  zpredsucc-succpred zer = refl zer
  zpredsucc-succpred (pos zero) = refl (pos zero)
  zpredsucc-succpred (pos (succ x)) = refl (pos (succ x))
  zpredsucc-succpred (neg zero) = refl (neg zero)
  zpredsucc-succpred (neg (succ x)) = refl (neg (succ x))

  zsuccpred-predsucc : (n : ℤ) → zsucc (zpred n) == zpred (zsucc n)
  zsuccpred-predsucc n = inv (zpredsucc-succpred n)

  -- Equivalence given by successor and predecessor
  zequiv-succ : ℤ ≃ ℤ
  zequiv-succ = qinv-≃ zsucc (zpred , (zsuccpred-id , zpredsucc-id))

  -- Negation
  - : ℤ → ℤ
  - zer     = zer
  - (pos x) = neg x
  - (neg x) = pos x

  double- : (z : ℤ) → - (- z) == z
  double- zer = refl _
  double- (pos x) = refl _
  double- (neg x) = refl _

  zequiv- : ℤ ≃ ℤ
  zequiv- = qinv-≃ - (- , (double- , double-))

  -- Addition on integers
  infixl 60 _+ᶻ_
  _+ᶻ_ : ℤ → ℤ → ℤ
  zer +ᶻ m = m
  pos zero +ᶻ m = zsucc m
  pos (succ x) +ᶻ m = zsucc (pos x +ᶻ m)
  neg zero +ᶻ m = zpred m
  neg (succ x) +ᶻ m = zpred (neg x +ᶻ m)

  -- Lemmas on addition
  +ᶻ-lunit : (n : ℤ) → n == n +ᶻ zer
  +ᶻ-lunit zer            = refl _
  +ᶻ-lunit (pos zero)     = refl _
  +ᶻ-lunit (pos (succ x)) = ap zsucc (+ᶻ-lunit (pos x))
  +ᶻ-lunit (neg zero)     = refl _
  +ᶻ-lunit (neg (succ x)) = ap zpred (+ᶻ-lunit (neg x))


  +ᶻ-unit-zsucc : (n : ℤ) → zsucc n == (n +ᶻ pos zero)
  +ᶻ-unit-zsucc zer = refl _
  +ᶻ-unit-zsucc (pos zero) = refl _
  +ᶻ-unit-zsucc (pos (succ x)) = ap zsucc (+ᶻ-unit-zsucc (pos x))
  +ᶻ-unit-zsucc (neg zero) = refl _
  +ᶻ-unit-zsucc (neg (succ x)) = inv (zpredsucc-id (neg x)) · ap zpred (+ᶻ-unit-zsucc (neg x))

  +ᶻ-unit-zpred : (n : ℤ) → zpred n == (n +ᶻ neg zero)
  +ᶻ-unit-zpred zer = refl _
  +ᶻ-unit-zpred (pos zero) = refl zer
  +ᶻ-unit-zpred (pos (succ x)) = inv (zsuccpred-id (pos x)) · ap zsucc (+ᶻ-unit-zpred (pos x))
  +ᶻ-unit-zpred (neg zero) = refl _
  +ᶻ-unit-zpred (neg (succ x)) = ap zpred (+ᶻ-unit-zpred (neg x))


  +ᶻ-pos-zsucc : (n : ℤ) → (x : ℕ) → zsucc (n +ᶻ pos x) == n +ᶻ pos (succ x)
  +ᶻ-pos-zsucc zer x = refl _
  +ᶻ-pos-zsucc (pos zero) x = refl _
  +ᶻ-pos-zsucc (pos (succ n)) x = ap zsucc (+ᶻ-pos-zsucc (pos n) x)
  +ᶻ-pos-zsucc (neg zero) x = zsuccpred-id (pos x)
  +ᶻ-pos-zsucc (neg (succ n)) x = zsuccpred-predsucc (neg n +ᶻ pos x) · ap zpred (+ᶻ-pos-zsucc (neg n) x)

  +ᶻ-neg-zpred : (n : ℤ) → (x : ℕ) → zpred (n +ᶻ neg x) == n +ᶻ neg (succ x)
  +ᶻ-neg-zpred zer x = refl _
  +ᶻ-neg-zpred (pos zero) x = zpredsucc-id (neg x)
  +ᶻ-neg-zpred (pos (succ n)) x = zpredsucc-succpred (pos n +ᶻ neg x) · ap zsucc (+ᶻ-neg-zpred (pos n) x)
  +ᶻ-neg-zpred (neg zero) x = refl _
  +ᶻ-neg-zpred (neg (succ n)) x = ap zpred (+ᶻ-neg-zpred (neg n) x)

  +ᶻ-comm : (n m : ℤ) → n +ᶻ m == m +ᶻ n
  +ᶻ-comm zer m = +ᶻ-lunit m
  +ᶻ-comm (pos zero) m = +ᶻ-unit-zsucc m
  +ᶻ-comm (pos (succ x)) m = ap zsucc (+ᶻ-comm (pos x) m) · +ᶻ-pos-zsucc m x
  +ᶻ-comm (neg zero) m = +ᶻ-unit-zpred m
  +ᶻ-comm (neg (succ x)) m = ap zpred (+ᶻ-comm (neg x) m) · +ᶻ-neg-zpred m x



  -- Decidable equality
  pos-inj : {n m : ℕ} → pos n == pos m → n == m
  pos-inj {n} {.n} idp = refl n

  neg-inj : {n m : ℕ} → neg n == neg m → n == m
  neg-inj {n} {.n} idp = refl n

  z-decEq : decEq ℤ
  z-decEq zer zer = inl (refl zer)
  z-decEq zer (pos x) = inr (λ ())
  z-decEq zer (neg x) = inr (λ ())
  z-decEq (pos x) zer = inr (λ ())
  z-decEq (pos n) (pos m) with (nat-decEq n m)
  z-decEq (pos n) (pos m) | inl p = inl (ap pos p)
  z-decEq (pos n) (pos m) | inr f = inr (f ∘ pos-inj)
  z-decEq (pos n) (neg m) = inr (λ ())
  z-decEq (neg n) zer = inr (λ ())
  z-decEq (neg n) (pos x₁) = inr (λ ())
  z-decEq (neg n) (neg m) with (nat-decEq n m)
  z-decEq (neg n) (neg m) | inl p = inl (ap neg p)
  z-decEq (neg n) (neg m) | inr f = inr (f ∘ neg-inj)

  z-isSet : isSet ℤ
  z-isSet = hedberg z-decEq


  -- Multiplication
  infixl 60 _*ᶻ_
  _*ᶻ_ : ℤ → ℤ → ℤ
  zer *ᶻ m = zer
  pos zero *ᶻ m = m
  pos (succ x) *ᶻ m = (pos x *ᶻ m) +ᶻ m
  neg zero *ᶻ m = - m
  neg (succ x) *ᶻ m = (neg x *ᶻ m) +ᶻ (- m)


  -- Ordering
  _<ᶻ_ : ℤ → ℤ → Type₀
  zer <ᶻ zer = ⊥
  zer <ᶻ pos x = ⊤
  zer <ᶻ neg x = ⊥
  pos x <ᶻ zer = ⊥
  pos x <ᶻ pos y = x <ₙ y
  pos x <ᶻ neg y = ⊥
  neg x <ᶻ zer = ⊤
  neg x <ᶻ pos y = ⊤
  neg x <ᶻ neg y = y <ₙ x

open Integers
module IntegerAction {ℓ} {M : Type ℓ} (grpst : GroupStructure M) where

  open GroupStructure grpst

    -- Integers acting on a group structure M.
  z-act : ℤ → M → M
  z-act zer            m = e
  z-act (pos zero)     m = m
  z-act (pos (succ x)) m = z-act (pos x) m * m
  z-act (neg zero)     m = ginv m
  z-act (neg (succ x)) m = (z-act (neg x) m) * ginv m


  -- Lemmas on how integers act on a group.
  zsucc-act : ∀ n a → z-act (zsucc n) a == (z-act n a * a)
  zsucc-act zer a = inv (lunit a)
  zsucc-act (pos x) a = refl _
  zsucc-act (neg zero) a = inv (grinv a)
  zsucc-act (neg (succ n)) a =
    begin
      z-act (neg n) a                   ==⟨ inv (runit (z-act (neg n) a)) ⟩
      z-act (neg n) a * e               ==⟨ ap (λ section → _*_ (z-act (neg n) a) section) (inv (grinv a)) ⟩
      z-act (neg n) a * (ginv a * a)    ==⟨ assoc (z-act (neg n) a) (ginv a) a ⟩
      ((z-act (neg n) a * ginv a) * a)
    ∎

  zpred-act : ∀ n a → z-act (zpred n) a == (z-act n a * ginv a)
  zpred-act zer a = inv (lunit (ginv a))
  zpred-act (pos zero) a = inv (glinv a)
  zpred-act (pos (succ x)) a =
    begin
      z-act (zpred (pos (succ x))) a   ==⟨ refl _ ⟩
      z-act (pos x) a                  ==⟨ inv (runit _) ⟩
      z-act (pos x) a * e              ==⟨ ap (λ section → _*_ (z-act (pos x) a) section) (inv (glinv a)) ⟩
      z-act (pos x) a * (a * ginv a)   ==⟨ assoc (z-act (pos x) a) a (ginv a) ⟩
      (z-act (pos x) a * a) * ginv a   ==⟨ refl _ ⟩
      z-act (pos (succ x)) a * ginv a
    ∎
  zpred-act (neg x) a = refl _


  act-zsucc : ∀ n a → z-act (zsucc n) a == (a * z-act n a)
  act-zsucc zer a = inv (runit a)
  act-zsucc (pos zero) a = refl _
  act-zsucc (pos (succ x)) a =
    begin
       ((z-act (pos x) a * a) * a) ==⟨ ap (λ u → u * a) (act-zsucc (pos x) a) ⟩
       ((a * z-act (pos x) a) * a) ==⟨ inv (assoc a (z-act (pos x) a) a) ⟩
       (a * (z-act (pos x) a * a))
    ∎
  act-zsucc (neg zero) a = inv (glinv a)
  act-zsucc (neg (succ x)) a =
    begin
       z-act (neg x) a                    ==⟨ inv (runit (z-act (neg x) a)) ⟩
       (z-act (neg x) a) * e              ==⟨ ap (λ section → _*_ (z-act (neg x) a) section) (inv (glinv a)) ⟩
       (z-act (neg x) a) * (a * ginv a)   ==⟨ assoc (z-act (neg x) a) a (ginv a) ⟩
       ((z-act (neg x) a) * a) * ginv a   ==⟨ ap (λ s → s * (ginv a)) (inv (zsucc-act (neg x) a)) ⟩
       (z-act (zsucc (neg x)) a) * ginv a ==⟨ ap (λ s → s * (ginv a)) (act-zsucc (neg x) a) ⟩
       (a * (z-act (neg x) a)) * ginv a   ==⟨ inv (assoc a (z-act (neg x) a) (ginv a)) ⟩
       (a * (z-act (neg x) a * ginv a))
    ∎

  act-zpred : ∀ n a → z-act (zpred n) a == (ginv a * z-act n a)
  act-zpred n a =
    begin
      z-act (zpred n) a  ==⟨ inv (lunit (z-act (zpred n) a)) ⟩
      e * z-act (zpred n) a  ==⟨ ap (λ section → _*_ section (z-act (zpred n) a)) (inv (grinv a)) ⟩
      (ginv a * a) * z-act (zpred n) a  ==⟨ inv (assoc _ a _) ⟩
      ginv a * (a * z-act (zpred n) a)  ==⟨ ap (λ section → _*_ (ginv a) section) (inv (act-zsucc (zpred n) a)) ⟩
      ginv a * z-act (zsucc (zpred n)) a ==⟨ ap (λ u → (ginv a * (z-act u a))) (zsuccpred-id n) ⟩
      ginv a * z-act n a
    ∎

  z-act+ : ∀ n m a → z-act (n +ᶻ m) a == (z-act n a * z-act m a)
  z-act+ zer m a = inv (lunit (z-act m a))
  z-act+ (pos zero) m a = act-zsucc m a
  z-act+ (pos (succ x)) m a =
    begin
      z-act (zsucc (pos x +ᶻ m)) a        ==⟨ act-zsucc (pos x +ᶻ m) a ⟩
      a * z-act (pos x +ᶻ m) a            ==⟨ ap (λ s → a * s) (z-act+ (pos x) m a) ⟩
      a * (z-act (pos x) a * z-act m a)   ==⟨ assoc a (z-act (pos x) a) (z-act m a) ⟩
      (a * z-act (pos x) a) * z-act m a   ==⟨ ap (_* z-act m a) (inv (act-zsucc (pos x) a)) ⟩
      (z-act (pos (succ x)) a) * z-act m a
    ∎
  z-act+ (neg zero) m a = act-zpred m a
  z-act+ (neg (succ x)) m a =
    begin
      z-act (zpred (neg x +ᶻ m)) a             ==⟨ act-zpred (neg x +ᶻ m) a ⟩
      ginv a * z-act (neg x +ᶻ m) a            ==⟨ ap (λ section → _*_ (ginv a) section) (z-act+ (neg x) m a) ⟩
      ginv a * (z-act (neg x) a * z-act m a)  ==⟨ assoc (ginv a) (z-act (neg x) a) (z-act m a) ⟩
      (ginv a * z-act (neg x) a) * z-act m a  ==⟨ inv (ap (λ s → s * (z-act m a)) (act-zpred (neg x) a)) ⟩
      z-act (neg (succ x)) a * z-act m a
    ∎

open IntegerAction public
module Interval where

  private
    -- The interval is defined as a type with a nontrivial equality
    -- between its two elements.
    data !I : Type₀ where
      !Izero : !I
      !Ione : !I

  I : Type₀
  I = !I

  Izero : I
  Izero = !Izero

  Ione : I
  Ione = !Ione

  postulate
    seg : Izero == Ione

  -- Recursion principle on points.
  I-rec : ∀ {ℓ} {A : Type ℓ}
        → (a b : A)
        → (p : a == b)
        --------------
        → (I → A)
  I-rec a _ _ !Izero = a
  I-rec _ b _ !Ione  = b

  -- Recursion principle on paths.
  postulate
    I-βrec : ∀ {ℓ}
      → (A : Type ℓ)
      → (a b : A)
      → (p : a == b)
      ---------------------------
      → ap (I-rec a b p) seg == p

open Interval public
module Circle where

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
    S¹-βrec : ∀ {ℓ} (A : Type ℓ)
            → (a : A)
            → (p : a == a)
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

module Suspension where

  module S where

  private
    data Suspₚ {ℓ} (A : Type ℓ) : Type ℓ where
      Nₚ : Suspₚ A
      Sₚ : Suspₚ A

    data Suspₓ {ℓ} (A : Type ℓ) : Type ℓ where
      mkSusp : Suspₚ A → (𝟙 → 𝟙) → Suspₓ A

  Susp = Suspₓ

  -- point-constructors
  North : ∀ {ℓ} {A : Type ℓ} → Susp A
  North = mkSusp Nₚ _

  South : ∀ {ℓ} {A : Type ℓ} → Susp A
  South = mkSusp Sₚ _

  -- path-constructors
  postulate
    merid : ∀ {ℓ} {A : Type ℓ}
          → A
          → Path {ℓ}{Susp A} North South

  -- Recursion principle on points
  Susp-rec : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ}{C : Type ℓⱼ}
           → (cₙ cₛ  : C)
           → (merid' : A → cₙ == cₛ)
           ------------------------
           → (Susp A → C)
  Susp-rec cₙ _ _ (mkSusp Nₚ _) = cₙ
  Susp-rec _ cₛ _ (mkSusp Sₚ _) = cₛ

  -- Recursion principle on paths
  postulate
    Susp-βrec : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ}{C : Type ℓⱼ}
              → {cₙ cₛ : C} {mer : A → cₙ == cₛ}
              → {a : A}
              -------------------------------------------
              → ap (Susp-rec cₙ cₛ mer) (merid a) == mer a

  -- Induction principle on points
  Susp-ind : ∀ {ℓ} {A : Type ℓ} (C : Susp A → Type ℓ)
              → (N' : C North)
              → (S' : C South)
              → (merid' : (x : A) → N' == S' [ C ↓ (merid x) ])
              --------------------------------------------------
              → ((x : Susp A) → C x)

  Susp-ind _ N' S' _ (mkSusp Nₚ _) = N'
  Susp-ind _ N' S' _ (mkSusp Sₚ _) = S'

  -- Induction principle on paths
  postulate
    Susp-βind : ∀ {ℓ} {A : Type ℓ} (C : Susp A → Type ℓ)
              → (N' : C North)
              → (S' : C South)
              → (merid' : (x : A) → N' == S' [ C ↓ (merid x)]) {x : A}
              --------------------------------------------------------
              → apd (Susp-ind C N' S' merid') (merid x) == merid' x

open Suspension
module FundamentalGroup where

  -- Definition of the fundamental group.
  Ω : ∀ {ℓ} (A : Type ℓ) → (a : A) → Type ℓ
  Ω A a = (a == a)

  -- Its group structure.
  Ω-st : ∀ {ℓ} (A : Type ℓ) → (a : A) → GroupStructure (Ω A a)
  Ω-st A a = group-structure _·_ (refl a)
    (λ a → inv (·-lunit a)) (λ a → inv (·-runit a))
    (λ x y z → inv (·-assoc x y z))
    inv ·-rinv ·-linv

  Ω-gr : ∀ {ℓ} (A : Type ℓ) → (a : A) → Group {ℓ}
  Ω-gr A a = group (a == a) (Ω-st A a)

  Ω-st-r : ∀ {ℓ} (A : Type ℓ) → (a : A) → GroupStructure (Ω A a)
  Ω-st-r A a = group-structure (λ x y → y · x) (refl a)
    (λ a → inv (·-runit a)) (λ a → inv (·-lunit a))
    (λ x y z → ·-assoc z y x)
    inv ·-linv ·-rinv
open FundamentalGroup public
module FundGroupCircle where
  open Circle
  -- Winds a loop n times on the circle.
  loops : ℤ → Ω S¹ base
  loops n = z-act (Ω-st S¹ base) n loop

  private
  -- Uses univalence to unwind a path over the integers.
    code : S¹ → Type₀
    code = S¹-rec Type₀ ℤ (ua zequiv-succ)

  tcode-succ : (n : ℤ) → transport code loop n == zsucc n
  tcode-succ n =
    begin
      transport code loop n ==⟨ refl _ ⟩
      transport ((λ a → a) ∘ code) loop n ==⟨ transport-family loop n ⟩
      transport (λ a → a) (ap code loop) n ==⟨ ap (λ u → transport (λ a → a) u n) (S¹-βrec _ ℤ (ua zequiv-succ)) ⟩
      transport (λ a → a) (ua zequiv-succ) n ==⟨ ap (λ e → (lemap e) n) (ua-β zequiv-succ) ⟩
      zsucc n
    ∎

  tcode-pred : (n : ℤ) → transport code (inv loop) n == zpred n
  tcode-pred n =
    begin
      transport code (inv loop) n
        ==⟨ refl _ ⟩
      transport ((λ a → a) ∘ code) (inv loop) n
        ==⟨ transport-family (inv loop) n ⟩
      transport (λ a → a) (ap code (inv loop)) n
        ==⟨ ap (λ u → transport (λ a → a) u n) (ap-inv code loop) ⟩
      transport (λ a → a) (inv (ap code loop)) n
        ==⟨ ap (λ u → transport (λ a → a) (inv u) n) (S¹-βrec _ ℤ (ua zequiv-succ)) ⟩
      transport (λ a → a) (inv (ua zequiv-succ)) n
        ==⟨ ap (λ u → transport (λ a → a) u n) (inv (ua-inv zequiv-succ)) ⟩
      transport (λ a → a) (ua (≃-sym zequiv-succ)) n
        ==⟨ ap (λ e → (lemap e) n) ((ua-β (≃-sym zequiv-succ))) ⟩
      zpred n
    ∎

  private
    encode : (x : S¹) → (base == x) → code x
    encode x p = transport code p zer

    decode : (x : S¹) → code x → (base == x)
    decode = S¹-ind (λ x → (code x → (base == x))) loops (
      begin
        transport (λ x → code x → base == x) loop loops
          ==⟨ transport-fun loop loops ⟩
        transport (λ x → base == x) loop ∘ (loops ∘ transport code (inv loop))
          ==⟨ ap (λ u → u ∘ (loops ∘ transport code (inv loop))) (funext λ p → transport-concat-r loop p) ⟩
        (_· loop) ∘ (loops ∘ transport code (inv loop))
          ==⟨ ap (λ u → (_· loop) ∘ (loops ∘ u)) (funext tcode-pred) ⟩
        (_· loop) ∘ (loops ∘ zpred)
          ==⟨ funext lemma ⟩
        loops
      ∎)
      where
        lemma : (n : ℤ) → ((_· loop) ∘ (loops ∘ zpred)) n == loops n
        lemma zer            = ·-linv loop
        lemma (pos zero)     = refl _
        lemma (pos (succ x)) = refl _
        lemma (neg zero) =
          ·-assoc (inv loop) (inv loop) loop ·
          ap (inv loop ·_) (·-linv loop) ·
          inv (·-runit (inv _))
        lemma (neg (succ x)) =
          ·-assoc (loops (neg x) · inv loop) _ loop ·
          ap ((loops (neg x) · (inv loop)) ·_) (·-linv loop) ·
          inv (·-runit _)

    decode-encode : (x : S¹) → (p : base == x) → decode x (encode x p) == p
    decode-encode .base idp = refl (refl base)

    encode-decode : (x : S¹) → (c : code x) → encode x (decode x c) == c
    encode-decode x = S¹-ind
        ((λ y → (c : code y) → encode y (decode y c) == c))
        lemma (funext λ _ → z-isSet _ _ _ _) x
      where
        lemma : (n : ℤ) → encode base (loops n) == n
        lemma zer = refl zer
        lemma (pos 0) = tcode-succ zer
        lemma (pos (succ n)) =
          inv (transport-comp-h (loops (pos n)) loop zer) ·
          ap (transport code loop) (lemma (pos n)) ·
          tcode-succ _
        lemma (neg zero) = tcode-pred zer
        lemma (neg (succ n)) =
          inv (transport-comp-h (loops (neg n)) (inv loop) zer) ·
          ap (transport code (inv loop)) (lemma (neg n)) ·
          tcode-pred _

  -- Creates an equivalence between paths and encodings.
  equiv-family : (x : S¹) → (base == x) ≃ code x
  equiv-family x = qinv-≃ (encode x) (decode x , (encode-decode x , decode-encode x))


  -- The fundamental group of the circle is the integers.  In this
  -- proof, univalence is crucial. The next lemma will prove that the
  -- equivalence in fact preserves the group structure.
  fundamental-group-of-the-circle : Ω S¹ base ≃ ℤ
  fundamental-group-of-the-circle = equiv-family base

  preserves-composition : ∀ n m → loops (n +ᶻ m) == loops n · loops m
  preserves-composition n m = z-act+ (Ω-st S¹ base) n m loop
