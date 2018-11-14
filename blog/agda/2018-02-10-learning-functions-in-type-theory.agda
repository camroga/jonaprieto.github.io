open import Relation.Binary.PropositionalEquality using (_≡_; refl)

postulate
  A B : Set
  t : B

f : A → B
f x = t

f₁ : A → B
f₁ = λ x → f x

f≡f₁ : f ≡ f₁
f≡f₁ = refl
g :  A → A → A
g = λ x y → y

h : A → A → A
h =  λ w z → z
g≡h : g ≡ h
g≡h = refl
postulate
  FunExt
    : ∀ {A B : Set}
    → ∀ {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
    → f ≡ g
𝒰 = Set
data ℕ : 𝒰 where
 zero : ℕ
 suc  : ℕ → ℕ

add : ℕ → ℕ → ℕ
add = recℕ (ℕ → ℕ) (λ m → m) (λ n g m → suc (g m))
  where
    recℕ : (C : 𝒰) → C → (ℕ → C → C) → ℕ → C
    recℕ C c₀ cₛ zero    = c₀
    recℕ C c₀ cₛ (suc n) = cₛ n (recℕ C c₀ cₛ n)

add₂ : ℕ → ℕ → ℕ
add₂ zero    m = m
add₂ (suc n) m = suc (add₂ n m)

_+_ = add
infix 6 _+_
add≡add₂ : add ≡ add₂
add≡add₂ = FunExt (λ n → FunExt λ m → helper n m)
  where
    +-cong : ∀ {n m : ℕ} → n ≡ m → suc n ≡ suc m
    +-cong refl = refl

    helper : (n m : ℕ) → add n m ≡ add₂ n m
    helper zero    m = refl
    helper (suc n) m = +-cong (helper n m)
open import Level
open import Relation.Binary.PropositionalEquality using (cong)
open import Function using (_∘_; _$_)
Extensionality : (a b : Level) → Set _
Extensionality a b =
  {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
  (∀ x → f x ≡ g x) → f ≡ g
extensionality-for-lower-levels
  : ∀ {a₁ b₁} a₂ b₂
  → Extensionality (a₁ ⊔ a₂) (b₁ ⊔ b₂)
  → Extensionality a₁ b₁

extensionality-for-lower-levels a₂ b₂ ext f≡g =
  cong (λ h → lower ∘ h ∘ lift) $
    ext (cong (lift {ℓ = b₂}) ∘ f≡g ∘ lower {ℓ = a₂})
∀-extensionality
  : ∀ {a b}
  → Extensionality a (Level.suc b)
  → {A : Set a} (B₁ B₂ : A → Set b)
  → (∀ x → B₁ x ≡ B₂ x) → (∀ x → B₁ x) ≡ (∀ x → B₂ x)

∀-extensionality ext B₁ B₂ B₁≡B₂ with ext B₁≡B₂
∀-extensionality ext B .B  B₁≡B₂ | refl = refl
