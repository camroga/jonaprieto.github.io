{-# OPTIONS --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
pi
  : ∀ {i j} {A : Set i}
  → (C : (x y : A) → x ≡ y → Set j)
  → (∀ (x : A) → C x x refl)
  → ∀ (x y : A) (p : x ≡ y) → C x y p
pi {A} C c x .x refl = c x
infixr 20 _·_
_·_ : ∀ {A : Set} {x y z : A}
    → (p : x ≡ y)
    → (q : y ≡ z)
    ------------
    → x ≡ z

_·_ {A} {x} {y} {z} p q = D₁ x y p z q
  where
    D₂ : (x z : A) (q : x ≡ z) → x ≡ z
    D₂ = pi (λ x z q → x ≡ z) (λ x → refl)

    D₁ : (x y : A) → (x ≡ y) → ((z : A) → (q : y ≡ z) → x ≡ z)
    D₁ = pi (λ x y p → ((z : A) → (q : y ≡ z) → x ≡ z)) (λ x → D₂ x)
infixl 20 _⁻¹
_⁻¹ : ∀ {A : Set} {x y : A} → (p : x ≡ y) → y ≡ x
_⁻¹ {A}{x}{y} p =
  pi (λ x y p → y ≡ x)
     (λ x → refl {x = x})
     x y p
l1 : ∀ {A : Set} {x : A} → (refl ⁻¹) ≡ refl
l1 {A}{x} =
  pi (λ x y p → (refl ⁻¹) ≡ refl {x = x})
     (λ x → refl {x = refl {x = x}})
     x x refl
l2 : ∀ {A : Set} (x y : A) → (p : x ≡ y) → (p · (p ⁻¹))  ≡ refl
l2 =
  pi (λ x y p → (p · (p ⁻¹))  ≡ refl)
     (λ x → refl { x = refl {x = x}})
l3 : ∀ {A : Set} (x y : A) → (p : x ≡ y) → refl · p ≡ p
l3 =
  pi (λ x y p → refl · p ≡ p)
     (λ x → refl { x = refl {x = x}})
l4 : ∀ {A : Set} (x y : A) → (p : x ≡ y) → refl · p ≡ p
l4 = pi (λ x y p → refl · p ≡ p)
        (λ x → refl {x = refl {x = x}})
l5 : ∀ {A : Set} (x y : A) → (p : x ≡ y) → (p  ⁻¹) ⁻¹ ≡ p
l5 = pi (λ x y p → (p  ⁻¹) ⁻¹ ≡ p)
        (λ x → refl {x = refl {x = x}})
transp : ∀ {A : Set}{x x' : A}
      → (B : A → Set) → (y : B x) → (u : x ≡ x') → B x'
transp B y refl  = y
open import Relation.Binary.PropositionalEquality using (subst)

trans' : ∀ {A : Set}{x x' : A}
      → (B : A → Set) → (y : B x) → (u : x ≡ x') → B x'
trans' B y u = subst B u y
