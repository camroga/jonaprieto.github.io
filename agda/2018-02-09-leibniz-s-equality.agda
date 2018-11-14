Eq : ∀ {A : Set} → (x y : A) → Set₁
Eq {A} x y = (P : A → Set) → (P x → P y)
refl : ∀ {A : Set} → (x : A) → Eq x x
refl {A} x = λ P Px₁ → Px₁
trans : ∀ {A : Set} → (x y z : A) → Eq x y → Eq y z → Eq x z
trans {A} x y z x≡y P₁ y≡z P₂ = P₁ y≡z (x≡y y≡z P₂)
sym : ∀ {A : Set} → (x y : A) → Eq x y → Eq y x
sym {A} x y x≡y P = x≡y p₁ (λ z → z)
  where
    p₁ : A → Set
    p₁ = λ z → P z → P x
