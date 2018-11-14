infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x
pi
  : ∀ {i} {A : Set}
  → (C : (x y : A) → x ≡ y → Set i)
  → (∀ (x : A) → C x x refl)
  -----------------------------------
  → ∀ (x y : A) (p : x ≡ y) → C x y p
pi {A} C c x .x refl = c x
bpi
  : ∀ {i} {A : Set}
  → (a : A)   -- Fixed
  → (C : (y : A) → a ≡ y → Set i)
  → C a refl
  -----------------------------
  → (y : A) (p : a ≡ y) → C y p

bpi a C c .a refl = c
bpi⇒pi
  : ∀ {A : Set}
  → (C : (x y : A) → x ≡ y → Set)
  → (c : (x : A) → C x x refl)
  → (x y : A) (p : x ≡ y) → C x y p

bpi⇒pi {A} C c x = g
  where
    C′ : (y : A) → x ≡ y → Set
    C′ = C x

    c′ : C x x refl
    c′  = c x

    g : ∀ (y : A) (p : x ≡ y) → C′ y p
    g = bpi x C′ c′
pi⇒bpi
  : ∀ {A : Set}
  → (a : A)
  → (C : (y : A) → a ≡ y → Set)
  → (c : C a refl)
  → ∀ (y : A) (p : a ≡ y) → C y p

pi⇒bpi {A} a C c y p = f a y p C c
  where
    D : ∀ (x y : A) → x ≡ y → Set₁
    D x y p = (L : (z : A) → x ≡ z → Set) → L x refl → L y p

    d : ∀ (x : A) → D x x refl
    d = λ x C c → c

    f : ∀ (x y : A) (p : x ≡ y) → D x y p
    f = pi D d
