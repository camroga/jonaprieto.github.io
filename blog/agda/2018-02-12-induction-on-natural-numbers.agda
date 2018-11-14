𝒰 = Set
data ℕ : 𝒰 where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}
bigNumber : ℕ
bigNumber = 123456789  -- instead of suc (suc ( ... (suc ..)..
recℕ
  : (C : 𝒰)
  → C
  → (ℕ → C → C)
  -------------
  → ℕ → C
recℕ C c₀ cₛ zero    = c₀
recℕ C c₀ cₛ (suc n) = cₛ n (recℕ C c₀ cₛ n)
add : ℕ → ℕ → ℕ
add = recℕ (ℕ → ℕ) (λ m → m) (λ n g m → suc (g m))

_+_ = add
infix 6 _+_
add₂ : ℕ → ℕ → ℕ
add₂ zero    m = m
add₂ (suc n) m = suc (add₂ n m)
double : ℕ → ℕ
double = recℕ ℕ 0 (λ n y → suc (suc y))
double₂ : ℕ → ℕ
double₂ zero = zero
double₂ n    = suc (suc n)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; sym)

2+5 : add 2 5 ≡ 7
2+5 = refl

25+25 : add 25 25 ≡ 50
25+25 = refl
_*_ : ℕ → ℕ → ℕ
_*_ = recℕ (ℕ → ℕ) (λ m → zero) (λ n g m → add m (g m))
infix 7 _*_
m₁ : 2 * 0 ≡ 0
m₁ = refl

m₂ : 2 * 3 ≡ 6
m₂ = refl

m₃ : 10 * 3 ≡ 30
m₃ = refl
indℕ
  : ∀ {C : ℕ → 𝒰}
  → C zero
  → (∀ (n : ℕ) → C n → C (suc n))
  -------------------
  → ∀ (n : ℕ) → C n
indℕ c₀ cₛ zero    = c₀
indℕ c₀ cₛ (suc n) = cₛ n (indℕ c₀ cₛ n)
suc-cong
  : ∀ {n m : ℕ}
  -----------------------
  → n ≡ m → suc n ≡ suc m

suc-cong refl = refl
add≡add₂
  : ∀ (n m : ℕ)
  --------------------
  → add n m ≡ add₂ n m

add≡add₂ zero    m = refl
add≡add₂ (suc n) m = suc-cong (add≡add₂ n m)
assoc
  : (i j k : ℕ)
  ---------------------------
  → i + (j + k) ≡ (i + j) + k
assoc₀
  : ∀ (j k : ℕ)
  ---------------------------
  → 0 + (j + k) ≡ (0 + j) + k

assoc₀ j k = refl
assoc₁
  : ∀ (i : ℕ)
  → ((j k : ℕ) → i + (j + k) ≡ (i + j) + k)
  ---------------------------------------------------
  → (j k : ℕ) → (suc i) + (j + k) ≡ ((suc i) + j) + k

assoc₁ i p j₁ k₁ = suc-cong (p j₁ k₁)
assoc = indℕ assoc₀ assoc₁
+-comm₀
  : ∀ (m : ℕ)
  ---------------
  → 0 + m ≡ m + 0

+-comm₀ = indℕ refl (λ n indHyp → suc-cong indHyp)
+-identity
  : ∀ (n : ℕ)
  --------------
  → n + zero ≡ n

+-identity = indℕ refl (λ n indHyp → suc-cong indHyp)
+-suc
  : ∀ m n
  -------------------------
  → m + suc n ≡ suc (m + n)

+-suc zero    n = refl
+-suc (suc m) n = suc-cong (+-suc m n)
trans
  : ∀ {m n p : ℕ}
  → m ≡ n → n ≡ p
  ---------------
  → m ≡ p

trans refl refl = refl
≡sym
  : ∀ {m n p : ℕ}
  → m ≡ n → n ≡ m

≡sym refl = refl
+-comm
  : ∀ (m n : ℕ)
  ---------------
  → m + n ≡ n + m

+-comm =
  indℕ
    sproof₁
    sproof₂
  where
    sproof₁
      : ∀ (n : ℕ)
      ----------------
      → n ≡ (n + zero)

    sproof₁ = indℕ refl (λ n n≡n+zero → suc-cong n≡n+zero)

    sproof₂
      : ∀ (n : ℕ)
      → ((m : ℕ) → (n + m) ≡ (m + n))
      ---------------------------------------
      → ((m : ℕ) → suc (n + m) ≡ (m + suc n))

    sproof₂ n hyp₁ =
      indℕ
        (suc-cong
          (hyp₁ zero) )
        (λ m hyp₂ →
            suc-cong
              (trans
                  (hyp₁ (suc m))
              (trans
                  (suc-cong
                      (sym (hyp₁ m)))
                  hyp₂)))
0+n≡n
  : ∀ (n : ℕ)
  -----------
  → 0 + n ≡ n

0+n≡n = indℕ refl (λ n p → suc-cong p)
p₂
  : ∀ (n : ℕ)
  -----------------------------------------
  → double (n + 1) ≡ (suc (suc (double n)))

p₂ = indℕ refl (λ n indHyp → suc-cong (suc-cong indHyp))
n+0≡n
  : ∀ (n : ℕ)
  -----------
  → n + 0 ≡ n

n+0≡n = indℕ refl (λ n indHyp → suc-cong indHyp)
n+0≡n₂
  : ∀ (n : ℕ)
  -----------
  → n + 0 ≡ n

n+0≡n₂ zero    = refl
n+0≡n₂ (suc n) = suc-cong (n+0≡n₂ n)
module ℕ-transInd (P : ℕ → 𝒰) where

  data _<_ : ℕ → ℕ → 𝒰 where
    z<s : ∀ {n : ℕ}   → zero < suc n
    s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

  data _⊎_ : 𝒰 → 𝒰 → 𝒰 where
    inj₁ : ∀ {A B : 𝒰} → A → A ⊎ B
    inj₂ : ∀ {A B : 𝒰} → B → A ⊎ B

  ⊎-elim
    : ∀ {A B C : 𝒰}
    → (A → C)
    → (B → C)
    -------------
    → (A ⊎ B → C)

  ⊎-elim f g (inj₁ x) = f x
  ⊎-elim f g (inj₂ y) = g y

  subst : {k n : ℕ} → k ≡ n → P k → P n
  subst refl pk = pk

  split-k<sucn
    : ∀ {k : ℕ} {n : ℕ}
    → k < suc n
    -------------------
    → (k < n) ⊎ (k ≡ n)

  split-k<sucn {zero}  {zero}  k<sucn = inj₂ refl
  split-k<sucn {zero}  {suc n} k<sucn = inj₁ z<s
  split-k<sucn {suc k} {zero}  (s<s ())
  split-k<sucn {suc k} {suc n} (s<s k<sucn) =
    ⊎-elim
      (λ k<n → inj₁ (s<s k<n))
      (λ k≡n → inj₂ (suc-cong k≡n))
      (split-k<sucn k<sucn)
-- proof:
  indℕ⇒transFindℕ
    : (hyp : (n : ℕ) → ((k : ℕ) → (k < n) → P k) → P n)
    → ((n : ℕ) → P n)

  indℕ⇒transFindℕ hyp zero    = hyp zero (λ k → λ ())
  indℕ⇒transFindℕ hyp (suc n) = hyp (suc n) (G (suc n))
    where
      G : ∀ (n : ℕ) → ((k : ℕ) → (k < n) → P k)
      G zero    k () -- impossible case
      G (suc n) k k<n+1 =
        ⊎-elim
          -- 1. when k < n
          (λ k<n → G n k k<n)
          -- 2. when k ≡ n
          (λ k≡n → subst (sym k≡n) (hyp n (G n)))
          -- eliminiting two cases: (k < n) ⊎ (k ≡ n)
          (split-k<sucn k<n+1)
