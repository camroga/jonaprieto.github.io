{-# OPTIONS --without-K #-}
open import 2018-07-06-mini-hott
module _ where
data Vec (A : Type₀) : Nat → Type₀ where
  nil  : Vec A zero
  cons : ∀ {n : Nat} → (a : A) → Vec A n → Vec A (succ n)

_+Nat_ : Nat → Nat → Nat
_+Nat_ zero     n = n
_+Nat_ (succ n) m = succ (n +Nat m)


n+0=n : (n : Nat) → (n +Nat zero) == n
n+0=n zero = idp
n+0=n (succ n) = ap succ (n+0=n n)

concat
  : ∀ {A : Type₀}{n m : Nat}
  → Vec A n → Vec A m
  → Vec A (n +Nat m)

concat nil b = b
concat (cons a xs) b = cons a (concat xs b)

-- infixl 40 _<>_
syntax concat v u = v <> u

[]-runit : ∀ {A : Type₀} {n : Nat} {v : Vec A n} → concat nil v == v
[]-runit = idp

[]-lunit : ∀ {A : Type₀} {n : Nat} (v : Vec A n)
        → concat v nil == v [ Vec A ↓ (n+0=n n) ]
[]-lunit {A} {.0} nil = idp
[]-lunit {A} {(succ n)} (cons a v) = apOver succ (cons a) (n+0=n n) ([]-lunit v)


+Nat-assoc : (i j k : Nat) → (i +Nat (j +Nat k)) == ((i +Nat j) +Nat k)
+Nat-assoc zero j k = idp
+Nat-assoc (succ i) j k = ap succ (+Nat-assoc i j k)

[]-assoc
  : ∀ {A : Type₀}{n m p : Nat}
  → {v₁ : Vec A n} → {v₂ : Vec A m} → {v₃ : Vec A p}
  → (v₁ <> (v₂ <> v₃)) == ((v₁ <> v₂) <> v₃) [ Vec A ↓ (+Nat-assoc n m p) ]
  --------------------------------------------------

[]-assoc {A} {.0} {m} {p} {nil} {v₂} {v₃} = idp
[]-assoc {A} {(succ n)} {.0} {.0} {cons a v₁} {nil} {nil} = {!   !}
[]-assoc {A} {.(succ _)} {.0} {.(succ _)} {cons a v₁} {nil} {cons a₁ v₃} = {!   !}
[]-assoc {A} {.(succ _)} {.(succ _)} {.0} {cons a v₁} {cons a₁ v₂} {nil} = {!   !}
[]-assoc {A} {.(succ _)} {.(succ _)} {.(succ _)} {cons a v₁} {cons a₁ v₂} {cons a₂ v₃} = {!   !}
contr→prop : {A : Set} → isContr A → isProp A
contr→prop (w , d) x y = ((d x) ⁻¹) · d y
contr-if-inhabited→prop : {A : Set} → (A → isContr A) → isProp A
contr-if-inhabited→prop {A} g x y = contr→prop (g x) x y
-- prop→set : {A : Set} → isProp A → isSet A
-- prop→set  {A = A} f a _ p q = lemma p · inv (lemma q)
--   where
--     triang : {y z : A} {p : y == z} → (f a y) · p == f a z
--     triang {y}{p = idp} = inv (·-runit (f a y))
--
--     lemma : {y z : A} (p : y == z) → p == ! (f a y) · (f a z)
--     lemma {y} {z} p =
--       begin
--         p                       ==⟨ ap (_· p) (inv (·-linv (f a y))) ⟩
--         ! (f a y) · f a y · p   ==⟨ ·-assoc (! (f a y)) (f a y) p ⟩
--         ! (f a y) · (f a y · p) ==⟨ ap (! (f a y) ·_) triang ⟩
--         ! (f a y) · (f a z)
--       ∎
prop→all-contr : {A : Set} → isProp A → ((x y : A) → isContr (x == y))
prop→all-contr f x y = (f x y  , λ p → ((prop→set f) x y) (f x y) p)
all-contr→prop : {A : Set} → ((x y : A) → isContr (x == y)) → isProp A
all-contr→prop g = λ x y → contr→prop (x , λ w → fst (g x y) · (fst (g y w))) x y
-- does this suggest a pattern in the definition of homotopy n-types?
vacuum-cord : {A : Set} → (a : A) → isContr (Σ A (λ x → x == a))
vacuum-cord {A} a = ((a , idp) , f)
  where
    f : (x : Σ A (λ x₁ → x₁ == a)) → a , idp == x
    f (b , d) = pair= ((! d) , t)
      where
        t : transport (λ x → x == a) (! d) idp == d
        t = begin
          transport (λ x → x == a) (! d) idp
            ==⟨ transport-concat-l (! d) idp ⟩
          ! (! d) · idp
            ==⟨ ! (·-runit (! ! d)) ⟩
          ! (! d)
            ==⟨ involution ⟩
          d
                  ∎
contr-is-contr : {A : Set} → isContr A → isContr (isContr A)
contr-is-contr {A} (c , p) = (c , p) , ctr
  where
    ctr : (x : isContr A) → c , p == x
    ctr (xc , xp) = pair= (p xc , t)
      where
        t : transport (λ x → (a : A) → x == a) (p xc) p == xp
        t =
          begin
              transport (λ x → (a : A) → x == a) (p xc) p
          ==⟨ dependent-back-and-forth (p xc) p ⟩
              (λ (a : A) → tr {!   !} {! !  !} {!   !})
          ==⟨ {!   !} ⟩
              {!   !}
          ==⟨ {!   !} ⟩
              {!   !}
          ==⟨ {!   !} ⟩
              xp
          ∎

-- prop-is-prop-always : {A : Set} → isProp (isProp A)
-- prop-is-prop-always {A} =
--   λ x y → funext (λ a → funext (λ b → prop→set x a b (x a b) (y a b)))
adjointify : {A B : Set} → (f : A → B) → qinv f → ishae f
adjointify f = qinv-ishae {f = f}
-- Exercise 6: Prove that A is contractible iff A ≃ 1
contr→trivial : {A : Set} → isContr A → A ≃ ⊤
contr→trivial {A} (ctr , p) = qinv-≃ f (g , f-g , g-f)
  where
    f : A → ⊤
    f = λ _ → unit

    g : ⊤ → A
    g = λ _ → ctr

    f-g : f ∘ g ∼ id
    f-g ★ = idp

    g-f : g ∘ f ∼ id
    g-f a = p a
trivial→contr : {A : Set} → A ≃ ⊤ → isContr A
trivial→contr {A} e = (remap e) unit , λ (a : A) → (rlmap-inverse-h e) a
voevoedsky→equiv : {A B : Set} → (f : A → B) →
                   ((y : B) → isContr (fib f y)) → isEquiv f
voevoedsky→equiv {A}{B} f p b = ctr , λ (x : fib f b) → {!   !}
  where
    ctr : fib f b
    ctr = fst (p b)
equiv→bifun
  : {A B : Set}
  → (f : A → B)
  → isEquiv f
  → Σ (A → B → Set)
        (λ R →
          Σ ((a : A) → isContr (Σ B λ b → R a b)) (λ _ → ((b : B) → isContr (Σ A λ a → R a b))))
equiv→bifun f p = {!  !}
pr : ∀ {l} {A B : Type l} → isSet (A ≃ B)
pr {l}{A}{B} x .x p idp =
  begin
    p
      ==⟨ {!   !} ⟩
    {!   !}
      ==⟨ {!   !} ⟩
    idp
    ∎
-- pep
--   : ∀ {ℓ} {A B : Type ℓ}
--   →  isProp A → isProp B → (A ⇔ B)
--   -------------------------------
--   → A == B
--
-- pep propA propB (fun f , fun g) =
--   ua (qinv-≃ f (g , (λ x → propB _ _) , (λ x → propA _ _)))
-- pep
--   : ∀ {ℓ} {A B : Type ℓ}
--   →  isProp A → isProp B → (A ⇔ B)
--   -------------------------------
--   → isProp (A == B)
--
