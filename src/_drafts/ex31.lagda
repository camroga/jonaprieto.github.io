\begin{code}
{-# OPTIONS --without-K #-}
open import HoTT

isSet : ∀ {i} (A : Type i) → Type _
isSet A = ∀ (x y : A) → (p q : x == y) → p == q

lem : ∀ {i j} {A : Type i}{B : Type j}{x y : A} (f g : A → B) →
     f ∼ g → (p : x == y) → g x == g y
lem {i}{j}{A}{B}{x}{y} f g f-g p = (! (f-g x)) ∙ (ap f p) ∙ f-g y

idB : ∀ {i} {B : Type i} → B → B
idB x = x

postulate
  l23 : ∀ {i j} {A : Type i}{B : Type j}{x y : B}
        {f : A → B}{g : B → A} {p : x == y}
      → ap (f ∘ g) p == ap f (ap g p)

  l24 : ∀ {i}{B : Type i} {x y : B} → {p : x == y} → ap idB p == p

-- lem {A = B}{B = B} {x = x}{y = y} (f∘g~idB)
ex1 : ∀ {i j} (A : Type i)(B : Type j) → isSet A → A ≃ B → isSet B
ex1 {i}{j} A B issetA (f , record { g = g ; f-g = f-g ; g-f = g-f ; adj = adj })
  x  y p q
  = lll (ap (lem (f ∘ g) idB {! f∘g~idB  !}) {!   !})
  where
    f∘g~idB : (f ∘ g) ∼ idB
    f∘g~idB  = f-g

    lll : ap idB p == ap idB q → p == q
    lll path = (! l24) ∙ (path ∙ l24)

    pp :
      ∀ {x y : B} → x == y → f (g x) == f (g y)
    pp {x} {y} p = ap f (ap g p)
    --
    m : ap f (ap g p) == ap f (ap g q)
    m = (ap (ap f) (issetA (g x) (g y) (ap g p) (ap g q)))

    m2 : ap (f ∘ g) p == ap (f ∘ g) q
    m2 = l23 ∙ (m ∙ (! l23))

    m3 : ∀ {x y : B} {p : x == y} → ap idB p == ap (f ∘ g) p
    m3 = {! lem  !}
\end{code}