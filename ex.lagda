\begin{code}
{-# OPTIONS --without-K #-}
open import HoTT

apd'
  : ∀ {i j}{A : Type i}{B : A → Type j}{x y : A}
  → (f : (x : A) → B x)
  → (p : x == y)
  → transport B p (f x) == f y
apd' f idp = idp

lem
  : ∀{i j k}{A : Type i}{B : Type j}{x y : A}{P : B → Type k}
  → (f : A → B)
  → (p : x == y)
  → (u : P (f x))
  → transport (λ x → P (f x)) p u == transport P (ap f p) u
lem f idp u = idp

thm
  : ∀ {i j}{A : Type i}{x y : A}{B : A → Type j}{w w' : Σ A (λ a → B a) }
  → (w == w')
  → (Σ (fst w == fst w')
       (λ p → transport B p (snd w) == snd w'))
-- thm {w = (x , y)}{w' = .(x , y)} idp  = (idp , idp)
thm {w = w} r = (ap fst r , ! (lem fst r (snd w)) ∙ apd' snd r)

!thm
  : ∀ {i j}{A : Type i}{x y : A}{B : A → Type j}{w w' : Σ A (λ a → B a) }
  → (Σ (fst w == fst w')
  (λ p → transport B p (snd w) == snd w'))
  → (w == w')
!thm (idp , s) = pair= idp s


ap-fst-pair=
  : ∀ {i j} {A : Type i}{B : A → Type j}{x y : A}
  → (p : x == y)
  → {u : B x}{v : B y} (q : PathOver B p u v)
  → ap fst (pair= p q) == p
ap-fst-pair= idp idp = idp


apd-snd-pair=
  : ∀ {i j} {A : Type i}{B : A → Type j}{x y : A}
  → (p : x == y)
  → {u : B x}{v : B y} (q : PathOver B p u v)
  → apd snd (pair= p q) == ↓-cst2-in p q q
apd-snd-pair= idp idp = idp

-- lem-pair
--   : ∀ {i j} {A : Type i} {B : A → Type j}{x y : A}{u : B x}{v : B y}
--   → (q : (x , u) == (y , v) )
--   → pair= (ap fst q) {!!} == {!!}
-- lem-pair = {!!}


transpconst
  : ∀ {i j}{A : Type i}{x y : A}
  → (B : Type j)
  → (p : x == y)
  → (u : B)
  → transport (λ _ → B) p u == u
transpconst B idp u = idp

--
f : ∀ {i j}{A : Type i}{B : A → Type j}{x y : A}{p : x == y}{u : B x}{v : B y}
  → Σ ((x , u) == (y , v)) (λ q → (ap fst q) == p)
  → transport B p u == v
f {i = i} {B = B} {x = x} {u = u} (idp , idp)
  = transpconst {i = i} (B x) (idp {a = x}) u

g : ∀ {i j}{A : Type i}{B : A → Type j}{x y : A}{p : x == y}{u : B x}{v : B y}
  → (r : PathOver B p u v)
  → Σ ((x , u) == (y , v)) (λ q → (ap fst q) == p)
g {p = p} r = (pair= p r , ap-fst-pair= p r)


f-g
  : ∀ {i j}{A : Type i}{B : A → Type j}{x y : A}{p : x == y}{u : B x}{v : B y}
  → (r : transport B p u == v)
  → f {A = A}{B = B} (g r) == r
f-g idp = idp

g-f
  : ∀ {i j}{A : Type i}{B : A → Type j}{x y : A}{p : x == y}{u : B x}{v : B y}
  → (pair :  Σ ((x , u) == (y , v)) (λ q → (ap fst q) == p))
  → g {A = A}{B = B} (f pair) == {!!}
g-f {x = x} {y = .x} {p = idp} {u} (s , h) = {!!}

\end{code}
