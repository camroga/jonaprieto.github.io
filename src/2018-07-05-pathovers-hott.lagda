---
layout: "post"
title: "PathOvers"
date: "2018-07-05"
categories: type-theory
toc: true
agda: true
---

(Working in progress with Marc Bezem)

We want to formalise in HoTT the intuition behind a correspondance between the
concept of *path-over* and its respective *total space*.

% - That the pathover has its own (certain paths in the total space). --TODO

The term *pathover* was briefly mentioned in {% cite hottbook %} and they were
later defined in {% cite Licata2015%} as a dependent path.
The concept is extensivily used in {%cite hott-in:agda %}.

% (in words) about the transport and the notation in the book -- TODO
% which is shorthand for ... using transport function for the definition.

![path](/assets/ipe-images/pathovers-total-space.png)

Let's review first an equality type that is closely related with these PathOvers.
(See also {% cite Licata2015 %} for some extra comments).

{: .foldable}
\begin{code}

--  Agda code type-checked with v2.5.4

{-# OPTIONS --without-K #-}

open import Agda.Primitive public

Type : (ℓ : Level) → Set (lsuc ℓ)
Type ℓ = Set ℓ
\end{code}

## Homogeneous equality

The *homogeneous equality* is a type `Path` that relates two elements `a₀` and
`a₁` whose types are *definitionally/judgementally* equal. We denote this type as `Path
{A} a₀ a₁`. The curly braces in Agda stand for *implicit arguments*.
We also use the symbol (`_==_`) to denote this type.

\begin{code}
infix 30 _==_
data _==_ {ℓᵢ} {A : Type ℓᵢ} (a : A) : A → Type ℓᵢ where
  idp : a == a

Path = _==_
\end{code}

## Heterogeneous equality

The heterogeneous equality  in {% cite Licata2015 %} relates two elements
of two different types along an equality α between the types mentioned.
This kind of equality can be formalised as follows in Agda:

\begin{code}
data HEq₁ {ℓ} (A : Type ℓ)
       : (B : Type ℓ)
       → (α : A == B) (a : A) (b : B)
       → Type ℓ where
  idp : ∀ {a : A} → HEq₁ A A idp a a
\end{code}

{% comment %}
> In {%cite McBride2004 %} the author introduced a *heterogeneous equality*, which is an equality type
> `a:A= b:B` that relates two elements `a:A` and `b:B` which may have two judgementally
> distinct types, though the reflexivity constructor applies only when both the
> two types and the two terms are judgementally equal.


> However, McBride’s heterogeneous equality is **logically equivalent** to a
> homogeneous equality type *satisfying uniqueness of identity proofs*, which
> is undesirable **in homotopy type theory, because not all types should be sets**.
{% endcomment %}

We adopt the same name `idp` for the reflexivity constructor of the `Path` type
for the heterogeneous equality. This name is convenient because we want to
maintain some consistency in the following proofs. We will switch between
different definitions of heterogeneous equality but also between definitions for
the homogeneous equality.

Let us recall the transport function and the coercion function  along a
homogeneous equality.

\begin{code}
transport : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} (P : A → Type ℓⱼ) {a b : A}
  → a == b
  → P a
  → P b
transport P idp = (λ x → x)
\end{code}

\begin{code}
coe : ∀ {ℓ}{A B : Type ℓ}
    → A == B
    → (A → B)
coe A==B A = transport (λ X → X) A==B A
\end{code}


{: .foldable}
\begin{code}
--- Somme HoTT machinery necessary for the following sections.
--- This includes homotopies, equivalences, among other concepts.
module hott where

  infixr 60 _,_
  record Σ {ℓᵢ ℓⱼ} (S : Type ℓᵢ)(T : S → Type ℓⱼ) : Type (ℓᵢ ⊔ ℓⱼ) where
    constructor _,_
    field
      fst : S
      snd : T fst
  open Σ public

  Π : ∀ {ℓᵢ ℓⱼ} (A : Type ℓᵢ) (P : A → Type ℓⱼ) → Type (ℓᵢ ⊔ ℓⱼ)
  Π A P = (x : A) → P x

  _×_ : ∀{ℓᵢ ℓⱼ} (S : Type ℓᵢ) (T : Type ℓⱼ) → Type (ℓᵢ ⊔ ℓⱼ)
  A × B = Σ A (λ _ → B)

  infixr 80 _+_
  data _+_ {ℓᵢ ℓⱼ} (S : Type ℓᵢ) (T : Type ℓⱼ) : Type (ℓᵢ ⊔ ℓⱼ) where
    inl : S → S + T
    inr : T → S + T

  id : ∀ {ℓ} {A : Type ℓ} → A → A
  id a = a

  infixr 80 _∘_
  _∘_ : ∀{ℓᵢ ℓⱼ ℓₖ}
      {A : Type ℓᵢ}
      {B : A → Type ℓⱼ}
      {C : (a : A) → (B a → Type ℓₖ)}
      → (g : {a : A} → Π (B a) (C a)) → (f : Π A B) → Π A (λ a → C a (f a))
  g ∘ f = λ x → g (f x)

  infixr 0 _$_
  _$_ : ∀ {i j} {A : Type i} {B : A → Type j}
      → (∀ x → B x) → (∀ x → B x)
  f $ x = f x

  infixl 50 _·_
  _·_ : ∀ {ℓ} {A : Type ℓ}  {a b c : A} → a == b → b == c → a == c
  idp · q = q

  inv : ∀{ℓ} {A : Type ℓ}  {a b : A} → a == b → b == a
  inv idp = idp

  ap : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ}  {a b : A} → (f : A → B)
    →   a == b
    → f a == f b
  ap f idp = idp

  module EquationalReasoning {ℓᵢ} {A : Type ℓᵢ} where

    infixr 2 _==⟨⟩_
    _==⟨⟩_ : ∀ (x {y} : A) → x == y → x == y
    _ ==⟨⟩ p = p

    infixr 2 _==⟨_⟩_
    _==⟨_⟩_ :  (x : A) {y z : A} → x == y → y == z → x == z
    _ ==⟨ p1 ⟩ p2 = p1 · p2

    infix  3 _∎
    _∎ : (x : A) → x == x
    _∎ = λ x → idp

    infix  1 begin_
    begin_ : {x y : A} → x == y → x == y
    begin_ p = p

  open EquationalReasoning public

  module ·-Properties {ℓ} {A : Type ℓ} where
    ·-runit : {a b : A} (p : a == b) → p == p · idp
    ·-runit idp = idp

    ·-lunit : {a b : A} (p : a == b) → p == idp · p
    ·-lunit idp = idp

    ·-assoc : {a b c d : A} (p : a == b) → (q : b == c) → (r : c == d)
            → (p · q) · r == p · (q · r)
    ·-assoc idp q r = idp

    ·-linv : {a b : A} (p : a == b) → (inv p) · p == idp
    ·-linv idp = idp

    ·-rinv : {a b : A} (p : a == b) → p · (inv p) == idp
    ·-rinv idp = idp

    ·-cancellation : {a : A} (p : a == a) → (q : a == a) → p · q == p → q == idp
    ·-cancellation {a} p q α =
      begin
        q                   ==⟨ ap (_· q) (inv (·-linv p)) ⟩
        inv p · p · q       ==⟨ (·-assoc (inv p) _ _) ⟩
        inv p · (p · q)     ==⟨ (ap (inv p ·_) α) ⟩
        inv p · p           ==⟨ ·-linv p ⟩
        idp
      ∎
  open ·-Properties

  module Transport-Properties {ℓᵢ} {A : Type ℓᵢ} where

    -- Some lemmas on the transport operation.
    transport-concat-r : {a : A} {x y : A} → (p : x == y) → (q : a == x) →
      transport (λ x → a == x) p q == q · p
    transport-concat-r idp q = ·-runit q

    transport-concat-l : {a : A} {x y : A} → (p : x == y) → (q : x == a) →
      transport (λ x → x == a) p q == (inv p) · q
    transport-concat-l idp q = idp

    transport-concat : {x y : A} → (p : x == y) → (q : x == x) →
      transport (λ x → x == x) p q == (inv p) · q · p
    transport-concat idp q = ·-runit q

    transport-eq-fun : ∀{ℓⱼ} {B : Type ℓⱼ} (f g : A → B) {x y : A} (p : x == y) (q : f x == g x)
                      → transport (λ z → f z == g z) p q == inv (ap f p) · q · (ap g p)
    transport-eq-fun f g idp q = ·-runit q

    transport-comp : ∀{ℓⱼ} {a b c : A} {P : A → Type ℓⱼ} (p : a == b) (q : b == c)
                     → ((transport P q) ∘ (transport P p)) == transport P (p · q)
    transport-comp {P = P} idp q = idp {a = (transport P q)}

    transport-comp-h : ∀{ℓⱼ} {a b c : A} {P : A → Type ℓⱼ} (p : a == b) (q : b == c) (x : P a)
                     → ((transport P q) ∘ (transport P p)) x == transport P (p · q) x
    transport-comp-h {P = P} idp q x = idp {a =  (transport P q x)}

    -- A shorter notation for transport.
    _✶ : ∀{ℓⱼ} {P : A → Type ℓⱼ} {a b : A} → a == b → P a → P b
    _✶ = transport _
  open Transport-Properties public

  ap-id : ∀{ℓᵢ} {A : Type ℓᵢ} {a b : A} (p : a == b) → ap id p == p
  ap-id idp = idp

  ap-comp : ∀{ℓᵢ ℓⱼ ℓₖ} {A : Type ℓᵢ} {B : Type ℓⱼ} {C : Type ℓₖ}  {a b : A}
          → (f : A → B) → (g : B → C) → (p : a == b)
          → ap g (ap f p) == ap (g ∘ f) p
  ap-comp f g idp = idp

  ap-const : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {C : Type ℓⱼ} {a b : A} {c : C} (p : a == b)
           → ap (λ _ → c) p == idp
  ap-const {c = c} idp = idp {a = idp {a = c}}

  ap-· : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} {a b c : A}
       → (f : A → B) → (p : a == b) → (q : b == c)
       → ap f (p · q) == ap f p · ap f q
  ap-· f idp q = idp {a = (ap f q)}

  ap-inv : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} {a b : A}
         → (f : A → B) → (p : a == b)
         → ap f (inv p) == inv (ap f p)
  ap-inv f idp = idp

  transport-eq-fun-l : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} {b : B} (f : A → B) {x y : A}
                       → (p : x == y) (q : f x == b)
                       → transport (λ z → f z == b) p q == inv (ap f p) · q
  transport-eq-fun-l {b = b} f p q =
    begin
      transport (λ z → f z == b) p q      ==⟨ transport-eq-fun f (λ _ → b) p q ⟩
      inv (ap f p) · q · ap (λ _ → b) p   ==⟨ ap (inv (ap f p) · q ·_) (ap-const p) ⟩
      inv (ap f p) · q · idp           ==⟨ inv (·-runit _) ⟩
      inv (ap f p) · q
    ∎

  transport-eq-fun-r : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} {b : B} (g : A → B) {x y : A}
                       → (p : x == y) (q : b == g x)
                       → transport (λ z → b == g z) p q == q · (ap g p)
  transport-eq-fun-r {b = b} g p q =
    begin
      transport (λ z → b == g z) p q      ==⟨ transport-eq-fun (λ _ → b) g p q ⟩
      inv (ap (λ _ → b) p) · q · ap g p   ==⟨ ·-assoc (inv (ap (λ _ → b) p)) q (ap g p) ⟩
      inv (ap (λ _ → b) p) · (q · ap g p) ==⟨ ap (λ u → inv u · (q · ap g p)) (ap-const p) ⟩
      (q · ap g p)
    ∎

  transport-inv-l : ∀{ℓ} {A B : Type ℓ} → (p : A == B) → (b : B)
                → transport (λ v → v) p (transport (λ v → v) (inv p) b) == b
  transport-inv-l idp b = idp

  transport-inv-r : ∀{ℓ} {A B : Type ℓ} → (p : A == B) → (a : A)
                → transport (λ v → v) (inv p) (transport (λ v → v) p a) == a
  transport-inv-r idp b = idp

  transport-family : ∀{ℓᵢ ℓⱼ ℓₖ} {A : Type ℓᵢ} {B : Type ℓⱼ} {P : B → Type ℓₖ}
                   → {f : A → B} → {x y : A} → (p : x == y) → (u : P (f x))
                   → transport (P ∘ f) p u == transport P (ap f p) u
  transport-family idp u = idp

  transport-fun : ∀{ℓᵢ ℓⱼ ℓₖ} {X : Type ℓᵢ} {x y : X} {A : X → Type ℓⱼ} {B : X → Type ℓₖ}
                  → (p : x == y) → (f : A x → B x)
                  → transport (λ x → (A x → B x)) p f == (λ x → transport B p (f (transport A (inv p) x)))
  transport-fun idp f = idp

  apd : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ}  {P : A → Type ℓⱼ} {a b : A}
      → (f : (a : A) → P a) → (p : a == b)
      → transport P p (f a) == f b
  apd f idp = idp


  module Homotopy {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {P : A → Type ℓⱼ} where
    -- A homotopy is a natural isomorphism between two functions, we will write
    -- f ∼ g when (f x == g x) for all x.
    homotopy : (f g : ((x : A) → P x)) → Type (ℓᵢ ⊔ ℓⱼ)
    homotopy f g = (x : A) → f x == g x

    _∼_ : (f g : ((x : A) → P x)) → Type (ℓᵢ ⊔ ℓⱼ)
    f ∼ g = homotopy f g

    -- Homotopy is an equivalence relation
    h-refl : (f : (x : A) → P x) → f ∼ f
    h-refl f x = idp

    h-simm : (f g : (x : A) → P x) → f ∼ g → g ∼ f
    h-simm f g u x = inv (u x)

    h-comp : (f g h : (x : A) → P x) → f ∼ g → g ∼ h → f ∼ h
    h-comp f g h u v x = (u x)·(v x)

    _●_ : {f g h : (x : A) → P x} → f ∼ g → g ∼ h → f ∼ h
    α ● β = h-comp _ _ _ α β

  open Homotopy public

  -- Composition with homotopies
  module HomotopyComposition {ℓᵢ ℓⱼ ℓₖ} {A : Type ℓᵢ} {B : Type ℓⱼ} {C : Type ℓₖ} where
    hl-comp : (f g : A → B) → (j k : B → C) → f ∼ g → j ∼ k → (j ∘ f) ∼ (k ∘ g)
    hl-comp f g j k α β x = ap j (α x) · β (g x)

    rcomp-∼ : (f : A → B) → {j k : B → C} → j ∼ k → (j ∘ f) ∼ (k ∘ f)
    rcomp-∼ f β = hl-comp _ _ _ _ (h-refl f) β

    lcomp-∼ : {f g : A → B} → (j : B → C) → f ∼ g → (j ∘ f) ∼ (j ∘ g)
    lcomp-∼ j α = hl-comp _ _ _ _ α (h-refl j)

  open HomotopyComposition public

  module Fibers {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ}  where

    -- The fiber of a map over a point is given by
    fib : (f : A → B) → B → Type (ℓᵢ ⊔ ℓⱼ)
    fib f b = Σ A (λ a → f a == b)

    -- A function applied over the fiber returns the original point
    fib-eq : {f : A → B} → {b : B} → (h : fib f b) → f (fst h) == b
    fib-eq (a , α) = α

    -- Each point is on the fiber of its image
    fib-image : {f : A → B} → {a : A} → fib f (f a)
    fib-image {f} {a} = a , idp

  open Fibers public

  module Contractible where

    -- Contractible types. A contractible type is a type such that every
    -- element is equal to a center of contraction.
    isContr : ∀{ℓ}  (A : Type ℓ) → Type ℓ
    isContr A = Σ A (λ a → ((x : A) → a == x))
  open Contractible public

  module Equivalence where

    module DefinitionOfEquivalence {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where
      -- Contractible maps. A map is contractible if the fiber in any
      -- point is contractible, that is, each element has a unique
      -- preimage.
      isContrMap : (f : A → B) → Type (ℓᵢ ⊔ ℓⱼ)
      isContrMap f = (b : B) → isContr (fib f b)

      -- There exists an equivalence between two types if there exists a
      -- contractible function between them.
      isEquiv : (f : A → B) → Type (ℓᵢ ⊔ ℓⱼ)
      isEquiv = isContrMap
    open DefinitionOfEquivalence public

    -- Equivalence of types.
    _≃_ : ∀{ℓᵢ ℓⱼ}  (A : Type ℓᵢ) (B : Type ℓⱼ) → Type (ℓᵢ ⊔ ℓⱼ)
    A ≃ B = Σ (A → B) isEquiv

    module EquivalenceMaps {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where

      -- Maps of an equivalence
      lemap : A ≃ B → (A → B)
      lemap = fst

      remap : A ≃ B → (B → A)
      remap (f , contrf) b = fst (fst (contrf b))

      -- The maps of an equivalence are inverses in particular
      lrmap-inverse : (eq : A ≃ B) → {b : B} → (lemap eq) ((remap eq) b) == b
      lrmap-inverse (f , eqf) {b} = fib-eq (fst (eqf b))

      rlmap-inverse : (eq : A ≃ B) → {a : A} → (remap eq) ((lemap eq) a) == a
      rlmap-inverse (f , eqf) {a} = ap fst ((snd (eqf (f a))) fib-image)

      lrmap-inverse-h : (eq : A ≃ B) → ((lemap eq) ∘ (remap eq)) ∼ id
      lrmap-inverse-h eq = λ x → lrmap-inverse eq {x}

      rlmap-inverse-h : (eq : A ≃ B) → ((remap eq) ∘ (lemap eq)) ∼ id
      rlmap-inverse-h eq = λ x → rlmap-inverse eq {x}
    open EquivalenceMaps public

  open Equivalence public

  module FunctionExtensionality {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : A → Type ℓⱼ} {f g : (a : A) → B a} where
    -- Application of an homotopy
    happly : f == g → ((x : A) → f x == g x)
    happly idp x = idp

    -- The axiom of function extensionality postulates that the
    -- application of homotopies is an equivalence.
    postulate axiomFunExt : isEquiv happly

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

  open FunctionExtensionality public

  -- Function extensionality in the transport case
  module FunctionExtensionalityTransport
    {ℓᵢ ℓⱼ} {X : Type ℓᵢ} {A B : X → Type ℓⱼ} {x y : X} where

    funext-transport
      : (p : x == y) → (f : A x → B x) → (g : A y → B y)
      → ((p ✶) f == g) ≃ ((a : A(x)) → (p ✶) (f a) == g ((p ✶) a))
    funext-transport idp f g = eqFunExt

    funext-transport-l
      : (p : x == y) → (f : A x → B x) → (g : A y → B y)
      → ((p ✶) f == g) → ((a : A(x)) → (p ✶) (f a) == g ((p ✶) a))
    funext-transport-l p f g = lemap (funext-transport p _ _)

    funext-transport-r
      : (p : x == y) → (f : A x → B x) → (g : A y → B y)
      → ((a : A(x)) → (p ✶) (f a) == g ((p ✶) a)) → ((p ✶) f == g)
    funext-transport-r p f g = remap (funext-transport p _ _)

  open FunctionExtensionalityTransport public

  module Sigma {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {P : A → Type ℓⱼ} where

    -- Two dependent pairs are equal if they are componentwise equal.
    Σ-componentwise : {v w : Σ A P} → v == w → Σ (fst v == fst w) (λ p → (p ✶) (snd v) == snd w)
    Σ-componentwise  idp = (idp , idp)

    Σ-bycomponents : {v w : Σ A P} → Σ (fst v == fst w) (λ p → (p ✶) (snd v) == snd w) → v == w
    Σ-bycomponents (idp , idp) = idp

  open Sigma public

  module CartesianProduct {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where

    -- In a pair, the equality of the two components of the pairs is
    -- equivalent to equality of the two pairs.
    prodComponentwise : {x y : A × B} → (x == y) → ((fst x == fst y) × (snd x == snd y))
    fst (prodComponentwise idp) = idp
    snd (prodComponentwise idp) = idp

    prodByComponents : {x y : A × B} → ((fst x == fst y) × (snd x == snd y)) → (x == y)
    prodByComponents (idp , idp) = idp

    -- This is in fact an equivalence.
    prodCompInverse : {x y : A × B} (b : ((fst x == fst y) × (snd x == snd y))) →
                      prodComponentwise (prodByComponents b) == b
    prodCompInverse (idp , idp) = idp

    prodByCompInverse : {x y : A × B} (b : x == y) →
                      prodByComponents (prodComponentwise b) == b
    prodByCompInverse idp = idp

  open CartesianProduct public

  module Propositions where

    -- A type is a mere proposition if any two inhabitants of the type
    -- are equal
    isProp : ∀{ℓ}  (A : Type ℓ) → Type ℓ
    isProp A = ((x y : A) → x == y)

    -- The type of mere propositions
    hProp : ∀{ℓ} → Type (lsuc ℓ)
    hProp {ℓ} = Σ (Type ℓ) isProp


    -- The dependent function type to proposition types is itself a
    -- proposition.
    piProp : ∀{ℓᵢ ℓⱼ} → {A : Type ℓᵢ} → {B : A → Type ℓⱼ}
           → ((a : A) → isProp (B a)) → isProp ((a : A) → B a)
    piProp props f g = funext λ a → props a (f a) (g a)

    -- The product of propositions is itself a proposition.
    isProp-prod : ∀{ℓᵢ ℓⱼ} → {A : Type ℓᵢ} → {B : Type ℓⱼ}
                → isProp A → isProp B → isProp (A × B)
    isProp-prod p q x y = prodByComponents ((p _ _) , (q _ _))

  open Propositions public

  module Sets where

    -- A type is a "set" by definition if any two equalities on the type
    -- are equal.
    isSet : ∀{ℓ}  (A : Type ℓ) → Type ℓ
    isSet A = (x y : A) → isProp (x == y)

    -- The type of sets.
    hSet : ∀{ℓ} → Type (lsuc ℓ)
    hSet {ℓ} = Σ (Type ℓ) isSet

    -- Product of sets is a set.
    isSet-prod : ∀{ℓᵢ ℓⱼ}  {A : Type ℓᵢ} → {B : Type ℓⱼ}
               → isSet A → isSet B → isSet (A × B)
    isSet-prod sa sb (a , b) (c , d) p q = begin
       p
        ==⟨ inv (prodByCompInverse p) ⟩
       prodByComponents (prodComponentwise p)
        ==⟨ ap prodByComponents (prodByComponents (sa a c _ _ , sb b d _ _)) ⟩
       prodByComponents (prodComponentwise q)
        ==⟨ prodByCompInverse q ⟩
       q
      ∎

  open Sets public

  module HLevels where

    -- Propositions are Sets.
    propIsSet : ∀{ℓ} {A : Type ℓ} → isProp A → isSet A
    propIsSet {A = A} f a _ p q = lemma p · inv (lemma q)
      where
        triang : {y z : A} {p : y == z} → (f a y) · p == f a z
        triang {b}{p = idp} = inv (·-runit (f a b))

        lemma : {y z : A} (p : y == z) → p == inv (f a y) · (f a z)
        lemma {y} {z} p =
          begin
            p                         ==⟨ ap (_· p) (inv (·-linv (f a y))) ⟩
            inv (f a y) · f a y · p   ==⟨ ·-assoc (inv (f a y)) (f a y) p ⟩
            inv (f a y) · (f a y · p) ==⟨ ap (inv (f a y) ·_) triang ⟩
            inv (f a y) · (f a z)
          ∎

    -- Contractible types are Propositions.
    contrIsProp : ∀{ℓ}  {A : Type ℓ} → isContr A → isProp A
    contrIsProp (a , p) x y = inv (p x) · p y

    -- To be contractible is itself a proposition.
    isContrIsProp : ∀{ℓ}  {A : Type ℓ} → isProp (isContr A)
    isContrIsProp {_} {A} (a , p) (b , q) = Σ-bycomponents (inv (q a) , piProp (AisSet b) _ q)
      where
        AisSet : isSet A
        AisSet = propIsSet (contrIsProp (a , p))

  open HLevels public

  module EquivalenceProp {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where

    -- Contractible maps are propositions
    isContrMapIsProp : (f : A → B) → isProp (isContrMap f)
    isContrMapIsProp f = piProp λ a → isContrIsProp

    isEquivIsProp : (f : A → B) → isProp (isEquiv f)
    isEquivIsProp = isContrMapIsProp

    -- Equality of same-morphism equivalences
    sameEqv : {α β : A ≃ B} → fst α == fst β → α == β
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

  module Naturality {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where
    h-naturality : {f g : A → B} (H : f ∼ g) → {x y : A} → (p : x == y)
                 → H x · ap g p == ap f p · H y
    h-naturality  H {x = x} (idp ) = inv (·-runit (H x))
  open Naturality
  h-naturality-id : ∀{ℓ} {A : Type ℓ} {f : A → A} (H : f ∼ id) → {x : A}
                  → H (f x) == ap f (H x)
  h-naturality-id {f = f} H {x = x} =
    begin
      H (f x)                            ==⟨ ·-runit (H (f x)) ⟩
      H (f x) · (idp {a = f x})          ==⟨ ap (H (f x) ·_) (inv (·-rinv (H x))) ⟩
      H (f x) · (H x · inv (H x))        ==⟨ inv (·-assoc (H (f x)) _ (inv (H x))) ⟩
      H (f x) · H x · inv (H x)          ==⟨ ap (λ u → H (f x) · u · inv (H x)) (inv (ap-id _)) ⟩
      H (f x) · ap id (H x) · inv (H x)  ==⟨ ap (_· inv (H x)) (h-naturality H (H x)) ⟩
      ap f (H x) · H x · inv (H x)       ==⟨ ·-assoc (ap f (H x)) _ (inv (H x)) ⟩
      ap f (H x) · (H x · inv (H x))     ==⟨ ap (ap f (H x) ·_) (·-rinv (H x)) ⟩
      ap f (H x) · (idp {a = f x})       ==⟨ inv (·-runit (ap f (H x))) ⟩
      ap f (H x)
    ∎

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
        lemma : (c c' : fib f y) → Σ (fst c == fst c') (λ γ → (ap f γ) · snd c' == snd c) → c == c'
        lemma c c' (p , q) = Σ-bycomponents (p , lemma2)
          where
            lemma2 : transport (λ z → f z == y) p (snd c) == snd c'
            lemma2 =
              begin
                transport (λ z → f z == y) p (snd c)
                  ==⟨ transport-eq-fun-l f p (snd c) ⟩
                inv (ap f p) · (snd c)
                  ==⟨ ap (inv (ap f p) ·_) (inv q) ⟩
                inv (ap f p) · ((ap f p) · (snd c'))
                  ==⟨ inv (·-assoc (inv (ap f p)) (ap f p) (snd c')) ⟩
                inv (ap f p) · (ap f p) · (snd c')
                  ==⟨ ap (_· (snd c')) (·-linv (ap f p)) ⟩
                snd c'
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

    -- Definitions for quasiinverses, left-inverses, right-inverses and
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
        γ1 = rcomp-∼ g (h-simm (h ∘ f) id α)

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
        lemma1 : (a : A) → ap f (η (g (f a))) · ε (f a) == ε (f (g (f a))) · ap f (η a)
        lemma1 a =
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
              ==⟨ ap (inv (ε (f (g (f a)))) ·_) (inv (lemma1 a)) ⟩
            inv (ε (f (g (f a)))) · (ap f (η (g (f a))) · ε (f a))
              ==⟨ inv (·-assoc (inv (ε (f (g (f a))))) _ (ε (f a))) ⟩
            inv (ε (f (g (f a)))) · ap f (η (g (f a))) · ε (f a)
          ∎

    -- Quasiinverses create equivalences.
    qinv-≃ : (f : A → B) → qinv f → A ≃ B
    qinv-≃ f = ishae-≃ ∘ qinv-ishae

    ≃-qinv : A ≃ B → Σ (A → B) qinv
    ≃-qinv eq = lemap eq , (remap eq , (lrmap-inverse-h eq , rlmap-inverse-h eq))

    -- Half-adjoint equivalences are quasiinverses.
    ishae-qinv : {f : A → B} → ishae f → qinv f
    ishae-qinv {f} (hae g η ε τ) = g , (ε , η)

  open Quasiinverses public

  module EquivalenceComposition where

    -- Composition of quasiinverses
    qinv-comp : ∀{ℓ} {A B C : Type ℓ} → Σ (A → B) qinv → Σ (B → C) qinv → Σ (A → C) qinv
    qinv-comp (f , (if , (εf , ηf))) (g , (ig , (εg , ηg))) = (g ∘ f) , ((if ∘ ig) ,
       ( (λ x → ap g (εf (ig x)) · εg x)
       ,  λ x → ap if (ηg (f x)) · ηf x))

    qinv-inv : ∀{ℓ} {A B : Type ℓ} → Σ (A → B) qinv → Σ (B → A) qinv
    qinv-inv (f , (g , (ε , η))) = g , (f , (η , ε))

    -- Composition of equivalences
    idEqv : ∀{ℓ} {A : Type ℓ} → A ≃ A
    idEqv = id , λ a → (a , idp) , λ { (_ , idp) → idp }

    compEqv : ∀{ℓ} {A B C : Type ℓ} → A ≃ B → B ≃ C → A ≃ C
    compEqv {ℓ} {A} {B} {C} eqf eqg = qinv-≃ (fst qcomp) (snd qcomp)
     where
       qcomp : Σ (A → C) qinv
       qcomp = qinv-comp (≃-qinv eqf) (≃-qinv eqg)

    invEqv : ∀{ℓ} {A B : Type ℓ} → A ≃ B → B ≃ A
    invEqv {ℓ} {A} {B} eqf = qinv-≃ (fst qcinv) (snd qcinv)
     where
       qcinv : Σ (B → A) qinv
       qcinv = qinv-inv (≃-qinv eqf)

    -- Lemmas about composition
    compEqv-inv : ∀{ℓ} {A B : Type ℓ} → (α : A ≃ B) → compEqv α (invEqv α) == idEqv
    compEqv-inv {_} {A} {B} α = sameEqv (
     begin
       fst (compEqv α (invEqv α)) ==⟨ idp ⟩
       fst (invEqv α) ∘ fst α     ==⟨ funext (rlmap-inverse-h α) ⟩
       id
     ∎)

  open EquivalenceComposition public

open hott public
\end{code}


Let be `α : A == B`, `a : A`, and `b : B` then the following types are equivalent
to the previous type `HEq₁`.

- \begin{code}
HEq₂ : ∀ {ℓ} (A : Type ℓ)(B : Type ℓ) (α : A == B)(a : A)(b : B) → Type ℓ
HEq₂ A B α a b = Path (coe α a) b
\end{code}

- \begin{code}
HEq₃  : ∀ {ℓ} (A : Type ℓ)(B : Type ℓ) (α : A == B)(a : A)(b : B) → Type ℓ
HEq₃ A B α a b = Path a (coe (inv α) b)
\end{code}

- \begin{code}
HEq₄ : ∀ {ℓ} (A : Type ℓ)(B : Type ℓ) (α : A == B)(a : A)(b : B) → Type ℓ
HEq₄ A .A idp a b = Path a b
\end{code}

\begin{code}
-- data Vec (X : Type) : Type₁ → Type where
  -- something


-- _ : ?
-- _ = Heq (Vec Nat (n + m))

\end{code}

### Equivalences

{: .foldable}
\begin{code}
-- A proof that HEq₁-≃-HEq₂

module _ {ℓ}(A : Type ℓ) (B : Type ℓ) where

  HEq₁-to-HEq₂ : {α : A == B}{a : A}{b : B}
               → HEq₁ A B α a b
               → HEq₂ A B α a b
  HEq₁-to-HEq₂ {idp} {a} {.a} idp = idp

  HEq₂-to-HEq₁ : {α : A == B}{a : A}{b : B}
               → HEq₂ A B α a b
               → HEq₁ A B α a b
  HEq₂-to-HEq₁ {idp} {a} {.a} idp = idp

  HEq₁-≃-HEq₂ : {α : A == B}{a : A}{b : B}
             → HEq₁ A B α a b ≃ HEq₂ A B α a b
  HEq₁-≃-HEq₂ {idp} {a} {b} =
    qinv-≃ HEq₁-to-HEq₂ (HEq₂-to-HEq₁ , HEq₁-~-HEq₂ , HEq₂-~-HEq₁)
    where
      HEq₁-~-HEq₂ : ( p : HEq₂ A B idp a b)
                  → ( HEq₁-to-HEq₂ (HEq₂-to-HEq₁ p ) == p)
      HEq₁-~-HEq₂ idp = idp

      HEq₂-~-HEq₁ : ( p : HEq₁ A B idp a b)
                  → ( HEq₂-to-HEq₁ (HEq₁-to-HEq₂ p ) == p)
      HEq₂-~-HEq₁ idp = idp
\end{code}

{: .foldable}
\begin{code}
-- A proof that HEq₂-≃-HEq₃

module _ {ℓ}(A : Type ℓ) (B : Type ℓ) where

  HEq₂-to-HEq₃ : {α : A == B}{a : A}{b : B}
               → HEq₂ A B α a b
               → HEq₃ A B α a b
  HEq₂-to-HEq₃ {idp}  idp = idp

  HEq₃-to-HEq₂ : {α : A == B}{a : A}{b : B}
               → HEq₃ A B α a b
               → HEq₂ A B α a b
  HEq₃-to-HEq₂ {idp} {a} {.a} idp = idp

  HEq₂-≃-HEq₃ : {α : A == B}{a : A}{b : B}
             → HEq₂ A B α a b ≃ HEq₃ A B α a b
  HEq₂-≃-HEq₃ {idp} {a} {b} =
    qinv-≃ HEq₂-to-HEq₃ (HEq₃-to-HEq₂ , HEq₂-~-HEq₃ , HEq₃-~-HEq₂)
    where
      HEq₂-~-HEq₃ : ( p : HEq₃ A B idp a b)
                  → ( HEq₂-to-HEq₃ (HEq₃-to-HEq₂ p ) == p)
      HEq₂-~-HEq₃ idp = idp

      HEq₃-~-HEq₂ : ( p : HEq₂ A B idp a b)
                  → ( HEq₃-to-HEq₂ (HEq₂-to-HEq₃ p ) == p)
      HEq₃-~-HEq₂ idp = idp
\end{code}

{: .foldable}
\begin{code}
-- A proof that HEq₃-≃-HEq₄

module _ {ℓ}(A : Type ℓ) (B : Type ℓ) where

  HEq₃-to-HEq₄ : {α : A == B}{a : A}{b : B}
               → HEq₃ A B α a b
               → HEq₄ A B α a b
  HEq₃-to-HEq₄ {idp}  idp = idp

  HEq₄-to-HEq₃ : {α : A == B}{a : A}{b : B}
               → HEq₄ A B α a b
               → HEq₃ A B α a b
  HEq₄-to-HEq₃ {idp} {a} {.a} idp = idp

  HEq₃-≃-HEq₄ : {α : A == B}{a : A}{b : B}
             → HEq₃ A B α a b ≃ HEq₄ A B α a b
  HEq₃-≃-HEq₄ {idp} {a} {b} =
    qinv-≃ HEq₃-to-HEq₄ (HEq₄-to-HEq₃ , HEq₃-~-HEq₄ , HEq₄-~-HEq₃)
    where
      HEq₃-~-HEq₄ : ( p : HEq₄ A B idp a b)
                  → ( HEq₃-to-HEq₄ (HEq₄-to-HEq₃ p ) == p)
      HEq₃-~-HEq₄ idp = idp

      HEq₄-~-HEq₃ : ( p : HEq₃ A B idp a b)
                  → ( HEq₄-to-HEq₃ (HEq₃-to-HEq₄ p ) == p)
      HEq₄-~-HEq₃ idp = idp
\end{code}

Finally, we complete the chain of equivalence with `HEq₄-≃-HEq₁`.

{: .foldable}
\begin{code}
-- A proof that HEq₄-to-HEq₁

module _ {ℓ}(A : Type ℓ) (B : Type ℓ) where

  HEq₄-to-HEq₁ : {α : A == B}{a : A}{b : B}
               → HEq₄ A B α a b
               → HEq₁ A B α a b
  HEq₄-to-HEq₁ {idp} idp = idp

  HEq₁-to-HEq₄ : {α : A == B}{a : A}{b : B}
               → HEq₁ A B α a b
               → HEq₄ A B α a b
  HEq₁-to-HEq₄ {idp} {a} {.a} idp = idp

  HEq₄-≃-HEq₁ : {α : A == B}{a : A}{b : B}
             → HEq₄ A B α a b ≃ HEq₁ A B α a b
  HEq₄-≃-HEq₁ {idp} {a} {b} =
    qinv-≃ HEq₄-to-HEq₁ (HEq₁-to-HEq₄ , HEq₄-~-HEq₁ , HEq₁-~-HEq₄)
    where
      HEq₄-~-HEq₁ : ( p : HEq₁ A B idp a b)
                  → ( HEq₄-to-HEq₁ (HEq₁-to-HEq₄ p ) == p)
      HEq₄-~-HEq₁ idp = idp

      HEq₁-~-HEq₄ : ( p : HEq₄ A B idp a b)
                  → ( HEq₁-to-HEq₄ (HEq₄-to-HEq₁ p ) == p)
      HEq₁-~-HEq₄ idp = idp
\end{code}

For the follwing discussion, we may use heterogeneous using the first definition.
\begin{code}
HEq = HEq₁
\end{code}

## Path over a path

Given a type family $$C: A → Type$$ and a path $$α : a₁ = a₂$$, a *pathover* is a
path connecting $$c₁ : C a₁$$ with  $$c₂ : C a₂$$  lying over $$α$$.
types.

% -- TODO
The geometry intuition is a path (x,u)= (y,v) which projects down on to p0
them ΣAC is the total space and "projecting down" means ap proj q = p with proj : ΣAC

% --TODO
The geometry intuition has been formalised by {% cite Licata2015 %}
in five different ways as follows.

% The PathOver is the dependent version of a *path*, what it means that the path
% is between two endpoints from maybe different types. This is of course what we
% saw in the definition of the heterogeneous equality. The difference is that
% we simplify `HEq`  definition with `PathOver` by factorizing the type family
% that is involved in the paths.
%
% We define `PathOver₁` as the inductive family with only one constructor,
% the reflexivity over the reflexivity on the base space `A`. To eliminate this
% type, we can use path-over induction. In Agda, we just do pattern matching along
% the path on the base `A`. Additionaly, we can define this notion of PathOvers in at least
% four different ways. Let us see these definitions, all equivalent. To refer to a pathover,
% we adopt the notation `c₁ == c₂ [ C ↓ α ]` from the HoTT-Agda library.

A more direct formalisation is the type

- \begin{code}
data PathOver₁ {ℓᵢ ℓⱼ} {A : Set ℓᵢ} (C : A → Type ℓⱼ) {a₁ : A} :
      {a₂ : A} (α : a₁ == a₂) (c₁ : C a₁) (c₂ : C a₂) → Type ℓⱼ where
      idp : {c₁ : C a₁} → PathOver₁ C idp c₁ c₁
\end{code}

- \begin{code}
PathOver₂ : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} → (C : A → Type ℓⱼ) {a₁ a₂ : A}
          → (α : a₁ == a₂) (c₁ : C a₁) (c₂ : C a₂) → Type ℓⱼ
PathOver₂ {A = A} C {a₁} {a₂} α c₁ c₂ = HEq (C a₁) (C a₂) (ap C α) c₁ c₂
\end{code}

- \begin{code}
PathOver₃ : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ}(C : A → Type ℓⱼ) {a₁ a₂ : A}
          → (α : a₁ == a₂) (c₁ : C a₁)(c₂ : C a₂) → Type ℓⱼ
PathOver₃ {A = A} C {a₁} {a₂} α c₁ c₂ = transport C α c₁ == c₂
\end{code}

![path](/assets/ipe-images/pathover-3.png)

- \begin{code}
PathOver₄ : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ}(C : A → Type ℓⱼ) {a₁ a₂ : A}
          → (α : a₁ == a₂) (c₁ : C a₁)(c₂ : C a₂) → Type ℓⱼ
PathOver₄ {A = A} C {a₁} {a₂} α c₁ c₂ = c₁ == transport C (inv α) c₂
\end{code}

![path](/assets/ipe-images/pathover-4.png)

- \begin{code}
PathOver₅ : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ}(C : A → Type ℓⱼ) {a₁ a₂ : A}
          → (α : a₁ == a₂) (c₁ : C a₁)(c₂ : C a₂) → Type ℓⱼ
PathOver₅ C idp c₁ c₂ = c₁ == c₂
\end{code}

Notice that above when we used `transport C α c₁`, we could also have used `coe (ap C α)`,
we mention this because in HoTT-Agda library, it's defined `transport` using `coe`.

### Equivalences

{: .foldable}
\begin{code}
-- PathOver₁-≃-PathOver₂

module _ {ℓ} (A : Type ℓ) (C : A → Type ℓ) where

  PathOver₁-to-PathOver₂ : {a₁ a₂ : A} {α : a₁ == a₂} {c₁ : C a₁}{c₂ : C a₂}
         → PathOver₁ C α c₁ c₂
         → PathOver₂ C α c₁ c₂
  PathOver₁-to-PathOver₂ {a₁} {.a₁} {idp} {c₁} {.c₁} idp = idp

  PathOver₂-to-PathOver₁ : {a₁ a₂ : A} {α : a₁ == a₂} {c₁ : C a₁}{c₂ : C a₂}
         → PathOver₂ C α c₁ c₂
         → PathOver₁ C α c₁ c₂
  PathOver₂-to-PathOver₁ {a₁} {.a₁} {idp} {c₁} {.c₁} idp = idp
  --
  PathOver₁-≃-PathOver₂ : {a₁ a₂ : A} {α : a₁ == a₂} {c₁ : C a₁}{c₂ : C a₂}
        → PathOver₁ C α c₁ c₂ ≃ PathOver₂ C α c₁ c₂
  PathOver₁-≃-PathOver₂ {a₁}{.a₁}{idp}{c₁}{c₂} =
    qinv-≃
      PathOver₁-to-PathOver₂
      (PathOver₂-to-PathOver₁
        , PathOver₁~PathOver₅ , PathOver₂~PathOver₁)
    where
      PathOver₁~PathOver₅ : (p : PathOver₂ C idp c₁ c₂)
          → PathOver₁-to-PathOver₂ (PathOver₂-to-PathOver₁ p) == p
      PathOver₁~PathOver₅ idp = idp

      PathOver₂~PathOver₁ : (p : PathOver₁ C idp c₁ c₂)
          → PathOver₂-to-PathOver₁ (PathOver₁-to-PathOver₂ p) == p
      PathOver₂~PathOver₁ idp = idp
\end{code}

{: .foldable}
\begin{code}
-- PathOver₂-≃-PathOver₃

module _ {ℓ} (A : Type ℓ) (C : A → Type ℓ) where

  PathOver₂-to-PathOver₃ : {a₁ a₂ : A} {α : a₁ == a₂} {c₁ : C a₁}{c₂ : C a₂}
         → PathOver₂ C α c₁ c₂
         → PathOver₃ C α c₁ c₂
  PathOver₂-to-PathOver₃ {a₁} {.a₁} {idp} {c₁} {.c₁} idp = idp

  PathOver₃-to-PathOver₂ : {a₁ a₂ : A} {α : a₁ == a₂} {c₁ : C a₁}{c₂ : C a₂}
         → PathOver₃ C α c₁ c₂
         → PathOver₂ C α c₁ c₂
  PathOver₃-to-PathOver₂ {a₁} {.a₁} {idp} {c₁} {.c₁} idp = idp
  --
  PathOver₂-≃-PathOver₃ : {a₁ a₂ : A} {α : a₁ == a₂} {c₁ : C a₁}{c₂ : C a₂}
        → PathOver₂ C α c₁ c₂ ≃ PathOver₃ C α c₁ c₂
  PathOver₂-≃-PathOver₃ {a₁}{.a₁}{idp}{c₁}{c₂} =
    qinv-≃
      PathOver₂-to-PathOver₃
      (PathOver₃-to-PathOver₂
        , PathOver₂~PathOver₅ , PathOver₃~PathOver₂)
    where
      PathOver₂~PathOver₅ : (p : PathOver₃ C idp c₁ c₂)
          → PathOver₂-to-PathOver₃ (PathOver₃-to-PathOver₂ p) == p
      PathOver₂~PathOver₅ idp = idp

      PathOver₃~PathOver₂ : (p : PathOver₂ C idp c₁ c₂)
          → PathOver₃-to-PathOver₂ (PathOver₂-to-PathOver₃ p) == p
      PathOver₃~PathOver₂ idp = idp
\end{code}


{: .foldable}
\begin{code}
-- PathOver₃-≃-PathOver₄

module _ {ℓ} (A : Type ℓ) (C : A → Type ℓ) where

  PathOver₃-to-PathOver₄ : {a₁ a₂ : A} {α : a₁ == a₂} {c₁ : C a₁}{c₂ : C a₂}
         → PathOver₃ C α c₁ c₂
         → PathOver₄ C α c₁ c₂
  PathOver₃-to-PathOver₄ {a₁} {.a₁} {idp} {c₁} {.c₁} idp = idp

  PathOver₄-to-PathOver₃ : {a₁ a₂ : A} {α : a₁ == a₂} {c₁ : C a₁}{c₂ : C a₂}
         → PathOver₄ C α c₁ c₂
         → PathOver₃ C α c₁ c₂
  PathOver₄-to-PathOver₃ {a₁} {.a₁} {idp} {c₁} {.c₁} idp = idp
  --
  PathOver₃-≃-PathOver₄ : {a₁ a₂ : A} {α : a₁ == a₂} {c₁ : C a₁}{c₂ : C a₂}
        → PathOver₃ C α c₁ c₂ ≃ PathOver₄ C α c₁ c₂
  PathOver₃-≃-PathOver₄ {a₁}{.a₁}{idp}{c₁}{c₂} =
    qinv-≃
      PathOver₃-to-PathOver₄
      (PathOver₄-to-PathOver₃
        , PathOver₃~PathOver₅ , PathOver₄~PathOver₃)
    where
      PathOver₃~PathOver₅ : (p : PathOver₄ C idp c₁ c₂)
          → PathOver₃-to-PathOver₄ (PathOver₄-to-PathOver₃ p) == p
      PathOver₃~PathOver₅ idp = idp

      PathOver₄~PathOver₃ : (p : PathOver₃ C idp c₁ c₂)
          → PathOver₄-to-PathOver₃ (PathOver₃-to-PathOver₄ p) == p
      PathOver₄~PathOver₃ idp = idp
\end{code}

{: .foldable}
\begin{code}
-- PathOver₄-≃-PathOver₅
--
-- module _ {ℓ} (A : Type ℓ) (C : A → Type ℓ) where
--
--   PathOver₄-to-PathOver₅ : {a₁ a₂ : A} {α : a₁ == a₂} {c₁ : C a₁}{c₂ : C a₂}
--          → PathOver₄ C α c₁ c₂
--          → PathOver₅ C α c₁ c₂
--   PathOver₄-to-PathOver₅ {a₁} {.a₁} {idp} {c₁} {.c₁} idp = idp
--
--   PathOver₅-to-PathOver₄ : {a₁ a₂ : A} {α : a₁ == a₂} {c₁ : C a₁}{c₂ : C a₂}
--          → PathOver₅ C α c₁ c₂
--          → PathOver₄ C α c₁ c₂
--   PathOver₅-to-PathOver₄ {a₁} {.a₁} {idp} {c₁} {.c₁} idp = idp
--   --
--   PathOver₄-≃-PathOver₅ : {a₁ a₂ : A} {α : a₁ == a₂} {c₁ : C a₁}{c₂ : C a₂}
--         → PathOver₄ C α c₁ c₂ ≃ PathOver₅ C α c₁ c₂
--   PathOver₄-≃-PathOver₅ {a₁}{.a₁}{idp}{c₁}{c₂} =
--     qinv-≃
--       PathOver₄-to-PathOver₅
--       (PathOver₅-to-PathOver₄
--         , PathOver₄~PathOver₅ , PathOver₅~PathOver₄)
--     where
--       PathOver₄~PathOver₅ : (p : PathOver₅ C idp c₁ c₂)
--           → PathOver₄-to-PathOver₅ (PathOver₅-to-PathOver₄ p) == p
--       PathOver₄~PathOver₅ idp = idp
--
--       PathOver₅~PathOver₄ : (p : PathOver₄ C idp c₁ c₂)
--           → PathOver₅-to-PathOver₄ (PathOver₄-to-PathOver₅ p) == p
--       PathOver₅~PathOver₄ idp = idp
\end{code}

{: .foldable}
\begin{code}
-- PathOver₅-≃-PathOver₁
--
-- module _ {ℓ} (A : Type ℓ) (C : A → Type ℓ) where
--
--   PathOver₅-to-PathOver₁ : {a₁ a₂ : A} {α : a₁ == a₂} {c₁ : C a₁}{c₂ : C a₂}
--          → PathOver₅ C α c₁ c₂
--          → PathOver₁ C α c₁ c₂
--   PathOver₅-to-PathOver₁ {a₁} {.a₁} {idp} {c₁} {.c₁} idp = idp
--
--   PathOver₁-to-PathOver₅ : {a₁ a₂ : A} {α : a₁ == a₂} {c₁ : C a₁}{c₂ : C a₂}
--          → PathOver₁ C α c₁ c₂
--          → PathOver₅ C α c₁ c₂
--   PathOver₁-to-PathOver₅ {a₁} {.a₁} {idp} {c₁} {.c₁} idp = idp
--   --
--   PathOver₅-≃-PathOver₁ : {a₁ a₂ : A} {α : a₁ == a₂} {c₁ : C a₁}{c₂ : C a₂}
--         → PathOver₅ C α c₁ c₂ ≃ PathOver₁ C α c₁ c₂
--   PathOver₅-≃-PathOver₁ {a₁}{.a₁}{idp}{c₁}{c₂} =
--     qinv-≃
--       PathOver₅-to-PathOver₁
--       (PathOver₁-to-PathOver₅
--         , PathOver₅~PathOver₁ , PathOver₁~PathOver₅)
--     where
--       PathOver₅~PathOver₁ : (p : PathOver₁ C idp c₁ c₂)
--           → PathOver₅-to-PathOver₁ (PathOver₁-to-PathOver₅ p) == p
--       PathOver₅~PathOver₁ idp = idp
--
--       PathOver₁~PathOver₅ : (p : PathOver₅ C idp c₁ c₂)
--           → PathOver₁-to-PathOver₅ (PathOver₅-to-PathOver₁ p) == p
--       PathOver₁~PathOver₅ idp = idp
\end{code}

We prefer the third definition for pathovers that comes from the HoTT book, that is,
PathOver defined by an inductive family. Nevertheless, in the following definition,
the reader can change the subindex of the `PathOver` word to use any other definition.

\begin{code}
PathOver = PathOver₁

infix 30 PathOver
syntax PathOver C α c₁ c₂ = c₁ == c₂ [ C ↓ α ]
\end{code}

> While we have motivated PathOver as a factored heterogeneous equality, there
> is also a geometric intuition. **Dependent types correspond to fibrations**, so a
> type `C : A → Type` can be pictured as its total space `∑ a:A . C` a projecting
> down to `A` by first projection.

> A **path-over** `γ : PathOver C α c­₁ c₂` represents a path σ in `∑ a:A . C` a
> a between `(a₁, c₁)` and `(a₂,c₂)`, such that ap fst σ is exactly `α`. That
> is, it is a path in the total space that projects down to, or lies over, `α`
> (path pairing `pair= α γ` will be made precise below).


\begin{code}
-- An extra and useful function:
-- to make dependent pairs
pair= : ∀ {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {C : A → Type ℓⱼ}
  {a₁ a₂ : A} {c₁ : C a₁} {c₂ : C a₂}
  → (α : a₁ == a₂)
  → (γ : c₁ == c₂ [ C ↓ α ])

  → (a₁ , c₁) == (a₂ , c₂)
pair= idp idp = ap (_ ,_) idp
\end{code}

## Total spaces

We want to prove the following lemma:

**Lemma.** Let be `A : Type` and `C : A → Type` with two terms `a₁ a₂ : A` and a
path between them `α : a₁ == a₂`. If  `c₁ : C a₁`, `c₂ : C a₂` then there is an
correspondence between a term in the total space and the pathover between c₁ and c₁
along the path `α`.

<p class="equation">
$$
 \sum\limits_{(a₁ , c₁) = (a₂ , c₂)} \ (\mathsf{ap}~\mathsf{fst}~q~= \alpha)
  \simeq \mathsf{PathOver}~C~α~c₁~c₂.
$$
</p>

To show such a equivalence, we proceed defining the functions back and forth,
the two homotopies associated to these functions with the identity and finally,
we prove the equivalence using the quasiinverse version for the equivalence type.

- Let us define the function `Σ-to-==[↓]` that maps a term of the sigma type to
a pathover. This construction is using Σ-induction followed by two
path-induction on the identity types from the components.

\begin{code}
module _ {ℓᵢ ℓⱼ}{A : Type ℓᵢ}{C : A → Type ℓⱼ}{a₁ a₂ : A} where
\end{code}

\begin{code}
-- Def.
  Σ-to-==[↓] : {α : a₁ == a₂}{c₁ : C a₁}{c₂ : C a₂}
    → Σ ((a₁ , c₁) == (a₂ , c₂)) (λ q → (ap fst q) == α)
    → c₁ == c₂ [ C ↓  α ]
  Σ-to-==[↓] (idp , idp) = idp

\end{code}

- The inverse function to the previous one is `==[↓]-to-Σ`, which sends
  pathovers to a dependent pair as it follows. Its construction is by using
  path-induction on `α` in the base space, follows by path-induction on `γ`. The
  goal after this becomes in a pair of two reflexivity proofs `(a₁ , c₁) == (a₁
  , c₁)` and `(a₁ == a₁) == (a₁ == a₁)`.

\begin{code}
-- Def.
  ==[↓]-to-Σ : {α : a₁ == a₂}{c₁ : C a₁}{c₂ : C a₂}
    → (γ : c₁ == c₂ [ C ↓ α ])
    → Σ ((a₁ , c₁) == (a₂ , c₂)) (λ q → (ap fst q) == α)
  ==[↓]-to-Σ {idp} idp = (idp , idp)

  -- -- more explict:
  -- ==[↓]-to-Σ {idp}{c₁}{c₂} idp = (idp {a = (a₁ , c₁)}, idp {a = idp {a = a₁}})

  -- -- Alternative way to construct this function is (also type-checked):
  -- ==[↓]-to-Σ {α = α} γ = (pair= α γ , ap-fst-pair= α γ)
  --   where
  --
  --   ap-fst-pair= : (α : a₁ == a₂)
  --       → {c₁ : C a₁}{c₂ : C a₂} (γ : c₁ == c₂ [ C ↓ α ] )
  --       → ap fst (pair= α γ) == α
  --   ap-fst-pair= idp idp = idp
\end{code}

The respective homotopies

\begin{code}
-- Homotopies
  Σ-to-==[↓]∘==[↓]-to-Σ∼id
    : {α : a₁ == a₂}{c₁ : C a₁}{c₂ : C a₂}
    → (γ : c₁ == c₂ [ C ↓ α ])
    → Σ-to-==[↓] {α = α} (==[↓]-to-Σ γ) == γ
  Σ-to-==[↓]∘==[↓]-to-Σ∼id {α = idp} idp = idp

  ==[↓]-to-Σ∘Σ-to-==[↓]∼id
    : {α : a₁ == a₂}{c₁ : C a₁}{c₂ : C a₂}
    → (pair : Σ ((a₁ , c₁) == (a₂ , c₂)) (λ q → (ap fst q) == α))
    → ==[↓]-to-Σ (Σ-to-==[↓] pair) == pair
  ==[↓]-to-Σ∘Σ-to-==[↓]∼id (idp , idp) = idp
\end{code}

Finally, we show the equivalence using the fact above proved.

\begin{code}
-- Equivalence
  Σ-≃-==[↓] : {α : a₁ == a₂}{c₁ : C a₁}{c₂ : C a₂}
    → (Σ ((a₁ , c₁) == (a₂ , c₂)) (λ q → (ap fst q) == α))
    ≃ (c₁ == c₂ [ C ↓ α ])

  Σ-≃-==[↓] =
    qinv-≃
      Σ-to-==[↓]    -- equivalence
      ((==[↓]-to-Σ  -- inverse
      , (Σ-to-==[↓]∘==[↓]-to-Σ∼id , ==[↓]-to-Σ∘Σ-to-==[↓]∼id))) -- homotopies
\end{code}


## Other facts

We can build a dependent path by applying a depedent function to a homogeneous path.

\begin{code}
apdo : ∀ {ℓ} {A : Type ℓ} {B : A → Type ℓ} (f : (a : A) → B a)
      {a₁ a₂ : A} → (α : a₁ == a₂) → (PathOver B α (f a₁) (f a₂))
apdo f idp = idp
\end{code}

## Extra

- **Lemma 1**. If $$A: U$$ and $$P: A → U$$ and $$f: A' \simeq A$$, then
$$\sum_A P \simeq \sum_{A'} (P ∘ f)$$.

- **Lemma 2.** If $$A: U$$ and $$P: A → U$$ and $$a: A$$,
then $$\sum_{(w:\sum_{A} P)}  \(\mathsf{fst } w = a) \simeq Pa$$

The previous fact can also seen as a case of the following lemma.
If `A : Type` and `C : A → Type`, we can show that:

\begin{code}
module _ {ℓᵢ}{ℓⱼ} {A : Type ℓᵢ}{P : A → Type ℓⱼ} where

  l→ : {B : Type ℓᵢ}
      → (e : B ≃ A)
      → Σ A P
      -----
      → Σ B (λ b → P ((lemap e) b))
  l→ {B} e (a , pₐ) = f⁻¹ a , p'
    where
      f : B → A
      f = lemap e

      f⁻¹ : A → B
      f⁻¹ = remap e

      equalsPs : P a  == P (f (f⁻¹ a))
      equalsPs = ap P (inv (lrmap-inverse e))

      p' : P (f (f⁻¹ a))
      p' = coe equalsPs pₐ

  l← : {B : Type ℓᵢ}
      → (e : B ≃ A)
      → Σ B (λ b → P ((lemap e) b))
      -----
      → Σ A P
  l← {B} e (b , p) = (lemap e) b , p

  l→∘l←-~-id : {B : Type ℓᵢ}
          → (e : B ≃ A)
          → (pΣbP' : Σ B (λ b → P ((fst e) b)) )
          → l→ e (l← e pΣbP') == pΣbP'
  l→∘l←-~-id (f , eqf) p =
    Σ-bycomponents
      ((begin {!   !}
          ==⟨ {!   !} ⟩
            {!   !}
          ==⟨ {!   !} ⟩
            ({!   !} ∎)) , {!   !})
  --
  l←∘l→-~-id : {B : Type ℓᵢ}
          → (e : B ≃ A)
          → (pΣaP : Σ A P)
          → l← e (l→ e pΣaP) == pΣaP
  l←∘l→-~-id e (b , p) = Σ-bycomponents ({!   !} , {!   !})
  --
  --
  -- lemma : {B : Type ℓᵢ} → (e : B ≃ A) → Σ A P ≃ Σ B (λ b → P ((fst e) b))
  -- lemma {B} e = qinv-≃ (l→ e) (l← e , l→∘l←-~-id e , {!   !})
\end{code}


Using Univalence axiom:

{: .foldable}
\begin{code}
module Univalence where

  -- Voevodsky's Univalence Axiom.
  module UnivalenceAxiom {ℓ} {A B : Type ℓ} where
    idtoeqv : A == B → A ≃ B
    idtoeqv p = qinv-≃
      (transport (λ x → x) p)
      (transport (λ x → x) (inv p) , (transport-inv-l p , transport-inv-r p))

    -- The Univalence axiom induces an equivalence between equalities
    -- and equivalences.
    postulate axiomUnivalence : isEquiv idtoeqv
    eqvUnivalence : (A == B) ≃ (A ≃ B)
    eqvUnivalence = idtoeqv , axiomUnivalence

    -- Introduction rule for equalities.
    ua : A ≃ B → A == B
    ua = remap eqvUnivalence

    -- Computation rules
    ua-β : (eqv : A ≃ B) → idtoeqv (ua eqv) == eqv
    ua-β eqv = lrmap-inverse eqvUnivalence

    ua-η : (p : A == B) → ua (idtoeqv p) == p
    ua-η p = rlmap-inverse eqvUnivalence
  open UnivalenceAxiom public
open Univalence public
\end{code}

\begin{code}
module _ {ℓᵢ}{ℓⱼ} {A : Type ℓᵢ}{P : A → Type ℓⱼ} where


  lemma : {B : Type ℓᵢ} → (e : B ≃ A) → Σ A P ≃ Σ B (λ b → P ((fst e) b))
  lemma {B} e = qinv-≃ {! f  !} {!   !}
    where
      α : A == B
      α = inv (ua e)

      f :  Σ A P → Σ B (λ b → P ((fst e) b))
      f (a , p) = {!   !} , {!   !}

\end{code}

{: .references}

  - https://github.com/HoTT/HoTT-Agda/

  - https://mroman42.github.io/ctlc/agda-hott/Total.html
