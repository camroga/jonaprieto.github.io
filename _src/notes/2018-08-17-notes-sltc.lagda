---
layout: "post"
title: "Simple Typed Lambda Calculus"
date: "2018-08-17"
categories: type-theory
toc: true
agda: true
latex: true
---

We present a formalisation of the syntax in Agda for the *Simple Typed Lambda
Calculus (STLC)* with some of its properties and the description of the
type-checking for this type system. We refactor the implementation by
[@gergoerdi](https://github.com/gergoerdi/stlc-agda/) for this calculus,
in particular the [Scopecheck](https://github.com/jonaprieto/stlctalk/blob/master/src/Scopecheck.agda)
and [Typecheck](https://github.com/jonaprieto/stlctalk/blob/master/src/Typecheck.agda) module.

The following source code tested with:

- Agda v2.5.4
- Agda Standard Library v0.16

The original content was firstly exposed at EAFIT in Seminar of Logic:

  - [Slides](https://github.com/jonaprieto/stlctalk/raw/master/slides/slides.pdf).
  - Repository: [https://github.com/jonaprieto/stlctalk](https://github.com/jonaprieto/stlctalk).

{: .foldable }
\begin{code}
-- Agda Imports

open import Data.String using (String)
open import Relation.Nullary.Decidable using (False)
open import Relation.Binary using (IsDecEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

\end{code}

### Syntax

First definition of Typed Lambda Calculus

\begin{code}
Name : Set
Name = String

module Syntax (Type : Set) where

  data Formal : Set where
    _∶_ : Name → Type → Formal

  data Expr : Set where
    var : Name   → Expr
    lam : Formal → Expr → Expr
    _∙_ : Expr   → Expr → Expr

  infixl 20 _∙_
\end{code}

#### Examples

\begin{code}

  private
    postulate
      A : Type

    x = var "x"
    y = var "y"
    z = var "z"

    -- λ(x:A).x
    I : Expr
    I = lam ("x" ∶ A) x

    -- λ(x,y:A).x
    K : Expr
    K = lam ("x" ∶ A) (lam ("y" ∶ A) x)

    -- λ(x,y,z:A).xz(yz)
    S : Expr
    S =
      lam ("x" ∶ A)
        (lam ("y" ∶ A)
          (lam ("z" ∶ A)
            ((x ∙ z) ∙ (y ∙ z))))
\end{code}

### Bound

Lambda terms using De Bruijn indexes.

\begin{code}

module Bound (Type : Set) where

  open import Data.Nat    hiding (_≟_)
  open import Data.Fin    using (Fin; #_; suc)
  open import Data.String using (_≟_)
  open import Data.Vec    using (Vec; _∷_; [])

  module S = Syntax Type
  open S hiding (Expr; module Expr) public
\end{code}

Syntax using indexes.

\begin{code}

  data Expr (n : ℕ) : Set where
    var : Fin n  → Expr n
    lam : Type   → Expr (suc n) → Expr n
    _∙_ : Expr n → Expr n       → Expr n

  infixl 20 _∙_

  -- The context for variables: vector of fixed length
  -- of strings.
  Binder : ℕ → Set
  Binder = Vec Name

  infixl 5 _,_
  _,_ : ∀ {n} → Binder n → Name → Binder (suc n)
  Γ , x = x ∷ Γ

  infixl 3 _⊢_⇝_
  data _⊢_⇝_ : ∀ {n} → Binder n → S.Expr → Expr n → Set where

    var-zero
      : ∀ {n x} {Γ : Binder n}
      ---------------------------
      → Γ , x ⊢ var x ⇝ var (# 0)

    var-suc
      : ∀ {n x y k} {Γ : Binder n} {p : False (x ≟ y)}
      → Γ ⊢ var x ⇝ var k
      -----------------------------
      → Γ , y ⊢ var x ⇝ var (suc k)

    lam
      : ∀ {n x A t t'} {Γ : Binder n}
      → Γ , x ⊢ t ⇝ t'
      ------------------------------
      → Γ ⊢ lam (x ∶ A) t ⇝ lam A t'

    _∙_
      : ∀ {n t₁ t₁' t₂ t₂'} {Γ : Binder n}
      → Γ ⊢ t₁ ⇝ t₁'
      → Γ ⊢ t₂ ⇝ t₂'
      -------------------------
      → Γ ⊢ t₁ ∙ t₂ ⇝ t₁' ∙ t₂'
\end{code}

#### Examples

\begin{code}
  private
    ∅ : Binder 0
    ∅ = []

    Γ : Binder 2
    Γ = [] , "x" , "y"

    e1 : Γ ⊢ var "x" ⇝ var (# 1)
    e1 = var-suc var-zero

    postulate A : Type

    I : [] ⊢ lam ("x" ∶ A) (var "x")
           ⇝ lam A (var (# 0))
    I = lam var-zero

    K : [] ⊢ lam ("x" ∶ A) (lam ("y" ∶ A) (var "x"))
           ⇝ lam A (lam A (var (# 1)))
    K = lam (lam (var-suc var-zero))

    K₂ : [] ⊢ lam ("x" ∶ A) (lam ("y" ∶ A) (var "y"))
            ⇝ lam A (lam A (var (# 0)))
    K₂ = lam (lam var-zero)

    P : Γ ⊢ lam ("x" ∶ A) (lam ("y" ∶ A) (lam ("z" ∶ A) (var "x")))
           ⇝ lam A (lam A (lam A (var (# 2))))
    P = lam (lam (lam (var-suc (var-suc var-zero))))
\end{code}

### Scopecheck

Check representation of λ-terms using de Bruijn indexes.
Get a λ-term using de Bruijn indexes by given a λ-term with names.

{: .foldable }
\begin{code}
-- ∃-syntax and ∄-syntax

open import Data.Product hiding (∃-syntax; ∄-syntax) renaming (_,_ to _-by-_)
open import Data.Product using (∃; ∄)

∃-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set _
∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∄-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set _
∄-syntax = ∄
syntax ∄-syntax (λ x → B) = ∄[ x ] B
\end{code}

{: .foldable }
\begin{code}

module Scopecheck (Type : Set) where

  open Bound Type public

  open import Data.Fin     using (Fin; suc; #_)
  open import Data.Nat     hiding (_≟_)
  open import Data.String  using (_≟_)
  open import Data.Sum     using (_⊎_; inj₁ ; inj₂)
  open import Data.Vec     using (Vec; []; _∷_)

  open import Function     using (_$_)

  open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
  open import Relation.Nullary                      using (Dec; no; yes)
  open import Relation.Nullary.Decidable
    using (fromWitnessFalse; fromWitness; toWitness; True)
\end{code}

\begin{code}

  name-dec
    : ∀ {n} {Γ : Binder n} {x y : Name} {t : Expr (suc n)}
    → Γ , y ⊢ var x ⇝ t
    ----------------------------------
    → x ≡ y ⊎ ∃[ t′ ] (Γ ⊢ var x ⇝ t′)

  name-dec var-zero = inj₁ refl
  name-dec {t = var (suc k)} (var-suc w) = inj₂ (var k -by- w)
                                  --  ↪ witness
\end{code}


\begin{code}

  ⊢subst
    : ∀ {n} {x y} {Γ : Binder n} {t}
     → x ≡ y
     → Γ , x ⊢ var x ⇝ t
     -------------------
     → Γ , y ⊢ var x ⇝ t

  ⊢subst {n}{x}{y}{Γ}{t} x≡y Γ,x⊢varx⇝t
   = subst (λ z → Γ , z ⊢ var x ⇝ t) x≡y Γ,x⊢varx⇝t
\end{code}

\begin{code}
  find-name
    : ∀ {n}
    → (Γ : Binder n) → (x : Name)
    ------------------------------
    → Dec (∃[ t ] (Γ ⊢ var x ⇝ t))

  -- By induction on the variable context:
  find-name [] x = no helper
    where
      helper : ∄[ t ] ([] ⊢ var x ⇝ t)
      helper (_ -by- ())

  find-name (y ∷ Γ) x
    with x ≟ y
  ...  | yes x≡y = yes (var (# 0) -by- ⊢subst x≡y var-zero)
  ...  | no  x≢y
       with find-name Γ x
          -- case analysis for the output of the recursion
  ...     | yes (lam _ _ -by- ())
  ...     | yes (_ ∙ _   -by- ())
  ...     | yes (var k -by- Γ⊢x⇝vark)
            = yes $ var (suc k) -by- var-suc {p = fromWitnessFalse x≢y} Γ⊢x⇝vark
  ...     | no ∄t⟨Γ⊢varx⇝t⟩ = no helper
          where
            helper : ∄[ t ] (Γ , y ⊢ var x ⇝ t)
            helper (t -by- Γ,y⊢varx⇝t)
              with name-dec Γ,y⊢varx⇝t
            ...  | inj₁ x≡y                    = x≢y x≡y
            ...  | inj₂ p@(t′ -by- Γ⊢varx⇝t′) = ∄t⟨Γ⊢varx⇝t⟩ p
\end{code}

We want to determine if given a variable context and a term,
it is possible to find its encoding using De Bruijn indexes.
If so, we got its respective construction for that lambda term.

\begin{code}
  check
    : ∀ {n}
    → (Γ : Binder n)
    → (t : S.Expr)
    → Dec (∃[ t′ ] (Γ ⊢ t ⇝ t′))

  -- By induction on the term syntax.
  check Γ (var x) = find-name Γ x
  check Γ (lam (x ∶ τ) t)
    with check (Γ , x) t                          -- TODO: under revision.
  ...  | yes (t′ -by- Γ,x⊢t⇝t′)
         = yes (lam τ t′ -by- lam Γ,x⊢t⇝t′)
  ...  | no ∄t′⟨Γ,x⊢t⇝t′⟩ = no helper
       where
         helper : ∄[ t′ ] (Γ ⊢ lam (x ∶ τ) t ⇝ t′)
         helper (var x′ -by- ())
         helper (_ ∙ _  -by- ())
         helper (lam .τ t′ -by- lam Γ,x⊢t⇝t′)
           = ∄t′⟨Γ,x⊢t⇝t′⟩ (t′ -by- Γ,x⊢t⇝t′)

  check Γ (t₁ ∙ t₂)
    with check Γ t₁ | check Γ t₂
  ...  | yes (t₁′ -by- Γ⊢t₁⇝t₁′) | (yes (t₂′ -by- Γ⊢t₂⇝t₂′))
         = yes (t₁′ ∙ t₂′ -by- Γ⊢t₁⇝t₁′ ∙ Γ⊢t₂⇝t₂′)
  ...  | yes (t₁′ -by- Γ⊢t₁⇝t₁′) | (no ∄t⟨Γ⊢t₂⇝t⟩) = no helper
       where
         appʳ : ∀ {n} {Γ : Binder n} {t₁ t₂ t₁′ t₂′}
              → Γ ⊢ t₁ ∙ t₂ ⇝ t₁′ ∙ t₂′
              → Γ ⊢ t₂ ⇝ t₂′
         appʳ (_ ∙ Γ⊢t₂⇝t₂′) = Γ⊢t₂⇝t₂′

         helper : ∄[ t ] (Γ ⊢ t₁ ∙ t₂ ⇝ t)
         helper (var _ -by- ())
         helper (lam _ _ -by- ())
         helper (t₁″ ∙ t₂″ -by- Γ⊢t₁∙t₂⇝t)
           = ∄t⟨Γ⊢t₂⇝t⟩ (t₂″ -by- appʳ Γ⊢t₁∙t₂⇝t)

  ... | no ∄t⟨Γ⊢t₁⇝t⟩  | _ = no helper
      where
        appˡ : ∀ {n} {Γ : Binder n} {t₁ t₂ t₁′ t₂′}
          → Γ ⊢ t₁ ∙ t₂ ⇝ t₁′ ∙ t₂′
          → Γ ⊢ t₁ ⇝ t₁′
        appˡ (Γ⊢t₁⇝t₁′ ∙ _) = Γ⊢t₁⇝t₁′

        helper : ∄[ t₁′ ] (Γ ⊢ (t₁ ∙ t₂) ⇝ t₁′)
        helper (var _ -by- ())
        helper (lam _ _ -by- ())
        helper (t₁″ ∙ t₂″ -by- Γ⊢t₁∙t₂⇝t)
          = ∄t⟨Γ⊢t₁⇝t⟩ (t₁″ -by- appˡ Γ⊢t₁∙t₂⇝t)

  -- Go from a representation that uses Names to one that uses de Bruijn indices
  scope : (t : S.Expr) → {p : True (check [] t)} → Expr 0
  scope t {p} = proj₁ (toWitness p)
\end{code}

#### Examples

\begin{code}

  private

  -- postulate
  --   A : Type

  -- I₁ : S.Expr
  -- I₁ = S.lam ("x" ∶ A) (S.var "x")

  -- open import Data.Unit

  -- I : Expr 0
  -- I = scope I₁ {p = ⊤.tt}

    postulate A : Type
    x : S.Expr
    x = var "x"

    y : S.Expr
    y = var "y"

    z : S.Expr
    z = var "z"

    S₁ : S.Expr
    S₁ =
      lam ("x" ∶ A)
        (lam ("y" ∶ A)
        (lam ("z" ∶ A)
        ((x ∙ z) ∙ (y ∙ z))))

    w = check [] S₁
    -- S = scope S₁ {p = ⊤.tt}
\end{code}


### Typing

Type system and its derivation rules.

\begin{code}
module Typing (U : Set) where

  data Type : Set where
    base : U    → Type
    _↣_  : Type → Type → Type

  open Bound Type hiding (_,_)

  open import Data.Nat using (ℕ; suc)
  open import Data.Vec using (Vec; _∷_; lookup; [])
  open import Data.Fin using (Fin; #_)


  Ctxt : ℕ → Set
  Ctxt = Vec Type

  _,_ : ∀ {n} → Ctxt n → Type → Ctxt (suc n)
  Γ , x = x ∷ Γ

  infixl 20 _,_

  data _⊢_∶_ : ∀ {n} → Ctxt n → Expr n → Type → Set where
    tVar : ∀ {n Γ} {x : Fin n}
         → Γ ⊢ var x ∶ lookup x Γ

    tLam : ∀ {n} {Γ : Ctxt n} {t} {τ τ′}
         → Γ , τ ⊢ t ∶ τ′
         → Γ ⊢ lam τ t ∶ τ ↣ τ′

    _∙_  : ∀ {n} {Γ : Ctxt n} {t₁ t₂} {τ τ′}
         → Γ ⊢ t₁ ∶ τ ↣ τ′
         → Γ ⊢ t₂ ∶ τ
         → Γ ⊢ t₁ ∙ t₂ ∶ τ′

  infixr 30 _↣_
  infixl 20 _∙_
  infixl 20 _⊢_∶_
\end{code}

#### Examples

\begin{code}
  private
    postulate
      Bool : Type

    ex : [] , Bool ⊢ var (# 0) ∶ Bool
    ex = tVar

    ex2 : [] ⊢ lam Bool (var (# 0)) ∶ Bool ↣ Bool
    ex2 = tLam tVar

    postulate
      Word : Type
      Num  : Type

    K : [] ⊢ lam Word (lam Num (var (# 1))) ∶ Word ↣ Num ↣ Word
    K = tLam (tLam tVar)

    postulate
      A : Type
      B : Type
      C : Type

    -- S : [] ⊢ lam (A ↣ (B ↣ C))
    --              (lam (A ↣ B)
    --                   (lam A
    --                     ((var (# 2)) ∙ (var (# 0))) ∙ ((var (# 1)) ∙ (var (# 0))) ))
    --        ∶ (A ↣ (B ↣ C)) ↣ (A ↣ B) ↣ A ↣ C
    -- S = tLam (tLam ((tLam ({! tVar  !} ∙ {!   !})) ∙ ({! tVar  !} ∙ {!   !}))) --  tLam (tLam (tLam ((tVar ∙ tVar) ∙ (tVar ∙ tVar))))
\end{code}

## Type-checking

\begin{code}
module Typecheck {U : Set} (UEq : IsDecEquivalence {A = U} _≡_) where

  ------------------------------------------------------------------------------

  open IsDecEquivalence UEq using (_≟_)

  open Typing U
    using (Type; base; _↣_; _⊢_∶_; Ctxt; tVar; tLam; _∙_)
  open Bound Type

  open import Data.Nat      hiding (_≟_)
  open import Data.Product  hiding (∃-syntax; ∄-syntax) renaming (_,_ to _-by-_)
  open import Data.Product  using (∃; ∄)
  open import Data.Vec      using (Vec; _∷_; lookup)

  open import Function         using (_∘_; _$_)
  open import Relation.Binary.PropositionalEquality
    using (refl; cong; cong₂; sym)
  open import Relation.Nullary using (Dec; yes; no; ¬_)

  ------------------------------------------------------------------------------

  -- Equality between Types.
  _T≟_ : (τ τ′ : Type) → Dec (τ ≡ τ′)

  base A T≟ base B with A ≟ B
  ... | yes A≡B = yes (cong base A≡B)
  ... | no  A≢B = no (A≢B ∘ helper)
    where
      helper : base A ≡ base B → A ≡ B
      helper refl = refl
  base A T≟ (_ ↣ _) = no (λ ())

  (τ₁ ↣ τ₂) T≟ base B = no (λ ())
  (τ₁ ↣ τ₂) T≟ (τ₁′ ↣ τ₂′) with τ₁ T≟ τ₁′
  ... | no  τ₁≢τ₁′ = no (τ₁≢τ₁′ ∘ helper)
    where
      helper :  τ₁ ↣ τ₂ ≡ τ₁′ ↣ τ₂′ → τ₁ ≡ τ₁′
      helper refl = refl

  ... | yes τ₁≡τ₁′ with τ₂ T≟ τ₂′
  ...            | yes τ₂≡τ₂′ = yes (cong₂ _↣_ τ₁≡τ₁′ τ₂≡τ₂′)
  ...            | no  τ₂≢τ₂′ = no (τ₂≢τ₂′ ∘ helper)
    where
      helper : τ₁ ↣ τ₂ ≡ τ₁′ ↣ τ₂′ → τ₂ ≡ τ₂′
      helper refl = refl


  ⊢-inj : ∀ {n Γ} {t : Expr n} → ∀ {τ σ}
        → Γ ⊢ t ∶ τ
        → Γ ⊢ t ∶ σ
        → τ ≡ σ
  ⊢-inj tVar tVar = refl
  ⊢-inj {t = lam τ t} (tLam Γ,τ⊢t:τ′) (tLam Γ,τ⊢t:τ″)
    = cong (_↣_ τ) (⊢-inj Γ,τ⊢t:τ′ Γ,τ⊢t:τ″)
  ⊢-inj (Γ⊢t₁:τ↣τ₂ ∙ Γ⊢t₂:τ) (Γ⊢t₁:τ₁↣σ ∙ Γ⊢t₂:τ₁)
    = helper (⊢-inj Γ⊢t₁:τ↣τ₂ Γ⊢t₁:τ₁↣σ)
    where
      helper : ∀ {τ τ₂ τ₁ σ} → (τ ↣ τ₂ ≡ τ₁ ↣ σ) → τ₂ ≡ σ
      helper refl = refl

  -- Typability.
  infer : ∀ {n} Γ (t : Expr n) → Dec (∃[ τ ] (Γ ⊢ t ∶ τ))

  -- Var case.
  infer Γ (var x) = yes (lookup x Γ -by- tVar)

  -- Abstraction case.
  infer Γ (lam τ t) with infer (τ ∷ Γ) t
  ... | yes (σ -by- Γ,τ⊢t:σ) = yes (τ ↣ σ -by- tLam Γ,τ⊢t:σ)
  ... | no  Γ,τ⊬t:σ = no helper
    where
      helper : ∄[ τ′ ] (Γ ⊢ lam τ t ∶ τ′)
      helper (base A -by- ())
      helper (.τ ↣ σ -by- tLam Γ,τ⊢t:σ) = Γ,τ⊬t:σ (σ -by- Γ,τ⊢t:σ)

  -- Application case.
  infer Γ (t₁ ∙ t₂) with infer Γ t₁ | infer Γ t₂
  ... | no  ∄τ⟨Γ⊢t₁:τ⟩ | _ = no helper
      where
        helper : ∄[ σ ] (Γ ⊢ t₁ ∙ t₂ ∶ σ)
        helper (τ -by- Γ⊢t₁:τ ∙ _) = ∄τ⟨Γ⊢t₁:τ⟩ (_ ↣ τ -by- Γ⊢t₁:τ)

  ... | yes (base x -by- Γ⊢t₁:base) | _ = no helper
      where
        helper : ∄[ σ ] (Γ ⊢ t₁ ∙ t₂ ∶ σ)
        helper (τ -by- Γ⊢t₁:_↣_ ∙ _)
          with ⊢-inj Γ⊢t₁:_↣_ Γ⊢t₁:base
        ...  | ()

  ... | yes (τ₁ ↣ τ₂ -by- Γ⊢t₁:τ₁↣τ₂) | no  ∄τ⟨Γ⊢t₂:τ⟩ = no helper
      where
        helper : ∄[ σ ] (Γ ⊢ t₁ ∙ t₂ ∶ σ)
        helper (τ -by- Γ⊢t₁:τ₁′↣τ₂′ ∙ Γ⊢t₂:τ)
          with ⊢-inj Γ⊢t₁:τ₁↣τ₂ Γ⊢t₁:τ₁′↣τ₂′
        ...  | refl = ∄τ⟨Γ⊢t₂:τ⟩ (τ₁ -by- Γ⊢t₂:τ)

  ... | yes (τ₁ ↣ τ₂ -by- Γ⊢t₁:τ₁↣τ₂) | yes (τ₁′ -by- Γ⊢t₂:τ₁′)
      with τ₁ T≟ τ₁′
  ...  | yes τ₁≡τ₁′ = yes (τ₂ -by- Γ⊢t₁:τ₁↣τ₂ ∙ helper)
       where
         helper : Γ ⊢ t₂  ∶ τ₁
         helper = subst (_⊢_∶_ Γ t₂) (sym τ₁≡τ₁′) Γ⊢t₂:τ₁′
  ...  | no  τ₁≢τ₁′ = no helper
       where
         helper : ∄[ σ ] (Γ ⊢ t₁ ∙ t₂ ∶ σ)
         helper (_ -by- Γ⊢t₁:τ↣τ₂ ∙ Γ⊢t₂:τ₁)
           with ⊢-inj  Γ⊢t₁:τ↣τ₂ Γ⊢t₁:τ₁↣τ₂
         ...  | refl = τ₁≢τ₁′ (⊢-inj Γ⊢t₂:τ₁ Γ⊢t₂:τ₁′)


  -- Type-checking.
  check : ∀ {n} Γ (t : Expr n) → ∀ τ → Dec (Γ ⊢ t ∶ τ)

  -- Var case.
  check Γ (var x) τ with lookup x Γ T≟ τ
  ... | yes refl = yes tVar
  ... | no ¬p    = no (¬p ∘ ⊢-inj tVar)

  -- Abstraction case.
  check Γ (lam τ t) (base A) = no (λ ())
  check Γ (lam τ t) (τ₁ ↣ τ₂) with τ₁ T≟ τ
  ... | no τ₁≢τ = no (τ₁≢τ ∘ helper)
      where
        helper : Γ ⊢ lam τ t ∶ (τ₁ ↣ τ₂) → τ₁ ≡ τ
        helper (tLam t) = refl

  ... | yes refl with check (τ ∷ Γ) t τ₂
  ...               | yes Γ,τ⊢t:τ₂ = yes (tLam Γ,τ⊢t:τ₂)
  ...               | no  Γ,τ⊬t:τ₂ = no helper
    where
      helper : ¬ Γ ⊢ lam τ t ∶ τ ↣ τ₂
      helper (tLam Γ,τ⊢t:_) = Γ,τ⊬t:τ₂ Γ,τ⊢t:_

  -- Application case.
  check Γ (t₁ ∙ t₂) σ with infer Γ t₂
  ... | yes (τ -by- Γ⊢t₂:τ)
      with check Γ t₁ (τ ↣ σ)
  ...    | yes Γ⊢t₁:τ↣σ = yes (Γ⊢t₁:τ↣σ ∙ Γ⊢t₂:τ)
  ...    | no  Γ⊬t₁:τ↣σ = no helper
    where
      helper : ¬ Γ ⊢ t₁ ∙ t₂ ∶ σ
      helper (Γ⊢t₁:_↣_ ∙ Γ⊢t₂:τ′)
        with ⊢-inj Γ⊢t₂:τ Γ⊢t₂:τ′
      ...  | refl = Γ⊬t₁:τ↣σ Γ⊢t₁:_↣_

  check Γ (t₁ ∙ t₂) σ | no Γ⊬t₂:_ = no helper
    where
      helper : ¬ Γ ⊢ t₁ ∙ t₂ ∶ σ
      helper (_∙_ {τ = σ} t Γ⊢t₂:τ′) = Γ⊬t₂:_ (σ -by- Γ⊢t₂:τ′)
\end{code}

### References

- Barendregt, Henk, Wil Dekkers, and Richard Statman (2013). *Lambda calculus with types*. Cambridge University Press.
- Danielsson, Nils Anders. [*Normalisation for the simply typed lambda calculus*](http://www.cse.chalmers.se/~nad/listings/simply-typed/).
- Érdi, Gergő (2013). [*Simply Typed Lambda Calculus in Agda, Without Shortcuts*](https://gergo.erdi.hu/blog/2013-05-01-simply_typed_lambda_calculus_in_agda,_without_shortcuts/).
