---
title: "Function Type"
layout: "post"
date: "2018-02-10"
categories: type-theory
agda: true

---

# Function Type Rules

In type theory we do not define a function since this is an undefined concept
also refer to it as a *primitive notion*. In contrast to set theory where we
have the function as the relationship between two sets, the domain and the
codomain.

In type theory, the function also called *map* is introduced as follows:

+ name of the type or symbol: `(_→_)`

+ formation rule:
```
  Γ ⊢ A  and Γ ⊢ B then Γ ⊢ f : A → B
```

+ introduction rule (λ-abstraction):
```
  Γ , x : A ⊢ t : B then Γ ⊢ λ (x : A) . t : A → B
```

+ elimination rule:
```
  Γ ⊢ λ (x : A) . t : A → B and Γ ⊢ y : A then Γ ⊢ (λ (x : A) . t) y : B
```

+ computation rule (also called β-reduction or β-conversion):
```
  Γ ⊢ (λ (x : A) . t) y : B then Γ ⊢ t[ x := y] : B
```
We use the last notation `t[x := y]` to say that replace every occurrance of
$$x$$ in the term $$t$$ by $$y$$.

+ simplication rule (also called η-conversion):
```
  Γ ⊢ λ (x : A) . f x : A → B then Γ ⊢ f : A → B
```
  This conversion is also given by a definitional equality:

\begin{code}
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
\end{code}

Related:

+ Two functions are *judgemental* equal if they are equal by α-conversion,
that is, if after renaming the variable names they are definitionally equal.

\begin{code}
g :  A → A → A
g = λ x y → y

h : A → A → A
h =  λ w z → z
\end{code}

Both $$g$$ and $$h$$ function produce the same result.
Then if we sustitute in $$h$$, $$w$$ by $$x$$, and $$z$$ by $$y$$,
we get the definition of $$g$$, so at the end, $$g$$ and $$h$$ are
*judgemental* equal.

\begin{code}
g≡h : g ≡ h
g≡h = refl
\end{code}

# Functional extensionality

Very related to the above matter is the [*functional extensionality*](https://ncatlab.org/nlab/show/function+extensionality)
axiom that establishes the pointwise equality between two functions.
This axiom has the following type:

\begin{code}
postulate
  FunExt
    : ∀ {A B : Set}
    → ∀ {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
    → f ≡ g
\end{code}

Then, lets use this axiom in a complete example, proving that two defintions
of the add function are indeed equal. The example also includes a reference
to a note presented later about
[induction on natural numbers](https://jonaprieto.github.io/2018/02/14/induction-on-identity-types/):

The definitions:

\begin{code}
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
\end{code}

By function extensionality axiom :

\begin{code}
add≡add₂ : add ≡ add₂
add≡add₂ = FunExt (λ n → FunExt λ m → helper n m)
  where
    +-cong : ∀ {n m : ℕ} → n ≡ m → suc n ≡ suc m
    +-cong refl = refl

    helper : (n m : ℕ) → add n m ≡ add₂ n m
    helper zero    m = refl
    helper (suc n) m = +-cong (helper n m)
\end{code}

-----------------------------------------------------------------------------

+ In *Agda standard library*

In the the library `stdlib`, there is a section for [function
extensionality](https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4385
) showed in the following excerpts.

Some imports:

\begin{code}
open import Level
open import Relation.Binary.PropositionalEquality using (cong)
open import Function using (_∘_; _$_)
\end{code}

\begin{code}
Extensionality : (a b : Level) → Set _
Extensionality a b =
  {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
  (∀ x → f x ≡ g x) → f ≡ g
\end{code}

If extensionality holds for a given universe level, then it also
holds for lower ones.

\begin{code}
extensionality-for-lower-levels
  : ∀ {a₁ b₁} a₂ b₂
  → Extensionality (a₁ ⊔ a₂) (b₁ ⊔ b₂)
  → Extensionality a₁ b₁

extensionality-for-lower-levels a₂ b₂ ext f≡g =
  cong (λ h → lower ∘ h ∘ lift) $
    ext (cong (lift {ℓ = b₂}) ∘ f≡g ∘ lower {ℓ = a₂})
\end{code}

Functional extensionality implies a form of extensionality for
Π-types.

\begin{code}
∀-extensionality
  : ∀ {a b}
  → Extensionality a (Level.suc b)
  → {A : Set a} (B₁ B₂ : A → Set b)
  → (∀ x → B₁ x ≡ B₂ x) → (∀ x → B₁ x) ≡ (∀ x → B₂ x)

∀-extensionality ext B₁ B₂ B₁≡B₂ with ext B₁≡B₂
∀-extensionality ext B .B  B₁≡B₂ | refl = refl
\end{code}

-----------------------------------------------------------------------------

+ Homotopy Type Theory

<div class="todo">
Univalance implies function extensionality and the uniqueness principle for functions.
</div>

### References

- {% reference hottbook %}
