---
layout: "post"
title: "functions in type theory"
date: "2018-02-10 14:12"
---


In type theory we do not define function since this is an undefined concept also
refer to it as a primitive notion.
In contrast, we have in set theory that a function is
a correspondance between two sets, a **relation** between the domain
and the codomain.

In type theory, we have a function type for the functions
also called *maps*. The function type is introduced as usual with other types:

+ name of the type or symbol: (_→_)

+ formation rule:

  Γ ⊢ A  and Γ ⊢ B then Γ ⊢ f : A → B

+ introduction rule (λ-abstraction):

  Γ , x : A ⊢ t : B then Γ ⊢ λ (x : A) . t : A → B

+ elimination rule:

  Γ ⊢ λ (x : A) . t : A → B and Γ ⊢ y : A then Γ ⊢ (λ (x : A) . t) y : B

+ computation rule (also called β-reduction or β-conversion):

  Γ ⊢ (λ (x : A) . t) y : B then Γ ⊢ t[ x := y] : B

  We use the last notation `t[x := y]` to say that replace every occurrance of
  x in the term t by y.

+ simplication rule (also called η-conversion):

  Γ ⊢ λ (x : A) . f x : A → B then Γ ⊢ f : A → B

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

+ Two functions are **judgementally* equal if they are equal by α-conversion,
that is, if after renaming the variable names they are definitionally equal.

\begin{code}
g :  A → A → A
g = λ x y → y

h : A → A → A
h =  λ w z → z
\end{code}

But g and h functions producing the same, then if que sustitute in h, w by x,
and z by y, we get the definition of g, so at the end, g and h are **judgementally* equal.

\begin{code}
g≡h : g ≡ h
g≡h = refl
\end{code}

+ Currying.
