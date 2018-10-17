---
layout: "post"
title: "Path Algebra in HoTT"
date: "2018-02-16"
latex: true
references: true
agda: true
gallery: true
categories: learning
---

In Univalence we have a different interpretation of type theory {% cite hottbook
%}. We replace the set-theoretical notion of sets for types and we use the
*topological space* notion instead. The judgement $$a : A$$ for a type $$A$$ is
now the point $$a$$ in the topological space $$A$$. We also include the identity
type as a primary type. Changing the notation of this type about a proof of the
equality $$a = b$$ to a *path space*. This path space comprehends all paths with
$$a$$ as the starting point and $$b$$ as the end point. The inhabitant of this
type is called a *path*.

### Prerequisites

To formalize some of the HoTT concepts, let's use Agda {% cite agdateam %}.
To work with the identity type, we `(_≡_)` defined in
the Agda standard library but using the following pragma to make our code
compatible with HoTT.

\begin{code}
{-# OPTIONS --without-K #-}
\end{code}

\begin{code}
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code}

### Path Induction

The elimination principle for the identity type is the path induction.
It allows us to define an outgoing function from the identity type to
a dependent type $$C$$ as we see in the `pi` definition. It worths to
mention this principle is also called `J`.

\begin{code}
pi
  : ∀ {i j} {A : Set i}
  → (C : (x y : A) → x ≡ y → Set j)
  → (∀ (x : A) → C x x refl)
  → ∀ (x y : A) (p : x ≡ y) → C x y p
pi {A} C c x .x refl = c x
\end{code}

### Path Concatenation

To join two paths when one ends where the other starts, we
define the _concatenation_ operator between paths denoted by the symbol (`_·_`).
Let's see its picture.

![path](/assets/ipe-images/path-concatenation.png){: width="%40" }

{: .foldable until="6"  }
\begin{code}
infixr 20 _·_
_·_ : ∀ {A : Set} {x y z : A}
    → (p : x ≡ y)
    → (q : y ≡ z)
    ------------
    → x ≡ z

_·_ {A} {x} {y} {z} p q = D₁ x y p z q
  where
    D₂ : (x z : A) (q : x ≡ z) → x ≡ z
    D₂ = pi (λ x z q → x ≡ z) (λ x → refl)

    D₁ : (x y : A) → (x ≡ y) → ((z : A) → (q : y ≡ z) → x ≡ z)
    D₁ = pi (λ x y p → ((z : A) → (q : y ≡ z) → x ≡ z)) (λ x → D₂ x)
\end{code}

To make the above code shorter in Agda, we could have defined the function by
pattern-matching. Nonetheless, the idea here was use path induction --- the pi
function--- entirely.

### Path Inverse

The path inverse for a given path `p : a = b` is denoted by `p⁻¹ : b = a`.
This path only change the original direction of the path `p`. Let's see it.

\begin{code}
infixl 20 _⁻¹
_⁻¹ : ∀ {A : Set} {x y : A} → (p : x ≡ y) → y ≡ x
_⁻¹ {A}{x}{y} p =
  pi (λ x y p → y ≡ x)
     (λ x → refl {x = x})
     x y p
\end{code}

As you can see, path inversion is just the symmetric property for this
identity type. Now let's see some algebra.

-----------------------------------------------------------------------------

### Algebra

+ l1 : $$(\mathsf{refl}_{x})^{-1} \equiv \mathsf{refl}_{x}$$
+ l2 : $$p \cdot p^{-1} \equiv \mathsf{refl}_{x}$$
+ l3 : $$\mathsf{refl}_{x} \cdot p \equiv p$$
+ l4 : $$p \cdot \mathsf{refl} y \equiv p$$
+ l5 : $$ (p ^{-1})^{-1} \equiv p$$

![path](/assets/ipe-images/path-algebra.png)

-----------------------------------------------------------------------------

Proofs:

+ l1 : $$(\mathsf{refl}_{x})^{-1} \equiv \mathsf{refl}_{x}$$
\begin{code}
l1 : ∀ {A : Set} {x : A} → (refl ⁻¹) ≡ refl
l1 {A}{x} =
  pi (λ x y p → (refl ⁻¹) ≡ refl {x = x})
     (λ x → refl {x = refl {x = x}})
     x x refl
\end{code}

+ l2 : $$p \cdot p^{-1} \equiv \mathsf{refl}_{x}$$

\begin{code}
l2 : ∀ {A : Set} (x y : A) → (p : x ≡ y) → (p · (p ⁻¹))  ≡ refl
l2 =
  pi (λ x y p → (p · (p ⁻¹))  ≡ refl)
     (λ x → refl { x = refl {x = x}})
\end{code}

+ l3 : $$\mathsf{refl}_{x} \cdot p \equiv p$$

\begin{code}
l3 : ∀ {A : Set} (x y : A) → (p : x ≡ y) → refl · p ≡ p
l3 =
  pi (λ x y p → refl · p ≡ p)
     (λ x → refl { x = refl {x = x}})
\end{code}

+ l4 : $$p \cdot \mathsf{refl} y \equiv p$$

\begin{code}
l4 : ∀ {A : Set} (x y : A) → (p : x ≡ y) → refl · p ≡ p
l4 = pi (λ x y p → refl · p ≡ p)
        (λ x → refl {x = refl {x = x}})
\end{code}

+ l5 : $$ (p ^{-1})^{-1} \equiv p$$

\begin{code}
l5 : ∀ {A : Set} (x y : A) → (p : x ≡ y) → (p  ⁻¹) ⁻¹ ≡ p
l5 = pi (λ x y p → (p  ⁻¹) ⁻¹ ≡ p)
        (λ x → refl {x = refl {x = x}})
\end{code}

### Transport

\begin{code}
transp : ∀ {A : Set}{x x' : A}
      → (B : A → Set) → (y : B x) → (u : x ≡ x') → B x'
transp B y refl  = y
\end{code}

![path](/assets/ipe-images/transport-fiber.png)

Transport is the *path* version of the Leibniz's Law in one direction:

$$
  \forallx \forally (x \equiv y \to \forall P \ (P(x) \Leftrightarrow P(y))
$$

We should also say, we're already familiar with its type since it
shows up as the susbstitution of equals in type theory. Actually,
in the Agda standard library, we found `subst` that follows from the same principle:

\begin{code}
open import Relation.Binary.PropositionalEquality using (subst)

trans' : ∀ {A : Set}{x x' : A}
      → (B : A → Set) → (y : B x) → (u : x ≡ x') → B x'
trans' B y u = subst B u y
\end{code}
