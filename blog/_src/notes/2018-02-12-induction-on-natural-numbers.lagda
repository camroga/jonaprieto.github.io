---
layout: "post"
permalink: /induction-natural-numbers/
title: "Induction on Natural Numbers"
date: "2018-02-12"
toc: true
categories: type-theory
latex: true
references: true
agda: true
showcitation: true
home: true
---

## Introduction

The induction principle comes from a generalization of a dependent function that
makes recursion on natural numbers. We first define what is a natural number and
later, we show how to define functions by means of the recursor and induction
principles.

The universe will be denoted by `𝒰`:

\begin{code}
𝒰 = Set
\end{code}

If we follow an algorithmic procedure to define natural numbers, we will encounter
two rules to construct them, one rule to get the zero and another rule for the rest,
that we call it, `suc` for successor.

\begin{code}
data ℕ : 𝒰 where
  zero : ℕ
  suc  : ℕ → ℕ
\end{code}

For convenience, we use the following Agda pragma to write down numbers in decimal
notation, otherwise, we should write the number down using only the constructors.

\begin{code}
{-# BUILTIN NATURAL ℕ #-}
\end{code}

And this is what we got.

\begin{code}
bigNumber : ℕ
bigNumber = 123456789  -- instead of suc (suc ( ... (suc ..)..
\end{code}

-------------------------------------------------------------------------------

## Recursion principle

The principle of *primitive recursion* for natural numbers establishes that to
create a non-dependent outgoing function with natural numbers as its domain, we
just need to tell it the type in the codomain, and the function behavior on the
`ℕ` constructors. Which means, says what return in the case when the number is `zero`
and when the number was built using `suc` constructor.

{: .equation }
  $$
  \mathsf{rec_{\mathbb{N}}} : \prod\limits_{C : \mathcal{U}}\, C \to (\mathbb{N} \to C \to C) \to \mathbb{N} \to C
  $$

In Agda, the `recℕ` also called *recursor* for natural number
has been defined by pattern-matching as follows.

\begin{code}
recℕ
  : (C : 𝒰)
  → C
  → (ℕ → C → C)
  -------------
  → ℕ → C
\end{code}

With the following equations:

\begin{code}
recℕ C c₀ cₛ zero    = c₀
recℕ C c₀ cₛ (suc n) = cₛ n (recℕ C c₀ cₛ n)
\end{code}

-------------------------------------------------------------------------------

### Examples

#### Add

\begin{code}
add : ℕ → ℕ → ℕ
add = recℕ (ℕ → ℕ) (λ m → m) (λ n g m → suc (g m))

_+_ = add
infix 6 _+_
\end{code}

Instead of using the following definition:

\begin{code}
add₂ : ℕ → ℕ → ℕ
add₂ zero    m = m
add₂ (suc n) m = suc (add₂ n m)
\end{code}

**Double**

\begin{code}
double : ℕ → ℕ
double = recℕ ℕ 0 (λ n y → suc (suc y))
\end{code}

Instead of:

\begin{code}
double₂ : ℕ → ℕ
double₂ zero = zero
double₂ n    = suc (suc n)
\end{code}

For testing purposes, let's import from the equaility definition
type (`_≡_`) and its rule (`refl`) from the std-lib library.

\begin{code}
open import Relation.Binary.PropositionalEquality using (refl; _≡_; sym)

2+5 : add 2 5 ≡ 7
2+5 = refl

25+25 : add 25 25 ≡ 50
25+25 = refl
\end{code}

It's time to unpacking the the definition of `add`:

  + By [Currying](https://en.wikipedia.org/wiki/Currying), the binary
  function `add` can be seen as a function that returns a unary function fixing the
  first argument. Thus, the domain for the `recℕ`, `C` is `ℕ → ℕ` (a unary funciton).

  ```
  add : ℕ → (ℕ → ℕ)
  add n : ℕ → ℕ
  ```

  + When the first argument is zero, we just return the second argument, that is,
  `add 0` is the identity function. Thus `c₀` is `(λ m → m)`.

  ```agda
  add zero m = m
  ```

  + Question: why `((λ n g m → suc (g m)))`?


#### Multiplication

\begin{code}
_*_ : ℕ → ℕ → ℕ
_*_ = recℕ (ℕ → ℕ) (λ m → zero) (λ n g m → add m (g m))
\end{code}

With the binding for this operation more tighly than (_+_)

\begin{code}
infix 7 _*_
\end{code}

\begin{code}
m₁ : 2 * 0 ≡ 0
m₁ = refl

m₂ : 2 * 3 ≡ 6
m₂ = refl

m₃ : 10 * 3 ≡ 30
m₃ = refl
\end{code}

## Induction principle

The induction here is a generalization of the principle of recursion. In
first-order we can write the induction schema or the principle of mathematical
induction.

$$
P\,0 \wedge (\forall n . P n \to P (\mathsf{suc} n)) \to \forall n . P n
$$

  > In particular, a property of natural numbers is represented by a family of
  types P : ℕ → 𝒰. From this point of view, the above induction principle says
  that if we can prove P(0), and if for any n we can prove P(succ(n)) assuming
  P(n), then we have P(n) for all n. (Pp. 50-51 in {% cite hottbook %})

By using a *dependent* function to obtain its version in type theory we have the
following

\begin{code}
indℕ
  : ∀ {C : ℕ → 𝒰}
  → C zero
  → (∀ (n : ℕ) → C n → C (suc n))
  -------------------
  → ∀ (n : ℕ) → C n
\end{code}

with the defining equations

\begin{code}
indℕ c₀ cₛ zero    = c₀
indℕ c₀ cₛ (suc n) = cₛ n (indℕ c₀ cₛ n)
\end{code}

Now, we have the power of induction to prove some properties.

###  Congruence

\begin{code}
suc-cong
  : ∀ {n m : ℕ}
  -----------------------
  → n ≡ m → suc n ≡ suc m

suc-cong refl = refl
\end{code}

As we can see in the type of `suc-cong` we used implicit
arguments for the numbers n and m. That's pretty convenient to get
some help by letting infer Agda about those implicit argument.

Using congruence we can now prove that both definitions above
for the add function are indeed equal using ι-,β- reductions:

\begin{code}
add≡add₂
  : ∀ (n m : ℕ)
  --------------------
  → add n m ≡ add₂ n m

add≡add₂ zero    m = refl
add≡add₂ (suc n) m = suc-cong (add≡add₂ n m)
\end{code}


### Associativity

\begin{code}
assoc
  : (i j k : ℕ)
  ---------------------------
  → i + (j + k) ≡ (i + j) + k
\end{code}

To prove this property by induction we need first to provide the term `assoc₀`, that
is the base case and then build an inhabitant of the induction hypothesis.

\begin{code}
assoc₀
  : ∀ (j k : ℕ)
  ---------------------------
  → 0 + (j + k) ≡ (0 + j) + k

assoc₀ j k = refl
\end{code}

\begin{code}
assoc₁
  : ∀ (i : ℕ)
  → ((j k : ℕ) → i + (j + k) ≡ (i + j) + k)
  ---------------------------------------------------
  → (j k : ℕ) → (suc i) + (j + k) ≡ ((suc i) + j) + k

assoc₁ i p j₁ k₁ = suc-cong (p j₁ k₁)
\end{code}

Then, by indℕ:

\begin{code}
assoc = indℕ assoc₀ assoc₁
\end{code}

### Commutativity

\begin{code}
+-comm₀
  : ∀ (m : ℕ)
  ---------------
  → 0 + m ≡ m + 0

+-comm₀ = indℕ refl (λ n indHyp → suc-cong indHyp)
\end{code}

\begin{code}
+-identity
  : ∀ (n : ℕ)
  --------------
  → n + zero ≡ n

+-identity = indℕ refl (λ n indHyp → suc-cong indHyp)
\end{code}

\begin{code}
+-suc
  : ∀ m n
  -------------------------
  → m + suc n ≡ suc (m + n)

+-suc zero    n = refl
+-suc (suc m) n = suc-cong (+-suc m n)
\end{code}

Let's define the transitivity and symmetric property of the equality.

\begin{code}
trans
  : ∀ {m n p : ℕ}
  → m ≡ n → n ≡ p
  ---------------
  → m ≡ p

trans refl refl = refl
\end{code}

\begin{code}
≡sym
  : ∀ {m n p : ℕ}
  → m ≡ n → n ≡ m

≡sym refl = refl
\end{code}

\begin{code}
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
\end{code}

### Exercises

+ Exercise 1

\begin{code}
0+n≡n
  : ∀ (n : ℕ)
  -----------
  → 0 + n ≡ n

0+n≡n = indℕ refl (λ n p → suc-cong p)
\end{code}

+ Exercise 2

\begin{code}
p₂
  : ∀ (n : ℕ)
  -----------------------------------------
  → double (n + 1) ≡ (suc (suc (double n)))

p₂ = indℕ refl (λ n indHyp → suc-cong (suc-cong indHyp))
\end{code}

In the above definition may it's worth to notice that `indHyp`
is indeed the induction hypothesis:

    indHyp : double (n + 1) ≡ suc (suc (double n))

+ Exercise 3

Without using pattern-matching find the term `n+0≡n`:

\begin{code}
n+0≡n
  : ∀ (n : ℕ)
  -----------
  → n + 0 ≡ n

n+0≡n = indℕ refl (λ n indHyp → suc-cong indHyp)
\end{code}

\begin{code}
n+0≡n₂
  : ∀ (n : ℕ)
  -----------
  → n + 0 ≡ n

n+0≡n₂ zero    = refl
n+0≡n₂ (suc n) = suc-cong (n+0≡n₂ n)
\end{code}


## Alternative induction

<div class="exercise">
Assuming the ordinary induction principle (i.e., <a href="#induction">indℕ</a>)
derives the transfinite induction principle.<br/>

For a unary predicate $$P : \mathbb{N} \to \mathcal{U}$$, if

<p class="equation">
$$
\prod\limits_{n : \mathbb{N}} \left ( \prod\limits_{k : \mathbb{N}} (k < n \to P(k)) \to P(n) \right)
$$
</p>

then for all $$n : \mathbb{N}$$, $$P(n)$$.
</div>

To solve this problem, we need to define a type for the *less than* relationship
(`_<_`) between natural numbers but we also have to define the disjunction to
make a case analysis that we need for our proof. Let's see. You may skip this
first part.

\begin{code}
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
\end{code}

<div class="proof">
Proof.<br/>
We use induction to get an inhabitant of the $$G$$ proposition.
The induction was using pattern matching on $$n$$ in Agda.
At the end, we use the hypothesis with this inhabitant of $$G$$.

{: .equation }
  $$
  G : \prod\limits_{(n : \mathbb{N})}\ \left(\prod\limits_{(k : \mathbb{N})}\ ((k < n) \to P (k))\right)
  $$

where $$P : \mathbb{N} \to \mathcal{U}$$.

<br/>
<br/>

\begin{code}
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
\end{code}
</div>

## Summary

The recursor `recℕ` is the *no-dependent* version of `indℕ` function that allows
us to define functions `f : ℕ → C` where `C : 𝒰` by defining two equations:

+ `f(0) ≡ c₀` for `c₀ : C`

+ `f(suc n) ≡ cₛ(n, f(n))` for `cₛ : ℕ → C → C`

{: .references }

  - {% reference hottbook %}
  - {% reference Coquand1992 %}
  - [Induction in PLAgda](https://plfa.github.io/Induction/)
