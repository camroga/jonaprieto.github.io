---
layout: "post"
title: "Induction on Natural Numbers"
date: "2018-02-12"
categories: type-theory
---

The induction principle comes from a generalization of a dependent function that
makes recursion on natural numbers. We first define what is a natural number
then we show how to define functions on natural numbers using a *recursor* in
pro to show the induction principle.

First let's use in Agda a synonymous for the universe of types.

\begin{code}
𝒰 = Set
\end{code}

We can define the natural numbers by following its algorithmic or also called finite
definition, that is, finite rules to construct them, one for the zero number and
another, the successor, for the rest of numbers.

\begin{code}
data ℕ : 𝒰 where
  zero : ℕ
  suc  : ℕ → ℕ
\end{code}

* Remark: we can write down numbers as usual if we use the following Agda pragma.

\begin{code}
{-# BUILTIN NATURAL ℕ #-}
\end{code}

Then, we can now type big numbers like usual instead of `suc (suc (...))`:

\begin{code}
bigNumber : ℕ
bigNumber = 123456789
\end{code}

### Recursion

Now let us define the principle of primitive recursion for natural numbers:

```agda
recℕ : Π(C : 𝒰). C → (ℕ → C → C) → ℕ → C
```
recℕ is the so-called *recursor* for natural numbers.
In Agda, we can define it as follows.

\begin{code}
recℕ
  : (C : 𝒰)     -- type for the outcome
  → C            -- base case when n = 0
  → (ℕ → C → C)  -- recursion when n > 0
  → ℕ            -- the natural number in the recursion call
  → C
\end{code}

With the following equations:

\begin{code}
recℕ C c₀ cₛ zero    = c₀
recℕ C c₀ cₛ (suc n) = cₛ n (recℕ C c₀ cₛ n)
\end{code}

Now, we can define some common functions using this recursor to see how it works.

+ The add function.

\begin{code}
add : ℕ → ℕ → ℕ
add = recℕ (ℕ → ℕ) (λ m → m) (λ n g m → suc (g m))

_+_ = add
infix 6 _+_
\end{code}

\end{code}

Instead of using the following definition:

\begin{code}
add₂ : ℕ → ℕ → ℕ
add₂ zero m = m
add₂ (suc n) m = suc (add₂ n m)
\end{code}

+ The double function.

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

Now, just for testing the definitions above. We import the equality definition
type (`_≡_`) and its rule (`refl`).

\begin{code}
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

2+5 : add 2 5 ≡ 7
2+5 = refl

25+25 : add 25 25 ≡ 50
25+25 = refl
\end{code}

It's time to unpacking the the definition of `add`:

  + By [Currying](https://en.wikipedia.org/wiki/Currying), the `add`
  function can be seen as a function that returns a function. That happens if we
  fix the first argument to have an unary function. That's why C  has ℕ → ℕ type.

  ```agda
  add : ℕ → (ℕ → ℕ)
  ```

  + When the first argument in the sum is zero, we just have to return the
  identity function, that's why c₀ is (λ m → m).

  ```agda
  add zero m = m
  ```

  + Question: why `((λ n g m → suc (g m)))`?

Let us try with another function, the multiplication, but this time
let use a better name for this function (_*_).

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

### Induction

The induction here is a generalization of the priniciple of recursion. In
first-order we can write the induction schema or the principle of mathematical
induction.

```
P 0 ∧ (∀ n . P n → P (suc n)) → ∀ n . P n
```

  > In particular, a property of natural numbers is represented by a family of
  types P : ℕ → 𝒰. From this point of view, the above induction principle says
  that if we can prove P(0), and if for any n we can prove P(succ(n)) assuming
  P(n), then we have P(n) for all n. (HoTT Book. Pag.50-51.)

By using a *dependent* function to obtain its version in type theory we have the
following

\begin{code}
indℕ
  : ∀ {C : ℕ → 𝒰}
  → C zero
  → (∀ (n : ℕ) → C n → C (suc n))
  → (∀ (n : ℕ) → C n)
\end{code}

with the defining equations

\begin{code}
indℕ c₀ cₛ zero    = c₀
indℕ c₀ cₛ (suc n) = cₛ n (indℕ c₀ cₛ n)
\end{code}

Now, we have the power of induction to prove some properties.

+ *Congruence*

\begin{code}
+-cong : ∀ {n m : ℕ} → n ≡ m → suc n ≡ suc m
+-cong refl = refl
\end{code}

As we can see in the type of `+-cong` we used implicit
arguments for the numbers n and m. That's pretty convenient to get
some help by letting infer Agda about those implicit argument.

Using congruence we can now prove that both definitions above
for the add function are indeed equal using ι-,β- reductions:

\begin{code}
add≡add₂ : ∀ (n m : ℕ) → add n m ≡ add₂ n m
add≡add₂ zero    m = refl
add≡add₂ (suc n) m = +-cong (add≡add₂ n m)
\end{code}


+ *Associativity*

\begin{code}
assoc : (i j k : ℕ) → i + (j + k) ≡ (i + j) + k
\end{code}

To prove this property by induction we need first to provide the term `assoc₀`, that
is the base case and then build an inhabitant of the induction hypothesis.

\begin{code}
assoc₀ : ∀ (j k : ℕ) → 0 + (j + k) ≡ (0 + j) + k
assoc₀ j k = refl
\end{code}

\begin{code}
assoc₁
  : ∀ (i : ℕ)
  → (∀ (j k : ℕ) → i + (j + k) ≡ (i + j) + k)
  → ∀ (j k : ℕ) → (suc i) + (j + k) ≡ ((suc i) + j) + k
assoc₁ i p j₁ k₁ = +-cong (p j₁ k₁)
\end{code}

Then, by indℕ:

\begin{code}
assoc = indℕ assoc₀ assoc₁
\end{code}

+ *Commutatity*

\begin{code}
+-comm₀ : ∀ (m : ℕ) → zero + m ≡ m + zero
+-comm₀ = indℕ refl λ n indHyp → +-cong indHyp

postulate  -- TODO
  +-identity : ∀ (n : ℕ) → n + zero ≡ n
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

postulate  -- TODO
  +-commₛ
    : ∀ (m : ℕ)
    → (∀ (n : ℕ) → m + n ≡ n + m)
    → ∀ (n : ℕ)  → suc m + n ≡ n + suc m
-- +-commₛ m indHyp zero = +-identity (suc m)
-- +-commₛ m indHyp (suc n) = {!   !}
\end{code}

Instead of using `rewrite` in Agda, we can use transitivity
of the identity.

\begin{code}
trans : ∀ {m n p : ℕ} → m ≡ n → n ≡ p → m ≡ p
trans refl refl = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm = indℕ +-comm₀ +-commₛ
\end{code}

### Exercises

+ Exercise 1

\begin{code}
0+n≡n : ∀ (n : ℕ) → 0 + n ≡ n
0+n≡n = indℕ refl (λ n p → +-cong p)
\end{code}

+ Exercise 2

\begin{code}
p₂ : ∀ (n : ℕ) → double (n + 1) ≡ (suc (suc (double n)))
p₂ = indℕ refl (λ n indHyp → +-cong (+-cong indHyp))
\end{code}

In the above definition may it's worth to notice that indHyp
is actually our induction hypothesis.

    indHyp : double (n + 1) ≡ suc (suc (double n))

+ Exercise 3

Without pattern-matching:

\begin{code}
n+0≡n : ∀ (n : ℕ) → n + 0 ≡ n
n+0≡n = indℕ refl (λ n indHyp → +-cong indHyp)
\end{code}

With pattern-matching:

\begin{code}
n+0≡n₂ : ∀ (n : ℕ) → n + 0 ≡ n
n+0≡n₂ zero    = refl
n+0≡n₂ (suc n) = +-cong (n+0≡n₂ n)
\end{code}

### Conclusion

Induction as it was presented here is stronger than recursion. We can say this
because the recursor recℕ is the *no-dependent* function of indℕ.

The recursor recℕ allows to define a function f : ℕ → C by defining
two equations:

+ f(0) ≡ c₀ for c₀ : C
+ f(suc n) ≡ cₛ(n, f(n)) for cₛ : ℕ → C → C

### References

* [Univalent Foundations Program, T. (2013). Homotopy Type Theory: Univalent Foundations of Mathematics. Institute for Advanced Study][HoTT]

* [Coquand, T. (1992). Pattern matching with dependent types. Informal Proceedings
of Logical Frameworks.][Coquand]

[HoTT]:https://homotopytypetheory.org/book.
[Grayson]:http://arxiv.org/abs/1711.01477
[Coquand]:https://doi.org/10.1.1.37.9541
