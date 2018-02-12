---
layout: "post"
title: "Induction on Natural Numbers"
date: "2018-02-12 13:25"
updated: 2018-02-12
---

We define the natural numbers by following its algorithmic or finite definition,
that is, using a rule to construct the zero and a successor for any number.

\begin{code}
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
\end{code}

* Remark: to be more comfortable with the usual notation we can use the following
pragma in Agda

\begin{code}
{-# BUILTIN NATURAL ℕ #-}
\end{code}

Then, we can now write numbers like usual:

\begin{code}
bigNumber : ℕ
bigNumber = 123456789
\end{code}

### Recursion

Now let us define the principle of primitive recursion for natural numbers:

```agda
recℕ : Π(C : 𝒰) C → (ℕ → C → C) → ℕ → C
```
recℕ is the so-called *recursor* for natural numbers. In Agda,

\begin{code}
recℕ
  : (C : Set)    -- type for the outcome
  → C            -- base case
  → (ℕ → C → C)  -- recursion
  → ℕ            -- the natural number as the argument
  → C            -- outcome
\end{code}

With the following equations:

\begin{code}
recℕ C c₀ cₛ zero = c₀
recℕ C c₀ cₛ (suc n) = cₛ n (recℕ C c₀ cₛ n)
\end{code}

Now, we can define some common functions using this recursor to see how it works.

+ Adding two numbers.

\begin{code}
add : ℕ → ℕ → ℕ
add = recℕ (ℕ → ℕ) (λ m → m) (λ n g m → suc (g m))
\end{code}

Instead of the usual add function:

\begin{code}
add₂ : ℕ → ℕ → ℕ
add₂ zero m = m
add₂ (suc n) m = suc (add₂ n m)
\end{code}

For comodity we use the usual symbol for adding numbers,
and also we declare the precedence of this symbol.

\begin{code}
_+_ = add
infix 6 _+_
\end{code}

+ Doubling a number.

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
type (_≡_) and its rule (refl).

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
_*_ = recℕ (ℕ → ℕ) (λ m → zero) λ n g m → add m (g m)
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

#### Induction

The induction here is a generalization of the priniciple of recursion. In
first-order we can write the induction schema or the principle of mathematical
induction.

```
P 0 ∧ (∀ n. P n → P (suc n)) → ∀n. P n
```

  > In particular, a property of natural numbers is represented by a family of
  types P : ℕ → 𝒰. From this point of view, the above induction principle says
  that if we can prove P(0), and if for any n we can prove P(succ(n)) assuming
  P(n), then we have P(n) for all n. (HoTT Book. Pag.50-51.)

By using a *dependent* function to obtain its version in type theory we have the
following

\begin{code}
indℕ
  : ∀ (C : ℕ → Set)
  → C zero
  → (∀ (n : ℕ) → C n → C (suc n))
  → (∀ (n : ℕ) → C n)
\end{code}

with the defining equations

\begin{code}
indℕ C c₀ cₛ zero    = c₀
indℕ C c₀ cₛ (suc n) = cₛ n (indℕ C c₀ cₛ n)
\end{code}

* Remark: the usage of forall symbol is not necessary but it makes more
likely to the schemata presented above.

Now, we have the power of induction to prove some properties.

+ *Associativity*

\begin{code}
assoc : (i j k : ℕ) → i + (j + k) ≡ (i + j) + k
assoc = {!  !}
\end{code}

To prove this property by induction we need first to provide the term assoc₀, that
is the base case and then build a inhabitant of the hypotesis of induction.

\begin{code}
assoc₀ : ∀ (j k : ℕ) → 0 + (j + k) ≡ (0 + j) + k
assoc₀ = {!   !}
\end{code}

\begin{code}
assoc₁
  : ∀ (i : ℕ)
  → ∀ (j k : ℕ) → i + (j + k) ≡ (i + j) + k
  → ∀ (j k : ℕ) → (suc i) + (j + k) ≡ ((suc i) + j) + k
assoc₁ = {!   !}
\end{code}

+ *Commutatity*

\begin{code}
+-comm : ∀ (n m : ℕ) → n + m ≡ m + n
+-comm = indℕ {!   !} {!   !} {!   !}
\end{code}

+ *Congruence*

\begin{code}
+-cong : ∀ (n m : ℕ) → n ≡ m → suc n ≡ suc m
+-cong = indℕ {!   !} {!   !} {!   !}
\end{code}

+ Exercise 1

\begin{code}
0+n : ∀ (n : ℕ) → 0 + n ≡ 0
0+n = indℕ {!   !} {!   !} {!   !}
\end{code}

+ Exercise 2

\begin{code}
p₂ : ∀ (n : ℕ) → double (n + 1) ≡ (suc (suc (double n)))
p₂ = indℕ {!   !} {!   !} {!   !}
\end{code}

+ Exercise 3

\begin{code}
p₃ : ∀ (n : ℕ) → double (n + 1) ≡ (suc (suc (double n)))
p₃ = indℕ {!   !} {!   !} {!   !}
\end{code}