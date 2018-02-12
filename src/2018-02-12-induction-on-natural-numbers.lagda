---
layout: "post"
title: "Induction on Natural Numbers"
date: "2018-02-12 13:25"
---

We define the natural numbers by following its
algorithmic or finite definition, that is, using a
rule to construct the zero and a successor for any number.

\begin{code}
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
\end{code}

* Remark: to be more comfortable with the usual notation let use
the following pragma:

\begin{code}
{-# BUILTIN NATURAL ℕ #-}
\end{code}

Then, we can now write numbers like usual:

\begin{code}
bigNumber : ℕ
bigNumber = 123456789
\end{code}

#### Recursion

Now let us define the principle of primitive recursion for natural numbers:

```agda
recℕ : Π(C : 𝒰) C → (ℕ → C → C) → ℕ → C
```
recℕ is the so-called *recursor* for natural numbers. In Agda,

\begin{code}
recℕ
  : (C : Set)    -- type for the outcome
  → C            -- base case
  → (ℕ → C → C)  -- recursion call
  → ℕ            -- the number in the input
  → C            -- outcome
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

+ Doubling a number.

\begin{code}
double : ℕ → ℕ
double = recℕ ℕ 0 (λ n y → suc (suc y))
\end{code}

Instead of

\begin{code}
double₂ : ℕ → ℕ
double₂ zero = zero
double₂ n    = suc (suc n)
\end{code}

Before unpacking these definition, let test some examples. To this purpose we
import the equality definition type (_≡_) and its introduction rule (refl).

\begin{code}
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
\end{code}

Then testing the definitional equality for some sums, we certaintly start to
believe.

\begin{code}
2+5 : add 2 5 ≡ 7
2+5 = refl

25+25 : add 25 25 ≡ 50
25+25 = refl
\end{code}

In the definition of `add` we have the following:

  + By [curryfication](https://en.wikipedia.org/wiki/Currying), the `add` function can
  be seen as a function that returns a function. How is this possible? just fix
  the first argument, and then you have an unary function, and that's why C : ℕ → ℕ.

  ```agda
  add : ℕ → (ℕ → ℕ)
  ```

  + When the first argument in the sum is zero, we just have to return the
  identity function, that's why c₀ is (λ m → m).

  ```agda
  add zero m = m
  ```

  + To understand the last argument, ((λ n g m → suc (g m))), remember that
  this is indeed cₛ : ℕ → C → C, and by the equation of recℕ:

  ```
  recℕ C c₀ cₛ (suc n) = cₛ n (recℕ C c₀ cₛ n)
  ```

  Question: why the n variable is not present in the returned value?


#### Induction
