---
layout: "post"
title: "HoTT exercises"
date: "2018-04-08"
categories: type-theory
toc: true
---

This is a self-contained version of some solutions for HoTT-Book's exercises.
The idea is to unpackage all as long as possible to get a better understanding.
Many changes can appear running this experiment. Solutions are
type-checked as a whole using Agda v2.5.3.

## Requirements

-------------------------------------------------------------------------------

Agda has a pragma to work with HoTT:

\begin{code}
{-# OPTIONS --without-K #-}
\end{code}

-------------------------------------------------------------------------------

Equality type definition also called Identity type:

\begin{code}
infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
\end{code}

Some functions to work with this type:

\begin{code}
sym : ∀ {i} {A : Set i} {x y : A}
    → x ≡ y → y ≡ x
sym refl = refl

_·_ : ∀ {i}{X : Set i}{x y z : X}
    → x ≡ y → y ≡ z → x ≡ z
refl · p = p
trans = _·_

infixl 9 _·_

ap : ∀ {i j}{A : Set i}{B : Set j}{x y : A}
   → (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

ap₂ : ∀ {i j} {A B : Set i}{C : Set j}
      {x₀ x₁ : A}{y₀ y₁ : B}
    → (f : A → B → C) → (x₀ ≡ x₁) → (y₀ ≡ y₁)
    → f x₀ y₀ ≡ f x₁ y₁
ap₂ f refl refl = refl

subst : ∀ {i j} {A : Set i}{x y : A}
      → (B : A → Set j) → x ≡ y
      → B x → B y
subst B refl = (λ z → z)

\end{code}

Path induction:

\begin{code}
J' : ∀ {i j}{X : Set i}{x : X}
   → (P : (y : X) → x ≡ y → Set j)
   → P x refl
   → (y : X)
   → (p : x ≡ y)
   → P y p
J' P u y refl = u

J : ∀ {i j}{X : Set i}
  → (P : (x y : X) → x ≡ y → Set j)
  → ((x : X) → P x x refl)
  → (x y : X)
  → (p : x ≡ y)
  → P x y p
J P u x y p = J' (P x) (u x) y p
\end{code}

-----------------------------------------------------------------------------

## Chapter 1

### Exercise 1.1

{: .exercise}
  Given functions $$f : A \to B$$ and $$g:B\to C$$, define
  their composite $$ g\circ f:A\to C$$.
  Show that we have $$h \circ (g\circ f) \equiv (h\circ g)\circ f$$.


We define the composition operation in Agda as follows.

\begin{code}
_∘_ : ∀ {i j k} {A : Set i}{B : Set j}{C : Set k}
    → (B → C)
    → (A → B)
    → A → C
g ∘ f = λ x → g (f x)
\end{code}

Then, the `∘-assoc` shows us that associativity of this composition holds.

\begin{code}
∘-assoc : ∀ {i j k l} {A : Set i}{B : Set j}{C : Set k}{D : Set l}
        → (h : C → D)(g : B → C)(f : A → B)
        → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
∘-assoc f g h = refl
\end{code}

### Exercise 1.2

<div class="exercise">
Derive the recursion principle for products $$\mathsf{rec}_{A\times B}$$
using only the projections, and verify that the definitional equalities
are valid. Do the same for $$\Sigma$$-types.
</div>

To solve this problem we need to know:

  - The recursion principle for Σ-types:

    <p class="equation">
    $$ \mathsf{rec}_{ A \times B}
      : \prod\limits_{C : \mathcal{U}} (A \to B \to C) → A \times B \to C.
    $$
    </p>

  - The recursion principle for Σ-types:

    <p class="equation">
    $$ \mathsf{rec}_{\sum\limits_{(x : A) } B(x)}
      : \prod\limits_{(C : U)} (\Pi_{(x : A)} B(x) \rightarrow C) \rightarrow
        \sum_{(x : A)} B(x) \rightarrow C
    $$
    </p>

<div class="proof" id="proof-1.2">
Proof.<br/>
For products:<br/>
If we have the projections,
$$\mathsf{proj}_1 : A \times B \to \mathsf{A}$$ and $$\mathsf{proj}_2 : A \times B \to \mathsf{B}$$,
then $$\mathsf{rec}_2$$ is another inhabitant where

<p class="equation">
$$
\begin{align*}
&\mathsf{rec}_1 : \prod\limits_{C : \mathcal{U}} (A \to B \to C) \to A \times B \to C\\
&\mathsf{rec}_1~C~g~c~:\equiv~g~(\mathsf{proj}_1 c,~\mathsf{proj}_2 c).
\end{align*}
$$
</p>
By reflexivity, we prove the equality between $$\mathsf{rec}_{ A \times B}$$ and $$\mathsf{rec}_1$$.
<br/>
<br/>
For sums:<br/>
The projections are $$\mathsf{proj}_1 : \sum_{x : A}  Bx \to \mathsf{A}$$ and
$$\mathsf{proj}_2 :  \prod_{(p : \sum_{x : A}  Bx)} \to \mathsf{B} (\mathsf{proj}_1 p)$$.<br/>
By using these projections, we got another recursor defined as follows:
<p class="equation">
$$
\begin{aling*}
&\mathsf{rec}_2 : \prod\limits_{C : \mathcal{U}}  (\prod_{x : A} Bx \to C) \to \sum\limits_{x : A} B x \to C\\
&\mathsf{rec}_2~C~g~c~=~g~(\mathsf{proj}_1 c)~(\mathsf{proj}_2 c)
\end{align*}
$$
</p>

By reflexivity, we prove the equality between $$\mathsf{rec}_{\sum\limits_{(x : A) } B(x)}$$ and $$\mathsf{rec}_2$$.
</div>

-------------------------------------------------------------------------------

In Agda.<br>

Let's add some machinery to handle levels of the universe needed for
the following exercises including this one:

\begin{code}
open import Agda.Primitive
  using (Level; _⊔_; lzero; lsuc)
\end{code}

Σ-type (sigma type) definition (see the definition without projections
[here](https://github.com/jonaprieto/hott-book/blob/master/other/prelim.agda#L20)):

\begin{code}
module Σ-Def₁ where

  record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B proj₁

  open Σ public
-- _,_ : (proj₁ : A) → B proj₁ → Σ A B.
\end{code}

Its recursor with a function $$g : \prod_{(x : A)} B(x)\rightarrow C$$
that we provide.

\begin{code}
module Σ-Rec₁ {i j k}{A : Set i}{B : A → Set j}{C : Set k}
             (g : (x : A) → B x → C) where

  open Σ-Def₁ using (Σ ; proj₁; proj₂; _,_ )

  rec : Σ A B → C
  rec p = g (proj₁ p) (proj₂ p)

  rec-β : (x : A)(y : B x) → rec (x , y) ≡ g x y
  rec-β x y = refl
\end{code}

-------------------------------------------------------------------------------

On the other hand, the product type is just a particular case of the sigma type
when the codomain is not dependent, as we can see next by omitting the argument
in `(λ _ → B)`.

\begin{code}
module ×-Def₁ where
  open Σ-Def₁ public

  _×_ : {l k : Level} (A : Set l) (B : Set k) → Set (l ⊔ k)
  A × B = Σ A (λ _ → B)
\end{code}

Its recursor with a function $$g : A \rightarrow B \rightarrow C$$ that we provide.

\begin{code}
module ×-Rec₁ {i j k}{A : Set i}{B : Set j}{C : Set k} (g : A → B → C) where

  open ×-Def₁ using (_×_; proj₁; proj₂; _,_)

  rec : A × B → C
  rec p = g (proj₁ p) (proj₂ p)

  rec-β : (x : A)(y : B) → rec (x , y) ≡ g x y
  rec-β x y = refl
\end{code}

### Exercise 1.3

<p class="exercise">
Derive the induction principle for products $$\mathsf{ind}_{A\times B}$$,
using only the projections and the propositional uniqueness principle
$$\mathsf{uniq}_{A\times B}$$.
Verify that the definitional equalities are valid.
</p>

To solve this problem, recall the uniqueness principle (Pp. 29. HoTT-Book)

- The **propositional uniqueness principle** says that
every element of $$A\times B$$ is equal to a pair.

<p class="equation">
  $$ \mathsf{uniq}_{A\times B}
     : \prod_{(x : A \times B)} ((\mathsf{proj}_{1}(x) , \mathsf{proj}_{2}(x))
       \equiv_{A\times B} x).
  $$
</p>

Product type definition using `data`:

\begin{code}
-- this would be trivial in agda due to definitional η for records
-- so Capriotti defined a product type without η:
module ×-Def₂ where

  data _×_ {i j}(A : Set i)(B : Set j) : Set (i ⊔ j) where
    _,_ : A → B → A × B

  proj₁ : ∀ {i j}{A : Set i}{B : Set j}
        → A × B → A
  proj₁ (a , b) = a

  proj₂ : ∀ {i j}{A : Set i}{B : Set j}
        → A × B → B
  proj₂ (a , b) = b
\end{code}

Projections and $$\mathsf{uniq}_{A\times B}$$:

\begin{code}
module ×-Fun₂ {i j}{A : Set i}{B : Set j} where
  open ×-Def₂ using ( _×_;_,_; proj₁; proj₂)

  -- propositional uniqueness principle:
  uppt : (x : A × B) → (proj₁ x , proj₂ x) ≡ x
  uppt (a , b) = refl

  -- (ap functions): (a)ction over a (p)ath
  ap-proj₁ : {A B : Set}{x y : A × B}
           → (x ≡ y) → proj₁ x ≡ proj₁ y
  ap-proj₁ refl = refl

  ap-proj₂ : {A B : Set}{x y : A × B}
           → (x ≡ y) → proj₂ x ≡ proj₂ y
  ap-proj₂ refl = refl

  pair= : ∀ {A B : Set} {x w : A} {y z : B}
        → x ≡ w → y ≡ z → (x , y) ≡ (w , z)
  pair= refl refl = refl
\end{code}

The induction principle for the product type:

<p class="equation">
$$\mathsf{ind}_{A\times B} : \prod\limits_{C : A \times B \to \mathcal{U}}
  \left( \prod\limits_{x:A}\ \prod\limits_{y:B}\ \,C( (x,y) ) \right)
  \to \prod\limits_{x:A \times B}\ \,C(x)
$$
</p>

\begin{code}
module ×-Ind₂ {i j}{A : Set i}{B : Set j} where
  open ×-Def₂ using (_×_; _,_;proj₁;proj₂)
  open ×-Fun₂ using (uppt)

  ind : ∀ {k}(C : A × B → Set k)
        → ((x : A)(y : B) → C (x , y))
        → (x : A × B) → C x
  ind C g x = subst C (uppt x) (g (proj₁ x) (proj₂ x))

  ind-β : ∀ {k} (C : A × B → Set k)
          → (g : (x : A)(y : B) → C (x , y))
          → (x : A)(y : B)
          → ind C g (x , y) ≡ g x y
  ind-β C g x y = refl
\end{code}

<p class="exercise">
Generalize $$\mathsf{uniq}_{A\times B}$$ to Σ-types, and do the same for
$$\Sigma$$-types, i.e. show induction and verify the definitional equality
is valid.
</p>

Σ-type definition using `data`:

\begin{code}
module Σ-Def₂ where

  data Σ {i j}(A : Set i)(B : A → Set j) : Set (i ⊔ j) where
    _,_ : (x : A) → B x → Σ A B
\end{code}

Projections and uniqueness propositional principle:

\begin{code}
module Σ-Fun₂ {i j } {A : Set i}{B : A → Set j} where
  open Σ-Def₂ using (Σ; _,_ )

  proj₁ : Σ A B → A
  proj₁ (a , b) = a

  proj₂ : (x : Σ A B) → B (proj₁ x)
  proj₂ (a , b) = b

  uppt : (x : Σ A B) → (proj₁ x , proj₂ x) ≡ x
  uppt (a , b) = refl
\end{code}

Its induction principle:

\begin{code}
module Σ-Ind₂ {i j}{A : Set i}{B : A → Set j} where
  open Σ-Def₂ public
  open Σ-Fun₂ public

  ind : (C : Σ A B → Set (i ⊔ j))
        → ((x : A)(y : B x) → C (x , y))
        → (x : Σ A B) → C x
  ind C g (a , b) = g a b

  ind-β : (C : Σ A B → Set (i ⊔ j))
          → (g : (x : A)(y : B x) → C (x , y))
          → (x : A) (y : B x)
          → (ind C g (x , y)) ≡ g x y
  ind-β C g x y = refl
\end{code}

### Exercise 1.4

<div class="exercise">
Assuming as given only the <em>iterator</em> for natural numbers
<p class="equation">
$$\mathsf{ite} : \prod\limits_{C:\mathcal{U}} C \to (C \to C) \to \mathbb{N} \to C $$
</p>
with the defining equations
<p class="equation">
$$
\begin{align*}
\mathsf{ite}(C,c_0,c_s,0)               &\equiv c_0, \\
\mathsf{ite}(C,c_0,c_s,\mathsf{suc}(n)) &\equiv c_s(\mathsf{ite}(C,c_0,c_s,n)),
\end{align*}
$$
</p>
derive a function having the type of the recursor $$\mathsf{rec}$$.
Show that the defining equations of the recursor hold propositionally for this
function, using the induction principle for $$\mathbb{N}$$.
</div>

To solve this problem, let us define the recursor and also the induction principle
for natural numbers. (See more details about these functions in
[Induction on Natural Numbers]({% post_url 2018-02-12-induction-on-natural-numbers %})).

\begin{code}
module ℕ-Def where

  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

module ℕ-Rec where
  open ℕ-Def
  rec : ∀ (C : Set) → C → (ℕ → C → C) → ℕ → C
  rec C c₀ cₛ zero    = c₀
  rec C c₀ cₛ (suc n) = cₛ n (rec C c₀ cₛ n)

module ℕ-Ind where
  open ℕ-Def
  ind : ∀ (C : ℕ → Set)
       → (C zero)
       → (∀ (n : ℕ) → C n → C (suc n))
       → (∀ (n : ℕ) → C n)
  ind C c₀ cₛ zero    = c₀
  ind C c₀ cₛ (suc n) = cₛ n (ind C c₀ cₛ n)
\end{code}

Now, we define the iterator following the equations above:

\begin{code}
module ℕ-Fun where
  open ℕ-Def using (ℕ; zero; suc)
  open ℕ-Rec using (rec)

  ite : ∀ (C : Set) → C → (C → C) → ℕ → C
  ite C c₀ cₛ zero    = c₀
  ite C c₀ cₛ (suc n) = cₛ (ite C c₀ cₛ n)
\end{code}

Then, we now can define the recursor using this `ite` by iterating over the type
`ℕ × C` (*reloading recursion*?).


\begin{code}
-- recursor
  open ×-Def₂ using (_×_; proj₁; proj₂; _,_)

  rec₂ : ∀ (C : Set) → C → (ℕ → C → C) → ℕ → (ℕ × C)
  rec₂ C c₀ cₛ n =
      (ite (ℕ × C)
           (zero , c₀)
           (λ (p : ℕ × C) → (suc (proj₁ p) , cₛ (proj₁ p) (proj₂ p)))
           n)
\end{code}

Now, we need to establish the propositional equality between these two
definitions of recursor, i.e, between `rec` and `rec₂`. Let's use
induction to prove that.

\begin{code}
module ex1-4 where

  open ℕ-Def using (ℕ; zero; suc)
  open ℕ-Rec using (rec)
  open ℕ-Ind using (ind)
  open ℕ-Fun using (ite; rec₂)

  open ×-Def₂ using (_×_; proj₁; proj₂; _,_)
  open ×-Fun₂

  proof : (C : Set)(c₀ : C)(cₛ : ℕ → C → C)
        → ∀ (n : ℕ) → rec₂ C c₀ cₛ n ≡ (n , rec C c₀ cₛ n)

  proof C c₀ cₛ zero    = refl
  proof C c₀ cₛ (suc n) = pair= {A = ℕ}{B = C} (ap suc v) (ap₂ cₛ v u)
    where
      v : proj₁ {A = ℕ}{B = C}
        (ite
            (ℕ × C)
            (zero , c₀)
            (λ p → suc (proj₁ p) , cₛ (proj₁ p) (proj₂ p)) n)
         ≡ n
      v = (ap-proj₁ {A = ℕ}{B = C} (proof C c₀ cₛ n))

      u : proj₂ {A = ℕ}{B = C} (rec₂ C c₀ cₛ n) ≡ rec C c₀ cₛ n
      u = ap-proj₂  {A = ℕ}{B = C} (proof C c₀ cₛ n)
\end{code}


### Exercise 1.5

<div class="exercise">

Show that if we define

  $$A+B :\equiv \sum\limits_{(x : \mathbbbold{2})} \mathsf{rec}_{\mathbbbold{2}} (\mathcal{U}, A , B, x),$$

then we can give a definition of $$\ind\limits_{A + B}$$ for which the
definitional equalities holds.

</div>

To solve this problem, let us introduce the $$\mathcal{2}$$ type, that is, the
type with two constructors also called **Bool**. The constructors are also called
false and true respectively.

\begin{code}
module 𝟚-Def₁ where

  data 𝟚 : Set where
    𝟘 : 𝟚
    𝟙 : 𝟚
\end{code}


With the recursor:

\begin{code}
module 𝟚-Rec₁ where

  open 𝟚-Def₁  using (𝟘;𝟙;𝟚)

  rec : ∀ {i} {C : Set i} (a : C) (b : C ) → 𝟚 → C
  rec a b 𝟘 = a
  rec a b 𝟙 = b
  -- rec is the same if_then_else
\end{code}

and its induction principle:

\begin{code}
module 𝟚-Ind₁ where

  open 𝟚-Def₁ using (𝟘;𝟙;𝟚)

  ind : ∀ {i} {C : 𝟚 → Set i} → C 𝟘 → C 𝟙 → (c : 𝟚) → C c
  ind c₀ c₁ 𝟘 = c₀
  ind c₀ c₁ 𝟙 = c₁
\end{code}

The we define the **coproduct** $$A+B$$ as follows:

\begin{code}
module +-Def₁ where

  open Σ-Def₁ using (Σ;_,_;proj₁; proj₂) public

  open 𝟚-Def₁ using (𝟘;𝟙;𝟚)
  open 𝟚-Rec₁ using (rec)

  _+_ : ∀ {i} (A B : Set i) → Set _
  A + B = Σ 𝟚 (rec A B) -- if it's 𝟘 return A otherwise returns B

  -- the tradional constructors
  inl : ∀ {i}{A B : Set i} → A → A + B
  inl a = (𝟘 , a)

  inr : ∀ {i}{A B : Set i} → B → A + B
  inr b = (𝟙 , b)
\end{code}


Now, let's try to define the recursor for this coproduct, and later,
we'll try the dependent version of it to complete the exercise.

\begin{code}
module +-Rec₁ where

  open +-Def₁ using (_+_; inl;inr;_,_)
  open 𝟚-Def₁ using (𝟘;𝟙;𝟚)

  rec : ∀ {i j} {A B : Set i} {C : Set j}
      → (A → C)
      → (B → C)
      → A + B → C
  rec f g (𝟘 , a) = f a
  rec f g (𝟙 , b) = g b
\end{code}

Notice how the recursor of the coproduct matches with the elimination
rule of the disjunction conective also called *case analysis*. That's follows from the
[**propositions-as-types**](https://ncatlab.org/nlab/show/propositions+as+types).

![path](/assets/latexit-images/disj-elimination.png)

Finally, the induction principle for the coproduct:

\begin{code}
module +-Ind₁ where

  open +-Def₁ using (_+_; inl;inr; _,_)
  open 𝟚-Def₁ using (𝟘;𝟙;𝟚)

  ind : ∀ {i j} {A B : Set i} {C : A + B → Set j}
      → ((a : A) → C (inl a))
      → ((b : B) → C (inr b))
      → (p : A + B) → C p
  ind f g (𝟘 , a) = f a
  ind f g (𝟙 , b) = g b

  ind-β₁ : ∀ {i j} {A B : Set i} {C : A + B → Set j}
      → (f : (a : A) → C (inl a))
      → (g : (b : B) → C (inr b))
      → (x : A) → ind {C = C} f g (inl x) ≡ f x
  ind-β₁ f g x = refl

  ind-β₂ : ∀ {i j} {A B : Set i} {C : A + B → Set j}
      → (f : (a : A) → C (inl a))
      → (g : (b : B) → C (inr b))
      → (x : B) → ind {C = C} f g (inr x) ≡ g x
  ind-β₂ f g x = refl
\end{code}

### Exercise 1.6

<div class="exercise" id="ex-1.6">
Show that if we define $$A \times B :≡ \prod_{x:\mathbf{2}}\mathsf{rec}_{\mathbf{2}}\ (\mathcal{U}\, A\, B\, x)$$,
then we can give a definition of $$\mathsf{ind}_{A\times B}$$ for which the definitional
equalities propositionally (i.e. using equality types).
</div>

\begin{code}
module ×-Def₃ where
  open 𝟚-Def₁ using (𝟘;𝟙;𝟚) public
  open 𝟚-Rec₁ using (rec)

  _×_ : (A B : Set) → Set
  A × B = (x : 𝟚) → rec A B x

  _,_ : ∀ {A B} → A → B → A × B
  (a , b) 𝟘 = a
  (a , b) 𝟙 = b

  proj₁ : ∀ {A B : Set} → A × B → A
  proj₁ x = x 𝟘

  proj₂ : ∀ {A B : Set} → A × B → B
  proj₂ x = x 𝟙

module ×-Fun₃ where
  open ×-Def₃

  pair= : ∀  {A}{B} {x y : A}{a b : B}
        → x ≡ y → a ≡ b → (x , a) ≡ (y , b)
  pair= = ap₂ _,_

  postulate
    Extensionality
      : {A : Set} {B : A → Set} {f g : (x : A) → B x}
      → (∀ x → f x ≡ g x) → f ≡ g

  uniq : ∀ {A B} → (c : A × B) → (proj₁ c , proj₂ c) ≡ c
  uniq {A}{B} c = Extensionality helper
    where
      helper : ∀ (x : 𝟚) → (proj₁ c , proj₂ c) x ≡ c x
      helper 𝟘 = refl
      helper 𝟙 = refl

module ×-Ind₃ where
  open ×-Def₃
  open ×-Fun₃

  ind : ∀ {A B} (C : A × B → Set)
      → ((a : A)(b : B) → C (a , b))
      → (c : A × B) → C c
  ind {A}{B} C f c = subst C (uniq c) (f (c 𝟘) (c 𝟙))

  ind-β : ∀ {A B} (C : A × B → Set)
        → (g : (a : A)(b : B) → C (a , b))
        → ((a : A)(b : B) → ind C g (a , b) ≡ g a b)
  ind-β {A}{B} C g a b = {! !}
    where
      helper :  (u : A × B) → (proj₁ u , proj₂ u) ≡ u
      helper u =  sym (uniq (proj₁ u , proj₂ u)) · uniq u

      uniq-compute : (x : A)(y : B) → helper (x , y) ≡ refl
      uniq-compute x y = right-inverse (uniq (x , y))
        where
          right-inverse : ∀ {i}{X : Set i}{x y : X}
                        → (p : x ≡ y)
                        → (sym p) · p ≡ refl
          right-inverse refl = refl
\end{code}

### Exercise 1.8

<div class="exercise" id="exercise-1.8">

Define multiplication and exponentiation using $$\mathsf{rec}{\mathbb{N}}$$.
Verify that $$(\mathbb{N},+,0,\times,1)$$ is a semiring using only
$$\ind{\mathbb{N}}$$.

</div>

### Exercise 1.9

<div class="exercise" id="exercise-1.9">

Define the type family $$\mathsf{Fin} : \mathbb{N} \to \mathcal{U}$$ mentioned
at the end of Section 1.3, and the dependent function $$\mathsf{fmax} :
\prod_{n:\mathbb{N}} \mathsf{Fin}(n+1)$$ mentioned in Section 1.4.
</div>

\begin{code}
module Ex1-9 where

  open ℕ-Def

  data _<_ : ℕ → ℕ → Set where
    z<n : (n : ℕ) → zero < n
    s<s : (n : ℕ) (m : ℕ) → n < m → suc n < suc m

  data _≤_ : ℕ → ℕ → Set where
    z≤n : (n : ℕ) → zero ≤ n
    s≤s : (n : ℕ) (m : ℕ) → n ≤ m → suc n ≤ suc m

  open Σ-Def₁

  Fin : ℕ → Set
  Fin = λ (n : ℕ) → (Σ ℕ (λ m → (suc m ≤ n)))

  _+_ : ℕ → ℕ → ℕ
  zero    + n = n
  (suc n) + m = suc (n + m)


  fmax : (n : ℕ) → Fin (suc n)
  fmax zero    = (zero , s≤s zero zero (z≤n zero))
  fmax (suc n) = (suc n , s≤s (suc n) (suc n) (s≤s n n (helper n)))
    where
      helper : ∀ (n : ℕ) → n ≤ n
      helper zero    = z≤n zero
      helper (suc n) = s≤s n n (helper n)

  fmax-well : ∀ (n : ℕ)
            → (m : Fin (suc n))
            → proj₁ m ≤ proj₁ (fmax n)
  fmax-well zero (zero , p) = z≤n zero
  fmax-well zero (suc n , s≤s .(suc n) .zero p) = p
  fmax-well (suc n) (m , s≤s .m .(suc n) p) = p
\end{code}

### Exercise 1.11

<div class="exercise" id="exercise-1.11">
Show that for any type $$A$$, we have $$\neg\neg\neg A \to \neg A$$.
</div>

A propositional logic proof using [Agda-Prop](http://github.com/jonaprieto/agda-prop)
library:

\begin{code}
module Ex1-11 where
  open import Data.PropFormula 1

  proof : ∀ {Γ} {A}
        → Γ ⊢ ¬ ¬ ¬ A ⊃ ¬ A
  proof {Γ}{A} =
    ⊃-intro
      (¬-intro
          (¬-elim
              (weaken A (assume {Γ = Γ} (¬ (¬ (¬ A)))))
              (¬-intro
                (¬-elim
                  (assume {Γ = Γ , ¬ ¬ ¬ A , A} (¬ A))
                  (weaken (¬ A) (assume {Γ = Γ , ¬ ¬ ¬ A} A))))))
\end{code}

In type theory, the term is:

$$
λ (x : ((A → ⊥) → ⊥) → ⊥) (a : A) . x ((λ h : A → ⊥) . ha) :
((A → ⊥) → ⊥) → ⊥) → (A → ⊥)
$$

### Exercise 1.16

<div class="exercise" id="exercise-1.16">
Show that addition of natural numbers is commutative:
<p class="equation">
$$
\prod\limits_{i,j : \mathbb{N}}\ (i + j = j + i).
$$
</p>
</div>

Hint: by induction twice.

\begin{code}
module Ex1-16 where
  open ℕ-Def
  open ℕ-Ind
  open Ex1-9 using (_+_)

  proof : (i : ℕ) → ((j : ℕ) → i + j ≡ j + i)
  proof =
    ind (λ (i : ℕ) → ((j : ℕ) → i + j ≡ j + i))
      sproof₁
      sproof₂
    where
      sproof₁ : (j : ℕ) → j ≡ (j + zero)
      sproof₁ =
        ind (λ (j : ℕ) → j ≡ (j + zero))
            refl
            (λ n n≡n+zero → ap suc n≡n+zero)

      sproof₂ : (n : ℕ)
              → ((j : ℕ) → (n + j) ≡ (j + n))
              → ((j : ℕ) → suc (n + j) ≡ (j + suc n))
      sproof₂ n hyp₁ =
          ind (λ (j : ℕ) → suc (n + j) ≡ (j + suc n))
            (ap suc (sym (sproof₁ n)))
            (λ m hyp₂ →
                ap suc
                  (trans
                      (hyp₁ (suc m))
                  (trans
                      (ap suc (sym (hyp₁ m)))
                      hyp₂)))
\end{code}

## Chapter 2

### Exercise 2.6

<div class="exercise" id="exercise-2.6">
Prove that if $$p : x \equiv y$$, then the function
$$(p \cdot -) : (y \equiv z) \to (x \equiv z)$$ is an equivalence.
</div>

![path-triangle](/assets/ipe-images/path-triangle.png)

<div class="proof">
Solution. <br/>

To show the equivalence, it sufficies to show a function
$$g : x \equiv z \to y \equiv z$$ such that we can prove
$$ (p \cdot -) \circ g \sim \mathsf{id}_{x \equiv z}$$ and
$$ g \circ (p \cdot -) \sim \mathsf{id}_{y \equiv z}$$.

Let's define the function $$g$$.
<p class="equation">
$$
\begin{align*}
&g : x ≡ z → y ≡ z\\
&g~m~=~\mathsf{trans}~(\mathsf{sym}~p)~m
\end{align*}
$$
</p>
<br/>

($$(p \cdot -) \circ g \sim \mathsf{id}_{x \equiv z}$$).
Let be $$m : x ≡ z$$, we have,

<p class="equation">
$$
\begin{align*}
(p \cdot -) \circ g (m) &= (p \cdot -)~(g m)\\
                        &= (p \cdot -)~(\mathsf{trans}~(\mathsf{sym}~p)~m)\\
                        &= \mathsf{trans}~p (\mathsf{trans}~(\mathsf{sym}~p) m)\\
                        &= \mathsf{trans}~(\mathsf{trans}~p~(\mathsf{sym}~p)) m\\
                        &= \mathsf{trans}~\mathsf{refl}_{x≡z} m\\
                        &= m
\end{align*}
$$
</p>
<br/>
($$ g \circ (p \cdot -) \sim \mathsf{id}_{y \equiv z}$$).
Let be $$n : y ≡ z$$, we have,

<p class="equation">
$$
\begin{align*}
g \circ (p \cdot -) n &= g (\mathsf{trans}~p~n)\\
                      &= (\mathsf{trans}~(\mathsf{sym}~p)~(\mathsf{trans}~p~n)\\
                      &= (\mathsf{trans}~(\mathsf{trans}~(\mathsf{sym}~p)~p)~n\\
                      &= \mathsf{trans}~\mathsf{refl}_{y ≡ z} n\\
                      &= n.
\end{align*}
$$
</p>

</div>


### Exercise 2.10

<div class="exercise" id="exercise-2.10">
Prove that ∑-types are associative, in that for any $$A : \mathcal{U}$$
and families $$B : A  \to U$$ and $$C : \sum_{(x : A)} B(x) \to \mathcal{U}$$,
we have
<p class="equation">
$$\sum\limits_{(x : A)} \sum\limits_{(y : B(x))} C((x,y)) \simeq \sum\limits_{p : \sum_{x:A} B(x)} C(p)$$.
</p>
</div>

<div class="proof" id="proof-2.10">
Solution.<br/>
We can prove that the following functions $$f$$ and $$g$$ are inverses.

<p class="equation">
$$\sum\limits_{(x : A)} \sum\limits_{(y : B(x))} C((x,y)) \overset{f}{\underset{g}{\rightleftarrows}} \sum\limits_{p : \sum_{x:A} B(x)} C(p)$$.
</p>
defined by $$f(a,b,c) :\equiv ((a,b),c)$$, $$g(z,c) :\equiv (\mathsf{proj}_1 z,\mathsf{proj}_{2} z, c)$$.<br/>
Indeed,
<p class="equation">
$$
\begin{align*}
(f \circ g) (z, c) &:\equiv f (g (z,c))\\
&:\equiv f\,(\mathsf{proj}_1 z,\mathsf{proj}_{2} z, c)\\
&:\equiv ((\mathsf{proj}_1 z,\mathsf{proj}_{2} z), c)
\end{align*}
$$
</p>
</div>

\begin{code}
module Σ-Fun₁ where
  open Σ-Def₁ using (proj₁; proj₂; _,_;Σ)

  f : ∀ {A : Set} {B : A → Set} {C : Σ A B → Set}
    → Σ A (λ a → Σ (B a) (λ z → C (a , z))) → Σ (Σ A B) C
  f (a , (b , c)) = (a , b) , c

  g : ∀ {A : Set} {B : A → Set} {C : Σ A B → Set}
     → Σ (Σ A B) C → Σ A (λ a → Σ (B a) (λ z → C (a , z)))
  g {A}{B}{C} (z , c) = (proj₁ z , (proj₂ z , c))

  proof→ : ∀ {A : Set} {B : A → Set} {C : Σ A B → Set}
        → (x : Σ (Σ A B) C)
        → f {A = A}{B = B}{C = C} (g x) ≡ x
  proof→ x = refl

  proof← : ∀ {A : Set} {B : A → Set} {C : Σ A B → Set}
        → (x : Σ A (λ a → Σ (B a) (λ b → C (a , b))))
        → g {A = A}{B = B}{C = C} (f x) ≡ x
  proof← x = refl
\end{code}


### Exercise 2.13

<div class="exercise" id="exercise-2.13">
Show that $$(2 \simeq 2) \simeq 2$$.
</div>


### Exercise 2.14

<div class="exercise">

  Suppose we add to type theory [the equality reflection
  rule](https://www.youtube.com/watch?v=IlfQjWqrK6I) which says that if there is
  an element $$p : \mathsf{Id}(x,y) $$, then in fact $$ x :\equiv y$$. Prove
  that for any $$p : \mathsf{Id}(x,x)$$ we have $$p :\equiv \mathsf{refl}_x$$.\\

  <p class="equation">
  $$
    \begin{prooftree}
    \AxiomC{$\vdash p : \mathsf{Id}(x, y)$}
    \RightLabel{$\mathsf{Eq}$}
    \UnaryInfC{$\vdash x \equiv y.$}
    \end{prooftree}
    $$

  </p>

</div>

<div class="proof">
  Proof.<br/>
  We first fix the type of $$\mathsf{refl}_x$$ in order to apply effectively
  path induction.<br/>

  <p class="equation">
    $$
    \begin{prooftree}
    \AxiomC{$x : A, y : A, p : x = y ⊢ p : x = y$}
    \RightLabel{$\mathsf{Eq}$}
    \UnaryInfC{$x : A, y : A, p : x = y ⊢ x ≡ y$}
    \AxiomC{$x : A, y : A, p : x = y ⊢ \mathsf{refl}_x : x = x$}
    \BinaryInfC{$x : A, y : A, p : x = y ⊢ \mathsf{refl}_x : x = y.$}
    \end{prooftree}
    $$
    </p>
  Now, $$\mathsf{refl}_x$$ and $$p : x = y$$ in the formulation of path induction
  is well-typed. Therefore, by path induction, we show that
  $$\mathsf{Id}(p,\mathsf{refl_{x}})$$. Let be $$x : A$$ and $$C :\equiv
  \prod_{y : A} \prod_{p : x \equiv y }\ p \equiv \mathsf{refl}_{x}$$.
  It sufficies to show and inhabitant of $$C(x, \mathsf{refl}_{x})$$, and it is,
  $$\mathsf{refl}_{\mathsf{refl}_x} : \mathsf{refl}_x = \mathsf{refl}_x$$.
  By equation reflection rule, since we have an inhabitant of $$p \equiv
  \mathsf{refl}_x$$, these are judgemental equal,i.e., $$p \equiv \mathsf{refl}_x$$.

### Exercise 2.17

<div class="exercise">
<ul>
  <li> Show that if $$A \simeq A$$  and $$B \simeq B'$$, then $$(A\times B) \simeq (A'\times B')$$. </li>
  <li> Give two proofs of this fact, one using univalence and one not using it, and show that the two proofs are equal.</li>
  <li> Formulate and prove analogous results for the other type formers: $$\Sigma$$, $$\to$$, $$\Pi$$, and $$+$$. </li>
</ul>
</div>


## Chapter 3

To solve the following exercises, let us recall a few things:

- The *set* definition in HoTT:

A type $$A$$ is a **set** if for all $$x, y : A$$ and
all $$p, q : x \equiv y$$, we have $$ p \equiv q$$. In a proposition
we have

$$
\mathsf{isSet}(A) :\equiv \prod\limits_{(x,y : A)}\prod\limits_{(p,q : x \equiv y)} (p \equiv q).
$$

- The type for equivalence from $$A$$ to $$B$$

$$
  (A \simeq B) :\equiv \sum\limits_{f : A \to B} \mathsf{isequiv}(f),
$$

where

$$
\mathsf{isequiv(f)} :\equiv
  \left (\sum\limits_{g : B \to A} (f \circ g \sim \mathsf{id}_{B})\right) \times
  \left (\sum\limits_{h : B \to A} (h \circ f \sim \mathsf{id}_{A})\right)
$$

- The homotopy concept:

Let $$f , g : \prod\limits_{(x:A)} P(x)$$ be two sections of a
type family $$P : A \to \mathcal{U}$$. A **homotopy** from $$f$$ to $$g$$
is a dependent function of type

$$
(f \sim g) :\equiv \prod\limits_{x : A} (f(x) \equiv g(x)).
$$

### Exercise 3.1

<div class="exercise">
Prove that if $$A\simeq B$$ and $$A$$ is a set, then so is $$B$$.
</div>


<div class="proof" id="proof-3.1">
Proof 1.<br/>
Let be $$x,y : B$$ and $$p : x \equiv_{B} y$$ and $$q : x \equiv_{B} y$$.
We need to prove $$ p \equiv q$$.<br/>
Since $$A\simeq B$$ then there is a function $$f : A \to B$$ and some
$$g : B \to A$$ such that $$f \circ g \sim id_{B}$$.
Using this function $$g$$ over the path $$p$$ we get
$$\mathsf{ap}_{g} p : g x \equiv_{A} g y$$.
We do the same but this time over the path $$q$$, that is,
$$\mathsf{ap}_{g} q : g x \equiv_{A} g y$$.
Because of $$A$$ is a set, we have a new path called
$$m :\mathsf{ap}_{g} p \equiv_{gx \equiv_{A} gy} \mathsf{ap}_{g} q$$. <br/>

Now, an action over this path $$m$$
using the function $$\mathsf{ap}_{f} : x \equiv_{A} y \to f x \equiv_{B} f y$$
will give us


$$
\mathsf{ap}_{\mathsf{ap}_{f}} m :
(\mathsf{ap}_{f}) (\mathsf{ap}_{g} p) \equiv (\mathsf{ap}_{f})  (\mathsf{ap}_{g} q).
$$


By the lemmas in Chapter 2, we do the following reasoning:

$$
\begin{align*}
(\mathsf{ap}_{f}) (\mathsf{ap}_{g} p) \equiv (\mathsf{ap}_{f})  (\mathsf{ap}_{g} q) &=
  \mathsf{ap}_{f \circ g} p \equiv \mathsf{ap}_{f \circ g} q\\
  &=(\text{transporting by using} f \sim g)\\
  &=\mathsf{ap}_{\mathsf{id}_{B}} p \equiv \mathsf{ap}_{\mathsf{id}_{B}} q\\
  &=p \equiv q.
\end{align*}
$$

Then, we have the inhabitant, $$\mathsf{ap}_{\mathsf{ap}_{f}} m : p \equiv q$$.
</div>

<!-- <div class="proof" id="proof=3.1b"> -->
<!-- Proof 2.<br/> -->
<!-- Exhibit an equivalence. -->
<!-- </div> -->

In Agda, we can define the predicate `isSet` as follows:

\begin{code}
module sets where

  isSet : ∀ {i} (A : Set i) → Set _
  isSet A = (x y : A) → (p : x ≡ y) → (q : x ≡ y) → p ≡ q
  -- TODO
\end{code}

### Exercise 3.2

<div class="exercise">
Prove that if $$A$$ and $$B$$ are sets, then so is $$A+B$$.
</div>

To solve this exercise, we should take a look of some results from Chapter 2,
Section 2.12.

<div class="proof" id="proof-3.2">
Proof.<br/>

Let be $$x, y : A + B$$, and paths $$p : x \equiv y$$, $$q : x \equiv
y$$. Let's get a path $$p \equiv q$$.  We proceed by case analysis. If
$$x :\equiv \mathsf{inl} a$$ and $$y :\equiv \mathsf{inl} b$$, for
some $$a, b : A$$ then $$\mathsf{ap}_{\mathsf{inl}^{-1}} p : a
\equiv_{A} b$$ and $$\mathsf{ap}_{\mathsf{inl}^{-1}} q : a \equiv_{A}
b$$.

Since $$A$$ is a set, there is a path between these last two terms,
this is, $$m : \mathsf{ap}_{\mathsf{inl}^{-1}} p \equiv
\mathsf{ap}_{\mathsf{inl}^{-1}} q$$.  Now, an action over this path
$$m$$ using the $$\mathsf{inl}$$ function give us:
$$\mathsf{ap}_{\mathsf{inl}} m : \mathsf{ap}_{\mathsf{inl}}
(\mathsf{ap}_{\mathsf{inl}^{-1}} p) \equiv \mathsf{ap}_{\mathsf{inl}}
(\mathsf{ap}_{\mathsf{inl}^{-1}} q)$$.<br/>

By path algebra we get $$\mathsf{ap}_{\mathsf{inl}}
m : p \equiv q$$ since $$\mathsf{ap}_{\mathsf{inl}}
(\mathsf{ap}_{\mathsf{inl}^{-1}} p) \equiv p$$.<br/> Following the
same reasoning, we prove the case $$x :\equiv \mathsf{inr} a$$ and $$y
:\equiv \mathsf{inr} b$$.  For the latest cases, $$x :\equiv
\mathsf{inl} a$$ and $$y :\equiv \mathsf{inr} b$$ and $$x :\equiv
\mathsf{inr} a$$ and $$y :\equiv \mathsf{inl} b$$, we use the
encode-decode method to derive a proof term for 𝟘 from
$$p$$ and $$q$$. Then, we may conclude anything we wish, that is, $$p
\equiv q$$.
</div>

In Agda.

\begin{code}
module 𝟘-Def where
  data 𝟘 : Set where

module 𝟘-Rec where
  open 𝟘-Def
  rec : {A : Set} → 𝟘 → A
  rec = λ ()
\end{code}

\begin{code}
module +-Def₂ where

  data _+_ : Set → Set → Set₁ where
    inl : ∀ {B : Set} → (A : Set) → A + B
    inr : ∀ {A : Set} → (B : Set) → A + B

module +-Fun₂ where

  open +-Def₂
  open 𝟘-Def
  open 𝟘-Rec

  code : {A B : Set}
       → A + B → Set _
  code {A}{B} (inl a) = a ≡ a
  code {A}{B} (inr b) = {! !}

module +-Rec₂ where
  open +-Def₂

  rec : {A B : Set}
      → (C : Set)
      → (A → C)
      → (B → C)
      → A + B → C
  rec C f g (inl A) = f {! a  !}
  rec C f g (inr B) = g {!   !}

module +-Ind₂ where
  open +-Def₂

  -- ind : {A B : Set}
  --     → (C : A + B → Set)
  --     → ((x : A) → C (inl x))
  --     → ((x : B) → C (inr x))
  --     → (x : A + B) → C x
  -- ind C f g c x = {!   !}

-- module +-Fun₂ where
\end{code}


\begin{code}
module ex3-2 where
  open +-Def₂
  open sets using (isSet)

  p : {A B : Set}
    → isSet A → isSet B → isSet (A + B)
  p {.A} {B} setA setB (inl A) (inl .A) refl refl = refl
  p {A} {.B} setA setB (inr B) (inr .B) refl refl = refl
  p {.A} {.B} setA setB (inl A) (inr B) p q = {!   !}
  p {.A} {.B} setA setB (inr B) (inl A) p q = {!   !}
\end{code}

### Exercise 3.3

<div class="exercise">
Prove that if $$ A $$ is a set and $$B : A \to \mathcal{U}$$
is a type family such that $$B(x)$$ is a set for all
$$x : A$$, then $$\Sigma\limits_{(x:A)}\ B(x)$$ is a set.
</div>

### Exercise 3.4

<div class="exercise">
Show that $$A$$ is a mere proposition if and only
if $$A\to A$$ is contractible.
</div>

## References

{::options parse_block_html="true" /}
<div class="references">

  - {% reference hottbook %}

  - {% reference Grayson2017 %}

  - {% reference Wadler2015PT %}

  - [Capriotti's hott-exercises](https://github.com/pcapriotti/hott-exercises)

  - [Capriotti's agda-base](https://github.com/pcapriotti/agda-base/)
</div>
{::options parse_block_html="false" /}
