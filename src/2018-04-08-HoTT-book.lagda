<!DOCTYPE html>
<html lang="en-us">

  <head>
  <link href="http://gmpg.org/xfn/11" rel="profile">
  <meta http-equiv="X-UA-Compatible" content="IE=edge">
  <meta http-equiv="content-type" content="text/html; charset=utf-8">

  <!-- Enable responsiveness on mobile devices-->
  <meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=1">

  <title>
    
      HoTT-Book Exercises &middot; jonaprieto
    
  </title>

  <!-- CSS -->

  <link rel="stylesheet" href="/assets/main.css">
  <link rel="stylesheet" href="/public/css/poole.css">
  <link rel="stylesheet" href="/public/css/syntax.css">
  <link rel="stylesheet" href="/public/css/lanyon.css">
  <link rel="stylesheet" href="https://fonts.googleapis.com/css?family=PT+Serif:400,400italic,700%7CPT+Sans:400">

  <!-- TIMELINES -->
  <link title="timeline-styles" rel="stylesheet" href="https://cdn.knightlab.com/libs/timeline3/latest/css/timeline.css">

  <!-- Icons -->
  <link rel="apple-touch-icon-precomposed" sizes="144x144" href="/public/apple-touch-icon-precomposed.png">
  <link rel="shortcut icon" href="/public/favicon.ico">

  <!-- RSS -->
  <link rel="alternate" type="application/rss+xml" title="RSS" href="/atom.xml">
</head>


<head>
  <meta charset="utf-8">
  <meta http-equiv="X-UA-Compatible" content="IE=edge">
  <meta name="viewport" content="width=device-width, initial-scale=1">

  <title>HoTT-Book Exercises</title>
  <meta name="description" content="Jonathan Prieto-Cubides">

  <!-- Global site tag (gtag.js) - Google Analytics -->
  <script async src="https://www.googletagmanager.com/gtag/js?id=UA-114360791-1"></script>
  <script>
    window.dataLayer = window.dataLayer || [];
    function gtag(){dataLayer.push(arguments);}
    gtag('js', new Date());

    gtag('config', 'UA-114360791-1');
  </script>
  <!-- TIMELINE -->
  <script src="https://cdn.knightlab.com/libs/timeline3/latest/js/timeline.js"></script>

</head>




  <body>

    <!-- Target for toggling the sidebar `.sidebar-checkbox` is for regular
     styles, `#sidebar-checkbox` for behavior. -->
<input type="checkbox" class="sidebar-checkbox" id="sidebar-checkbox">

<!-- Toggleable sidebar -->
<div class="sidebar" id="sidebar">
  <div class="sidebar-item" >
    <p style="text-decoration:left">Jonathan Prieto-Cubides</p>
  </div>

  <nav class="sidebar-nav">
    <a class="sidebar-nav-item" href="/">Home</a>

    

    
    
      
    
      
    
      
    
      
    
      
    
      
        
      
    
      
        
          <a class="sidebar-nav-item" href="/about/">About</a>
        
      
    
      
        
      
    
      
        
      
    
      
        
          <a class="sidebar-nav-item" href="/HoTT-Timeline/">HoTT Timeline</a>
        
      
    
      
        
      
    
      
        
      
    
      
        
      
    
      
        
          <a class="sidebar-nav-item" href="/Interval-Analysis-Timeline/">Interval Analysis Timeline</a>
        
      
    
      
        
      
    
      
        
      
    
      
        
          <a class="sidebar-nav-item" href="/categories/">Post by category</a>
        
      
    
      
        
      
    
      
        
      
    
      
        
      
    

    <!-- <a class="sidebar-nav-item" href="/archive/v0.0.4.zip">Download</a> -->
    <!-- <a class="sidebar-nav-item" href="">GitHub project</a> -->
    <!-- <span class="sidebar-nav-item">Currently v0.0.4</span> -->
  </nav>
</div>


    <!-- Wrap is the content to shift when toggling the sidebar. We wrap the
         content to avoid any CSS collisions with our real content. -->
    <div class="wrap">
      <div class="masthead">
        <div class="container">
          <h3 class="masthead-title">
            <a href="https://github.com/jonaprieto"><img alt="@jonaprieto" class="avatar float-left mr-1" src="https://avatars3.githubusercontent.com/u/1428088?s=40&amp;v=4" height="20" width="20"></a>
            <a href="/" title="Home">jonaprieto</a>
            <small style="text-decoration:left">logs in progress<span class="modifications">(<span class="additions">+93045</span>/<span class="substractions">-70798</span>)</span></small>
          </h3>
        </div>
      
      <div class="container content">
        <div class="post">
  <h2 class="post-title">HoTT-Book Exercises</h2>
  <small><span class="post-date">Created on 08 Apr 2018  and modified on 22 Apr 2018 </small>
  </span>
  
  <p>This site is open source. {% github_edit_link "Improve this page" %}</p>

This is a self-contained version of some solutions for HoTT-Book's exercises.
The idea is to unpackage all as long as possible to get a better understanding.
Many changes can be appear running this experiment. The solutions are
type-checked as a whole using Agda v2.5.3.


## Requirements

-------------------------------------------------------------------------------

Agda pragma for consistency with HoTT:

\begin{code}
{-# OPTIONS --without-K #-}
\end{code}

-------------------------------------------------------------------------------


Equality type defintion also called Identity type:

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

<div class="exercise">
Given functions $$f : A \to B$$ and $$g:B\to C$$, define
their composite $$ g\circ f:A\to C$$.
</div>

\begin{code}
_∘_ : ∀ {i j k} {A : Set i}{B : Set j}{C : Set k}
    → (B → C)
    → (A → B)
    → A → C
g ∘ f = λ x → g (f x)
\end{code}
<div class="exercise">
Show that we have $$h \circ (g\circ f) \equiv (h\circ g)\circ f$$.
</div>
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

Let's add some machinery to handle levels of the universe needed for
the following exercises including this one:

\begin{code}
open import Agda.Primitive public
  using (Level; _⊔_; lzero; lsuc)
\end{code}

To solve this problem we need:

  - Σ-type definition

  - Product type definition

  - Review the recursion principle, what exactly it consists of.
    Maybe this refresh our minds (see Pp. 42 HoTT-Book).

    <p class="equation">
    $$ \mathsf{rec}_{\sum\limits_{(x : A) } B(x)}
      : \prod\limits_{(C : U)} (\Pi_{(x : A)} B(x) \rightarrow C) \rightarrow
        \sum_{(x : A)} B(x) \rightarrow C
    $$
    </p>

-------------------------------------------------------------------------------

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
[Induction on Natural Numbers](/type-theory/2018/02/12/induction-on-natural-numbers/)).

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
  ind f g (𝟘 , a) = f a -- TODO any reason to not use this definition?
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

## Chapter 2



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
Sketch of the proof.<br/>
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

<p class="equation">
$$
\mathsf{ap}_{\mathsf{ap}_{f}} m :
(\mathsf{ap}_{f}) (\mathsf{ap}_{g} p) \equiv (\mathsf{ap}_{f})  (\mathsf{ap}_{g} q).
$$
</p>
By the lemmas in Chapter 2, we do the following reasoning:

<p class="equation">
$$
\begin{align*}
(\mathsf{ap}_{f}) (\mathsf{ap}_{g} p) \equiv (\mathsf{ap}_{f})  (\mathsf{ap}_{g} q) &=
  \mathsf{ap}_{f \circ g} p \equiv \mathsf{ap}_{f \circ g} q\\
  &=\mathsf{ap}_{\mathsf{id}_{B}} p \equiv \mathsf{ap}_{\mathsf{id}_{B}} q\\
  &= p \equiv q.
\end{align*}
$$<br/>
</p>
Then, we have the inhabitant, $$\mathsf{ap}_{\mathsf{ap}_{f}} m : p \equiv q$$.
</div>

Now, let's verify this in Agda.

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
Sketch of the Proof.<br/>

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

We conclude by Lemmas in Chapter 2, that $$\mathsf{ap}_{\mathsf{inl}}
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

But first let's define the empty type:

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
  code {A}{B} (inr b) = {!!}

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

### References

* Univalent Foundations Program, T. (2013). Homotopy Type Theory: Univalent Foundations of Mathematics. Institute for Advanced Study.

* [Capriotti's hott-exercises](https://github.com/pcapriotti/hott-exercises).

* [Capriotti's agda-base](https://github.com/pcapriotti/agda-base/)

  
</div>

<div class="related">
  <h2>Related Posts</h2>
  <ul class="related-posts">
    
  </ul>
</div>

<div id="disqus_thread"></div>
<script>

/**
*  RECOMMENDED CONFIGURATION VARIABLES: EDIT AND UNCOMMENT THE SECTION BELOW TO INSERT DYNAMIC VALUES FROM YOUR PLATFORM OR CMS.
*  LEARN WHY DEFINING THESE VARIABLES IS IMPORTANT: https://disqus.com/admin/universalcode/#configuration-variables*/
/*
var disqus_config = function () {
this.page.url = PAGE_URL;  // Replace PAGE_URL with your page's canonical URL variable
this.page.identifier = PAGE_IDENTIFIER; // Replace PAGE_IDENTIFIER with your page's unique identifier variable
};
*/
(function() { // DON'T EDIT BELOW THIS LINE
var d = document, s = d.createElement('script');
s.src = 'https://jonaprieto-blog.disqus.com/embed.js';
s.setAttribute('data-timestamp', +new Date());
(d.head || d.body).appendChild(s);
})();
</script>
<noscript>Please enable JavaScript to view the <a href="https://disqus.com/?ref_noscript">comments powered by Disqus.</a></noscript>

      </div>
      
      </div>
    </div>

    <label for="sidebar-checkbox" class="sidebar-toggle"></label>
    <!-- Import jQuery -->
<script type="text/javascript" src="/assets/jquery.js"></script>

<!-- Script which allows for foldable code blocks -->
<script type="text/javascript">
 $('div.foldable pre').each(function(){
     var autoHeight = $(this).height();
     var lineHeight = parseFloat($(this).css('line-height'));
     var plus    = $("<div></div>");
     var horLine = $("<div></div>");
     var verLine = $("<div></div>");
     $(this).prepend(plus);
     plus.css({
         'position'         : 'relative',
         'float'            : 'right',
         'right'            : '-' + (0.5 * lineHeight - 1.5) + 'px',
         'width'            : lineHeight,
         'height'           : lineHeight});
     verLine.css({
         'position'         : 'relative',
         'height'           : lineHeight,
         'width'            : '3px',
         'background-color' : '#C1E0FF'});
     horLine.css({
         'position'         : 'relative',
         'top'              : '-' + (0.5 * lineHeight + 1.5) + 'px',
         'left'             : '-' + (0.5 * lineHeight - 1.5) + 'px',
         'height'           : '3px',
         'width'            : lineHeight,
         'background-color' : '#C1E0FF'});
     plus.append(verLine);
     plus.append(horLine);
     $(this).height(2.0 * lineHeight);
     $(this).css('overflow','hidden');
     $(this).click(function(){
         if ($(this).height() == autoHeight) {
             $(this).height(2.0 * lineHeight);
             plus.show();
         }
         else {
             $(this).height('auto');
             plus.hide();
         }
     });
 });
</script>

<!-- Script which renders TeX using tex.s2cms.ru -->
<script src="//tex.s2cms.ru/latex.js"></script>
<script type="text/javascript">
 $("script[type='math/tex']").replaceWith(
     function(){
         var tex = $(this).text();
         return "$$" + tex + "$$";
     });
 $("script[type='math/tex; mode=display']").replaceWith(
     function(){
         var tex = $(this).text().replace(/%.*?(\n|$)/g,"");
         return "<p class=\"equation\">" +
                 "$$" + tex + "$$" +
                "</p>";
     });
</script>


    <script>
      (function(document) {
        var toggle = document.querySelector('.sidebar-toggle');
        var sidebar = document.querySelector('#sidebar');
        var checkbox = document.querySelector('#sidebar-checkbox');

        document.addEventListener('click', function(e) {
          var target = e.target;

          if(!checkbox.checked ||
             sidebar.contains(target) ||
             (target === checkbox || target === toggle)) return;

          checkbox.checked = false;
        }, false);
      })(document);
    </script>
  </body>
</html>
