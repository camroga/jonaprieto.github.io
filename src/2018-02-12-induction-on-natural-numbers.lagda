<!DOCTYPE html>
<html lang="en-us">

  <head>
  <link href="http://gmpg.org/xfn/11" rel="profile">
  <meta http-equiv="X-UA-Compatible" content="IE=edge">
  <meta http-equiv="content-type" content="text/html; charset=utf-8">

  <!-- Enable responsiveness on mobile devices-->
  <meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=1">

  <title>
    
      Induction on Natural Numbers &middot; jonaprieto
    
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

  <title>Induction on Natural Numbers</title>
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
  <h2 class="post-title">Induction on Natural Numbers</h2>
  <small><span class="post-date">Created on 12 Feb 2018  and modified on 13 Apr 2018 </small>
  </span>
  
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

-------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------

#### Examples:

**Add**

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
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

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
  add   : ℕ → (ℕ → ℕ)
  add n : ℕ → ℕ
  ```

  + When the first argument is zero, we just return the second argument, that is,
  `add 0` is the identity function. Thus `c₀` is `(λ m → m)`.

  ```agda
  add zero m = m
  ```

  + Question: why `((λ n g m → suc (g m)))`?


**Multiplication**

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

-------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------

### Another induction principle

<div class="exercise">
Assuming the ordinary induction principle (i.e., <a href="#induction">indℕ</a>)
derives the transfinite induction principle.<br/>

For a unary predicate $$P : \mathbb{N} \to \mathcal{U}$$, if

<p class="equation">
$$
\prod\limits_{n : \mathbb{N}} \left ( \prod\limits_{k : \mathbb{N}} (k < n \to P(k)) \to P(n) \right)
$$
</p>

then for all $$n : \mathbb{N}$$ we have $$P(n)$$.
</div>

To solve this problem, we need to define a type for the *less than* (`_<_`) relationship
between natural numbers but we also have to define the disjunction to
make a case analysis in our proof. Let's see. You may skip this first part.

\begin{code}
module ℕ-transInd (P : ℕ → 𝒰) where

  data _<_ : ℕ → ℕ → Set where
    z<s : ∀ {n : ℕ}   → zero < suc n
    s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

  data _⊎_ : Set → Set → Set where
    inj₁ : ∀ {A B : Set} → A → A ⊎ B
    inj₂ : ∀ {A B : Set} → B → A ⊎ B

  ⊎-elim : ∀ {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
  ⊎-elim f g (inj₁ x) = f x
  ⊎-elim f g (inj₂ y) = g y

  sym : {k n : ℕ} → k ≡ n → n ≡ k
  sym refl = refl

  subst : {k n : ℕ} → k ≡ n → P k → P n
  subst refl pk = pk

  postulate -- TODO
    <-property : ∀ {k : ℕ} {n : ℕ}
             → k < suc n
             → (k < n) ⊎ (k ≡ n)
\end{code}

**Proof**:
We use induction to get an inhabitant of the $$G$$ proposition.
The induction was using pattern matching on $$n$$ in Agda.
At the end, we use the hypothesis with this inhabitant of $$G$$.

$$
G : \prod\limits_{(n : \mathbb{N})}\ \left(\prod\limits_{(k : \mathbb{N})}\ ((k < n) \to P (k))\right)
$$

where $$P : \mathbb{N} \to \mathcal{U}$$.


\begin{code}
-- proof
  indℕ⇒transFindℕ
    : (hyp : (n : ℕ) → ((k : ℕ) → (k < n) → P k) → P n)
    → ((n : ℕ) → P n)

  indℕ⇒transFindℕ hyp zero    = hyp zero (λ k → λ ())
  indℕ⇒transFindℕ hyp (suc n) = hyp (suc n) (G (suc n))
    where
      G : ∀ (n : ℕ) → ((k : ℕ) → (k < n) → P k)
      G zero    = λ k → λ () -- imposible
      G (suc n) k k<n+1 =
        ⊎-elim --
          -- 1. when k < n
          (λ k<n → G n k k<n)
          -- 2. when k ≡ n
          (λ k≡n → subst (sym k≡n) (hyp n (G n)))
          -- eliminiting two cases: (k < n) ⊎ (k ≡ n)
          (<-property k<n+1)
\end{code}

### Conclusion

Induction as it was presented here is stronger than recursion.
The recursor `recℕ` is the *no-dependent* version of `indℕ` function.

Summing up, the recursor `recℕ` allows to define a function `f : ℕ → C` where `C : 𝒰`
by defining two equations:

+ `f(0) ≡ c₀` for `c₀ : C`
+ `f(suc n) ≡ cₛ(n, f(n))` for `cₛ : ℕ → C → C`

### References

* [Univalent Foundations Program, T. (2013). Homotopy Type Theory: Univalent Foundations of Mathematics. Institute for Advanced Study][HoTT]

* [Coquand, T. (1992). Pattern matching with dependent types. Informal Proceedings
of Logical Frameworks.][Coquand]

[HoTT]:https://homotopytypetheory.org/book.
[Grayson]:http://arxiv.org/abs/1711.01477
[Coquand]:https://doi.org/10.1.1.37.9541

  
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
