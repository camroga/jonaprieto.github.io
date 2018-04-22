<!DOCTYPE html>
<html lang="en-us">

  <head>
  <link href="http://gmpg.org/xfn/11" rel="profile">
  <meta http-equiv="X-UA-Compatible" content="IE=edge">
  <meta http-equiv="content-type" content="text/html; charset=utf-8">

  <!-- Enable responsiveness on mobile devices-->
  <meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=1">

  <title>
    
      Function Type &middot; jonaprieto
    
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

  <title>Function Type</title>
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
            <small style="text-decoration:left">logs in progress<span class="modifications">(<span class="additions">+59040</span>/<span class="substractions">-36711</span>)</span></small>
          </h3>
        </div>
      
      <div class="container content">
        <div class="post">
  <h2 class="post-title">Function Type</h2>
  <small><span class="post-date">Created on 10 Feb 2018  and modified on 15 Apr 2018 </small>
  </span>
  
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
