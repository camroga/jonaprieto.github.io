<!DOCTYPE html>
<html lang="en-us">

  <head>
  <link href="http://gmpg.org/xfn/11" rel="profile">
  <meta http-equiv="X-UA-Compatible" content="IE=edge">
  <meta http-equiv="content-type" content="text/html; charset=utf-8">

  <!-- Enable responsiveness on mobile devices-->
  <meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=1">

  <title>
    
      Path Algebra in HoTT &middot; jonaprieto
    
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

  <title>Path Algebra in HoTT</title>
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
  <h2 class="post-title">Path Algebra in HoTT</h2>
  <small><span class="post-date">Created on 16 Feb 2018  and modified on 16 Apr 2018 </small>
  </span>
  
  In Univalence we have a different interpretation of type theory. We replace the
set-theoretical notion of sets for types and we use the *topological space*
notion instead. The judgement $$a : A$$ for a type $$A$$ is now the point $$a$$ in the
topological space $$A$$. We also include the identity type as a primary type.
Changing the notation of this type about a proof of the equality $$a = b$$ to a
*path space*. This path space comprehends all paths with $$a$$ as the starting
point and $$b$$ as the end point. The inhabitant of this type is called a *path*.

### Prerequisites

To work with the identity type let's use the type `(_≡_)` defined in
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

![path](/assets/ipe-images/path-concatenation.png)

\begin{code}
infixr 20 _·_
_·_ : ∀ {A : Set}
    → {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → x ≡ z
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

As you can see, the path inversion is the symmetric property for the
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
trans : ∀ {A : Set}{x x' : A}
      → (B : A → Set) → (y : B x) → (u : x ≡ x') → B x'
trans B y refl  = y
\end{code}

![path](/assets/ipe-images/transport-fiber.png)

  
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
