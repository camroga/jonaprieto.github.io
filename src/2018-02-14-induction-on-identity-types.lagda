<!DOCTYPE html>
<html lang="en-us">

  <head>
  <link href="http://gmpg.org/xfn/11" rel="profile">
  <meta http-equiv="X-UA-Compatible" content="IE=edge">
  <meta http-equiv="content-type" content="text/html; charset=utf-8">

  <!-- Enable responsiveness on mobile devices-->
  <meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=1">

  <title>
    
      Induction on Identity Types &middot; jonaprieto
    
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

  <title>Induction on Identity Types</title>
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
  <h2 class="post-title">Induction on Identity Types</h2>
  <small><span class="post-date">Created on 14 Feb 2018  and modified on 16 Apr 2018 </small>
  </span>
  
  We present here a new type former to introduce identities.
The identity or equality type is defined as follows:

```agda
data Id (A : Set) (x y : A) : Set where
  refl : Id A x y
```

The only rule/constructor is `refl` that represents the reflexivity property of
the inductive types. Sometimes we can another definition for refl, that is
similar as the presented above but using the equality symbol (`_≡_`) and Π-type.

```
refl: Π x:A. x ≡ x
```

In Agda we will write this

```agda
infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x
```

instead of

```agda
infix 3 _≡_
_≡_ : ∀ {A : Set} → (x y : A) → Id A x y
x ≡ y = refl
```

However, this type is already present in the Agda standard library, so let's use it

\begin{code}
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
\end{code}

### Martin-Löf's rules about identity type

- ML1. For any type `X`, for each `a` and `b` of it, there is a type `a = b`

- ML2. There is an element `refl x : x = x` for each `x : X`

- ML3. Induction for equality:

    > For any type $$X$$ and for any element $$a$$ of it, given a family of types $$P(b,e)$$
    depending on parameters $$b$$ of type $$X$$ and $$e$$ of type $$a=b$$, in order to
    define elements $$f(b,e) : P(b,e)$$ of all of them it suffices to provide an
    element $$p$$ of $$P(a, refl\ a)$$.  The resulting function $$f$$ may be regarded as
    having been completely defined by the single definition $$f(a, refl\ a) := p$$.


    > Intuitively, the induction principle for equality amounts to saying that the
    element $$refl a$$ ``generates'' the system of types $$a=b$$, as $$b$$ ranges
    over elements of $$A$$.
    <cite>[Daniel Grayson](http://arxiv.org/abs/1711.01477)</cite>

We will show in a moment more about ML3 rule from the univalance perspective,
that is, the homotopy type theory perspective. The main diference up to now, we
give another meaning of `a = b`, insteaf of thinking about it as a proof of such
a equality, we are going to think as a `path space` in a topological space
associated to `A`


In the following, we may encounter with [levels](https://pigworker.wordpress.com/2015/01/09/universe-hierarchies/) in Agda.
The small types are those that belongs to the first level 0, types of level 1 are
those formed by using small types, and so on. The small types in Agda has `Set` type ,
types formed by these small types have `Set 1` type, and so on with `Set i` type.

### Path induction

We call *path* to the inhabitant of the identity type, that is, p : x ≡ y for
some x and y of type A. We can probably think that there is only one p, but
there are many identifications between x and y from the HoTT perspective. That's
the reason we talk about one path and one set of paths, the *path space*.

![path](/assets/ipe-images/path.png)

Now, we introduce the induction principle for the identity type with `pi`
abbreviation of path induction also called elimination identity and noted
[`J`](https://homotopytypetheory.org/2011/04/10/just-kidding-understanding-identity-elimination-in-homotopy-type-theory/).

\begin{code}
pi
  : ∀ {i} {A : Set}
  → (C : (x y : A) → x ≡ y → Set i)
  → (∀ (x : A) → C x x refl)
  → ∀ (x y : A) (p : x ≡ y) → C x y p
\end{code}

defined by the equation

\begin{code}
pi {A} C c x .x refl = c x
\end{code}

Let us unpackage this:

To contruct something of the type (∀ (x y : A) (p : x ≡ y) → C x y p) we need that:

+ C can construct types from three arguments: two points and one path.

+ C holds in the *diagonal*, that is, we need to prove or find an
inhabitant of C x x refl for all x.

Then, as result, the property C holds for all paths in general.

### Based path induction

A differente or more customized version of path induction is the based
path induction abbreviated as `bpi`.

\begin{code}
bpi
  : ∀ {i} {A : Set}
  → (a : A)
  → (C : (y : A) → a ≡ y → Set i)
  → C a refl
  → (y : A) (p : a ≡ y) → C y p
\end{code}

defined by the equation

\begin{code}
bpi a C c .a refl = c
\end{code}

*Remark*: we can not repeat in Agda a name variable in an equation. But using
the dot accompanying as a prefix of a variable, it tells the typechecker that
there is only one possible value and it corresponds to that variable.

Let us unpackage this:

+ With a fixed endpoint a

+ if we consider all paths whiches start with a

+ to have the property for all y:A and for all paths a ≡ y the only
necessary is to have C a refl, that is, holds C for the *base case*.


### Equivalence between path induction and base path induction

Path-induction follows from path based induction.

\begin{code}
bpi⇒pi
  : ∀ {A : Set}
  → (C : (x y : A) → x ≡ y → Set)
  → (c : (x : A) → C x x refl)
  → (x y : A) (p : x ≡ y) → C x y p

bpi⇒pi {A} C c x = g
  where
    C′ : (y : A) → x ≡ y → Set
    C′ = C x

    c′ : C x x refl
    c′  = c x

    g : ∀ (y : A) (p : x ≡ y) → C′ y p
    g = bpi x C′ c′
\end{code}

The other direction:

\begin{code}
pi⇒bpi
  : ∀ {A : Set}
  → (a : A)
  → (C : (y : A) → a ≡ y → Set)
  → (c : C a refl)
  → ∀ (y : A) (p : a ≡ y) → C y p

pi⇒bpi {A} a C c y p = f a y p C c
  where
    D : ∀ (x y : A) → x ≡ y → Set₁
    D x y p = (L : (z : A) → x ≡ z → Set) → L x refl → L y p

    d : ∀ (x : A) → D x x refl
    d = λ x C c → c

    f : ∀ (x y : A) (p : x ≡ y) → D x y p
    f = pi D d
\end{code}

## References

* [Univalent Foundations Program, T. (2013). Homotopy Type Theory: Univalent Foundations of Mathematics. Institute for Advanced Study][HoTT]
* [Grayson, D. R. (2017). An introduction to univalent foundations for mathematicians.][Grayson]


[HoTT]:https://homotopytypetheory.org/book.
[Grayson]:http://arxiv.org/abs/1711.01477

  
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
