<!DOCTYPE html>
<html lang="en-us">

  <head>
  <link href="http://gmpg.org/xfn/11" rel="profile">
  <meta http-equiv="X-UA-Compatible" content="IE=edge">
  <meta http-equiv="content-type" content="text/html; charset=utf-8">

  <!-- Enable responsiveness on mobile devices-->
  <meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=1">

  <title>
    
      Π-type exercise &middot; jonaprieto
    
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

  <title>Π-type exercise</title>
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
  <h2 class="post-title">Π-type exercise</h2>
  <small><span class="post-date">Created on 09 Feb 2018  and modified on 18 Mar 2018 </small>
  </span>
  
  Consider the following type:

```
(Πx:A.Πy:A.(P x ⟶ Q x y)) ⟶ Πx:A.(P x ⟶ Πy:A.Q x y) .
```

In Agda:

\begin{code}
type : Set₁
type = ∀ {A : Set} {P : A → Set} {Q : A → A → Set}
       → ((x y : A) → P x → Q x y)
       → ((x : A) → (P x → (y : A) → Q x y))
\end{code}

with an inhabitant of this type:

\begin{code}
inhab : type
inhab {A}{P}{Q} f = λ x px y → f x y px
\end{code}

  
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
