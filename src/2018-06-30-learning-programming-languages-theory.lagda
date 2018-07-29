---
layout: "post"
title: "Programming languages"
date: "2018-06-30"
categories: learning
agda: true
toc: true
---

Functional programming is an exciting field that combines many disciplines like
logic, type theory, categories, algebra, and of course, programming languages.

\begin{code}
_ = Set -- Trick for .lagda in jekyll
\end{code}

## [Advanced Functional Programming CS410-17 by Conor McBride](https://github.com/pigworker/CS410-17/)

- [x] [Programs and Proofs](https://www.youtube.com/watch?v=O4oczQry9Jw)
- [x] [more Programs and Proofs, Introducing "with"](https://www.youtube.com/watch?v=qcVZxQTouDk)

{: .foldable}
\begin{code}

module Lec1Done where

  -- the -- mark introduces a "comment to end of line"

  ------------------------------------------------------------------------------
  -- some basic "logical" types
  ------------------------------------------------------------------------------

  data Zero : Set where
    -- to give a value in a data, choose one constructor
    -- there are no constructors
    -- so that's impossible

  record One : Set where
    -- to give a value in a record type, fill all its fields
    -- there are no fields
    -- so that's trivial
    --   (can we have a constructor, for convenience?)
    constructor <>

  {-# COMPILE GHC One = data () (()) #-}


  data _+_ (S : Set)(T : Set) : Set where -- "where" wants an indented block
    -- to offer a choice of constructors, list them with their types
    inl : S -> S + T     -- constructors can pack up stuff
    inr : T -> S + T
    -- in Haskell, this was called "Either S T"

  {-
  record _*_ (S : Set)(T : Set) : Set where
    field -- introduces a bunch of fields, listed with their types
      fst : S
      snd : T
    -- in Haskell, this was called "(S, T)"
  -}

  -- _*_ IS GENERALIZED BY SIGMA

  record Sg (S : Set)(T : S -> Set) : Set where  -- Sg is short for "Sigma"
    constructor _,_
    field -- introduces a bunch of fields, listed with their types
      fst : S
      snd : T fst
  open Sg public -- brings fst and snd into scope hereafter unto all inheritors
  -- make _*_ from Sg ?
  _*_ : Set -> Set -> Set
  S * T = Sg S \ _ -> T
  infixr 4 _*_ _,_



  ------------------------------------------------------------------------------
  -- some simple proofs
  ------------------------------------------------------------------------------

  comm-* : {A : Set}{B : Set} -> A * B -> B * A
  comm-* record { fst = a ; snd = b } = record { fst = b ; snd = a }

  assocLR-+ : {A B C : Set} -> (A + B) + C -> A + (B + C)
  assocLR-+ (inl (inl a)) = inl a
  assocLR-+ (inl (inr b)) = inr (inl b)
  assocLR-+ (inr c)       = inr (inr c)

  _$*_ : {A A' B B' : Set} -> (A -> A') -> (B -> B') -> A * B -> A' * B'
  (f $* g) (a , b) = f a , g b

  -- record syntax is rather ugly for small stuff; can we have constructors?

  _$+_ : {A A' B B' : Set} -> (A -> A') -> (B -> B') -> A + B -> A' + B'
  (f $+ g) (inl a) = inl (f a)
  (f $+ g) (inr b) = inr (g b)

  -- K for constant!
  combinatorK : {A E : Set} -> A -> E -> A
  combinatorK = \ a _ -> a

  -- Arrows associate to the right!
  -- Application associates to the left!
  combinatorS : {S T E : Set} -> (E -> S -> T) -> (E -> S) -> E -> T
  combinatorS = \ f s e -> (f e) (s e)

  -- all classical programms could be written using just K and S

  id : {X : Set} -> X -> X
  -- id x = x -- is the easy way; let's do it a funny way to make a point
  id = combinatorS combinatorK (combinatorK {_} {One})
  --                          no choice for -^   ^^^^- could be anything

  naughtE : {X : Set} -> Zero -> X
  naughtE = λ ()

  -- standard composition: f << g is "f after g"
  _<<_ : {X Y Z : Set} -> (Y -> Z) -> (X -> Y) -> (X -> Z)
  (f << g) x = f (g x)

  -- diagrammatic composition: f >> g is "f then g"
  _>>_ : {X Y Z : Set} -> (X -> Y) -> (Y -> Z) -> (X -> Z)
                       --       ^^^^^^^^          dominoes!
  (f >> g) x = g (f x)

  -- infix application
  _$_ : {S : Set}{T : S -> Set}(f : (x : S) -> T x)(s : S) -> T s
  f $ s = f s
  infixl 2 _$_


  ------------------------------------------------------------------------------
  -- from logic to data
  ------------------------------------------------------------------------------

  data Nat : Set where
    zero : Nat
    suc  : Nat -> Nat     -- recursive data type

  {-# BUILTIN NATURAL Nat #-}
  --  ^^^^^^^^^^^^^^^^^^^       this pragma lets us use decimal notation

  _+N_ : Nat -> Nat -> Nat
  zero  +N y = y
  suc x +N y = suc (x +N y)      -- there are other choices

  four : Nat
  four = 2 +N 2


  ------------------------------------------------------------------------------
  -- and back to logic
  ------------------------------------------------------------------------------

  -- A cructial notation in logic is the equility
  data _==_ {X : Set} : X -> X -> Set where
    refl : (x : X) -> x == x           -- the relation that's "only reflexive"

  {-# BUILTIN EQUALITY _==_ #-}  -- we'll see what that's for, later

  _=$=_ : {X Y : Set}{f f' : X -> Y}{x x' : X} ->
          f == f' -> x == x' -> f x == f' x'
  refl f =$= refl x = refl (f x)
  infixl 2 _=$=_

  zero-+N : (n : Nat) -> (zero +N n) == n
  zero-+N n = refl n

  +N-zero : (n : Nat) -> (n +N zero) == n
  +N-zero zero     = refl zero
  +N-zero (suc n)  = refl suc =$= +N-zero n

  assocLR-+N : (x y z : Nat) -> ((x +N y) +N z) == (x +N (y +N z))
  assocLR-+N zero    y z = refl (y +N z)
  assocLR-+N (suc x) y z = refl suc =$= assocLR-+N x y z


  ------------------------------------------------------------------------------
  -- computing types
  ------------------------------------------------------------------------------

  -- In Haskell the following function can not written. Types lives outside
  -- the universe where you write.
  _>=_ : Nat -> Nat -> Set
  x     >= zero   = One
  zero  >= suc y  = Zero
  suc x >= suc y  = x >= y

  refl->= : (n : Nat) -> n >= n
  refl->= zero    = record {}
  refl->= (suc n) = refl->= n

  trans->= : (x y z : Nat) -> x >= y -> y >= z -> x >= z
  trans->=      x       y  zero    x>=y y>=z = record {}
  trans->=      x  zero    (suc z) x>=y ()
  trans->= zero    (suc y) (suc z) ()   y>=z
  trans->= (suc x) (suc y) (suc z) x>=y y>=z = trans->= x y z x>=y y>=z


  ------------------------------------------------------------------------------
  -- construction by proof
  ------------------------------------------------------------------------------

  {- -- MOVED UP TO REPLACE _*_
  record Sg (S : Set)(T : S -> Set) : Set where  -- Sg is short for "Sigma"
    constructor _,_
    field -- introduces a bunch of fields, listed with their types
      fst : S
      snd : T fst
  -- make _*_ from Sg ?
  _*_ : Set -> Set -> Set
  S * T = Sg S \ _ -> T
  -}

  difference : (m n : Nat) -> m >= n -> Sg Nat \ d -> m == (n +N d)
                                     --       (                    )
  difference m       zero    m>=n = m , refl m
  difference zero    (suc n) ()
  difference (suc m) (suc n) m>=n with difference m n m>=n
  difference (suc m) (suc n) m>=n | d , q = d , (refl suc =$= q)

  tryMe      = difference 42 37 _
  -- don'tTryMe = difference 37 42 {!!}


  ------------------------------------------------------------------------------
  -- things to remember to say
  ------------------------------------------------------------------------------

  -- why the single colon?

  -- what's with all the spaces?

  -- what's with identifiers mixing letters and symbols?

  -- what's with all the braces?

  -- what is Set?

  -- are there any lowercase/uppercase conventions?

  -- what's with all the underscores?
  --   (i)   placeholders in mixfix operators
  --   (ii)  don't care (on the left)
  --   (iii) go figure (on the right)

  -- why use arithmetic operators for types?

  -- what's the difference between = and == ?

  -- can't we leave out cases?

  -- can't we loop?

  -- the function type is both implication and universal quantification,
  -- but why is it called Pi?

  -- why is Sigma called Sigma?

  -- B or nor B?

open Lec1Done
\end{code}

- [ ] [Proof by Induction](https://www.youtube.com/watch?v=8xFT9FPlm18)


{: .foldable}
\begin{code}
module Lec2Done where

  ------------------------------------------------------------------------------
  -- Vectors  -- the star of exercise 1
  ------------------------------------------------------------------------------

  data Vec (X : Set) : Nat -> Set where  -- like lists, but length-indexed
    []   :                              Vec X zero
    _,-_ : {n : Nat} -> X -> Vec X n -> Vec X (suc n)
  infixr 4 _,-_   -- the "cons" operator associates to the right

  ------------------------------------------------------------------------------
  -- Taking a Prefix of a Vector
  ------------------------------------------------------------------------------

  vTake : (m n : Nat) -> m >= n -> {X : Set} -> Vec X m -> Vec X n
  vTake m       zero    m>=n xs = []
  vTake zero    (suc n) ()   xs
  vTake (suc m) (suc n) m>=n (x ,- xs) = x ,- vTake m n m>=n xs

  ------------------------------------------------------------------------------
  -- Things to Prove
  ------------------------------------------------------------------------------

  vTakeIdFact : (n : Nat){X : Set}(xs : Vec X n) ->
                vTake n n (refl->= n) xs == xs
  vTakeIdFact zero    []        = refl []
  vTakeIdFact (suc n) (x ,- xs) = refl (x ,-_) =$= vTakeIdFact n xs

  vTakeCpFact : (m n p : Nat)(m>=n : m >= n)(n>=p : n >= p)
                {X : Set}(xs : Vec X m) ->
                vTake m p (trans->= m n p m>=n n>=p) xs ==
                  vTake n p n>=p (vTake m n m>=n xs)
  {- hit p first: why? -}
  vTakeCpFact m n zero m>=n n>=p xs = refl []
    {- hit n second: why? -}
  vTakeCpFact m zero (suc p) m>=n () xs
      {- hit m third: why? -}
  vTakeCpFact zero (suc n) (suc p) () n>=p xs
        {- hit xs fourth: why? -}
  vTakeCpFact (suc m) (suc n) (suc p) m>=n n>=p (x ,- xs) =
          {- build the shared skeleton -}
    refl (x ,-_) =$=
            {- invoke the induction (preferably by C-c C-a -}
      vTakeCpFact m n p m>=n n>=p xs


  ------------------------------------------------------------------------------
  -- Splittings (which bear some relationship to <= from ex1)
  ------------------------------------------------------------------------------

  data _<[_]>_ : Nat -> Nat -> Nat -> Set where
    zzz : zero <[ zero ]> zero
    lll : {l m r : Nat} ->      l <[     m ]> r
                        ->  suc l <[ suc m ]> r
    rrr : {l m r : Nat} ->      l <[     m ]>     r
                        ->      l <[ suc m ]> suc r

  _>[_]<_ : {X : Set}{l m r : Nat} ->
            Vec X l -> l <[ m ]> r -> Vec X r ->
            Vec X m
  {- why is the rrr line first? -}
  xl        >[ rrr nnn ]< (x ,- xr) = x ,- (xl >[ nnn ]< xr)
  (x ,- xl) >[ lll nnn ]< xr        = x ,- (xl >[ nnn ]< xr)
  []        >[ zzz     ]< []        = []

  data FindSplit {X : Set}{l m r : Nat}(nnn : l <[ m ]> r)
       : (xs : Vec X m) -> Set where
    splitBits : (xl : Vec X l)(xr : Vec X r) -> FindSplit nnn (xl >[ nnn ]< xr)

  findSplit : {X : Set}{l m r : Nat}(nnn : l <[ m ]> r)(xs : Vec X m) ->
              FindSplit nnn xs
  findSplit zzz [] = splitBits [] []
  findSplit (lll nnn) (x ,- xs) with findSplit nnn xs
  findSplit (lll nnn) (x ,- .(xl >[ nnn ]< xr)) | splitBits xl xr
    = splitBits (x ,- xl) xr
  findSplit (rrr nnn) (x ,- xs) with findSplit nnn xs
  findSplit (rrr nnn) (x ,- .(xl >[ nnn ]< xr)) | splitBits xl xr
    = splitBits xl (x ,- xr)


  ------------------------------------------------------------------------------
  -- what I should remember to say
  ------------------------------------------------------------------------------

  -- What's the difference between m>=n and m >= n ?
     {- m>=n (without spaces) is just an identifier; it could be anything,
        but it has been chosen to be suggestive of its *type* which is
        m >= n (with spaces) which is the proposition that m is at least n.
        By "proposition", I mean "type with at most one inhabitant", where
        we care more about whether there is an inhabitant or not than which
        one (because there's never a choice). Finished code does not show
        us the types of its components, and that's not always a good thing.
        Here, by picking nice names, we get something of an aide-memoire. -}

  -- What does (x ,-_) mean?
     {- It's a "left section". Right sections (_,- xs) also exist sometimes.
        Why only sometimes? -}

  -- "Why is it stuck?"
     {- Proof by induction isn't just flailing about, you know? The trick is
        to pick the case analysis that provokes the "stuck" programs to do a
        step of computation. Then the same reasoning that justifies the
        termination of the program will justify the induction in a proof
        about it. -}
\end{code}

- [ ] [Sigma, Difference, Vector Take](https://www.youtube.com/watch?v=OZeDRtRmgkw)
- [ ] [How Rewrite Works](https://www.youtube.com/watch?v=b5salYMZoyM)
- [ ] [A Comedy of (Entirely Non-Deliberate) Errors](https://www.youtube.com/watch?v=RW4aC_6n0yQ)
- [ ] ["Dominoes", no really, this time](https://www.youtube.com/watch?v=2LxtHeZlaVw)
- [ ] [Functors](https://www.youtube.com/watch?v=RCRddhYegzI)
- [ ] [From Functors to Monads](https://www.youtube.com/watch?v=vTmYvoDrBlc)
- [ ] [Natural Transformations and Monads](https://www.youtube.com/watch?v=2sykXdidZVA)
- [ ] [From Monads to Input/Output](https://www.youtube.com/watch?v=iYegg8Rzhr4)
- [ ] [How to Run a Program (and come a-cropper)](https://www.youtube.com/watch?v=8WUz2HmXBqI)
- [ ] [Monads on Indexed Sets (Ex2)](https://www.youtube.com/watch?v=MwtWdiyFJtA)
- [ ] [What is an Application?](https://www.youtube.com/watch?v=kX3mvyFHDDU)
- [ ] [Coinduction and Coalgebras](https://www.youtube.com/watch?v=ZCdYIEwcna0)
- [ ] [Polynomial Data and Codata](https://www.youtube.com/watch?v=AjyUNakYHRs)
- [ ] [A Polynomial Universe](https://www.youtube.com/watch?v=E8xIJolKEAI)
- [ ] [The Zipper (Differentiating Polynomial Types)](https://www.youtube.com/watch?v=-3MiZ80WldY)


## [Programming Language Foundations in Agda by Wen Kokke and Philip Wadler](https://plfa.github.io/)

### Part 1: Logical Foundations

  - [x] [Naturals: Natural numbers](https://plfa.github.io/Naturals/)
  - [x] [Induction: Proof by induction](https://plfa.github.io/Induction/)
  - [x] [Relations: Inductive definition of relations](https://plfa.github.io/Relations/)
  - [x] [Equality: Equality and equational reasoning](https://plfa.github.io/Equality/)
  - [ ] [Isomorphism: Isomorphism and embedding](https://plfa.github.io/Isomorphism/)
  - [ ] [Connectives: Conjunction, disjunction, and implication](https://plfa.github.io/Connectives/)
  - [ ] [Negation: Negation, with intuitionistic and classical Logic](https://plfa.github.io/Negation/)
  - [ ] [Quantifiers: Universals and existentials](https://plfa.github.io/Quantifiers/)
  - [ ] [Lists: Lists and higher-order functions](https://plfa.github.io/Lists/)
  - [ ] [Decidable: Booleans and decision procedures](https://plfa.github.io/Decidable/)

### Part 2: Programming Language Foundations

  - [ ] [Lambda: Lambda: Introduction to Lambda Calculus](https://plfa.github.io/Lambda/)
  - [ ] [Properties: Progress and Preservation](https://plfa.github.io/Properties/)
  - [ ] [DeBruijn: Inherently typed De Bruijn representation](https://plfa.github.io/DeBruijn/)
  - [ ] [More: More constructs of simply-typed lambda calculus](https://plfa.github.io/More/)
  - [ ] [Bisimulation: Relating reductions systems](https://plfa.github.io/Bisimulation/)
  - [ ] [Inference: Bidirectional type inference](https://plfa.github.io/Inference/)
  - [ ] [Untyped: Untyped lambda calculus with full normalisation](https://plfa.github.io/Untyped/)
