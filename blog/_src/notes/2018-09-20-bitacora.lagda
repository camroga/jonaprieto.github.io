---
layout: "post"
title: "Bitacora"
date: "2018-09-20"
categories: research
published: true
latex: true
references: true
agda: true
gallery: true
toc: true
linkify: true
---

Research meetings.

\begin{code}
{-# OPTIONS --without-K #-}
open import 2018-07-06-mini-hott
\end{code}

### Research topics

The goals and topics can change along the time, nowadays
I'm working on the following.

**(homotopy) type theory**

- [pathovers](http://tinyurl.com/pathorvers): proofs finished, fixing the writing ✍️
- [circle equivalences](http://tinyurl.com/pathorvers): removing a postulate  ✍️
- [mini-hott](http://tinyurl.com/mini-hott): a Mini-HoTT library for Agda ✍️
- A HIT can be seen as graph where each point-constructor is a node,
  each path-constructor is an edge. By changing the direction of one edge,
  can we get another HIT equivalent?

**Formal graph theory**

- What is a *good* characterization for planar graphs. What really does
  *good* means? good from the verification point of view or to be most suitable
  to use (depend, hott) type theory?

  When $$ A : Type$$ when want to have a property like `isPlanar` such that it
  is not a proposition in the HoTT context.

{:.equation }
  $$ \sum_{g:\mathsf{Graph}(A)}~\mathsf{isPlanar_{A}(g)}.$$

--------

### Meetings with [M]arc and [H]åkon

Showing the most recent to the oldest.

#### [H] **17-19** October

1. Definitions for Graphs in HoTT:
\begin{code}
module _ where
module C₂ where
\end{code}

Let's define first an auxiliary type for the this approach.

{: .foldable until="3"}
\begin{code}
  -- C₂ HIT
  data !C₂ : Set where
    !* : !C₂

  C₂ : Type₀
  C₂ = !C₂

  * : C₂
  * = !*

  postulate
    t : * == *
    q : t · t == refl *
    trunc : (x y : C₂)(α β : x == y)(ε δ : α == β) → ε == δ
    -- C₂ is h-level 3, h-groupoid?

  -- Def. Recursion on points:
  C₂-rec
    : ∀ {ℓ}
    → (A : Type ℓ)
    → (a : A)
    → (p : a == a)
    --------------
    → (C₂ → A)

  C₂-rec A a p !* = a

  -- Postulate. Recursion on paths:
  postulate
    C₂-βrec
      : ∀ {ℓ}
      → (A : Type ℓ)
      → (a : A)
      → (p : a == a)
      -----------------------------
      → ap (C₂-rec A a p) t == p

  -- Def.  Induction principle on points:
  C₂-ind
    : ∀ {ℓ} (P : C₂ → Type ℓ)
    → (x : P *)
    → (x == x [ P ↓ t ])
    ------------------------
    → ((t : C₂) → P t)

  C₂-ind P x p !* = x
  -- Postulate. Induction principle on paths:
  postulate
    C₂-βind
      : ∀ {ℓ} (P : C₂ → Type ℓ)
      → (x : P *)
      → (p : x == x [ P ↓ t ])
      -------------------------------
      → apd (C₂-ind P x p) t == p
\end{code}

Now, we define the type family for

{: .foldable until="2"}
\begin{code}
  -- P₂ Type family
  P₂ : C₂ → Set

  neg-eq : 𝟚 ≃ 𝟚
  neg-eq = qinv-≃ neg¬ (neg¬ , h , h)
    where
      h : neg¬ ∘ neg¬ ∼ id
      h true  = idp
      h false = idp

  P₂ = C₂-rec Type₀ 𝟚 (ua neg-eq)

  -- Defs.
  flip₁ : tr P₂ t false == true
  flip₁ = transport-ua P₂ t neg-eq (C₂-βrec Type₀ 𝟚 (ua neg-eq)) false

  flip₂ : tr P₂ t true == false
  flip₂ = transport-ua P₂ t neg-eq (C₂-βrec Type₀ 𝟚 (ua neg-eq)) true

  postulate
    tr-inv-t : ∀ {x} → transport P₂ (! t) x == neg¬ x
    -- Check the article tinyurl.com/circle-puzzle, it has how to remove this

\end{code}

A *graph* can be defined by using two constructors: `Node` and `Edge`.

\begin{code}
module GraphForm₁ where
  open C₂
\end{code}

- A set of vertices:
\begin{code}
  -- Def.
  postulate
    Node : Set
\end{code}

- A set of edges:

{: .eq }
  $$ \Edge :≡ \sum_{x : C₂} ~\Node^{P₂~x}$$

\begin{code}
  -- Def.
  postulate
    -- Edge : (x : C₂) → (P₂ x → Node) → Set
    Edge : Σ C₂ (λ x → (P₂ x) → Node) → Set
\end{code}

\begin{code}
  -- Ex.
  postulate
    x : Node
    y : Node

  x-y : P₂ * → Node
  x-y true  = x
  x-y false = y

  y-x : P₂ * → Node
  y-x true  = y
  y-x false = x

  e1 = Edge (* , x-y)
  e2 = Edge (* , y-x)


  e1=e2 : e1 == e2
  e1=e2 = ap Edge (pair= (t , η))
    where
      lem : (x : P₂ *) → x-y (neg¬ x) == y-x x
      lem true  = idp
      lem false = idp

      η : tr (λ x → P₂ x → Node) t x-y == y-x
      η =
        begin
          tr (λ x → P₂ x → Node) t x-y
            ==⟨ transport-fun t x-y ⟩
          (λ x → tr (λ _ → Node) t (x-y (tr P₂ (! t) x)))
            ==⟨ funext (λ x → transport-const t (x-y (tr P₂ (! t) x))) ⟩
          (λ x → x-y (tr P₂ (! t) x))
            ==⟨ funext (λ x → ap x-y tr-inv-t) ⟩
          (λ x → x-y (neg¬ x))
            ==⟨ funext (λ x → lem x) ⟩
          y-x
        ∎
\end{code}

1.2. Option B

\begin{code}
-- Node : Set
-- Edge : Node → Node → Set
-- data Graph₂ : Set where
--  α : ∀ {x y : Node} → Edge x y ≃ Edge y x
--  -- α x x == id?
\end{code}

Now we choose which definition we use:

\begin{code}
-- Graph = Graph₂
\end{code}

2. The graphs we are intended to represent are:

  - *Connected*
  - *Undirected*
  - *Multigraphs*

In order to support the undirected property,
the following are some proposed.

2.1

#### **2018-09-14**

With Håkon:

- HoTT stuff: we review the lemmas for the flattening lemma. We went
through Lemma 6.12.1 to Lemma 6.12.7.
- Graphs: I commented a little bit the MacLane's cycle-space and
Tutte's theorem which relies on the idea of contractible version of the graphs
to use later the Kuratowski theorem.

With Marc:
- Working on [the circle article](http://tinyurl.com/circle-hott) to remove the postulated lemmas


#### **2018-09-07**

With Håkon:
- We sketch briefly **alga** or *the algebra of graphs* described in (\cite{Mokhov2017}).
- We review the inductive definition for graphs in {% cite Tammet1996 %},
we wanted to have a predicate like $$ \sum_{g:\mathsf{Graph}}~\mathsf{isPlanar(g)}$$
- Håkon also pointed out MacLane's planar graph characterization to
review in future sessions.

With Marc:
- Making some improvements to [Pathovers' article](http://tinyurl.com/pathovers).

--------

### Formalization of graphs

- Papers relevant to formalizations of graphs:

**Inductive definitions**. Using inductive definitions allows us to
have for free an inductive principle to prove properties.
One issue using these kind of definitions is the difficulty that represents to
reason about their constructions. Which it's taking care of the order of the step
in the construction. So, how can we have a relation between these constructions
in such a away, a graph can be obtained by (homotopic?) constructions?.

#### {% cite yamamoto %}

In this paper, the authors show as their main result, the formalization of the
Euler formula. To achieve this they define inductively planar graphs by using the notion
of cycles. The formalization was done in `HOL`.


#### {% cite BauerN02 %}

This paper is about the formalization of the [Five-Colour
theorem](https://en.wikipedia.org/wiki/Five_color_theorem). In this, the authors
show an inductive definition for **near triangulations** in order to define
inductively planar graphs. This definition has three constructors:

  ![](/assets/png-images/2018-09-20-meetings-fde76f5f.png)
  ![](/assets/png-images/2018-09-20-meetings-4fc8e00a.png)

Some results:
  - Any planar graph has at least a vertex of at least degree less or equals five.
  - Idem for near triangulations.

#### {% cite Bauer %}
Continuing with near triangulations, Bauer in this thesis has an extra
constructor for it.

![](/assets/png-images/2018-09-20-bitacora-c68ebbd9.png)

He ends up Chapter 2 with the following summary of formalizations of
planar graphs.

  ![](/assets/png-images/2018-09-20-bitacora-485765ed.png)

  > Triangles vs. Polygons: The definition using triangles is by far eas- ier.
  > This simplifies proofs about the construction. If faces of arbi- trary
  > length can be added, the graph modifications and proofs about those are more
  > complex. On the other hand, a formalization based on triangles requires
  > operations to delete edges in order to construct non-triangular graphs,
  > which complicates a verification. Directed

#### {% cite Mokhov2017 %}

Alga. Missing description.

--------

### Questions and Related blog post

- 📆 https://mathoverflow.net/questions/278015/number-of-non-equivalent-graph-embeddings
- 📆 https://mathoverflow.net/questions/134010/embeddings-of-graphs-into-surfaces?rq=1
- 📆 Ricard Williams, Noam Zeilberger and Peter Heinig: https://goo.gl/xrn9im
- 📆 [Algebraic proof of Five-Color Theorem using chromatic polynomials by Birkhoff and Lewis in 1946](https://mathoverflow.net/questions/206270/algebraic-proof-of-five-color-theorem-using-chromatic-polynomials-by-birkhoff-an?rq=1)
- 📆 [Why are planar graphs so exceptional?](https://mathoverflow.net/questions/7114/why-are-planar-graphs-so-exceptional/7144#7144)
- 📆 [Kalai's Post](https://gilkalai.wordpress.com/2009/12/03/why-planar-graphs-are-so-exceptional/)
- 📆 [Generalizations of Planar Graphs](https://mathoverflow.net/questions/7650/generalizations-of-planar-graphs)
