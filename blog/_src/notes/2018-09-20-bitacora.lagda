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

Research happens every day!

## Topics

**(Homotopy) Type Theory**

- [Pathovers](http://tinyurl.com/pathorvers): proofs finished, fixing the writing ✍️
- [Circle equivalences](http://tinyurl.com/pathorvers): removing a postulate  ✍️
- [Mini-HoTT](http://tinyurl.com/mini-hott): a Mini-HoTT library for Agda ✍️
- A HIT can be seen as graph where each point-constructor is a node,
  each path-constructor is an edge. By changing the direction of one edge,
  can we get another HIT equivalent?

**(Formal) Graph Theory**

- What is a *good* characterization for planar graphs? What really does *good* means?
- The goal here is to came up with a property `isPlanar` to not be a h-proposition in the `HoTT` context.

{: .hide }
  - Porque NO tiene que ser h-prop?
    - Revisar el Sigma type. Que solamente hay una prueba de que el planar es grafo es planar, que
    seria equivalente a decir que solo hay un embedding, lo cual no es verdad en general.

{:.equation }
  $$ \sum_{g:\mathsf{Graph}(A)}~\mathsf{isPlanar_{A}(g)}.$$

Given a graph $g$, an inhabitant of $\mathsf{isPlanar_{A}(g)}$ is a proof
that the graph $g$ is planar.

## Progress

\begin{code}
{-# OPTIONS --without-K #-}

open import 2018-07-06-mini-hott hiding (Path)
open import Agda.Primitive using ( Level ; lsuc; lzero; _⊔_ )

_ = Set
\end{code}

### Graphs

{: .only-website }
  *This is a work in progress jointly with Håkon Robbestad. Some of
  the following proofs are collapsed or hidden to reduce the size of the document.
  Nevertheless, the reader can click on them to open the full description.
  Pictures are also clickable.*

{: .hide }
  - *[M]arc and [H]åkon*
  - 2018-10-26
    - We were checking the first definitions in Agda
    - We discuss why A=B is a Set when A and B are sets
    - `Π (x:A) B x` is a Set as long as $B$ is a Set
    - `Σ A B` is a Set as long as $A$ and $B$ is a Set
    - `A → B` is a Set when B is a Set.
    - contr => isProp => isSet

  - 2018-09-17 and 2018-09-19:
    - We discuss how to formalize a graph when it's undirected
  - 2018-09-14
     - [H] We review the lemmas for the *flattening lemma*. We went through Lemma 6.12.1 to Lemma 6.12.7.
     - I commented a little bit the MacLane’s cycle-space and Tutte’s theorem
       which relies on the idea of contractible version of the graphs to use
       later the Kuratowski theorem.
  - 2018-09-07
    - We sketch briefly **alga** or *the algebra of graphs* described in (\cite{Mokhov2017}).
    - We review the inductive definition for graphs in {% cite Tammet1996 %},
    we wanted to have a predicate like $$ \sum_{g:\mathsf{Graph}}~\mathsf{isPlanar(g)}$$
    - Håkon also pointed out MacLane's planar graph characterization to
    review in future sessions.
    - [M] Making some improvements to [Pathovers' article](http://tinyurl.com/pathovers).


#### First Approach

For this part, our goal will consist to formalise the notion of graph when they are:

- *undirected*,
- no *multi-graphs*, and
- connected.

![path](/assets/ipe-images/graph-approach1.png){: width="40%" }
*Figure 1. Connected, undirected, no multi-graphs.*

### Undirected and no multi-graph definition

\begin{code}
module BaseGraph {ℓ} where

  record Graph : Type {!   !} where
    constructor graph
    field
      -- G = (Node, Edge)
      Node : Type {!   !}
      Edge : Node → Node → Type {!   !}

      -- Properties
      -- ==========

      -- The vertices form a set.
      NodeIsSet : isSet Node

      -- No multi-graphs.
      EdgeIsProp : ∀ {x y : Node} → isProp (Edge x y)

      -- Undirected.
      undirected : ∀ {x y : Node} → Edge x y → Edge y x

  open Graph public

\end{code}

#### Isomorphisms

Let be $G, H : \Graph$. A *graph map* is a pair $(α, β)$ that consists of a *vertex function*
$α : \Node G → \Node H$ and an edge function $\beta_\alpha : \Edge G \to \Edge H$ such
that *incidence* for each vertex in $G$ is preserved in $H$ by means of $β$ using
$α$ for vertex correspondence.

{: .foldable until="7" }
\begin{code}
module Isomorphism {ℓ} where

  open BaseGraph {ℓ}

  _≃Iso_ : Graph → Graph → Type {!   !}
  G ≃Iso H =
    Σ (Node G ≃ Node H)                                                 -- α
      (λ α → (x y : Node G) → Edge G x y ⇔ Edge H ((α ∙) x) ((α ∙) y))  -- β

  -- Remarks: Edge is propositional.
  -- Agda Question:
  -- What to remove these parenthesis (α ∙)
\end{code}

A graph map $(α, β)$ is called an *isomorphism* if $(α, β) : \Iso{G}{H}$  i.e., if both its vertex
function and its edge function are equivalences.
Two graphs $G$ and $H$ are *isomorphic* when $\Iso{G}{H}$ holds.


\begin{code}
  -- Thm.
  thm : ∀ {G H : Graph} → (G == H) ≃ (G ≃Iso H)
  thm {G}{H} = qinv-≃ f (g , H₁ , H₂)
    where
      f : G == H → G ≃Iso H
      f p = (idtoeqv (ap Node p) , λ x y → fun t₁ , fun t₂)
        where
          t₁ : ∀ {x y : Node G}
            → Edge G x y
            → Edge H ((idtoeqv (ap Node p) ∙) x) ((idtoeqv (ap Node p) ∙) y)
          t₁ e = {!   !} 

          t₂
            : ∀ {x y : Node G}
            → Edge H ((idtoeqv (ap Node p) ∙) x) ((idtoeqv (ap Node p) ∙) y)
            → Edge G x y
          t₂ e = {!   !}

      g : G ≃Iso H → G == H
      g (α , β) =  {! ua  !}

      H₁ : f ∘ g ∼ id
      H₁ (α , β) = {! x  !}

      H₂ : g ∘ f ∼ id
      H₂ eq = {!   !}

\end{code}
#### Connected graphs

For connected graphs, we need to define the type `Path` to allow us
to establish the *connectedness* property which says that a graph is *connected* if
for any pair of nodes there is a path between them.

*Definition*. A *path* is a non-empty graph P =(V,E) of the form

![path](/assets/ipe-images/graph-connected.png){: width="40%" }
*Figure 3. Connected Graphs. Green graph is the path built by $α : \Path x\,y$ and $β : \Edge y z$, this is the
`cons` constructor in $\Path$ data type.*

\begin{code}

module ConnectedGraph
  {ℓ} (G : BaseGraph.Graph {ℓ})
  where

  open BaseGraph.Graph public

  -- Path Def.
  data Path : Node G → Node G → Type ℓ where
    edge
      : ∀ {x y : Node G}
      → Edge G x y
      ------------
      → Path x y

    cons
      : ∀ { x y z : Node G}
      → Path x y → Edge G y z
      ------------------------
      → Path x z

  record Graph : Type (lsuc ℓ) where
    constructor connectedGraph
    field
      connected
        : ∀ {x y : Node G}
        ------------------
        → Path x y

  open Graph public
\end{code}

❓ Our notion of *path* seems to be the *walk* notion. should we impose the predicate to not repeat vertices

- Rotation systems

Let's define the `Out` type to attempt define what a rotation system is.

![path](/assets/ipe-images/bitacora-out.png){: width="40%" }
*Figure 3. $\mathsf{Out}\,x$ when $x : \Node\,G$ in a graph $G$.*

\begin{code}
  -- Def.
  Out : Node G → Type ℓ
  Out = λ (x : Node G) → Σ (Node G) (λ y → Edge G y x)
\end{code}

❓ I forgot the purpose of `OutR`.
\begin{code}
  -- Relation.
  postulate
    OutR : ∀ {x : Node G} → Out x → Out x → Out x → Type ℓ

  postulate
    OutRIsProp : ∀ {x : Node G}{a b c : Out x} → isProp (OutR a b c)
  -- Each node has incident nodes.
\end{code}


#### Cycles

The reason to define a cyclic relation is that the faces or regions can be defined by
*combinatorial maps* or also called *rotation systems*.


![path](/assets/ipe-images/cyclic.png){: width="40%" }
*Figure 2. Cyclic relation `R`.*

Therefore, we present first an attempt to define cycle orders:

\begin{code}
module CyclicForm {ℓᵢ ℓⱼ} where

  record Cyclic (A : Type ℓᵢ)             -- Carrier
                (R : A → A → A → Type ℓⱼ) -- Clockwise
                : Type (ℓᵢ ⊔ ℓⱼ) where
    field

      RisProp : ∀ {a b c : A} → isProp (R a b c)

      axiom₀
        : ∀ {a b c : A}
        → R a b c
        → R a c b
        ---------
        → b == c

      axiom₁
        : ∀ {a b : A}
        -------------
        → R a b b

      axiom₂
        : ∀ {a b c : A}
        → R a b c
        ---------
        → R b c a

      axiom₃
        : ∀ {a b c d : A}
        → R a b c
        → R a c d
        ---------
        → R a b d

      axiomₓ
        : ∀ {a b c : A} → ∥ (R a b c) + (R a c b) ∥
\end{code}

\begin{code}
  -- Def.
  -- CyclicIsProp : ∀ {A}{R} → isProp (Cyclic A R)
  -- CyclicIsProp x y = {!   !}

  -- ∀ {x : Node G} → Cyclic (Out x) (OutR {x})
\end{code}

- Mention what is *dart*

❓ How to define $\Face\ G$ for $G : \Graph\ A$. (In progress)

❓ How to *decide* if the faces make up (compatibility property). (In progress)


### Related papers

Papers relevant to formalizations of graphs:

**Inductive definitions**. Using inductive definitions allows us to
have for free an inductive principle to prove properties.
One issue using these kind of definitions is the difficulty that represents to
reason about their constructions. Which it's taking care of the order of the step
in the construction. So, how can we have a relation between these constructions
in such a away, a graph can be obtained by (homotopic?) constructions?.

- {% cite yamamoto %}

In this paper, the authors show as their main result, the formalization of the
Euler formula. To achieve this they define inductively planar graphs by using the notion
of cycles. The formalization was done in `HOL`.


- {% cite BauerN02 %}

This paper is about the formalization of the [Five-Colour
theorem](https://en.wikipedia.org/wiki/Five_color_theorem). In this, the authors
show an inductive definition for **near triangulations** in order to define
inductively planar graphs. This definition has three constructors:

  ![](/assets/png-images/2018-09-20-meetings-fde76f5f.png){: width="40%" }
  ![](/assets/png-images/2018-09-20-meetings-4fc8e00a.png){: width="40%" }

  - Some results:
    - Any planar graph has at least a vertex of at least degree less or equals five.
    - Idem for near triangulations.

- {% cite Bauer %}

Continuing with near triangulations, Bauer in this thesis has an extra
constructor for it.

![](/assets/png-images/2018-09-20-bitacora-c68ebbd9.png){: width="40%" }

He ends up Chapter 2 with the following summary of formalizations of
planar graphs.

  ![](/assets/png-images/2018-09-20-bitacora-485765ed.png){: width="40%" }

  > Triangles vs. Polygons: The definition using triangles is by far eas- ier.
  > This simplifies proofs about the construction. If faces of arbi- trary
  > length can be added, the graph modifications and proofs about those are more
  > complex. On the other hand, a formalization based on triangles requires
  > operations to delete edges in order to construct non-triangular graphs,
  > which complicates a verification. Directed


### Related links

- [Face-walks in rotation systems for graphs](https://cstheory.stackexchange.com/questions/11838/face-walks-in-rotation-systems-for-graphs/11845)
- https://mathoverflow.net/questions/278015/number-of-non-equivalent-graph-embeddings
- https://mathoverflow.net/questions/134010/embeddings-of-graphs-into-surfaces?rq=1
- Ricard Williams, Noam Zeilberger and Peter Heinig: https://goo.gl/xrn9im
- [Algebraic proof of Five-Color Theorem using chromatic polynomials by Birkhoff and Lewis in 1946](https://mathoverflow.net/questions/206270/algebraic-proof-of-five-color-theorem-using-chromatic-polynomials-by-birkhoff-an?rq=1)
- [Why are planar graphs so exceptional?](https://mathoverflow.net/questions/7114/why-are-planar-graphs-so-exceptional/7144#7144)
- [Kalai's Post](https://gilkalai.wordpress.com/2009/12/03/why-planar-graphs-are-so-exceptional/)
- [Generalizations of Planar Graphs](https://mathoverflow.net/questions/7650/generalizations-of-planar-graphs)
- [Complexity of isotopy of embedded graphs](https://cstheory.stackexchange.com/questions/41546/complexity-of-isotopy-of-embedded-graphs)
