---
layout: "post"
title: "Bitacora"
permalink: /bitacora/
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

Research happens _every day_!

## Topics

**(Homotopy) Type Theory**

- [Pathovers](http://tinyurl.com/pathorvers): proofs finished, fixing the writing ✍️
- [Circle equivalences](http://tinyurl.com/pathorvers): removing a postulate  ✍️
- [Mini-HoTT](http://tinyurl.com/mini-hott): a Mini-HoTT library for Agda ✍️
- A HIT can be seen as graph where each point-constructor is a node,
  each path-constructor is an edge. By changing the direction of one edge,
  can we get another HIT equivalent?

**(Formal) Graph Theory**

- What is a *good* characterization for planar graphs? What really means *good* mean?
- The goal here is to came up with a property `isPlanar` to not be a h-proposition in the `HoTT` context.

{: .hide }
  - Porque NO tiene que ser h-prop?
    - Revisar el Sigma type. Que solamente hay una prueba de que el planar es grafo es planar, que
    seria equivalente a decir que solo hay un embedding, lo cual no es verdad en general.

{:.equation }
  $$ \sum_{g:\mathsf{Graph}(A)}~\mathsf{isPlanar_{A}(g)}.$$

Given a graph $g$, an inhabitant of $\mathsf{isPlanar_{A}(g)}$ is a proof
that the graph $g$ is planar.

## Graphs in HoTT

{: .only-website }
  *This is a work in progress jointly with Håkon Robbestad. Some of
  the following proofs are collapsed or hidden to reduce the size of the document.
  Nevertheless, the reader can click on them to open the full description.
  Pictures are also clickable even the terms in the .*

### Agda Imports

We chose `Agda` `v2.5.4` to type-check the following formalism. Since we are
working in the HoTT context, *Axiom K* is not used.

{: .foldable until="1"}
\begin{code}
{-# OPTIONS --without-K #-}
open import Agda.Primitive using ( Level ; lsuc; lzero; _⊔_ )
_ = Set
\end{code}

To use all the HoTT machinery, we are using the
[*Mini-HoTT*](http://jonaprieto.github.io/mini-hott/) Agda Library.

\begin{code}
open import 2018-07-06-mini-hott hiding (Path)
\end{code}

### What is a `Graph`?

In this part, the goal consists to formalise the notion of a *graph*. We
are particularly interested in graphs:

- *Undirected*,
- no *multi-graphs*, and
- *connected*.

![path](/assets/ipe-images/graph-approach1.png){: width="40%" }
*Figure 1. Connected, undirected, no multi-graphs.*

#### Undirected and no multi-graphs

\begin{code}
module BaseGraph {ℓ} where

  record Graph : Type (lsuc ℓ) where
    constructor graph
    field
      -- G = (Node, Edge)
      Node : Type ℓ
      Edge : Node → Node → Type ℓ

      -- Properties
      -- ==========

      -- The vertices form a set.
      NodeIsSet : isSet Node

      -- No multi-graphs.
      EdgeIsProp : ∀ (x y : Node) → isProp (Edge x y)

      -- Undirected.
      Undirected : ∀ (x y : Node) → Edge x y → Edge y x

  open Graph public
\end{code}

### Example
\begin{code}
  -- .
  -- data G4 : Type ℓ where
  --   v₁ v₂ v₃ v₄ : G4
  --
  -- e : G4 → G4 → Type ℓ
  -- e v₁ v₂ = v₁ == v₂
  -- e v₁ x₃ = v₁ == v₃
  -- e v₂ x₃ = v₂ == v₃
  -- e v₂ x₄ = v₂ == v₄
  -- e v₂ v₁ = v₂ == v₁
  -- e x₃ v₁ = v₃ == v₁
  -- e x₃ v₂ = v₃ == v₂
  -- e x₄ v₂ = v₄ == v₂
  --
  -- Example : Graph
  -- Node Example = G4
  -- Edge Example = e
  -- NodeIsSet Example = λ u v → λ { idp q → {!   !}}
  -- EdgeIsProp Example = λ u v → {!   !}
  -- Undirected Example = {!   !}
\end{code}


### Lemmas

{: .foldable until="21"}
\begin{code}
  -- Lem.
  lem₀'
    : ∀ {G H : Graph}
    → Σ (Node G == Node H) (λ α →
        Σ (tr (λ X → (X → X → Type ℓ)) α (Edge G) == Edge H) (λ β →
          (tr isSet α (NodeIsSet G) == NodeIsSet H)
        × (tr₂
            (Type ℓ)
            (λ X → X → X → Type ℓ)
            (λ X R → (x y : X) → isProp (R x y))
            α
            β
            (EdgeIsProp G) == (EdgeIsProp H)
        × (tr₂
            (Type ℓ)
            (λ X  → X → X → Type ℓ)
            (λ X R → (x y : X) →  R x y → R y x))
            α
            β
            (Undirected G) == (Undirected H))))
    ≃ G == H

  lem₀' = qinv-≃
    ( λ {(idp , (idp , (idp , (idp , idp)))) → idp })      -- Fun. Equiv.
    ((λ {idp → idp , idp , (idp , (idp , idp))})          -- Fun. Inverse
      , (λ {idp →  idp})                                  -- Homotopy
      , λ { (idp , (idp , (idp , (idp , idp))))  →  idp}  -- Homotopy
    )
\end{code}

{: .foldable until="17"}
\begin{code}
  -- Lem.
  lem₁'
    : ∀ {G H : Graph}
    → Σ (Node G == Node H) (λ α →
        (tr (λ X → (X → X → Type ℓ)) α (Edge G) == Edge H))
    ≃  Σ ((Node G == Node H)) (λ α →
        Σ (tr (λ X → (X → X → Type ℓ)) α (Edge G) == Edge H) λ β
        → (tr isSet α (NodeIsSet G) == NodeIsSet H)
        × (tr₂ (Type ℓ)
            (λ X  → X → X → Type ℓ)
            (λ X R → (x y : X) → isProp (R x y))
             α β (EdgeIsProp G) == (EdgeIsProp H)
        × (tr₂ (Type ℓ)
         (λ X  → X → X → Type ℓ)
         (λ X R → (x y : X) →  R x y → R y x))
          α β (Undirected G) == (Undirected H)))

  lem₁' {G}{H} = qinv-≃
    (λ { (α , β) →   -- Fun. Equiv.
      (α
        , (β
          , (set-is-prop-always _ _)
          , (pi-is-prop (λ x → pi-is-prop λ x → prop-is-prop-always) _ _)
          , pi-is-prop ((λ x → pi-is-prop λ x → pi-is-prop λ x → EdgeIsProp H _ _)) _ _))})

      ((λ {(α , (β , _)) → α , β})
        , (λ {(α , (β , _))
          → pair= (idp
              , pair= (idp
                , ispropA×B
                  (prop→set
                    (pi-is-prop λ a → pi-is-prop λ x → prop-is-prop-always)
                    _
                    _)
                  (ispropA×B
                    (prop→set
                      (pi-is-prop
                        (λ x → pi-is-prop
                          (λ a → prop-is-prop-always)
                        )
                      )
                      _ -- EdgeIsProp H
                      _
                      )
                    (prop→set
                      (pi-is-prop
                        (λ a → pi-is-prop λ b → pi-is-prop λ e → EdgeIsProp H _ _)) _ _)) _ _)) })
        , (λ {(α , β) → idp} ))
\end{code}

{: .foldable until="10"}
\begin{code}
  -- LemAux:
  lemAux
    : ∀ {G H : Graph}
    → (α : Node G == Node H)
    → (tr (λ X → (X → X → Type ℓ)) α (Edge G) == Edge H)
      ≃
      (∀ (x y : Node G)
          → Edge G x y == Edge H (coe α x) (coe α y))
  lemAux {G}{H} idp = qinv-≃
    f ( g , -- g
      H₁
      , H₂)
    where
      f : tr (λ X → (X → X → Type ℓ)) idp (Edge G) == Edge H
        → (∀ x y → Edge G x y == Edge H (coe idp x) (coe idp y))
      f idp x y = idp

      g : (∀ x y → Edge G x y == Edge H (coe idp x) (coe idp y))
        → tr (λ X → (X → X → Type ℓ)) idp (Edge G) == Edge H
      g k = funext (λ x → funext λ y → k x y)

      H₁ : f ∘ g ∼ id
      H₁ k = {!   !}

      H₂ : g ∘ f ∼ id
      H₂ idp = {! (g ∘ f) idp == id idp  !}


  -- Lem.
  lem₂'
    : ∀ {G H : Graph}
    → -- A :
      Σ (Node G == Node H) (λ α →
        (tr (λ X → (X → X → Type ℓ)) α (Edge G) == Edge H))
    ≃ -- B:
      Σ (Node G == Node H) (λ α →
        (∀ (x y : Node G)
            → Edge G x y == Edge H (coe α x) (coe α y)))

  lem₂' {G}{H} = qinv-≃
    -- f : A → B
    (λ { (idp , idp) → idp  , λ x y → happly (happly idp y) x }) -- or just idp?
    -- g : B → A
    ((λ {(idp , k) → (idp , funext (λ x → funext (λ y → k x y)) )})
      ,  -- f ∘ g ∼ id_B
        (λ { (idp , y) → pair= ({!   !} , {!   !}) })
      , -- g ∘ f ∼ id_A
      λ { (idp , idp) → pair= (idp , {!  !}) })
\end{code}

{: .foldable until="15"}
\begin{code}
  -- Lem.
  lem₀
    : ∀ {G H : Graph}
    → (α : Node G == Node H)
    → (β : tr (λ X → (X → X → Type ℓ)) α (Edge G) == Edge H)
    → (tr isSet α (NodeIsSet G) == NodeIsSet H)
    → tr₂ (Type ℓ)
          (λ X  → X → X → Type ℓ)
          (λ X R → (x y : X) → isProp (R x y))
           α β (EdgeIsProp G) == (EdgeIsProp H)
    → tr₂ (Type ℓ)
       (λ X  → X → X → Type ℓ)
       (λ X R → (x y : X) →  R x y → R y x)
        α β (Undirected G) == (Undirected H)
    →  G == H

  lem₀ idp idp idp idp idp = idp
\end{code}

{: .foldable until="6"}
\begin{code}
  -- Lem.
  lem₁
    : ∀ { G H : Graph}
    → (α : Node G == Node H)
    → (β : tr (λ X → (X → X → Type ℓ)) α (Edge G) == Edge H)
    →  G == H

  lem₁ {G}{H} α β = lem₀ α β
    (set-is-prop-always _ _)
    (pi-is-prop (λ x → pi-is-prop λ x → prop-is-prop-always) _ _) -- EdgeIsProp
    (pi-is-prop (λ x → pi-is-prop λ x → pi-is-prop λ x → EdgeIsProp H _ _) _ _) -- Undirected case
\end{code}

{: .foldable until="6"}
\begin{code}
  -- Lem.
  lem₂
    : ∀ {G H : Graph}
    → (α : Node G == Node H)
    → (β :  ∀ x y → Edge G x y == Edge H (coe α x) (coe α y))
    →  G == H

  lem₂ idp β = lem₁ idp (funext (λ x → funext (λ y → β x y)))
\end{code}

{: .foldable until="6"}
\begin{code}
  -- Lem.
  lem₃
    : ∀ { G H : Graph}
    → (α : Node G == Node H)
    → (β :  ∀ x y → Edge G x y ⇔ Edge H (coe α x) (coe α y))
    →  G == H

  lem₃ {G}{H} α β = lem₂ α λ x y → ispropA-B (EdgeIsProp G _ _) (EdgeIsProp H _ _) (β x y)
\end{code}

{: .foldable until="6"}
\begin{code}
  -- Lem.
  lem₄
    : ∀ { G H : Graph}
    → (α : Node G ≃ Node H)
    → (β :  ∀ x y → Edge G x y ⇔ Edge H ((α ∙) x) ((α ∙) y))
    →  G == H

  lem₄ {G}{H} α β = lem₃ (ua α) (λ x y
      → tr₂ (Node H)
            (λ X → Node H)
            (λ n m → Edge G x y ⇔ Edge H n m)
            (! (ua-coe α x))
            (transport-const (! (ua-coe α x)) _ · ! ua-coe α y)
           (β x y))
\end{code}

#### Isomorphisms

Let be $G, H : \Graph$. A *graph map* is a pair $(α, β)$ that consists of a
*vertex function* $α : \Node G → \Node H$ and an edge function $\beta_\alpha :
\Edge G \to \Edge H$ such that *incidence* for each vertex in $G$ is preserved
in $H$ by means of $β$ using $α$ for vertex correspondence.

{: .foldable until="8" }
\begin{code}
module Isomorphism {ℓ} where

  open BaseGraph {ℓ}

  _≃Iso_ : Graph → Graph → Type ℓ
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

{: .foldable until="5"}
\begin{code}
  -- Thm.
  A≃IsoA
    : ∀ {A : Graph }
    ----------
    → A ≃Iso A

  A≃IsoA {A} = ( idEqv , λ x y → fun id , fun id )
\end{code}

{: .foldable until="5"}
\begin{code}
  -- Thm.
  thm
    : ∀ {G H : Graph}
    ------------------------
    → (G == H) ≃ (G ≃Iso H)

  thm {G}{H} = qinv-≃ f (g , H₁ , H₂)
    where
      f : G == H → G ≃Iso H
      f p = tr (λ X → G ≃Iso X) p (A≃IsoA {A = G})

      g : G ≃Iso H → G == H
      g (α , β) =  lem₄ α β

      H₁ : f ∘ g ∼ id
      H₁ (α , β) = {!   !}

      H₂ : g ∘ f ∼ id
      H₂ idp = {! (g ∘ f) idp  !}

\end{code}

#### Connected graphs

For connected graphs, we need to define the type `Walk` to allow us
to establish the *connectedness* property which says that a graph is *connected* if
for any pair of nodes there is a *walk* between them.

![path](/assets/ipe-images/graph-connected.png){: width="40%" }
*Figure 3. In this graph, the green graph is a walk built up with $α : \Walk x\,y$ and $β : \Edge y z$.

\begin{code}

module ConnectedGraph
  {ℓ} (G : BaseGraph.Graph {ℓ})
  where

  open BaseGraph.Graph public

  -- Def.
  data Walk : Node G → Node G → Type ℓ where
    ⟨_⟩
      : ∀ {x : Node G}
      → Walk x x

    _⊙_
      : ∀ { x y z : Node G}
      → Walk x y → Edge G y z
      ------------------------
      → Walk x z

  record Graph : Type (lsuc ℓ) where
    constructor connectedGraph
    field
      connected
        : ∀ {x y : Node G}
        ------------------
        → Walk x y

  open Graph public

  -- Syntax.
  _⇢_ : ( x y : Node G) → Type ℓ
  x ⇢ y = Walk x y
\end{code}

- Rotation systems

Let's define the `Star` type to attempt define in the following the concept of a rotation system.

![path](/assets/ipe-images/bitacora-out.png){: width="40%" }
*Figure 3. $\mathsf{Star}\,x$ when $x : \Node\,G$ in a graph $G$.*

\begin{code}
  -- Def.
  Star
    : Node G
    --------
    → Type ℓ

  Star = λ (x : Node G) → Σ (Node G) (λ y → Edge G y x)
\end{code}

\begin{code}
  -- Relation.
  postulate
    StarRelation : ∀ {x : Node G} → Star x → Star x → Star x → Type ℓ

  postulate
    StarRelationIsProp : ∀ {x : Node G} {a b c : Star x} → isProp (StarRelation a b c)
  -- Each node has incident nodes.
\end{code}

#### Cycles

The reason to define a cyclic relation is that the faces or regions can be defined by
using these orders. The terminology is *combinatorial maps* also called *rotation systems*.

Put here the rotation system definition from the notes and also *face walks*.
Show the theorem 3.2.2. (G graph + R : RotationSystem) => Embedding in *some* surface.
❓ Still missing how to determine the output of T3.2.2. is a sphere.



![path](/assets/ipe-images/cyclic.png){: width="40%" }
*Figure 2. Cyclic relation `R`.*

Our first attempt to define this cycle relation (order):

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

  -- ∀ {x : Node G} → Cyclic (Star x) (StarRelation {x})
\end{code}

- Mention what is *dart*

❓ How to define $\Face\ G$ for $G : \Graph\ A$. (In progress session 9/11/18)
❓ How to *decide* if the faces make up (compatibility property). (In progress  9/11/18)

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

{: .links }
  - [Face-walks in rotation systems for graphs](https://cstheory.stackexchange.com/questions/11838/face-walks-in-rotation-systems-for-graphs/11845)
  - https://mathoverflow.net/questions/278015/number-of-non-equivalent-graph-embeddings
  - https://mathoverflow.net/questions/134010/embeddings-of-graphs-into-surfaces?rq=1
  - Ricard Williams, Noam Zeilberger and Peter Heinig: https://goo.gl/xrn9im
  - [Algebraic proof of Five-Color Theorem using chromatic polynomials by Birkhoff and Lewis in 1946](https://mathoverflow.net/questions/206270/algebraic-proof-of-five-color-theorem-using-chromatic-polynomials-by-birkhoff-an?rq=1)
  - [Why are planar graphs so exceptional?](https://mathoverflow.net/questions/7114/why-are-planar-graphs-so-exceptional/7144#7144)
  - [Kalai's Post](https://gilkalai.wordpress.com/2009/12/03/why-planar-graphs-are-so-exceptional/)
  - [Generalizations of Planar Graphs](https://mathoverflow.net/questions/7650/generalizations-of-planar-graphs)
  - [Complexity of isotopy of embedded graphs](https://cstheory.stackexchange.com/questions/41546/complexity-of-isotopy-of-embedded-graphs)

  - [Graph Embeddings and Symmetries- author: Jozef Širáň](http://tinyurl.com/y8w78v32)
  - [Beyond Planarity of Graphs - author: Bojan Mohar](http://tinyurl.com/y9dkdzzw)
  - [Definition Clarification Of Graph Embeddings](http://tinyurl.com/y7kruofw)


{: .hide }
  - *[M]arc and [H]åkon*

  - 2018-11-9
    - We discuss theorem 3.2.2, some topological stuff. How can we determine the surface
    given by the aforementioned theorem is indeed a sphere. After having that, we can punch it with "needle" to
    have a planar graph in R^2.

  - 2018-10-31, 2018-11-2
    - Proving some lemmas to have isomorphism between graphs.
  - 2018-10-26
    - We were checking the first definitions in Agda about graphs
    - We discuss why A=B is a Set when A and B are sets
    - `Π (x:A) B x` is a Set as long as $B$ is a Set
    - `Σ A B` is a Set as long as $A$ and $B$ is a Set
    - `A → B` is a Set when B is a Set.
    - contr => isProp => isSet

  - 2018-09-17 and 2018-09-19:
    - We discuss how to formalize a graph when it's Undirected
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
