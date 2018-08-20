---
layout: "post"
title: "Graphs"
date: "2018-06-27"
categories: learning
published: true
latex: true
references: true
agda: true
---

Learning graphs on youtube.

### Graph Theory by [Sarada Herke](https://www.youtube.com/channel/UCV8tyRakGZuXUwD-wYH1yGg)

- [x] [01. Seven Bridges of Konigsberg](https://www.youtube.com/watch?v=eIb1cz06UwI)

  * Seven Bridges problem

  ![](/assets/png-images/2018-06-27-learning-graph-theory-c13de192.png)

  * **Eulerian walk/path/trail** in a finite graph is a path which visits *every edge* exactly once

  * **Eulerian circuit/cycle** is an Eulerian path which starts and ends on the same vertex

  * **Degree/Valency**: is the number of edges incident to the vertex, with
  loops counted twice, denoted by $$\deg ⁡ ( v )$$

    - Odd degree for starting or ending nodes
    - Even degree for intermediate nodes

  * **Lemma**

  If a graph has an **Eulerian walk** then the number of **odd degree vertices** is
  either **0 or 2**. 0 when the path starts where it ends. 2 when there is a
  starting point different from the ending point.

  ![](/assets/png-images/2018-06-27-learning-graph-theory-bcb514e9.png)

- [x] [02. Definition of a Graph](https://www.youtube.com/watch?v=S1Zwhz-MhCs)

  A graph is a pair $$G = (V, E)$$, where $$V$$ is a set of vertices and $$E$$ is a subset
  of the cartesian product $$V \times V$$.

  - **Size** of the graph is denoted by \|E\|
  - **Order** of the graph is denoted by \|V\|

  Some kind of graphs:

  - **Simple graphs** : No loops, no multiple loops
  - **Directed graphs** : each edge has a direction associated to it
  - **Undirected graphs** : edges without any direction

- [x] [03. Examples of Graphs](https://www.youtube.com/watch?v=lLOvB1qFE1E)

  $$uv$$ stands for $$\{u, v\} \in E$$, in a graph $$G = (V(G), E(E))$$.

- [x] [04. Families of Graphs](https://www.youtube.com/watch?v=71XbdtoG7P8)

  - [**A Complete graph**](http://mathworld.wolfram.com/CompleteGraph.html)
    $$K_n$$ on $$n$$ vertices is a simple (no-loops, no-multiple loops) with an
    edge between every pair of vertices.

    - $$ \# (E) = n \cdot C_2$$, $$C_2$$ is the binomial coefficient

    ![](/assets/png-images/2018-06-27-learning-graph-theory-6b99df17.png)

  - Empty graphs
  - Bipartite graphs and (Complete Bipartite graphs $$K_{n,m}$$)

    ![](/assets/png-images/2018-06-27-learning-graph-theory-1837f36b.png)

  - Path $$P_n$$ is graph whose vertices can be arranged in a sequence.

  ![](/assets/png-images/2018-06-27-learning-graph-theory-1ff903e5.png)

  - Cycle $$C_6$$ is a graph whose vertices can be arranged in a cyclic sequence
    such That the ending vertex is connected with the starting vertex forming a
    chain. The cycle $$C_n$$ is just the path $$P_n$$ after adding the edge that
    connects the tail and the head of the path.

  ![](/assets/png-images/2018-06-27-learning-graph-theory-355a9076.png)

  - Triangle = $$C_3$$ and $$K_3$$

- [x] [05. Connected and Regular Graphs](https://www.youtube.com/watch?v=BEyuUXQs5ko)

  - [A **connected graph**](http://mathworld.wolfram.com/ConnectedGraph.html) is a
    graph which is connected in the sense of a topological space, i.e., there is
    a path from any point to any other point in the graph.

    ![](/assets/png-images/2018-06-27-learning-graph-theory-0f87473b.png)

  - A **disconnected graph** is a graph G is said to be disconnected if it is not
    connected, i.e., if there exist two nodes in G such that no path in G has
    those nodes as endpoints.

    ![](/assets/png-images/2018-06-27-learning-graph-theory-cee5a515.png)

  - **(Open) neighbourhood** of v in G is

    {: .equation}
      $$ N_{G}(v) = \{u | uv \in E(G) \}$$

  - **(Closed) neighbourhood** of v in G is

    {: .equation}
      $$ N_{G}[v] = N_{G}(v) \cup \{ v \}$$

  - The **degree of a vertex** $$v \in V(G)$$ in terms of neighbourhoods is

    {: .equation}
      $$ \deg_{G} (v) = \# N_{G}(v) $$

  - A graph is **r-regular** if $$\deg_{G}(v) = r$$ for all $$v \in V(G)$$
  - The **minimum degree** is denoted by $$\delta(G)$$
  - The **minimum degree** is denoted by $$\Delta(G)$$

  ![](/assets/png-images/2018-06-27-learning-graph-theory-95d01eee.png)

- [x] [06. Sum of Degrees is ALWAYS Twice the Number of Edges](https://www.youtube.com/watch?v=YoRhmz_OSBY)

  - **Theorem**:

    {: .equation}
      $$ \sum_{v \in V(G)} \deg(v) = 2 \# E(G) $$

  - **Corollary**: In any graph the number of odd degree vertices is even.

- [ ] [07. Adjacency Matrix and Incidence Matrix](https://www.youtube.com/watch?v=LUDNz2bIjWI)
- [ ] [08a. Basic Problem Set (part 1/2)](https://www.youtube.com/watch?v=Qe9e-XcEvlo)
- [ ] [08b. Basic Problem Set (part 2/2)](https://www.youtube.com/watch?v=t0UzHk53HjM)
- [ ] [09. Graph Isomorphisms](https://www.youtube.com/watch?v=yFpRpxOry-A)
- [ ] [10. Isomorphic and Non-Isomorphic Graphs](https://www.youtube.com/watch?v=z-GfKbzvtBA)
- [ ] [10b Graph Theory with Sage](https://www.youtube.com/watch?v=p67pxeLZXn4)
- [ ] [11. Neighbourhood and Bipartite Test with Colours](https://www.youtube.com/watch?v=za_BGCGJzSs)
- [ ] [12. Spanning and Induced Subgraphs](https://www.youtube.com/watch?v=dPHkyRvLtIU)
- [ ] [13. Degrees at Least Two Means a Cycle Exists](https://www.youtube.com/watch?v=voD1xLxZvAM)
- [ ] [14a. Basic Graph Theory Problem Set 2](https://www.youtube.com/watch?v=fFuIMMkIO9Q)
- [ ] [14b. Basic Graph Theory Problem Set 2](https://www.youtube.com/watch?v=3uS6toYt-Dw)
- [ ] [14c. Basic Graph Theory Problem Set 2](https://www.youtube.com/watch?v=lPLrNDdJEB0)
- [ ] [15.There Exists a 3-Regular Graph of All Even Order at least 4](https://www.youtube.com/watch?v=flYT0ku1dpQ)
- [ ] [16. Walks Trails and Paths](https://www.youtube.com/watch?v=koXFopNHE2U)
- [ ] [17. Distance Between Vertices and Connected Components](https://www.youtube.com/watch?v=m14uiz7Bats)
- [ ] [18. Every Walk Contains a Path](https://www.youtube.com/watch?v=vTzZ6jFOemc)
- [ ] [19. Graph is Bipartite iff No Odd Cycle](https://www.youtube.com/watch?v=YiGFhWxtHjQ)
- [ ] [20. Edge Weighted Shortest Path Problem](https://www.youtube.com/watch?v=38G5uSxylaY)
- [ ] [21. Dijkstra's Algorithm](https://www.youtube.com/watch?v=8njHSvS_inI)
- [ ] [22. Dijkstra Algorithm Examples](https://www.youtube.com/watch?v=EHZf1_gM3dM)
- [ ] [23. Euler Trails and Euler Tours](https://www.youtube.com/watch?v=1V_6nUUNoms)
- [ ] [24. Euler Trail iff 0 or 2 Vertices of Odd Degree](https://www.youtube.com/watch?v=g929VCcnz5Q)
- [ ] [25. Graph Decompositions](https://www.youtube.com/watch?v=lGth8VdtU88)
- [ ] [26. Cycle Decomposition iff All Vertices Have Even Degre](https://www.youtube.com/watch?v=Dvvqs375ax8)
- [ ] [27. Hamiltonian Graphs and Problem Set](https://www.youtube.com/watch?v=wh9mZCUf-z4)
- [ ] [28. Hamiltonian Graph Problems](https://www.youtube.com/watch?v=3xeYcRYccro)
- [ ] [29. Lovasz Conjecture on Hamilton Paths](https://www.youtube.com/watch?v=Bq1u9704csA)
- [ ] [30. The 5 Known Vertex-Transitive Non-Hamiltonian Graphs](https://www.youtube.com/watch?v=FgHuQw7kb-o)
- [ ] [31. Lemma on Hamiltonian Graphs](https://www.youtube.com/watch?v=XA8MDEYNWx8)
- [ ] [32. Necessary (not sufficient) Condition for Existence of a Hamilton Cycle](https://www.youtube.com/watch?v=0ksOKghZKdo)
- [ ] [33. Petersen Graph is Not Hamiltonian](https://www.youtube.com/watch?v=AVe-OA-fcV0)
- [ ] [34. Bridge edges](https://www.youtube.com/watch?v=zxu0dL436gI)
- [ ] [35. Bridges in Connected Graphs](https://www.youtube.com/watch?v=SFFEc8DbO0Y)
- [ ] [36. Definition of a Tree](https://www.youtube.com/watch?v=QFQlxtz7f6g)
- [ ] [37. Which Graphs are Trees](https://www.youtube.com/watch?v=BptJFixSseM)
- [ ] [38. Three ways to Identify Trees](https://www.youtube.com/watch?v=Yon2ndGQU5s)
- [ ] [39. Types of Trees](https://www.youtube.com/watch?v=2k_FFB5Rmwo)
- [ ] [40. Cayley's Formula and Prufer Sequences part 1/2](https://www.youtube.com/watch?v=Ve447EOW8ww)
- [ ] [41. Cayley's Formula and Prufer Sequences part 2/2](https://www.youtube.com/watch?v=utfW-xsDp3Y)
- [ ] [42. Degree Sequences and Graphical Sequences](https://www.youtube.com/watch?v=aNKO4ttWmcU)
- [ ] [43. Havel-Hakimi Theorem on Graphical Sequences](https://www.youtube.com/watch?v=iQJ1PFZ4gh0)
- [ ] [44. Degree Sequence of a Tree](https://www.youtube.com/watch?v=cCG4_mj9TgM)
- [ ] [45. Specific Degrees in a Tree](https://www.youtube.com/watch?v=SzPyRwZJLso)
- [ ] [46. Relation Between Minimum Degree and Subtrees](https://www.youtube.com/watch?v=IvLcmazpMPg)
- [ ] [47. Subgraphs of Regular Graphs](https://www.youtube.com/watch?v=KFtPHoaqUaQ)
- [ ] [48. Complement of a Graph](https://www.youtube.com/watch?v=VTgxv334KSU)
- [ ] [49. Cartesian Product of Graphs](https://www.youtube.com/watch?v=X8mnQJ5AlTM)
- [ ] [50. Maximum vs Maximal](https://www.youtube.com/watch?v=03PUwWef2Dg)
- [ ] [51. Eccentricity, Radius & Diameter](https://www.youtube.com/watch?v=YbCn8d4Enos)
- [ ] [52. Radius and Diameter Examples](https://www.youtube.com/watch?v=O4LVAGV8tok)
- [ ] [53. Cut-Vertices](https://www.youtube.com/watch?v=BxAgmaLWaq4)
- [ ] [54. Number of Cut-Vertices](https://www.youtube.com/watch?v=mPI8_qZm1_8)
- [ ] [55. Bridges and Blocks](https://www.youtube.com/watch?v=iGsxKUzW3cs)
- [ ] [56. Central Vertices are in a Single Block](https://www.youtube.com/watch?v=Wp-2_Paikt8)
- [ ] [57. Planar Graphs](https://www.youtube.com/watch?v=wnYtITkWAYA)
- [ ] [58. Euler's Formula for Plane Graphs](https://www.youtube.com/watch?v=5ywif1Zpeo4)
- [ ] [59. Maximal Planar Graphs](https://www.youtube.com/watch?v=_d_6JvceAwE)
- [ ] [60. Non Planar Graphs](https://www.youtube.com/watch?v=-m6Dq7v9ToM)
- [ ] [61. Characterisation of Planar Graphs](https://www.youtube.com/watch?v=UkjJE3bmPV0)
- [ ] [62. Graph Minors and Wagner's Theorem](https://www.youtube.com/watch?v=2hkLC2q2wT4)
- [ ] [63. Petersen Graph is Non-Planar](https://www.youtube.com/watch?v=tdw_ECm8kRE)


Considering this as well:
  - https://www.coursera.org/learn/graphs
