---
layout: "post"
title: "SAT solvers"
date: "2018-07-03"
categories: learning
published: true
references: true
home: false
---

This will contain some thoughts about sat solving. See the references.

- Many SATs solvers are based on Davis-Putnam-Logemann-Loveland (DPLL) procedure.
- The improvements in these programs are mostly:
  - better implementation techniques, such as the two-watched literal approach for unit propagation
  - several conceptual enhancements on the original DPLL procedure, aimed at reducing the amount of explored search space
  such as backjumping (a form of non-chronological backtracking), conflict-driven lemma learning, and restarts.
  - they can solve problems with even *tens of thousands of variables* and *millions of clauses*.

{: .references }

  - {% reference Nieuwenhuis2006 %}
