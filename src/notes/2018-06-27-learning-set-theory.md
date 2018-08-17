---
layout: "post"
title: "Set theory"
date: "2018-06-27"
categories: learning
published: true
latex: true
references: true
agda: true
---

<div class="references" markdown="1">

- Considering this playlist: https://www.youtube.com/playlist?list=PLR3z46pdylqSRkO1luzzwxR6mPyTyc6ne

## **ZFC's axioms**

 See a set theory formalisation in Agda in [acalles1/setform](https://github.com/acalles1/setform)
 The following was taken from that source and from (Suppes 1960, p. 56).

  - **ext (Extensionality)**: If two sets have exactly the same members,
   they are equal.

   - **empt (Empty Set Axiom)**: There is a set having no
   members. Allows us to define the empty set.

   - **pair (Pairing Axiom)**: For any sets y and z, there is a set having
   as members just y and z. Allows to define a set which is just
   the pair of any two sets.

   - **pow (Power Set Axiom)**: For any x there is a set whose members are
   exactly the subsets of x. Allows us to define the power set
   operation.

   - **sub (Subset Axiom, or Specification Axiom)**: This axiom asserts the
   existence of a set B whose members are exactly those sets x in y
   such that they satisfy certain property. Allows us to define
   many operations like cartesian products and difference of sets.

   - **uni (Union Axiom)**: For any set x, there exists a set A whose
   elements are exactly the members of x. Allows us to define the
   union of two sets.

  - **pem (Principle of the excluded middle)**: To prove some things
   not valid in intuitionistic logic and valid in classical logic. Taken
   from the Standford Encyclopedia entry on Intuitionistic Logic.
   (https://plato.stanford.edu/entries/logic-intuitionistic/).

   The sum axioms allow us to define the union operation
   over a family of sets.

- [How the Axiom of Choice Gives Sizeless Sets](https://www.youtube.com/embed/hcRZadc5KpI)

  ![](/assets/png-images/2018-06-27-learning-set-theory-fba52c79.png)

  - **Axiom of Choice** Given a infinite collection of nonempty sets we can
  form a new set that contains one element from each set.

  ![](/assets/png-images/2018-06-27-learning-set-theory-7cb7b20d.png)

</div>
