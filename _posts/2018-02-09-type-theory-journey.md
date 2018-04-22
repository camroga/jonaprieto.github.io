---
layout: "post"
title: "Type theories"
date: "2018-02-09"
categories: type-theory
---

Type theory

- is a *unification theory* about computation and logic

- A theory for constructions:

  - Type Zoo:

    * Functions  (`_→_`)
    * Products   (`_×_`)
    * Coproducts (`_+_`)
    * Π-types    (`Π_._`)
    * Σ-types    (`Σ_._`)
    * Id-types   (`_≡_`)
    * W-types    (`W__`)

- is about **deductive systems**, that are, *collection* of rules that derive things
  called *judgements*

- is a class of *formal systems* (also named *formalism*) that includes
    +  axioms
    +  primitive truths
    +  rules of inferences

- is an *alternative* to set theory as a foundation for all mathematics
- notation common uses the following symbols
  + the turnstile or vdash in `latex` (⊢), e.g. as a consequence relation
  for *syntax derivability* to separate assumptions from the conclusion like
      $$ a_{1}, a_{2}, \dots, a_{n} ⊢ c $$
  + the semicolon `:` to denote *judgments* like $$ term : Type $$

We mostly refer to type theories using the following abbreviations:

- (**TT**)  *Intuitionistic* type theory (*Constructive mathematics*).

- (**ITT**) *Intensional* type theory

    -  a intuitionistic type theory

    - [*Identity types*](https://ncatlab.org/nlab/show/identity+type) are not necessary propositions

    - It fails to satisfy [*function extensionality*](https://ncatlab.org/nlab/show/function+extensionality)

- (**ETT*) *Extensional* type theory

  - Can impose axioms to trivialise identity types

  - Force types to conform to our intuition about sets

  - Destroys computational content, decidability of type-checking...

- Homotopy type theory

  - Logic to natively formalise homotopy theory

  - Intuition for working with Id-types

  - *UnivalenceAxiom* : equality between types can be isomorphism.
    Gives (some) parametricity for free: all constructions on types invariant under iso.

- Cubical type theory
- Observational type theory
- [Computational higher type theory](https://github.com/CHTT-s18/lecture-notes)


### References

- {% reference hottbook %}
