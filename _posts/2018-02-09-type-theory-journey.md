---
title: TT Summary
layout: "post"
---

Type theory

- is a *unification theory* about computation and logic

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
      $$ a_{1}, a_{2}, \dots, a_{n} ⊢ c  $$
  + the semicolon `:` to denote *judgments* like $$ term : Type $$

We mostly refers to type theories using the following abbreviations:

- (**TT**)  *Intuitionistic* type theory (*Constructive mathematics*).

- (**ITT**) *Intensional* type theory

    -  a intuitionistic type theory

    - [*Identity types*](https://ncatlab.org/nlab/show/identity+type) are not necessary propositions

    - It fails to satisfy [*function extensionality*](https://ncatlab.org/nlab/show/function+extensionality)
