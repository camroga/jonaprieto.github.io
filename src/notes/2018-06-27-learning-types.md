---
layout: "post"
title: "Types"
date: "2018-06-27"
categories: learning
published: true
latex: true
references: true
agda: true
---

Texts from many sources. See a good list of resources to learn
[here](https://github.com/williamdemeo/TypeFunc).

## [Intro to Homotopy Type Theory by Thorsten Altenkirch](http://www.cs.nott.ac.uk/~psztxa/ewscs-17/notes.pdf)

The word type theory has at least two meanings:
  • The theory of types in programming language
  • Martin-Löf’s Type Theory as a constructive foundation of Mathematics


- Extensional Type Theory is now referred to as Computational Type Theory
- Type theory is an intuitive foundation of Mathematics

![](/assets/png-images/2018-06-27-learning-types-7385c80c.png)

### Higher Inductive Types

Higher Inductive Types even for sets are more general than set quotients
because we can define elements and equalities at the same time. An example for
this are infinite branching trees with permutations. That is we define infinitely
branching trees
![](/assets/png-images/2018-06-27-learning-types-91cfc8c2.png)
We inductively define a relation which identifies trees upto permutations of
subtrees:
![](/assets/png-images/2018-06-27-learning-types-acf5fbeb.png)
Now trees with permutations can be defined as PTree :≡ Tree/ ∼. However, it
turns out that this type is not as useful as we might hope. Let’s say we want
to lift the node construction to PTree that is we want to define

Using HITs we have an alternative: we can define permutable trees by
introducing the elements and the equalities at the same time
![](/assets/png-images/2018-06-27-learning-types-37c6e3f6.png)
