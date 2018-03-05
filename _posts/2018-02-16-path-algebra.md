---
layout: "post"
title: "Path Algebra"
date: "2018-02-16 21:57"
categories: type-theory
---

In univalence we have a different interpreation of type theory. We replace the
set-theoretical notion of sets for types and we use instead of it the *topological
space*. In this interpretation we also replace the notion of an element of `a =
b`, that is, the proof of such a equality and instead of it we use a new
concept, *path*, for this element, where `a` is the start of the path, and `b` is
the endpoint. Then, the identity type, `a = b`, is all paths that start in `a` and
end in `b` that's why we call this type *path space* for `a : A` and `b : A`.

Besides traditional type theory, recall HoTT comes from geometry and the beauty
of this is we can draw some of its concepts and for sure that will help us to
strengthen our intuition about paths. For instance, if `p : a = b`, we
write `p⁻¹ : b = a` for the reversed path. We can join two path that share
the endpoint of one to the start point of the other, we call this operation,
concatenation and we use the symbol (`_·_`). For instance we have the path
`p · p⁻¹ : a = a` and `p⁻¹ · p : b = b`.

### Path Algebra

properties

A proof for :
- Symmetry using bpi
- Transitivity using pi

![path](/assets/images/trans.png)

### Path induction again
