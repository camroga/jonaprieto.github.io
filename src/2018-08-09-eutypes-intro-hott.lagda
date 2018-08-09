---
layout: "post"
title: "EUTypes 2018 - HoTT"
date: "2018-07-06"
categories: type-theory
toc: true
agda: true
---

This file contains the exercises of *An Introduction
to Homotopy Type Theory*, a course given by [Fredrik Nordvall Forsberg](https://personal.cis.strath.ac.uk/fredrik.nordvall-forsberg/)
in [EUTypes summer school 2018](https://sites.google.com/view/2018eutypesschool/) in Ohrid, Macedonia.

{: .links }
  Links:
    - https://personal.cis.strath.ac.uk/fredrik.nordvall-forsberg/ohrid-school-hott2018/
    - Mini-HoTT Agda library: https://tinyurl.com/mini-hott

\begin{code}
{-# OPTIONS --without-K #-}
open import 2018-07-06-mini-hott
module _ where
\end{code}



## Exercise 1: prove the theorem on slide 5

\begin{code}
contr→prop : {A : Set} -> isContr A -> isProp A
contr→prop (w , d) x y = ((d x) ⁻¹) · d y

contr-if-inhabited→prop : {A : Set} -> (A -> isContr A) -> isProp A
contr-if-inhabited→prop {A} g x y = contr→prop (g x) x y

prop→set : {A : Set} -> isProp A -> isSet A
prop→set  = {!    !}
\end{code}

## Exercise 2: here is another characterisation of propositions:

\begin{code}
prop→all-contr : {A : Set} -> isProp A -> ((x y : A) -> isContr (x == y))
prop→all-contr f x y = ( f x y  , λ p → ((prop→set f) x y) (f x y) p)

all-contr→prop : {A : Set} -> ((x y : A) -> isContr (x == y)) -> isProp A
all-contr→prop g = λ x y → contr→prop (x , λ w → fst (g x y) · (fst (g y w))) x y

-- does this suggest a pattern in the definition of homotopy n-types?
\end{code}

## Exercise 3: prove the vacuum cord principle on slide 8

\begin{code}
vacuum-cord : {A : Set} -> (a : A) -> isContr (Σ A (λ x → x == a))
vacuum-cord a = {!   !}
\end{code}

## Exercise 4: Closure properties (harder)

\begin{code}
contr-is-contr : {A : Set} -> isContr A -> isContr (isContr A)
contr-is-contr p = {!   !}

prop-is-prop-always : {A : Set} -> isProp (isProp A)
prop-is-prop-always = λ x y → {!   !} -- Done with funext twice and using isSet of x
\end{code}

\begin{code}
adjointify : {A B : Set} -> (f : A -> B) -> qinv f -> isEquiv f
adjointify ff (f , η , ε) = {!   !} -- check the notes

-- Exercise 6: Prove that A is contractible iff A ≃ 1
contr→trivial : {A : Set} -> isContr A -> A ≃ ⊤
contr→trivial p = {!  !} --

trivial→contr : {A : Set} -> A ≃ ⊤ -> isContr A
trivial→contr q = {!  !}
\end{code}

## Exercise 7: Extract an equivalence from a Voevodsky equivalence

\begin{code}
fib : {A B : Set} -> (f : A -> B) -> B -> Set
fib {A} f y = Σ A λ x → f x == y

voevoedsky→equiv : {A B : Set} -> (f : A -> B) ->
                   ((y : B) -> isContr (fib f y)) -> isEquiv f
voevoedsky→equiv f p = {!  !}
\end{code}

## Exercise 8: Construct a "bi-functional relation" from an equivalence
\begin{code}
equiv→bifun : {A B : Set} -> (f : A -> B) -> isEquiv f ->
              Σ (A -> B -> Set) λ R →
                Σ ((a : A) → isContr (Σ B λ b → R a b)) λ _ →
                  ((b : B) → isContr (Σ A λ a → R a b))
equiv→bifun f p = {!  !}
\end{code}
