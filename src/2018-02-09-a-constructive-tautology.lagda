---
layout: "post"
title: "A Constructive Tautology"
date: "2018-02-09 22:20"
---

Consider the following type:

    (Πx:A.Πy:A.(P x ⟶ Q x y)) ⟶ Πx:A.(P x ⟶ Πy:A.Q x y) .

An its inhabitant:

\begin{code}
exchange : ∀ {A : Set} {P : A → Set} {Q : A → A → Set}
         → ((x y : A) → P x → Q x y)
         → ((x : A) → (P x → (y : A) → Q x y) )
exchange {A}{P}{Q} f = λ x px y → f x y px
\end{code}
