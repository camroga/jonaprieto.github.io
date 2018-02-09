---
layout: "post"
title: "Experiments"
date: "2018-02-09 22:20"
---


(Πx:A.Πy:A.(Px ⟶ Qxy)) → Πx:A.(Px → Πy:A.Qxy)

\begin{code}
exchange : ∀ {A : Set} {P : A → Set} {Q : A → A → Set}
         → ((x y : A) → P x → Q x y)
         → ((x : A) → (P x → (y : A) → Q x y) )
exchange {A}{P}{Q} f = λ x px y → f x y px
\end{code}
