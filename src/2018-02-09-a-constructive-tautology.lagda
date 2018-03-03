---
layout: "post"
title: "A Constructive Tautology"
date: "2018-02-09"
categories: type-theory
---

Consider the following type:

```
(Πx:A.Πy:A.(P x ⟶ Q x y)) ⟶ Πx:A.(P x ⟶ Πy:A.Q x y) .
```

In Agda:

\begin{code}
type : Set₁
type = ∀ {A : Set} {P : A → Set} {Q : A → A → Set}
       → ((x y : A) → P x → Q x y)
       → ((x : A) → (P x → (y : A) → Q x y))
\end{code}

with an inhabitant of this type:

\begin{code}
inhab : type
inhab {A}{P}{Q} f = λ x px y → f x y px
\end{code}
