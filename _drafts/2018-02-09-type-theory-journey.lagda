---
title: Type theory journey
layout: page
---

Type theory is :

  + unification theory about computation and logic
  + formal system in logic

*   Intuitionistic type theory? Why intuitionistic? (TT)
*   Intensional type theory? Why intensional? (ITT)
*   Extensional type theory? Why intensional? ITT + (ER) + UIP?
*   Homotopy type theory? ITT + HiT + UA?
*   Proof are form of constructions. Algorithms.
*   What is the notion of proof-relevance. proofs are now mathematical objects?
*   Equivalent between proofs of equations and paths in a space?
*   What does it mean "synthetic" vs "analytic"?
s
    synthetic geometry: euclidian proofs
    analytic geometry: cartesian analysis.

    synthetic HTT: model category theory.
    analytic HTT: traditional TT
                ,--->(Programing Language Theory)

    synthetic PLT: LF(logic framework)/Twelf
    analytic PLT: Coq.

    synthetic reasoning approach deals with things with take into accout
    their real nature underneth. Instead, analythic seems to talk about how
    to deal with the atoms of those things. But it stills unclear.

*   type theory is analysis + codification
    of Brower's intutionism,
    drawing on Gentzen's drawing.
    types classify *constructions*, what is a construction?
*   Inversion principle and Conservation of proof and its relation with elim/intro rules.
    ---> foundation of computing of  algorithm aspects

*   Why LEM and no other lemma bouwer chose? is about computation related topic?


*   Type theory aims to expand what does it mean something
 is computable? and HoTT to high dimesion topological
 objects.

* What is A true means? ans?: A is provable ()
* What is A false means? ans?: A is refutable.

(open-endedness)?

negation fragment of ITP?

- take care of using the word **proof**

(constructivism view)
propostions has computation content/

- TODO: Review the logic entailment! which is the notion of theres is prior
to implication.

* What is another name for *entailment*?

ans: as logical consequence or a hypothetical judgment

* Can we distinguish between *judgements* and *propostions*?

ans: we have judgements after declare a position about a proposition/statement.
  A prop  := "0 is a natural number"
  A false := Judgement says it's false.

* What are the two basic judgements in Martin-lof theory?

ans:
    - A prop (A is a well-formed proposition.)
    - A true (A has a proof)
* The difference of formation rules and (introduction/elimination rules)?

ans:
    - formation rules are such rules that deserves to create propositions.
        e.g: 
        A prop   B prop
        ———————————————  (∧F)
            A ∧ B prop
    - intro/elim rules are such rules that deals with judgements.
        e.g: 
        A true   B true
        ———————————————  (∧I)
            A ∧ B true

* What is the meaning of a proposition?

In a general sense, a proposition is something that admits a judgement.
Two basic judgements (basic atomic):

A prop
A true



* What is that about *internal coherence*, also known as Gentzen’s *principle of inversion*?

ans: The elimination rules should be strong enough to deduce all information
that was used to introduce A (local completeness), but not so strong as to
deduce information that might not have been used to introduce A (local
soundness).

* what not is there a elimination rule for ⊤?

ans: an elimination intends to extract information but what about a ⊤.
there is no extra information that just ⊤, so we'd be doing nothing.

* What does "negative fragment of ITP" refers after all?

* How does the inference rules looks when they are presented in a *local form*? :

ans:in which the context of assumptions was left implicit
Otherwise, the context should be explicit like this:

        φ, ψ ⊢ φ ∧ ψ
        —————————————
        φ, ψ ⊢ φ


* Which are the most important criticism of the homotopy type theory?v 

* hypothetical judgement: (entailment relation)

A₁ true, A₂ true, ..., An true ⊢ B true

  What is entailment?

  The entailement (⊢) is a relation that follows the next properties,
  the so-called *structural properties*:

    1) A true ⊢ A true (Refl)

    2) (Cuting)

       Γ1 ⊢ A true    Γ2, A true ⊢ B true
      ————————————————————————————————— (Trans)
        Γ1 Γ2 ⊢ B true
    
    The following are denagables (some people think they should denied)

    3) weaking

        Γ ⊢ A true
        —————
        Γ , B true ⊢ A true
     
     ... we can deny the weaking principle..
     ... review: formal logic.

     4) contraction:

        Γ , A true, A true ⊢ B true
        ————————————————————
        Γ , A true ⊢ B true

     5) permutation of assumitions that's matter.

        Γ ⊢ A
        ——————
        π(Γ) ⊢ A


     if the entailment relation follows the above (5) relations,
     we call a structural entailement relation.
     But! if some (3-5) is denied, we call this *substructural entailement*.

     If we assume the properties (1-5), we can freely write down the rules
     without taking into accout the contexts.

     i.e:
     
     * Accepting the properties (1-5):

     Γ ⊢ A true   Γ ⊢ A true ⟹ B true
     —————————————————————————————————— (⟹E)
        Γ ⊢ B true  

        why? use contraction, permutation and weaking.

        (Γ = Γ₁Γ₂)

        Γ₁ ⊢ A true   Γ₂ ⊢ A true ⟹ B true
         —————————————————————————————————— (W)
        Γ₁Γ₂ ⊢ A true   Γ₂Γ₁ ⊢ A true ⟹ B true
         —————————————————————————————————— (⟹E)
             Γ₁Γ₂Γ₂Γ₁ ⊢ B true
         —————————————————————————————————— (C)
             Γ₁Γ₂Γ₁ ⊢ B true
         —————————————————————————————————— (π)
              Γ₁Γ₁Γ₂ ⊢ B true
         —————————————————————————————————— (C)
              Γ₁Γ₂ ⊢ B true
        

     * Denying some (3-5):

        Γ₁ ⊢ A true   Γ₂ ⊢ A true ⟹ B true
     —————————————————————————————————— (⟹E)
        Γ₁ ∪ Γ₂ ⊢ B true  


* Order-theorically formulation:

A ≤ B, for A, B prop by (A true ⊢ B true)
    
    1) Preorder
        * Reflection:  A  ≤ A
        * trnasitive:
            A ≤ B   B ≤ C
        then
            A ≤ C   

    2) meets given by conjunction:


    ————————————————  and ————————————————
       A ∧ B ≤ A            A ∧ B ≤ B


       C ≤ A   C ≤ B
    ————————————————
        C ≤ A ∧ B

    Hessel diagram:

            __(C)_
           /   |   \
          |    v    \
          | (A ∧ B)  \
          | /   \    |
          |/     \   /
          v        v
         (A)      (B)
    
    3) Greatest element:

        A ≤ Γ

    partial order means! antisemetry:

    A ≤ B  and B ≤ A
    ———————————————— 
       A = B
    

For the positive fragment:

    Order:

     * least initial:  ⊥ ≤ A
     * Joins by disjunction:

     A ≤ A ∨ B     B ≤ A ∨ B

     * A ≤ C   and B ≤ C
     then:
        A ∨ B ≤ C

     * (Co)product diagram (hassle diagram)

     exponential: B^A  (A ⟹ B)
        A ∧ (A ⟹ B) ≤   B

        A ∧ C ≤ B
        C ≤ A ⟹ B


* What is really a lattice? is a mathematical structure? or what?
ans: Lattice! (a preorden or partial order where you find all meets and joins)

* What is a Heyting Algebra?
* Every Heyting Algebra is distribute, but why??

A ∧ ( B ∨ C) ≡ (A ∧ B) ∨ (A ∧ C)
    - use exponentials
    - use Yonneda's Lemma.

* What is about the Yonneda's Lemma?
ans:
    A ≤ B iff ∀ x, x ≤ A then x ≤ B     

* What about the negation?

ans:  ¬ A := A ⟹ ⊥
¬ A =  is the largest C inconsist with A

A ∧ ¬ A ≤ ⊥

A ∧ C ≤ ⊥
—————————
C ≤ A ⟹ ⊥ or C ≤ ¬ A

* Complement A* (A overbar)

A ∨ A* ≡ ⊤ ? just provable in boolean algebra.
But it is not true in HoTT (in general), 
there is not a global decidable property.

⊤ ≤ A ∨ A*

Boolean algebra (complemented distr. lattice has exponentials)

e.g: 

B^A = A ⟹ B  := A* ∨ B


* Heyting algebra (check the completeness theorem)

