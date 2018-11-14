---
layout: "post"
title: "Isabelle"
date: "2018-06-27"
categories: learning
published: true
toc: true
references: true
home: false
---


## Isabelle/HOL

Following {% cite TobiasNipkow2016 %}

![](/assets/png-images/2018-06-27-theorem-proving-d1fc95b9.png)


### Basic

- *Isabelle* is a generic system for implementing logical formalisms
- *Isabelle/HOL* is the specialization of Isabelle for HOL

- Basic types:
  - `bool` : truth values
  - `nat ` : natural numbers
  - `int ` : mathematical Integers

- Type constructors:
  - `list`: `nat list`
  - `set`:  `int set`

- function types, denoted by `⇒`. type
- type variables, denoted by ′a,... : `′a ⇒ ′b list`
- type constraint (or type annotation): `t :: τ` means the term `t` has type `τ`

- basic constructors (written for safety between parenthesis):

  - `(if b then t1 else t2)`
  - `(let x = t in u)`
  - `(case t of pat1 ⇒ t1 | ... | patn ⇒ tn)`

- formulas: `bool` terms
  - constants: `True`, `False`
  - connectives `¬, ∧, ∨, −→`

- equality: `= :: ′a ⇒ ′a`
- quantifiers: `∀ x. P` and `∃ x. P`
- *universal* quantifiers \Lambda and \LongRightarrow (from Isabelle not from HOL)
- Right-arrows of all kinds always associate to the right
- `[[ A1; ...; An ]] =⇒ A` is short for `A1 =⇒ ... =⇒ An =⇒ A`

- Theories: a **theory** is a named collection of types, functions, and theorems.

  - All Isabelle text needs to go into a theory
  - `T` must reside in a theory file named `T.thy`
  - The general format for a theory `T` is:

  {%- highlight isabelle -%}
  theory T
  imports T1 ... Tn
  begin
    ...
  end
  {%- endhighlight -%}

  - `Main` is a theory available, the union of all the basic predefined theories about arithmetic, lists, sets, etc.

  - more theories at http://afp.sourceforge.net

- "... " for types and formulas in HOL
- HOL syntax as the inner syntax
- enclosing theory language as the outer syntax

### Types

#### bool

{%- highlight isabelle -%}
datatype bool = True | False
{%- endhighlight -%}

- predefined functions: ¬, ∧, ∨, −→, among others.
- example of usage:

{%- highlight isabelle -%}
fun conj :: "bool ⇒ bool ⇒ bool" where
    "conj True True = True"
  | "conj _   _     = False"
{%- endhighlight -%}

#### nat

{%- highlight isabelle -%}
datatype nat = 0 | Suc nat
{%- endhighlight -%}

- predefined functions: +, ∗, !
- example of usage:

{%- highlight isabelle -%}
fun add :: "nat ⇒ nat ⇒ nat" where
    "add 0 n = n"
  | "add (Suc m) n = Suc(add m n)"
{%- endhighlight -%}

{%- highlight isabelle -%}
lemma m0eqm : "add m 0 = m"
  apply(induction m)
  apply(auto)
done
{%- endhighlight -%}

- the concept of **proof state** is about the hypothesis
to be eliminated from current stage. That is, what is
missing of the proof.

- **inspect the lemma**: `thm add_02`
- the keywords **lemma**, **theorem** and **rule** are interchangeably
- **IH** will stand for “induction hypothesis”.

#### list

{%- highlight isabelle -%}
datatype ′a list = Nil | Cons ′a "′a list"
{%- endhighlight -%}

Command `value` evaluates a term.
{%- highlight isabelle -%}
value "rev(Cons True (Cons False Nil))" yields
{%- endhighlight -%}

- **To suppress the qualified names** you can insert the command declare `[[names_short]]`

**Bookmark Page 11**.

- [ ] 2.3 Type and Function Definitions                 15
- [ ] 2.4 Induction Heuristics                          19
- [ ] 2.5 Simplification                                21
- [ ] 3 Case Study: IMP Expressions                     27
- [ ] 3.1 Arithmetic Expressions                        27
- [ ] 3.2 Boolean Expressions                           32
- [ ] 3.3 Stack Machine and Compilation                 35
- [ ] 4 Logic and Proof Beyond Equality                 37
- [ ] 4.1 Formulas                                      37
- [ ] 4.2 Sets                                          38
- [ ] 4.3 Proof Automation                              39
- [ ] 4.4 Single Step Proofs                            42
- [ ] 4.5 Inductive Definitions                         45
- [ ] 5 Isar: A Language for Structured Proofs          53
- [ ] 5.1 Isar by Example                               54
- [ ] 5.2 Proof Patterns                                56
- [ ] 5.3 Streamlining Proofs                           58
- [ ] 5.4 Case Analysis and Induction                   61

X Contents

Part II Semantics

- [ ] 6 Introduction                                    73
- [ ] 7 IMP: A Simple Imperative Language               75
- [ ] 7.1 IMP Commands                                  75
- [ ] 7.2 Big-Step Semantics                            77
- [ ] 7.3 Small-Step Semantics                          85
- [ ] 7.4 Summary and Further Reading                   90
- [ ] 8 Compiler                                        95
- [ ] 8.1 Instructions and Stack Machine                95
- [ ] 8.2 Reasoning About Machine Executions            98
- [ ] 8.3 Compilation                                   99
- [ ] 8.4 Preservation of Semantics                     102
- [ ] 8.5 Summary and Further Reading                   112
- [ ] 9 Types                                           115
- [ ] 9.1 TypedIMP                                      117
- [ ] 9.2 Security Type Systems                         128
- [ ] 9.3 Summary and Further Reading                   140
- [ ] 10 Program Analysis                               143
- [ ] 10.1 Definite Initialization Analysis             145
- [ ] 10.2 Constant Folding and Propagation             154
- [ ] 10.3 Live Variable Analysis                       164
- [ ] 10.4 True Liveness                                172
- [ ] 10.5 Summary and Further Reading                  178
- [ ] 11 Denotational Semantics                         179
- [ ] 11.1 A Relational Denotational Semantics          180
- [ ] 11.2 Summary and Further Reading                  188
- [ ] 12 Hoare Logic                                    191
- [ ] 12.1 Proof via Operational Semantics              191
- [ ] 12.2 Hoare Logic for Partial Correctness          192
- [ ] 12.3 Soundness and Completeness                   203
- [ ] 12.4 Verification Condition Generation            208
- [ ] 12.5 Hoare Logic for Total Correctness            212
- [ ] 12.6 Summary and Further Reading                  215
- [ ] Contents XI
- [ ] 13 Abstract Interpretation                        219
- [ ] 13.1 Informal Introduction                        220
- [ ] 13.2 Annotated Commands                           224
- [ ] 13.3 Collecting Semantics                         225
- [ ] 13.4 Abstract Values                              236
- [ ] 13.5 Generic Abstract Interpreter                 241
- [ ] 13.6 Executable Abstract States                   253
- [ ] 13.7 Analysis of Boolean Expressions              259
- [ ] 13.8 Interval Analysis                            264
- [ ] 13.9 Widening and Narrowing                       270
- [ ] 13.10 Summary and Further Reading                 279
- [ ] A Auxiliary Definitions                           281
- [ ] B Symbols                                         283
- [ ] C Theories                                        285
- [ ] References                                        287
