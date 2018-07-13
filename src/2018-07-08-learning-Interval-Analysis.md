---
layout: "post"
title: "Intervals"
date: "2018-07-08"
categories: learning
published: true
toc: true
---

Interval analysis literature search.

<div class="links" markdown="1">

## Interval and Related Software

### [ALIAS Library 2012](http://www-sop.inria.fr/coprin/logiciels/ALIAS/ALIAS-C++/ALIAS-C++.html)

Algorithms Library of Interval Analysis for Systems

  - https://www-sop.inria.fr/coprin/developpements/main.html
  - https://www-sop.inria.fr/coprin/logiciels/ALIAS/ALIAS-C++/manual-alias-C++2.7.pdf

  - [Tutorial: Analyse par intervalles et Applications](http://www-sop.inria.fr/coprin/logiciels/ALIAS/Examples/COURS/index.html)

  - Examples: [The COPRIN examples page](https://www-sop.inria.fr/coprin/logiciels/ALIAS/Benches/benches.html)

- [**Solve_intpakX with Graphics**](http://www2.math.uni-wuppertal.de/~xsc/software/intpakX/) is a set of Maple procedures for solving system of equations that takes the basic algorithms of ALIAS but allows the resolution in arbitrary precision.

  - [Multiple Precision Interval Packages:Comparing
Different Approaches. M. Grimmer](https://hal.inria.fr/inria-00071744/document)

  - [Interval Arithmetic in Maple with intpakX](http://www2.math.uni-wuppertal.de/wrswt/preprints/prep_02_5.pdf)

### [Arb](http://arblib.org/)

Arb is a C library for rigorous real and complex arithmetic with arbitrary precision. Arb tracks numerical errors automatically using ball arithmetic, a form of interval arithmetic based on a midpoint-radius representation

### [AWA](ftp://ftp.iam.uni-karlsruhe.de/pub/awa/)

A software package for verified solution of ordinary differential equations.

### [CAPD, Computer-Assisted Proofs in Dynamics](http://capd.ii.uj.edu.pl/)

A C++ package for rigorous numerics for dynamical systems, oriented mostly for computer assisted proofs in dynamics.
This library provides provides rigorous solvers for ODEs, variational equations for ODEs, differential inclusions, automatic computation of Poincare maps and their derivatives, computation of homology of spaces, maps and many other features.

### [COSY](http://cosy.pa.msu.edu/)

This software package is based on Taylor model and interval methods. It is intended for verified solution of such problems as ordinary differential equations, quadrature, range bounding, etc. It can either be used as a stand-alone program or via C++ and Fortran 90/95 frontends.

### [Euler](http://www.euler-math-toolbox.de/Programs/08%20-%20Intervals.html)

  - Interval Arithmetic
  - [Interval Solvers and Guaranteed Solutions](http://www.euler-math-toolbox.de/reference/numerical.html#Interval_Solvers_and_Guaranteed_Solutions)

### [INTLAB - INTerval LABoratory](http://www.ti3.tu-harburg.de/rump/intlab/index.html)

An interval toolbox for Matlab; free for non-commercial use.

  - [INTLAB references](http://www.ti3.tuhh.de/rump/intlab/INTLABref.pdf)

### [Pytaylor](http://gitorious.org/pytaylor)

A Python package implementing Taylor models and associated guaranteed ODE solvers.
Pytaylor uses

  - [mpmath](http://mpmath.org/doc/current/contexts.html#arbitrary-precision-interval-arithmetic-iv) for interval arithmetic. [Github](https://github.com/fredrik-johansson/mpmath)

    - http://mpmath.org/doc/current/calculus/odes.html

  - [sympy](https://docs.sympy.org/0.6.7/modules/mpmath/intervals.html) for symbolic manipulation.

  - http://homepages.math.uic.edu/~jan/mcs507f13/intervalarithmetic.pdf
  - http://homepages.math.uic.edu/~jan/mcs507f13/

### [VALENCIA-IVP](http://valencia-ivp.com/)

Software for VALidation of state ENClosures using Interval Arithmetic for Initial Value Problems

### [VNODE-LP](http://www.cas.mcmaster.ca/~nedialk/vnodelp/)
A C++ based Interval Solver for Initial Value Problems in Ordinary Differential Equations



</div>
