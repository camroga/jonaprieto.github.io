---
layout: "post"
title: "Intervals"
date: "2018-07-08"
categories: learning
published: true
toc: true
linkify: true

---

Interval analysis literature search.

<div class="links" markdown="1">

## Interval and Related Software

### ALIAS Library 2012

[Main link](http://www-sop.inria.fr/coprin/logiciels/ALIAS/ALIAS-C++/ALIAS-C++.html)

Algorithms Library of Interval Analysis for Systems

  - https://www-sop.inria.fr/coprin/developpements/main.html
  - https://www-sop.inria.fr/coprin/logiciels/ALIAS/ALIAS-C++/manual-alias-C++2.7.pdf

  - [Tutorial: Analyse par intervalles et Applications](http://www-sop.inria.fr/coprin/logiciels/ALIAS/Examples/COURS/index.html)

  - Examples: [The COPRIN examples page](https://www-sop.inria.fr/coprin/logiciels/ALIAS/Benches/benches.html)

- [**Solve_intpakX with Graphics**](http://www2.math.uni-wuppertal.de/~xsc/software/intpakX/) is a set of Maple procedures for solving system of equations that takes the basic algorithms of ALIAS but allows the resolution in arbitrary precision.

  - [Multiple Precision Interval Packages:Comparing
Different Approaches. M. Grimmer](https://hal.inria.fr/inria-00071744/document)

  - [Interval Arithmetic in Maple with intpakX](http://www2.math.uni-wuppertal.de/wrswt/preprints/prep_02_5.pdf)

### Arb

[Main link](http://arblib.org/)

Arb is a C library for rigorous real and complex arithmetic with arbitrary precision. Arb tracks numerical errors automatically using ball arithmetic, a form of interval arithmetic based on a midpoint-radius representation

### AWA

[Main link](ftp://ftp.iam.uni-karlsruhe.de/pub/awa/)

A software package for verified solution of ordinary differential equations.

### CAPD, Computer-Assisted Proofs in Dynamics

[Main link](http://capd.ii.uj.edu.pl/)

A C++ package for rigorous numerics for dynamical systems, oriented mostly for computer assisted proofs in dynamics.
This library provides provides rigorous solvers for ODEs, variational equations for ODEs, differential inclusions, automatic computation of Poincare maps and their derivatives, computation of homology of spaces, maps and many other features.

### COSY

[Main link](http://cosy.pa.msu.edu/)

This software package is based on Taylor model and interval methods. It is intended for verified solution of such problems as ordinary differential equations, quadrature, range bounding, etc. It can either be used as a stand-alone program or via C++ and Fortran 90/95 frontends.

### Euler

[Main link](http://www.euler-math-toolbox.de/Programs/08%20-%20Intervals.html)

  - Interval Arithmetic
  - [Interval Solvers and Guaranteed Solutions](http://www.euler-math-toolbox.de/reference/numerical.html#Interval_Solvers_and_Guaranteed_Solutions)

### INTLAB - INTerval LABoratory

[Main link](http://www.ti3.tu-harburg.de/rump/intlab/index.html)

An interval toolbox for Matlab; free for non-commercial use.

  - [INTLAB references](http://www.ti3.tuhh.de/rump/intlab/INTLABref.pdf)

### Pytaylor

[Main link](http://gitorious.org/pytaylor)

A Python package implementing Taylor models and associated guaranteed ODE solvers.
Pytaylor uses

  - [mpmath](http://mpmath.org/doc/current/contexts.html#arbitrary-precision-interval-arithmetic-iv) for interval arithmetic. [Github](https://github.com/fredrik-johansson/mpmath)

    - http://mpmath.org/doc/current/calculus/odes.html

  - [sympy](https://docs.sympy.org/0.6.7/modules/mpmath/intervals.html) for symbolic manipulation.

  - http://homepages.math.uic.edu/~jan/mcs507f13/intervalarithmetic.pdf
  - http://homepages.math.uic.edu/~jan/mcs507f13/

### VALENCIA-IVP

  [Main link](http://web.archive.org/web/20070716195309/http://www.valencia-ivp.com/)

  Software for VALidation of state ENClosures using Interval Arithmetic for
  Initial Value Problems.
  - https://interval.louisiana.edu/reliable-computing-journal/volume-15/no-4/reliable-computing-15-pp-370-381.pdf

  To obtain a FREE simplified C++ version of ValEncIA-IVP which contains the basic algorithmic components, please contact [Andreas Rauh](http://web.archive.org/web/20070625235940/http://www.mrm.e-technik.uni-ulm.de/homepage/rauh/rauh_e.htm) by e-mail (andreas.rauh(at)uni-rostock.de).

  In order to compile the source code of ValEncIA-IVP, the interval arithmetic library PROFIL/BIAS, the automatic differentiation package FADBAD++, as well as a compatible C++ compiler are required.

  - [PROFIL/BIAS](http://web.archive.org/web/20070716195309/http://www.ti3.tu-harburg.de/keil/profil/)
  - [FADBAD++](http://web.archive.org/web/20070716195309/http://www.imm.dtu.dk/fadbad.html)

### VNODE-LP

[Main link](http://www.cas.mcmaster.ca/~nedialk/vnodelp/)

A C++ based Interval Solver for Initial Value Problems in Ordinary Differential
Equations.

### VSPODE1.4

  [Main link](https://pdfs.semanticscholar.org/6b0f/6801ef866ed60ac64557cfe9b056ca06788e.pdf)

  Software is described in the paper, *Validated Solutions of Initial Value
  Problems for Parametric ODEs* by Youdong Lin and Mark A. Stadtherr.

  To use this software in OSX, we should install `gcc` which also install `gfortran`:

  {%- highlight bash -%}
  $ brew install gcc
  {%- endhighlight -%}

  To find the binaries and libraries we will need to add the following locations
  to our `PATH` in our `~/.bash_profile` or `.bashrc` file

  {%- highlight bash -%}
  $ open ~/.bash_profile
  {%- endhighlight -%}

  And add the following three lines at the end of the opened file.

  {%- highlight bash -%}
  $ cat ~/.bash_profile
  ...
  export PATH="/usr/local/lib:$PATH"
  export PATH="/usr/local/bin:$PATH"
  export PATH="/usr/local/sbin:$PATH"
  {%- endhighlight -%}

  Now, make sure the all `Makefile` in the sources use the `gcc` installed by
  Homebrew, which is, `CC = g++-8`.

  To install it:
  {%- highlight bash -%}
  $ cd source && make
  {%- endhighlight   -%}

  To run the examples:

  {%- highlight bash -%}
  $ cd example && make
  $ cat example/LV1.h
  {%- endhighlight   -%}

  So for instance with the ODE system of Lotka-Volterra, we got the following:

  {%- highlight c++ -%}
  {% raw %}

  // Uncertain parameters and fixed initial states
  template<class T1, class T2>
  void func(T1 *yp, const T1 *y, const T2 *theta, const double *rpar)
  {
    // Implement your model here
    yp[0] = (rpar[0] - theta[0]*y[1])*y[0] ;
    yp[1] = (-rpar[2] + theta[1]*y[0])*y[1] ;
  }
  #endif
  {% endraw %}
  {%- endhighlight -%}

  Running the test for the above model, we got:

  {%- highlight bash -%}
  $ ./example/LV1test
  t = 1
  y_1: 5.09407 [ 75.904003664541207, 80.998071424330519 ]
  y_2: 6.14852 [ 63.108029268335699, 69.256546553495951 ]
  t = 2
  y_1: 11.8951 [ 76.445090786414895, 88.340178987001693 ]
  y_2: 27.9625 [ 119.85108008918118, 147.81354829165241 ]
  t = 3
  y_1: 7.35047 [ 40.093897836313801, 47.444370504269045 ]
  y_2: 30.5832 [ 159.06166928505525, 189.64485917846628 ]
  t = 4
  y_1: 4.65562 [ 23.90462785195502, 28.560252546299107 ]
  y_2: 19.7938 [ 113.44055273186719, 133.23440177448074 ]
  t = 5
  y_1: 3.08082 [ 25.421820570397102, 28.502643893488159 ]
  y_2: 8.15812 [ 71.472181525915943, 79.630302354314566 ]
  t = 6
  y_1: 2.06519 [ 38.296567206835427, 40.361753140149752 ]
  y_2: 2.05428 [ 51.80701055024393, 53.861293542503383 ]
  t = 7
  y_1: 0.402663 [ 63.958447367150974, 64.361110617367856 ]
  y_2: 2.01219 [ 52.633028642163232, 54.645217689851769 ]
  t = 8
  y_1: 9.36482 [ 82.920602045770352, 92.285418215530655 ]
  y_2: 11.5579 [ 87.729119159071757, 99.287039670912776 ]
  t = 9
  y_1: 10.9103 [ 57.48453631237814, 68.39484510328181 ]
  y_2: 31.1925 [ 154.01426752935714, 185.20673926837242 ]
  t = 10
  y_1: 5.10405 [ 28.981713172910908, 34.085764313658906 ]
  y_2: 29.923 [ 137.63384214240136, 167.55682926210102 ]
  CPU time(sec) 0.049189
  {%- endhighlight -%}

  There are more examples in the sources! The sources were provided kindly by the
  authors to test in epidemiological models for Diana Lizarralde. 

</div>
