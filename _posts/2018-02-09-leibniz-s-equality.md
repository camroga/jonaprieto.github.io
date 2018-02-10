---
layout: "post"
title: "Leibniz's equality"
date: "2018-02-09 21:58"
---

Leibniz characterised the notion of equality as follows:
Given any x and y, x = y if and only if, given any
predicate P, P(x) if and only if P(y).

  ∀x ∀y (x = y → ∀P (P x ↔ Py)]

<pre class="Agda">

<a id="Eq" href="2018-02-09-leibniz-s-equality.html#Eq" class="Function">Eq <a id="275" class="Symbol">:</a> <a id="277" class="Symbol">∀</a> <a id="279" class="Symbol">{</a><a id="280" href="2018-02-09-leibniz-s-equality.html#280" class="Bound">A</a> <a id="282" class="Symbol">:</a> <a id="284" class="PrimitiveType">Set</a><a id="287" class="Symbol">}</a> <a id="289" class="Symbol">→</a> <a id="291" class="Symbol">(</a><a id="292" href="2018-02-09-leibniz-s-equality.html#292" class="Bound">x</a> <a id="294" href="2018-02-09-leibniz-s-equality.html#294" class="Bound">y</a> <a id="296" class="Symbol">:</a> <a id="298" href="2018-02-09-leibniz-s-equality.html#280" class="Bound">A</a><a id="299" class="Symbol">)</a> <a id="301" class="Symbol">→</a> <a id="303" class="PrimitiveType">Set₁</a>
<a id="308" href="2018-02-09-leibniz-s-equality.html#Eq" class="Function">Eq</a> <a id="311" class="Symbol">{</a><a id="312" href="2018-02-09-leibniz-s-equality.html#312" class="Bound">A</a><a id="313" class="Symbol">}</a> <a id="315" href="2018-02-09-leibniz-s-equality.html#315" class="Bound">x</a> <a id="317" href="2018-02-09-leibniz-s-equality.html#317" class="Bound">y</a> <a id="319" class="Symbol">=</a> <a id="321" class="Symbol">(</a><a id="322" href="2018-02-09-leibniz-s-equality.html#322" class="Bound">P</a> <a id="324" class="Symbol">:</a> <a id="326" href="2018-02-09-leibniz-s-equality.html#312" class="Bound">A</a> <a id="328" class="Symbol">→</a> <a id="330" class="PrimitiveType">Set</a><a id="333" class="Symbol">)</a> <a id="335" class="Symbol">→</a> <a id="337" class="Symbol">(</a><a id="338" href="2018-02-09-leibniz-s-equality.html#322" class="Bound">P</a> <a id="340" href="2018-02-09-leibniz-s-equality.html#315" class="Bound">x</a> <a id="342" class="Symbol">→</a> <a id="344" href="2018-02-09-leibniz-s-equality.html#322" class="Bound">P</a> <a id="346" href="2018-02-09-leibniz-s-equality.html#317" class="Bound">y</a>

</pre>

We can think about this equality definition saying that
x is equal to y if and only if every property (unary predicate variable P)
that x satisfies, y satisfies as well.

* Reflexivity

<pre class="Agda">

<a id="refl" href="2018-02-09-leibniz-s-equality.html#refl" class="Function">refl <a id="565" class="Symbol">:</a> <a id="567" class="Symbol">∀</a> <a id="569" class="Symbol">{</a><a id="570" href="2018-02-09-leibniz-s-equality.html#570" class="Bound">A</a> <a id="572" class="Symbol">:</a> <a id="574" class="PrimitiveType">Set</a><a id="577" class="Symbol">}</a> <a id="579" class="Symbol">→</a> <a id="581" class="Symbol">(</a><a id="582" href="2018-02-09-leibniz-s-equality.html#582" class="Bound">x</a> <a id="584" class="Symbol">:</a> <a id="586" href="2018-02-09-leibniz-s-equality.html#570" class="Bound">A</a><a id="587" class="Symbol">)</a> <a id="589" class="Symbol">→</a> <a id="591" href="2018-02-09-leibniz-s-equality.html#Eq" class="Function">Eq</a> <a id="594" href="2018-02-09-leibniz-s-equality.html#582" class="Bound">x</a> <a id="596" href="2018-02-09-leibniz-s-equality.html#582" class="Bound">x</a>
<a id="598" href="2018-02-09-leibniz-s-equality.html#refl" class="Function">refl</a> <a id="603" class="Symbol">{</a><a id="604" href="2018-02-09-leibniz-s-equality.html#604" class="Bound">A</a><a id="605" class="Symbol">}</a> <a id="607" href="2018-02-09-leibniz-s-equality.html#607" class="Bound">x</a> <a id="609" class="Symbol">=</a> <a id="611" class="Symbol">λ</a> <a id="613" href="2018-02-09-leibniz-s-equality.html#613" class="Bound">P</a> <a id="615" href="2018-02-09-leibniz-s-equality.html#615" class="Bound">Px₁</a> <a id="619" class="Symbol">→</a> 

</pre>

* Transitivity

<pre class="Agda">

<a id="trans" href="2018-02-09-leibniz-s-equality.html#trans" class="Function">trans <a id="672" class="Symbol">:</a> <a id="674" class="Symbol">∀</a> <a id="676" class="Symbol">{</a><a id="677" href="2018-02-09-leibniz-s-equality.html#677" class="Bound">A</a> <a id="679" class="Symbol">:</a> <a id="681" class="PrimitiveType">Set</a><a id="684" class="Symbol">}</a> <a id="686" class="Symbol">→</a> <a id="688" class="Symbol">(</a><a id="689" href="2018-02-09-leibniz-s-equality.html#689" class="Bound">x</a> <a id="691" href="2018-02-09-leibniz-s-equality.html#691" class="Bound">y</a> <a id="693" href="2018-02-09-leibniz-s-equality.html#693" class="Bound">z</a> <a id="695" class="Symbol">:</a> <a id="697" href="2018-02-09-leibniz-s-equality.html#677" class="Bound">A</a><a id="698" class="Symbol">)</a> <a id="700" class="Symbol">→</a> <a id="702" href="2018-02-09-leibniz-s-equality.html#Eq" class="Function">Eq</a> <a id="705" href="2018-02-09-leibniz-s-equality.html#689" class="Bound">x</a> <a id="707" href="2018-02-09-leibniz-s-equality.html#691" class="Bound">y</a> <a id="709" class="Symbol">→</a> <a id="711" href="2018-02-09-leibniz-s-equality.html#Eq" class="Function">Eq</a> <a id="714" href="2018-02-09-leibniz-s-equality.html#691" class="Bound">y</a> <a id="716" href="2018-02-09-leibniz-s-equality.html#693" class="Bound">z</a> <a id="718" class="Symbol">→</a> <a id="720" href="2018-02-09-leibniz-s-equality.html#Eq" class="Function">Eq</a> <a id="723" href="2018-02-09-leibniz-s-equality.html#689" class="Bound">x</a> <a id="725" href="2018-02-09-leibniz-s-equality.html#693" class="Bound">z</a>
<a id="727" href="2018-02-09-leibniz-s-equality.html#trans" class="Function">trans</a> <a id="733" class="Symbol">{</a><a id="734" href="2018-02-09-leibniz-s-equality.html#734" class="Bound">A</a><a id="735" class="Symbol">}</a> <a id="737" href="2018-02-09-leibniz-s-equality.html#737" class="Bound">x</a> <a id="739" href="2018-02-09-leibniz-s-equality.html#739" class="Bound">y</a> <a id="741" href="2018-02-09-leibniz-s-equality.html#741" class="Bound">z</a> <a id="743" href="2018-02-09-leibniz-s-equality.html#743" class="Bound">x≡y</a> <a id="747" href="2018-02-09-leibniz-s-equality.html#747" class="Bound">P₁</a> <a id="750" href="2018-02-09-leibniz-s-equality.html#750" class="Bound">y≡z</a> <a id="754" href="2018-02-09-leibniz-s-equality.html#754" class="Bound">P₂</a> <a id="757" class="Symbol">=</a> <a id="759" href="2018-02-09-leibniz-s-equality.html#747" class="Bound">P₁</a> <a id="762" href="2018-02-09-leibniz-s-equality.html#750" class="Bound">y≡z</a> <a id="766" class="Symbol">(</a><a id="767" href="2018-02-09-leibniz-s-equality.html#743" class="Bound">x≡y</a> <a id="771" href="2018-02-09-leibniz-s-equality.html#750" class="Bound">y≡z</a> <a id="775" href="2018-02-09-leibniz-s-equality.html#754" class="Bound">P₂</a>

</pre>

* Symmetry

<pre class="Agda">

<a id="sym" href="2018-02-09-leibniz-s-equality.html#sym" class="Function">sym <a id="820" class="Symbol">:</a> <a id="822" class="Symbol">∀</a> <a id="824" class="Symbol">{</a><a id="825" href="2018-02-09-leibniz-s-equality.html#825" class="Bound">A</a> <a id="827" class="Symbol">:</a> <a id="829" class="PrimitiveType">Set</a><a id="832" class="Symbol">}</a> <a id="834" class="Symbol">→</a> <a id="836" class="Symbol">(</a><a id="837" href="2018-02-09-leibniz-s-equality.html#837" class="Bound">x</a> <a id="839" href="2018-02-09-leibniz-s-equality.html#839" class="Bound">y</a> <a id="841" class="Symbol">:</a> <a id="843" href="2018-02-09-leibniz-s-equality.html#825" class="Bound">A</a><a id="844" class="Symbol">)</a> <a id="846" class="Symbol">→</a> <a id="848" href="2018-02-09-leibniz-s-equality.html#Eq" class="Function">Eq</a> <a id="851" href="2018-02-09-leibniz-s-equality.html#837" class="Bound">x</a> <a id="853" href="2018-02-09-leibniz-s-equality.html#839" class="Bound">y</a> <a id="855" class="Symbol">→</a> <a id="857" href="2018-02-09-leibniz-s-equality.html#Eq" class="Function">Eq</a> <a id="860" href="2018-02-09-leibniz-s-equality.html#839" class="Bound">y</a> <a id="862" href="2018-02-09-leibniz-s-equality.html#837" class="Bound">x</a>
<a id="864" href="2018-02-09-leibniz-s-equality.html#sym" class="Function">sym</a> <a id="868" class="Symbol">{</a><a id="869" href="2018-02-09-leibniz-s-equality.html#869" class="Bound">A</a><a id="870" class="Symbol">}</a> <a id="872" href="2018-02-09-leibniz-s-equality.html#872" class="Bound">x</a> <a id="874" href="2018-02-09-leibniz-s-equality.html#874" class="Bound">y</a> <a id="876" href="2018-02-09-leibniz-s-equality.html#876" class="Bound">x≡y</a> <a id="880" href="2018-02-09-leibniz-s-equality.html#880" class="Bound">P</a> <a id="882" class="Symbol">=</a> <a id="884" href="2018-02-09-leibniz-s-equality.html#876" class="Bound">x≡y</a> <a id="888" href="2018-02-09-leibniz-s-equality.html#913" class="Function">p₁</a> <a id="891" class="Symbol">(λ</a> <a id="894" href="2018-02-09-leibniz-s-equality.html#894" class="Bound">z</a> <a id="896" class="Symbol">→</a> <a id="898" href="2018-02-09-leibniz-s-equality.html#894" class="Bound">z</a><a id="899" class="Symbol">)</a>
  <a id="903" class="Keyword">where</a>
    <a id="913" href="2018-02-09-leibniz-s-equality.html#913" class="Function">p₁</a> <a id="916" class="Symbol">:</a> <a id="918" href="2018-02-09-leibniz-s-equality.html#869" class="Bound">A</a> <a id="920" class="Symbol">→</a> <a id="922" class="PrimitiveType">Set</a>
    <a id="930" href="2018-02-09-leibniz-s-equality.html#913" class="Function">p₁</a> <a id="933" class="Symbol">=</a> <a id="935" class="Symbol">λ</a> <a id="937" href="2018-02-09-leibniz-s-equality.html#937" class="Bound">z</a> <a id="939" class="Symbol">→</a> <a id="941" href="2018-02-09-leibniz-s-equality.html#880" class="Bound">P</a> <a id="943" href="2018-02-09-leibniz-s-equality.html#937" class="Bound">z</a> <a id="945" class="Symbol">→</a> <a id="947" href="2018-02-09-leibniz-s-equality.html#880" class="Bound">P</a> 

</pre>

## Related

  > The principle of identity of indiscernibles states that two objects
  are identical if they have all the same properties.
  This is also known as “Leibniz’s Law”
  + [https://ncatlab.org/nlab/show/identity+of+indiscernibles](https://ncatlab.org/nlab/show/identity+of+indiscernibles)
