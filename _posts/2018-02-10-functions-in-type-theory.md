---
layout: "post"
title: "Function Type"
date: "2018-02-10 14:12"
---


In type theory we do not define function since this is an undefined concept also
refer to it as a primitive notion.
In contrast, we have in set theory that a function is
a correspondance between two sets, a **relation** between the domain
and the codomain.

In type theory, we have a function type for the functions
also called *maps*. The function type is introduced as usual with other types:

+ name of the type or symbol: (_→_)

+ formation rule:

  Γ ⊢ A  and Γ ⊢ B then Γ ⊢ f : A → B

+ introduction rule (λ-abstraction):

  Γ , x : A ⊢ t : B then Γ ⊢ λ (x : A) . t : A → B

+ elimination rule:

  Γ ⊢ λ (x : A) . t : A → B and Γ ⊢ y : A then Γ ⊢ (λ (x : A) . t) y : B

+ computation rule (also called β-reduction or β-conversion):

  Γ ⊢ (λ (x : A) . t) y : B then Γ ⊢ t[ x := y] : B

  We use the last notation `t[x := y]` to say that replace every occurrance of
  x in the term t by y.

+ simplication rule (also called η-conversion):

  Γ ⊢ λ (x : A) . f x : A → B then Γ ⊢ f : A → B

  This conversion is also given by a definitional equality:

<pre class="Agda">{% raw %}<a id="1143" class="Keyword">open</a> <a id="1148" class="Keyword">import</a> <a id="1155" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="1193" class="Keyword">using</a> <a id="1199" class="Symbol">(</a><a id="1200" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_" class="Datatype Operator">_≡_</a><a id="1203" class="Symbol">;</a> <a id="1205" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_.refl" class="InductiveConstructor">refl</a><a id="1209" class="Symbol">)</a>

<a id="1212" class="Keyword">postulate</a>
  <a id="A" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="B" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#B" class="Postulate">B</a> <a id="1228" class="Symbol">:</a> <a id="1230" class="PrimitiveType">Set</a>
  <a id="t" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#t" class="Postulate">t</a> <a id="1238" class="Symbol">:</a> <a id="1240" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#B" class="Postulate">B</a>

<a id="f" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f" class="Function">f</a> <a id="1245" class="Symbol">:</a> <a id="1247" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1249" class="Symbol">→</a> <a id="1251" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#B" class="Postulate">B</a>
<a id="1253" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f" class="Function">f</a> <a id="1255" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1255" class="Bound">x</a> <a id="1257" class="Symbol">=</a> <a id="1259" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#t" class="Postulate">t</a>

<a id="f₁" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f%E2%82%81" class="Function">f₁</a> <a id="1265" class="Symbol">:</a> <a id="1267" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1269" class="Symbol">→</a> <a id="1271" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#B" class="Postulate">B</a>
<a id="1273" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f%E2%82%81" class="Function">f₁</a> <a id="1276" class="Symbol">=</a> <a id="1278" class="Symbol">λ</a> <a id="1280" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1280" class="Bound">x</a> <a id="1282" class="Symbol">→</a> <a id="1284" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f" class="Function">f</a> <a id="1286" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1280" class="Bound">x</a>

<a id="f≡f₁" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f%E2%89%A1f%E2%82%81" class="Function">f≡f₁</a> <a id="1294" class="Symbol">:</a> <a id="1296" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f" class="Function">f</a> <a id="1298" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_" class="Datatype Operator">≡</a> <a id="1300" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f%E2%82%81" class="Function">f₁</a>
<a id="1303" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f%E2%89%A1f%E2%82%81" class="Function">f≡f₁</a> <a id="1308" class="Symbol">=</a> <a id="1310" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_.refl" class="InductiveConstructor">refl</a>{% endraw %}</pre>

Related:

+ Two functions are **judgementally* equal if they are equal by α-conversion,
that is, if after renaming the variable names they are definitionally equal.

<pre class="Agda">{% raw %}<a id="g" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#g" class="Function">g</a> <a id="1508" class="Symbol">:</a>  <a id="1511" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1513" class="Symbol">→</a> <a id="1515" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1517" class="Symbol">→</a> <a id="1519" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a>
<a id="1521" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#g" class="Function">g</a> <a id="1523" class="Symbol">=</a> <a id="1525" class="Symbol">λ</a> <a id="1527" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1527" class="Bound">x</a> <a id="1529" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1529" class="Bound">y</a> <a id="1531" class="Symbol">→</a> <a id="1533" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1529" class="Bound">y</a>

<a id="h" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#h" class="Function">h</a> <a id="1538" class="Symbol">:</a> <a id="1540" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1542" class="Symbol">→</a> <a id="1544" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1546" class="Symbol">→</a> <a id="1548" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a>
<a id="1550" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#h" class="Function">h</a> <a id="1552" class="Symbol">=</a>  <a id="1555" class="Symbol">λ</a> <a id="1557" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1557" class="Bound">w</a> <a id="1559" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1559" class="Bound">z</a> <a id="1561" class="Symbol">→</a> <a id="1563" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1559" class="Bound">z</a>{% endraw %}</pre>

But g and h functions producing the same, then if que sustitute in h, w by x,
and z by y, we get the definition of g, so at the end, g and h are **judgementally* equal.

<pre class="Agda">{% raw %}<a id="g≡h" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#g%E2%89%A1h" class="Function">g≡h</a> <a id="1764" class="Symbol">:</a> <a id="1766" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#g" class="Function">g</a> <a id="1768" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_" class="Datatype Operator">≡</a> <a id="1770" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#h" class="Function">h</a>
<a id="1772" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#g%E2%89%A1h" class="Function">g≡h</a> <a id="1776" class="Symbol">=</a> <a id="1778" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_.refl" class="InductiveConstructor">refl</a>{% endraw %}</pre>

+ Currying.
