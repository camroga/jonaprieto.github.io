---
layout: "post"
title: "functions in type theory"
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

<pre class="Agda">{% raw %}<a id="1154" class="Keyword">open</a> <a id="1159" class="Keyword">import</a> <a id="1166" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="1204" class="Keyword">using</a> <a id="1210" class="Symbol">(</a><a id="1211" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_" class="Datatype Operator">_≡_</a><a id="1214" class="Symbol">;</a> <a id="1216" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_.refl" class="InductiveConstructor">refl</a><a id="1220" class="Symbol">)</a>

<a id="1223" class="Keyword">postulate</a>
  <a id="A" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="B" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#B" class="Postulate">B</a> <a id="1239" class="Symbol">:</a> <a id="1241" class="PrimitiveType">Set</a>
  <a id="t" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#t" class="Postulate">t</a> <a id="1249" class="Symbol">:</a> <a id="1251" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#B" class="Postulate">B</a>

<a id="f" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f" class="Function">f</a> <a id="1256" class="Symbol">:</a> <a id="1258" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1260" class="Symbol">→</a> <a id="1262" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#B" class="Postulate">B</a>
<a id="1264" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f" class="Function">f</a> <a id="1266" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1266" class="Bound">x</a> <a id="1268" class="Symbol">=</a> <a id="1270" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#t" class="Postulate">t</a>

<a id="f₁" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f%E2%82%81" class="Function">f₁</a> <a id="1276" class="Symbol">:</a> <a id="1278" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1280" class="Symbol">→</a> <a id="1282" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#B" class="Postulate">B</a>
<a id="1284" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f%E2%82%81" class="Function">f₁</a> <a id="1287" class="Symbol">=</a> <a id="1289" class="Symbol">λ</a> <a id="1291" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1291" class="Bound">x</a> <a id="1293" class="Symbol">→</a> <a id="1295" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f" class="Function">f</a> <a id="1297" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1291" class="Bound">x</a>

<a id="f≡f₁" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f%E2%89%A1f%E2%82%81" class="Function">f≡f₁</a> <a id="1305" class="Symbol">:</a> <a id="1307" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f" class="Function">f</a> <a id="1309" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_" class="Datatype Operator">≡</a> <a id="1311" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f%E2%82%81" class="Function">f₁</a>
<a id="1314" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f%E2%89%A1f%E2%82%81" class="Function">f≡f₁</a> <a id="1319" class="Symbol">=</a> <a id="1321" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_.refl" class="InductiveConstructor">refl</a>{% endraw %}</pre>

Related:

+ Two functions are **judgementally* equal if they are equal by α-conversion,
that is, if after renaming the variable names they are definitionally equal.

<pre class="Agda">{% raw %}<a id="g" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#g" class="Function">g</a> <a id="1519" class="Symbol">:</a>  <a id="1522" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1524" class="Symbol">→</a> <a id="1526" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1528" class="Symbol">→</a> <a id="1530" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a>
<a id="1532" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#g" class="Function">g</a> <a id="1534" class="Symbol">=</a> <a id="1536" class="Symbol">λ</a> <a id="1538" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1538" class="Bound">x</a> <a id="1540" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1540" class="Bound">y</a> <a id="1542" class="Symbol">→</a> <a id="1544" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1540" class="Bound">y</a>

<a id="h" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#h" class="Function">h</a> <a id="1549" class="Symbol">:</a> <a id="1551" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1553" class="Symbol">→</a> <a id="1555" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1557" class="Symbol">→</a> <a id="1559" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a>
<a id="1561" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#h" class="Function">h</a> <a id="1563" class="Symbol">=</a>  <a id="1566" class="Symbol">λ</a> <a id="1568" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1568" class="Bound">w</a> <a id="1570" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1570" class="Bound">z</a> <a id="1572" class="Symbol">→</a> <a id="1574" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1570" class="Bound">z</a>{% endraw %}</pre>

But g and h functions producing the same, then if que sustitute in h, w by x,
and z by y, we get the definition of g, so at the end, g and h are **judgementally* equal.

<pre class="Agda">{% raw %}<a id="g≡h" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#g%E2%89%A1h" class="Function">g≡h</a> <a id="1775" class="Symbol">:</a> <a id="1777" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#g" class="Function">g</a> <a id="1779" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_" class="Datatype Operator">≡</a> <a id="1781" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#h" class="Function">h</a>
<a id="1783" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#g%E2%89%A1h" class="Function">g≡h</a> <a id="1787" class="Symbol">=</a> <a id="1789" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_.refl" class="InductiveConstructor">refl</a>{% endraw %}</pre>

+ Currying.
