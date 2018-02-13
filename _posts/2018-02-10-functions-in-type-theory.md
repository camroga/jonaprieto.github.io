---
title: "Function Type"
layout: "post"
date: "2018-02-10"
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

<pre class="Agda">{% raw %}<a id="1137" class="Keyword">open</a> <a id="1142" class="Keyword">import</a> <a id="1149" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="1187" class="Keyword">using</a> <a id="1193" class="Symbol">(</a><a id="1194" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_" class="Datatype Operator">_≡_</a><a id="1197" class="Symbol">;</a> <a id="1199" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_.refl" class="InductiveConstructor">refl</a><a id="1203" class="Symbol">)</a>

<a id="1206" class="Keyword">postulate</a>
  <a id="A" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="B" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#B" class="Postulate">B</a> <a id="1222" class="Symbol">:</a> <a id="1224" class="PrimitiveType">Set</a>
  <a id="t" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#t" class="Postulate">t</a> <a id="1232" class="Symbol">:</a> <a id="1234" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#B" class="Postulate">B</a>

<a id="f" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f" class="Function">f</a> <a id="1239" class="Symbol">:</a> <a id="1241" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1243" class="Symbol">→</a> <a id="1245" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#B" class="Postulate">B</a>
<a id="1247" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f" class="Function">f</a> <a id="1249" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1249" class="Bound">x</a> <a id="1251" class="Symbol">=</a> <a id="1253" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#t" class="Postulate">t</a>

<a id="f₁" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f%E2%82%81" class="Function">f₁</a> <a id="1259" class="Symbol">:</a> <a id="1261" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1263" class="Symbol">→</a> <a id="1265" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#B" class="Postulate">B</a>
<a id="1267" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f%E2%82%81" class="Function">f₁</a> <a id="1270" class="Symbol">=</a> <a id="1272" class="Symbol">λ</a> <a id="1274" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1274" class="Bound">x</a> <a id="1276" class="Symbol">→</a> <a id="1278" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f" class="Function">f</a> <a id="1280" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1274" class="Bound">x</a>

<a id="f≡f₁" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f%E2%89%A1f%E2%82%81" class="Function">f≡f₁</a> <a id="1288" class="Symbol">:</a> <a id="1290" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f" class="Function">f</a> <a id="1292" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_" class="Datatype Operator">≡</a> <a id="1294" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f%E2%82%81" class="Function">f₁</a>
<a id="1297" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#f%E2%89%A1f%E2%82%81" class="Function">f≡f₁</a> <a id="1302" class="Symbol">=</a> <a id="1304" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_.refl" class="InductiveConstructor">refl</a>{% endraw %}</pre>

Related:

+ Two functions are **judgementally* equal if they are equal by α-conversion,
that is, if after renaming the variable names they are definitionally equal.

<pre class="Agda">{% raw %}<a id="g" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#g" class="Function">g</a> <a id="1502" class="Symbol">:</a>  <a id="1505" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1507" class="Symbol">→</a> <a id="1509" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1511" class="Symbol">→</a> <a id="1513" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a>
<a id="1515" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#g" class="Function">g</a> <a id="1517" class="Symbol">=</a> <a id="1519" class="Symbol">λ</a> <a id="1521" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1521" class="Bound">x</a> <a id="1523" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1523" class="Bound">y</a> <a id="1525" class="Symbol">→</a> <a id="1527" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1523" class="Bound">y</a>

<a id="h" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#h" class="Function">h</a> <a id="1532" class="Symbol">:</a> <a id="1534" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1536" class="Symbol">→</a> <a id="1538" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1540" class="Symbol">→</a> <a id="1542" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a>
<a id="1544" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#h" class="Function">h</a> <a id="1546" class="Symbol">=</a>  <a id="1549" class="Symbol">λ</a> <a id="1551" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1551" class="Bound">w</a> <a id="1553" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1553" class="Bound">z</a> <a id="1555" class="Symbol">→</a> <a id="1557" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1553" class="Bound">z</a>{% endraw %}</pre>

But g and h functions producing the same, then if que sustitute in h, w by x,
and z by y, we get the definition of g, so at the end, g and h are **judgementally* equal.

<pre class="Agda">{% raw %}<a id="g≡h" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#g%E2%89%A1h" class="Function">g≡h</a> <a id="1758" class="Symbol">:</a> <a id="1760" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#g" class="Function">g</a> <a id="1762" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_" class="Datatype Operator">≡</a> <a id="1764" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#h" class="Function">h</a>
<a id="1766" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#g%E2%89%A1h" class="Function">g≡h</a> <a id="1770" class="Symbol">=</a> <a id="1772" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_.refl" class="InductiveConstructor">refl</a>{% endraw %}</pre>

+ Currying.
