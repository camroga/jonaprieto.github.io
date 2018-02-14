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

+ Two functions are *judgemental* equal if they are equal by α-conversion,
that is, if after renaming the variable names they are definitionally equal.

<pre class="Agda">{% raw %}<a id="g" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#g" class="Function">g</a> <a id="1499" class="Symbol">:</a>  <a id="1502" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1504" class="Symbol">→</a> <a id="1506" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1508" class="Symbol">→</a> <a id="1510" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a>
<a id="1512" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#g" class="Function">g</a> <a id="1514" class="Symbol">=</a> <a id="1516" class="Symbol">λ</a> <a id="1518" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1518" class="Bound">x</a> <a id="1520" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1520" class="Bound">y</a> <a id="1522" class="Symbol">→</a> <a id="1524" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1520" class="Bound">y</a>

<a id="h" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#h" class="Function">h</a> <a id="1529" class="Symbol">:</a> <a id="1531" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1533" class="Symbol">→</a> <a id="1535" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a> <a id="1537" class="Symbol">→</a> <a id="1539" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#A" class="Postulate">A</a>
<a id="1541" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#h" class="Function">h</a> <a id="1543" class="Symbol">=</a>  <a id="1546" class="Symbol">λ</a> <a id="1548" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1548" class="Bound">w</a> <a id="1550" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1550" class="Bound">z</a> <a id="1552" class="Symbol">→</a> <a id="1554" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#1550" class="Bound">z</a>{% endraw %}</pre>

Both g and h function produce the same result, then if que sustitute in h, w by
x, and z by y, we get the definition of g, so at the end, g and h are
*judgemental* equal.

<pre class="Agda">{% raw %}<a id="g≡h" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#g%E2%89%A1h" class="Function">g≡h</a> <a id="1757" class="Symbol">:</a> <a id="1759" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#g" class="Function">g</a> <a id="1761" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_" class="Datatype Operator">≡</a> <a id="1763" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#h" class="Function">h</a>
<a id="1765" href="{% endraw %}{% link _posts/2018-02-10-functions-in-type-theory.md %}{% raw %}#g%E2%89%A1h" class="Function">g≡h</a> <a id="1769" class="Symbol">=</a> <a id="1771" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_.refl" class="InductiveConstructor">refl</a>{% endraw %}</pre>

+ Currying.
  ...
