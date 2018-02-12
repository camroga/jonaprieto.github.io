---
layout: "post"
title: "Induction on Natural Numbers"
date: "2018-02-12 13:25"
---

We define the natural numbers by following its
algorithmic or finite definition, that is, using a
rule to construct the zero and a successor for any number.

<pre class="Agda">{% raw %}<a id="259" class="Keyword">data</a> <a id="ℕ" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95" class="Datatype">ℕ</a> <a id="266" class="Symbol">:</a> <a id="268" class="PrimitiveType">Set</a> <a id="272" class="Keyword">where</a>
  <a id="ℕ.zero" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95.zero" class="InductiveConstructor">zero</a> <a id="285" class="Symbol">:</a> <a id="287" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95" class="Datatype">ℕ</a>
  <a id="ℕ.suc" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95.suc" class="InductiveConstructor">suc</a>  <a id="296" class="Symbol">:</a> <a id="298" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95" class="Datatype">ℕ</a> <a id="300" class="Symbol">→</a> <a id="302" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95" class="Datatype">ℕ</a>{% endraw %}</pre>

* Remark: to be more comfortable with the usual notation let use
the following pragma:

<pre class="Agda">{% raw %}<a id="417" class="Symbol">{-#</a> <a id="421" class="Keyword">BUILTIN</a> NATURAL <a id="437" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95" class="Datatype">ℕ</a> <a id="439" class="Symbol">#-}</a>{% endraw %}</pre>

Then, we can now write numbers like usual:

<pre class="Agda">{% raw %}<a id="bigNumber" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#bigNumber" class="Function">bigNumber</a> <a id="522" class="Symbol">:</a> <a id="524" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95" class="Datatype">ℕ</a>
<a id="526" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#bigNumber" class="Function">bigNumber</a> <a id="536" class="Symbol">=</a> <a id="538" class="Number">123456789</a>{% endraw %}</pre>

#### Recursion

Now let us define the principle of primitive recursion for natural numbers:

```agda
recℕ : Π(C : 𝒰) C → (ℕ → C → C) → ℕ → C
```
recℕ is the so-called *recursor* for natural numbers. In Agda,

<pre class="Agda">{% raw %}<a id="recℕ" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#rec%E2%84%95" class="Function">recℕ</a>
  <a id="789" class="Symbol">:</a> <a id="791" class="Symbol">(</a><a id="792" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#792" class="Bound">C</a> <a id="794" class="Symbol">:</a> <a id="796" class="PrimitiveType">Set</a><a id="799" class="Symbol">)</a>    <a id="804" class="Comment">-- type for the outcome</a>
  <a id="830" class="Symbol">→</a> <a id="832" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#792" class="Bound">C</a>            <a id="845" class="Comment">-- base case</a>
  <a id="860" class="Symbol">→</a> <a id="862" class="Symbol">(</a><a id="863" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95" class="Datatype">ℕ</a> <a id="865" class="Symbol">→</a> <a id="867" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#792" class="Bound">C</a> <a id="869" class="Symbol">→</a> <a id="871" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#792" class="Bound">C</a><a id="872" class="Symbol">)</a>  <a id="875" class="Comment">-- recursion call</a>
  <a id="895" class="Symbol">→</a> <a id="897" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95" class="Datatype">ℕ</a>            <a id="910" class="Comment">-- the number in the input</a>
  <a id="939" class="Symbol">→</a> <a id="941" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#792" class="Bound">C</a>            <a id="954" class="Comment">-- outcome</a>
<a id="965" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#rec%E2%84%95" class="Function">recℕ</a> <a id="970" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#970" class="Bound">C</a> <a id="972" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#972" class="Bound">c₀</a> <a id="975" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#975" class="Bound">cₛ</a> <a id="978" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95.zero" class="InductiveConstructor">zero</a> <a id="983" class="Symbol">=</a> <a id="985" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#972" class="Bound">c₀</a>
<a id="988" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#rec%E2%84%95" class="Function">recℕ</a> <a id="993" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#993" class="Bound">C</a> <a id="995" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#995" class="Bound">c₀</a> <a id="998" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#998" class="Bound">cₛ</a> <a id="1001" class="Symbol">(</a><a id="1002" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95.suc" class="InductiveConstructor">suc</a> <a id="1006" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#1006" class="Bound">n</a><a id="1007" class="Symbol">)</a> <a id="1009" class="Symbol">=</a> <a id="1011" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#998" class="Bound">cₛ</a> <a id="1014" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#1006" class="Bound">n</a> <a id="1016" class="Symbol">(</a><a id="1017" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#rec%E2%84%95" class="Function">recℕ</a> <a id="1022" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#993" class="Bound">C</a> <a id="1024" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#995" class="Bound">c₀</a> <a id="1027" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#998" class="Bound">cₛ</a> <a id="1030" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#1006" class="Bound">n</a><a id="1031" class="Symbol">)</a>{% endraw %}</pre>

Now, we can define some common functions using this recursor to see how it works.

+ Adding two numbers.

<pre class="Agda">{% raw %}<a id="add" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#add" class="Function">add</a> <a id="1168" class="Symbol">:</a> <a id="1170" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95" class="Datatype">ℕ</a> <a id="1172" class="Symbol">→</a> <a id="1174" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95" class="Datatype">ℕ</a> <a id="1176" class="Symbol">→</a> <a id="1178" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95" class="Datatype">ℕ</a>
<a id="1180" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#add" class="Function">add</a> <a id="1184" class="Symbol">=</a> <a id="1186" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#rec%E2%84%95" class="Function">recℕ</a> <a id="1191" class="Symbol">(</a><a id="1192" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95" class="Datatype">ℕ</a> <a id="1194" class="Symbol">→</a> <a id="1196" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95" class="Datatype">ℕ</a><a id="1197" class="Symbol">)</a> <a id="1199" class="Symbol">(λ</a> <a id="1202" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#1202" class="Bound">m</a> <a id="1204" class="Symbol">→</a> <a id="1206" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#1202" class="Bound">m</a><a id="1207" class="Symbol">)</a> <a id="1209" class="Symbol">(λ</a> <a id="1212" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#1212" class="Bound">n</a> <a id="1214" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#1214" class="Bound">g</a> <a id="1216" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#1216" class="Bound">m</a> <a id="1218" class="Symbol">→</a> <a id="1220" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95.suc" class="InductiveConstructor">suc</a> <a id="1224" class="Symbol">(</a><a id="1225" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#1214" class="Bound">g</a> <a id="1227" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#1216" class="Bound">m</a><a id="1228" class="Symbol">))</a>{% endraw %}</pre>

Instead of the usual add function:

<pre class="Agda">{% raw %}<a id="add₂" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#add%E2%82%82" class="Function">add₂</a> <a id="1297" class="Symbol">:</a> <a id="1299" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95" class="Datatype">ℕ</a> <a id="1301" class="Symbol">→</a> <a id="1303" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95" class="Datatype">ℕ</a> <a id="1305" class="Symbol">→</a> <a id="1307" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95" class="Datatype">ℕ</a>
<a id="1309" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#add%E2%82%82" class="Function">add₂</a> <a id="1314" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95.zero" class="InductiveConstructor">zero</a> <a id="1319" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#1319" class="Bound">m</a> <a id="1321" class="Symbol">=</a> <a id="1323" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#1319" class="Bound">m</a>
<a id="1325" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#add%E2%82%82" class="Function">add₂</a> <a id="1330" class="Symbol">(</a><a id="1331" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95.suc" class="InductiveConstructor">suc</a> <a id="1335" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#1335" class="Bound">n</a><a id="1336" class="Symbol">)</a> <a id="1338" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#1338" class="Bound">m</a> <a id="1340" class="Symbol">=</a> <a id="1342" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95.suc" class="InductiveConstructor">suc</a> <a id="1346" class="Symbol">(</a><a id="1347" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#add%E2%82%82" class="Function">add₂</a> <a id="1352" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#1335" class="Bound">n</a> <a id="1354" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#1338" class="Bound">m</a><a id="1355" class="Symbol">)</a>{% endraw %}</pre>

+ Doubling a number.

<pre class="Agda">{% raw %}<a id="double" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#double" class="Function">double</a> <a id="1411" class="Symbol">:</a> <a id="1413" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95" class="Datatype">ℕ</a> <a id="1415" class="Symbol">→</a> <a id="1417" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95" class="Datatype">ℕ</a>
<a id="1419" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#double" class="Function">double</a> <a id="1426" class="Symbol">=</a> <a id="1428" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#rec%E2%84%95" class="Function">recℕ</a> <a id="1433" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95" class="Datatype">ℕ</a> <a id="1435" class="Number">0</a> <a id="1437" class="Symbol">(λ</a> <a id="1440" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#1440" class="Bound">n</a> <a id="1442" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#1442" class="Bound">y</a> <a id="1444" class="Symbol">→</a> <a id="1446" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95.suc" class="InductiveConstructor">suc</a> <a id="1450" class="Symbol">(</a><a id="1451" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95.suc" class="InductiveConstructor">suc</a> <a id="1455" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#1442" class="Bound">y</a><a id="1456" class="Symbol">))</a>{% endraw %}</pre>

Instead of

<pre class="Agda">{% raw %}<a id="double₂" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#double%E2%82%82" class="Function">double₂</a> <a id="1504" class="Symbol">:</a> <a id="1506" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95" class="Datatype">ℕ</a> <a id="1508" class="Symbol">→</a> <a id="1510" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95" class="Datatype">ℕ</a>
<a id="1512" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#double%E2%82%82" class="Function">double₂</a> <a id="1520" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95.zero" class="InductiveConstructor">zero</a> <a id="1525" class="Symbol">=</a> <a id="1527" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95.zero" class="InductiveConstructor">zero</a>
<a id="1532" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#double%E2%82%82" class="CatchallClause Function">double₂</a><a id="1539" class="CatchallClause"> </a><a id="1540" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#1540" class="CatchallClause Bound">n</a>    <a id="1545" class="Symbol">=</a> <a id="1547" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95.suc" class="InductiveConstructor">suc</a> <a id="1551" class="Symbol">(</a><a id="1552" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#%E2%84%95.suc" class="InductiveConstructor">suc</a> <a id="1556" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#1540" class="Bound">n</a><a id="1557" class="Symbol">)</a>{% endraw %}</pre>

Before unpacking these definition, let test some examples. To this purpose we
import the equality definition type (_≡_) and its introduction rule (refl).

<pre class="Agda">{% raw %}<a id="1739" class="Keyword">open</a> <a id="1744" class="Keyword">import</a> <a id="1751" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="1789" class="Keyword">using</a> <a id="1795" class="Symbol">(</a><a id="1796" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_.refl" class="InductiveConstructor">refl</a><a id="1800" class="Symbol">;</a> <a id="1802" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_" class="Datatype Operator">_≡_</a><a id="1805" class="Symbol">)</a>{% endraw %}</pre>

Then testing the definitional equality for some sums, we certaintly start to
believe.

<pre class="Agda">{% raw %}<a id="2+5" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#2%2B5" class="Function">2+5</a> <a id="1923" class="Symbol">:</a> <a id="1925" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#add" class="Function">add</a> <a id="1929" class="Number">2</a> <a id="1931" class="Number">5</a> <a id="1933" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_" class="Datatype Operator">≡</a> <a id="1935" class="Number">7</a>
<a id="1937" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#2%2B5" class="Function">2+5</a> <a id="1941" class="Symbol">=</a> <a id="1943" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_.refl" class="InductiveConstructor">refl</a>

<a id="25+25" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#25%2B25" class="Function">25+25</a> <a id="1955" class="Symbol">:</a> <a id="1957" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#add" class="Function">add</a> <a id="1961" class="Number">25</a> <a id="1964" class="Number">25</a> <a id="1967" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_" class="Datatype Operator">≡</a> <a id="1969" class="Number">50</a>
<a id="1972" href="{% endraw %}{% link _posts/2018-02-12-induction-on-natural-numbers.md %}{% raw %}#25%2B25" class="Function">25+25</a> <a id="1978" class="Symbol">=</a> <a id="1980" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#_%E2%89%A1_.refl" class="InductiveConstructor">refl</a>{% endraw %}</pre>

In the definition of `add` we have the following:

  + By [curryfication](https://en.wikipedia.org/wiki/Currying), the `add` function can
  be seen as a function that returns a function. How is this possible? just fix
  the first argument, and then you have an unary function, and that's why C : ℕ → ℕ.

  ```agda
  add : ℕ → (ℕ → ℕ)
  ```

  + When the first argument in the sum is zero, we just have to return the
  identity function, that's why c₀ is (λ m → m).

  ```agda
  add zero m = m
  ```

  + To understand the last argument, ((λ n g m → suc (g m))), remember that
  this is indeed cₛ : ℕ → C → C, and by the equation of recℕ:

  ```
  recℕ C c₀ cₛ (suc n) = cₛ n (recℕ C c₀ cₛ n)
  ```

  Question: why the n variable is not present in the returned value?


#### Induction
