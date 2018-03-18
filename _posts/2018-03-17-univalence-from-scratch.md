---
layout: "post"
title: "Univalence From Scratch"
date: "2018-03-17"
categories: type-theory
---

This is my reading of the paper:

> M.H. Escardo. [*A self-contained, brief and complete formulation of Voevodsky's
Univalence Axiom*](https://arxiv.org/abs/1803.02294), March 2018, arXiv:1803.02294.

For the original version of the Agda code, review the link of the paper.
The following type-checks in Agda 2.5.3.

<pre class="Agda">{% raw %}<a id="430" class="Symbol">{-#</a> <a id="434" class="Keyword">OPTIONS</a> <a id="442" class="Option">--without-K</a> <a id="454" class="Symbol">#-}</a>{% endraw %}</pre>

Basic imports:

<pre class="Agda">{% raw %}<a id="499" class="Keyword">open</a> <a id="504" class="Keyword">import</a> <a id="511" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>
  <a id="528" class="Keyword">using</a>    <a id="537" class="Symbol">(</a><a id="538" href="Agda.Primitive.html#_%E2%8A%94_" class="Primitive Operator">_⊔_</a><a id="541" class="Symbol">)</a>
  <a id="545" class="Keyword">renaming</a> <a id="554" class="Symbol">(</a><a id="555" href="Agda.Primitive.html#lzero" class="Primitive">lzero</a> <a id="561" class="Symbol">to</a> <a id="564" href="Agda.Primitive.html#lzero" class="Primitive">U₀</a> <a id="567" class="Symbol">;</a> <a id="569" href="Agda.Primitive.html#lsuc" class="Primitive">lsuc</a> <a id="574" class="Symbol">to</a> <a id="577" href="Agda.Primitive.html#lsuc" class="Primitive">_′</a> <a id="580" class="Symbol">;</a> <a id="582" href="Agda.Primitive.html#Level" class="Postulate">Level</a> <a id="588" class="Symbol">to</a> <a id="591" href="Agda.Primitive.html#Level" class="Postulate">Universe</a><a id="599" class="Symbol">)</a>{% endraw %}</pre>

### Σ-type and Identity type

<pre class="Agda">{% raw %}<a id="656" class="Keyword">data</a> <a id="Σ" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#%CE%A3" class="Datatype">Σ</a> <a id="663" class="Symbol">{</a><a id="664" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#664" class="Bound">U</a> <a id="666" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#666" class="Bound">V</a> <a id="668" class="Symbol">:</a> <a id="670" href="Agda.Primitive.html#Universe" class="Postulate">Universe</a><a id="678" class="Symbol">}</a>
       <a id="687" class="Symbol">{</a><a id="688" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#688" class="Bound">X</a> <a id="690" class="Symbol">:</a> <a id="692" class="PrimitiveType">Set</a> <a id="696" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#664" class="Bound">U</a><a id="697" class="Symbol">}</a>
       <a id="706" class="Symbol">(</a><a id="707" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#707" class="Bound">Y</a> <a id="709" class="Symbol">:</a> <a id="711" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#688" class="Bound">X</a> <a id="713" class="Symbol">→</a> <a id="715" class="PrimitiveType">Set</a> <a id="719" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#666" class="Bound">V</a><a id="720" class="Symbol">)</a>
      <a id="728" class="Symbol">:</a> <a id="730" class="PrimitiveType">Set</a> <a id="734" class="Symbol">(</a><a id="735" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#664" class="Bound">U</a> <a id="737" href="Agda.Primitive.html#_%E2%8A%94_" class="Primitive Operator">⊔</a> <a id="739" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#666" class="Bound">V</a><a id="740" class="Symbol">)</a> <a id="742" class="Keyword">where</a>
  <a id="Σ._,_" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#%CE%A3._%2C_" class="InductiveConstructor Operator">_,_</a> <a id="754" class="Symbol">:</a> <a id="756" class="Symbol">(</a><a id="757" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#757" class="Bound">x</a> <a id="759" class="Symbol">:</a> <a id="761" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#688" class="Bound">X</a><a id="762" class="Symbol">)</a> <a id="764" class="Symbol">(</a><a id="765" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#765" class="Bound">y</a> <a id="767" class="Symbol">:</a> <a id="769" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#707" class="Bound">Y</a> <a id="771" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#757" class="Bound">x</a><a id="772" class="Symbol">)</a> <a id="774" class="Symbol">→</a> <a id="776" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#%CE%A3" class="Datatype">Σ</a> <a id="778" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#707" class="Bound">Y</a>

<a id="781" class="Keyword">data</a> <a id="Id" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="789" class="Symbol">{</a><a id="790" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#790" class="Bound">U</a> <a id="792" class="Symbol">:</a> <a id="794" href="Agda.Primitive.html#Universe" class="Postulate">Universe</a><a id="802" class="Symbol">}</a> <a id="804" class="Symbol">{</a><a id="805" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#805" class="Bound">X</a> <a id="807" class="Symbol">:</a> <a id="809" class="PrimitiveType">Set</a> <a id="813" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#790" class="Bound">U</a><a id="814" class="Symbol">}</a> <a id="816" class="Symbol">:</a> <a id="818" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#805" class="Bound">X</a> <a id="820" class="Symbol">→</a> <a id="822" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#805" class="Bound">X</a> <a id="824" class="Symbol">→</a> <a id="826" class="PrimitiveType">Set</a> <a id="830" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#790" class="Bound">U</a>  <a id="833" class="Keyword">where</a>
  <a id="Id.refl" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id.refl" class="InductiveConstructor">refl</a> <a id="846" class="Symbol">:</a> <a id="848" class="Symbol">(</a><a id="849" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#849" class="Bound">x</a> <a id="851" class="Symbol">:</a> <a id="853" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#805" class="Bound">X</a><a id="854" class="Symbol">)</a> <a id="856" class="Symbol">→</a> <a id="858" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="861" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#849" class="Bound">x</a> <a id="863" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#849" class="Bound">x</a>{% endraw %}</pre>

### J eliminator

<pre class="Agda">{% raw %}<a id="J" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#J" class="Function">J</a> <a id="910" class="Symbol">:</a> <a id="912" class="Symbol">{</a><a id="913" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#913" class="Bound">U</a> <a id="915" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#915" class="Bound">V</a> <a id="917" class="Symbol">:</a> <a id="919" href="Agda.Primitive.html#Universe" class="Postulate">Universe</a><a id="927" class="Symbol">}</a> <a id="929" class="Symbol">{</a><a id="930" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#930" class="Bound">X</a> <a id="932" class="Symbol">:</a> <a id="934" class="PrimitiveType">Set</a> <a id="938" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#913" class="Bound">U</a><a id="939" class="Symbol">}</a>
  <a id="943" class="Symbol">→</a> <a id="945" class="Symbol">(</a><a id="946" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#946" class="Bound">A</a> <a id="948" class="Symbol">:</a> <a id="950" class="Symbol">(</a><a id="951" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#951" class="Bound">x</a> <a id="953" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#953" class="Bound">y</a> <a id="955" class="Symbol">:</a> <a id="957" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#930" class="Bound">X</a><a id="958" class="Symbol">)</a> <a id="960" class="Symbol">→</a> <a id="962" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="965" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#951" class="Bound">x</a> <a id="967" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#953" class="Bound">y</a> <a id="969" class="Symbol">→</a> <a id="971" class="PrimitiveType">Set</a> <a id="975" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#915" class="Bound">V</a><a id="976" class="Symbol">)</a>  <a id="979" class="Comment">-- type former</a>
  <a id="996" class="Symbol">→</a> <a id="998" class="Symbol">((</a><a id="1000" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1000" class="Bound">x</a> <a id="1002" class="Symbol">:</a> <a id="1004" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#930" class="Bound">X</a><a id="1005" class="Symbol">)</a> <a id="1007" class="Symbol">→</a> <a id="1009" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#946" class="Bound">A</a> <a id="1011" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1000" class="Bound">x</a> <a id="1013" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1000" class="Bound">x</a> <a id="1015" class="Symbol">(</a><a id="1016" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id.refl" class="InductiveConstructor">refl</a> <a id="1021" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1000" class="Bound">x</a><a id="1022" class="Symbol">))</a>        <a id="1032" class="Comment">-- diagonal proof</a>
  <a id="1052" class="Symbol">→</a> <a id="1054" class="Symbol">(</a><a id="1055" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1055" class="Bound">x</a> <a id="1057" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1057" class="Bound">y</a> <a id="1059" class="Symbol">:</a> <a id="1061" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#930" class="Bound">X</a><a id="1062" class="Symbol">)</a> <a id="1064" class="Symbol">(</a><a id="1065" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1065" class="Bound">p</a> <a id="1067" class="Symbol">:</a> <a id="1069" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="1072" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1055" class="Bound">x</a> <a id="1074" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1057" class="Bound">y</a><a id="1075" class="Symbol">)</a> <a id="1077" class="Symbol">→</a> <a id="1079" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#946" class="Bound">A</a> <a id="1081" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1055" class="Bound">x</a> <a id="1083" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1057" class="Bound">y</a> <a id="1085" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1065" class="Bound">p</a>
<a id="1087" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#J" class="Function">J</a> <a id="1089" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1089" class="Bound">A</a> <a id="1091" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1091" class="Bound">f</a> <a id="1093" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1093" class="Bound">x</a> <a id="1095" class="DottedPattern Symbol">.</a><a id="1096" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1093" class="DottedPattern Bound">x</a> <a id="1098" class="Symbol">(</a><a id="1099" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id.refl" class="InductiveConstructor">refl</a> <a id="1104" class="DottedPattern Symbol">.</a><a id="1105" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1093" class="DottedPattern Bound">x</a><a id="1106" class="Symbol">)</a> <a id="1108" class="Symbol">=</a> <a id="1110" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1091" class="Bound">f</a> <a id="1112" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1093" class="Bound">x</a>{% endraw %}</pre>

### Singleton

We say that a type `X` is a *singleton* if we have
an element `c : X` with `Id c x` for all `x : X`.

![path](/assets/images/issinglenton.png)

<pre class="Agda">{% raw %}<a id="isSingleton" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#isSingleton" class="Function">isSingleton</a> <a id="1310" class="Symbol">:</a> <a id="1312" class="Symbol">{</a><a id="1313" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1313" class="Bound">U</a> <a id="1315" class="Symbol">:</a> <a id="1317" href="Agda.Primitive.html#Universe" class="Postulate">Universe</a><a id="1325" class="Symbol">}</a> <a id="1327" class="Symbol">→</a> <a id="1329" class="PrimitiveType">Set</a> <a id="1333" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1313" class="Bound">U</a> <a id="1335" class="Symbol">→</a> <a id="1337" class="PrimitiveType">Set</a> <a id="1341" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1313" class="Bound">U</a>
<a id="1343" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#isSingleton" class="Function">isSingleton</a> <a id="1355" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1355" class="Bound">X</a> <a id="1357" class="Symbol">=</a> <a id="1359" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#%CE%A3" class="Datatype">Σ</a> <a id="1361" class="Symbol">\(</a><a id="1363" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1363" class="Bound">c</a> <a id="1365" class="Symbol">:</a> <a id="1367" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1355" class="Bound">X</a><a id="1368" class="Symbol">)</a> <a id="1370" class="Symbol">→</a> <a id="1372" class="Symbol">(</a><a id="1373" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1373" class="Bound">x</a> <a id="1375" class="Symbol">:</a> <a id="1377" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1355" class="Bound">X</a><a id="1378" class="Symbol">)</a> <a id="1380" class="Symbol">→</a> <a id="1382" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="1385" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1363" class="Bound">c</a> <a id="1387" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1373" class="Bound">x</a>{% endraw %}</pre>

### Fiber

<pre class="Agda">{% raw %}<a id="fiber" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#fiber" class="Function">fiber</a>
  <a id="1433" class="Symbol">:</a> <a id="1435" class="Symbol">{</a><a id="1436" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1436" class="Bound">U</a> <a id="1438" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1438" class="Bound">V</a> <a id="1440" class="Symbol">:</a> <a id="1442" href="Agda.Primitive.html#Universe" class="Postulate">Universe</a><a id="1450" class="Symbol">}</a> <a id="1452" class="Symbol">{</a><a id="1453" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1453" class="Bound">X</a> <a id="1455" class="Symbol">:</a> <a id="1457" class="PrimitiveType">Set</a> <a id="1461" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1436" class="Bound">U</a><a id="1462" class="Symbol">}</a> <a id="1464" class="Symbol">{</a><a id="1465" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1465" class="Bound">Y</a> <a id="1467" class="Symbol">:</a> <a id="1469" class="PrimitiveType">Set</a> <a id="1473" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1438" class="Bound">V</a><a id="1474" class="Symbol">}</a>
  <a id="1478" class="Symbol">→</a> <a id="1480" class="Symbol">(</a><a id="1481" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1453" class="Bound">X</a> <a id="1483" class="Symbol">→</a> <a id="1485" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1465" class="Bound">Y</a><a id="1486" class="Symbol">)</a>
  <a id="1490" class="Symbol">→</a> <a id="1492" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1465" class="Bound">Y</a>
  <a id="1496" class="Symbol">→</a> <a id="1498" class="PrimitiveType">Set</a> <a id="1502" class="Symbol">(</a><a id="1503" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1436" class="Bound">U</a> <a id="1505" href="Agda.Primitive.html#_%E2%8A%94_" class="Primitive Operator">⊔</a> <a id="1507" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1438" class="Bound">V</a><a id="1508" class="Symbol">)</a>
<a id="1510" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#fiber" class="Function">fiber</a> <a id="1516" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1516" class="Bound">f</a> <a id="1518" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1518" class="Bound">y</a> <a id="1520" class="Symbol">=</a> <a id="1522" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#%CE%A3" class="Datatype">Σ</a> <a id="1524" class="Symbol">\</a><a id="1525" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1525" class="Bound">x</a> <a id="1527" class="Symbol">→</a> <a id="1529" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="1532" class="Symbol">(</a><a id="1533" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1516" class="Bound">f</a> <a id="1535" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1525" class="Bound">x</a><a id="1536" class="Symbol">)</a> <a id="1538" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1518" class="Bound">y</a>{% endraw %}</pre>

### Equivalence

<pre class="Agda">{% raw %}<a id="isEquiv" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#isEquiv" class="Function">isEquiv</a>
  <a id="1592" class="Symbol">:</a> <a id="1594" class="Symbol">{</a><a id="1595" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1595" class="Bound">U</a> <a id="1597" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1597" class="Bound">V</a> <a id="1599" class="Symbol">:</a> <a id="1601" href="Agda.Primitive.html#Universe" class="Postulate">Universe</a><a id="1609" class="Symbol">}</a> <a id="1611" class="Symbol">{</a><a id="1612" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1612" class="Bound">X</a> <a id="1614" class="Symbol">:</a> <a id="1616" class="PrimitiveType">Set</a> <a id="1620" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1595" class="Bound">U</a><a id="1621" class="Symbol">}</a> <a id="1623" class="Symbol">{</a><a id="1624" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1624" class="Bound">Y</a> <a id="1626" class="Symbol">:</a> <a id="1628" class="PrimitiveType">Set</a> <a id="1632" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1597" class="Bound">V</a><a id="1633" class="Symbol">}</a>
  <a id="1637" class="Symbol">→</a> <a id="1639" class="Symbol">(</a><a id="1640" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1612" class="Bound">X</a> <a id="1642" class="Symbol">→</a> <a id="1644" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1624" class="Bound">Y</a><a id="1645" class="Symbol">)</a>
  <a id="1649" class="Symbol">→</a> <a id="1651" class="PrimitiveType">Set</a> <a id="1655" class="Symbol">(</a><a id="1656" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1595" class="Bound">U</a> <a id="1658" href="Agda.Primitive.html#_%E2%8A%94_" class="Primitive Operator">⊔</a> <a id="1660" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1597" class="Bound">V</a><a id="1661" class="Symbol">)</a>
<a id="1663" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#isEquiv" class="Function">isEquiv</a> <a id="1671" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1671" class="Bound">f</a> <a id="1673" class="Symbol">=</a> <a id="1675" class="Symbol">(</a><a id="1676" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1676" class="Bound">y</a> <a id="1678" class="Symbol">:</a> <a id="1680" class="Symbol">_)</a> <a id="1683" class="Symbol">→</a> <a id="1685" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#isSingleton" class="Function">isSingleton</a><a id="1696" class="Symbol">(</a><a id="1697" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#fiber" class="Function">fiber</a> <a id="1703" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1671" class="Bound">f</a> <a id="1705" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1676" class="Bound">y</a><a id="1706" class="Symbol">)</a>

<a id="1709" class="Comment">-- Eq : {U V : Universe} → U ̇ → V ̇ → U ⊔ V ̇</a>
<a id="1756" class="Comment">-- Eq X Y = Σ \(f : X → Y) → isEquiv f</a>
<a id="1795" class="Comment">--</a>
<a id="1798" class="Comment">-- singletonType : {U : Universe} {X : U ̇} → X → U ̇</a>
<a id="1852" class="Comment">-- singletonType x = Σ \y → Id y x</a>
<a id="1887" class="Comment">--</a>
<a id="1890" class="Comment">-- η : {U : Universe} {X : U ̇} (x : X) → singletonType x</a>
<a id="1948" class="Comment">-- η x = (x , refl x)</a>
<a id="1970" class="Comment">--</a>
<a id="1973" class="Comment">-- singletonTypesAreSingletons : {U : Universe} {X : U ̇} (x : X) → isSingleton(singletonType x)</a>
<a id="2070" class="Comment">-- singletonTypesAreSingletons {U} {X} = h</a>
<a id="2113" class="Comment">--  where</a>
<a id="2123" class="Comment">--   A : (y x : X) → Id y x → U ̇</a>
<a id="2157" class="Comment">--   A y x p = Id (η x) (y , p)</a>
<a id="2189" class="Comment">--   f : (x : X) → A x x (refl x)</a>
<a id="2223" class="Comment">--   f x = refl (η x)</a>
<a id="2245" class="Comment">--   φ : (y x : X) (p : Id y x) → Id (η x) (y , p)</a>
<a id="2296" class="Comment">--   φ = J A f</a>
<a id="2311" class="Comment">--   g : (x : X) (σ : singletonType x) → Id (η x) σ</a>
<a id="2363" class="Comment">--   g x (y , p) = φ y x p</a>
<a id="2390" class="Comment">--   h : (x : X) → Σ \(c : singletonType x) → (σ : singletonType x) → Id c σ</a>
<a id="2467" class="Comment">--   h x = (η x , g x)</a>
<a id="2490" class="Comment">--</a>
<a id="2493" class="Comment">-- id : {U : Universe} (X : U ̇) → X → X</a>
<a id="2534" class="Comment">-- id X x = x</a>
<a id="2548" class="Comment">--</a>
<a id="2551" class="Comment">-- idIsEquiv : {U : Universe} (X : U ̇) → isEquiv(id X)</a>
<a id="2607" class="Comment">-- idIsEquiv X = g</a>
<a id="2626" class="Comment">--  where</a>
<a id="2636" class="Comment">--   g : (x : X) → isSingleton (fiber (id X) x)</a>
<a id="2684" class="Comment">--   g = singletonTypesAreSingletons</a>
<a id="2721" class="Comment">--</a>
<a id="2724" class="Comment">-- IdToEq : {U : Universe} (X Y : U ̇) → Id X Y → Eq X Y</a>
<a id="2781" class="Comment">-- IdToEq {U} = J A f</a>
<a id="2803" class="Comment">--  where</a>
<a id="2813" class="Comment">--   A : (X Y : U ̇) → Id X Y → U ̇</a>
<a id="2849" class="Comment">--   A X Y p = Eq X Y</a>
<a id="2871" class="Comment">--   f : (X : U ̇) → A X X (refl X)</a>
<a id="2907" class="Comment">--   f X = (id X , idIsEquiv X)</a>
<a id="2939" class="Comment">--</a>
<a id="2942" class="Comment">-- isUnivalent : (U : Universe) → U ′ ̇</a>
<a id="2982" class="Comment">-- isUnivalent U = (X Y : U ̇) → isEquiv(IdToEq X Y)</a>{% endraw %}</pre>

Using projections pr₁ and pr₂ rather than pattern matching on Σ types
(by defining Σ as a record type), Agda calculates the following normal
form for the term isUnivalent:

λ U → (X Y : Set U) (y : Σ (λ f → (y₁ : Y) → Σ (λ c →
(x : Σ (λ x₁ → Id (f x₁) y₁)) → Id c x))) →
Σ (λ c → (x : Σ (λ x₁ → Id (J (λ X₁ Y₁ p → Σ (λ f →
(y₁ : Y₁) → Σ (λ c₁ → (x₂ : Σ (λ x₃ → Id (f x₃) y₁)) → Id c₁ x₂)))
(λ X₁ → (λ x₂ → x₂) , (λ x₂ → (x₂ , refl x₂) , (λ yp → J (λ y₁ x₃ p →
Id (x₃ , refl x₃) (y₁ , p)) (λ x₃ → refl (x₃ , refl x₃))
(pr₁ yp) x₂ (pr₂ yp)))) X Y x₁) y)) → Id c x)

This is with lots of subterms elided. With all of them explicitly
given, the normal form of isUnivalent is

λ U → (X Y : U ̇) (y : Σ {U} {U} {X → Y} (λ f → (y₁ : Y) → Σ {U} {U}
{Σ {U} {U} {X} (λ x → Id {U} {Y} (f x) y₁)} (λ c → (x : Σ {U} {U} {X}
(λ x₁ → Id {U} {Y} (f x₁) y₁)) → Id {U} {Σ {U} {U} {X} (λ x₁ → Id {U} {Y}
(f x₁) y₁)} c x))) → Σ {U ′} {U ′} {Σ {U ′} {U} {Id {U ′} {U ̇} X Y}
(λ x → Id {U} {Σ {U} {U} {X → Y} (λ f → (y₁ : Y) → Σ {U} {U}
{Σ {U} {U} {X} (λ x₁ → Id {U} {Y} (f x₁) y₁)} (λ c → (x₁ : Σ {U} {U} {X}
(λ x₂ → Id {U} {Y} (f x₂) y₁)) → Id {U} {Σ {U} {U} {X} (λ x₂ → Id {U} {Y}
(f x₂) y₁)} c x₁))} (J {U ′} {U} {U ̇} (λ X₁ Y₁ p → Σ {U} {U} {X₁ → Y₁}
(λ f → (y₁ : Y₁) → Σ {U} {U} {Σ {U} {U} {X₁} (λ x₁ → Id {U} {Y₁} (f x₁) y₁)}
(λ c → (x₁ : Σ {U} {U} {X₁} (λ x₂ → Id {U} {Y₁} (f x₂) y₁)) → Id {U}
{Σ {U} {U} {X₁} (λ x₂ → Id {U} {Y₁} (f x₂) y₁)} c x₁))) (λ X₁ → (λ x₁ → x₁)
, (λ x₁ → (x₁ , refl x₁) , (λ yp → J {U} {U} {X₁} (λ y₁ x₂ p → Id {U}
{Σ {U} {U} {X₁} (λ y₂ → Id {U} {X₁} y₂ x₂)} (x₂ , refl x₂) (y₁ , p))
(λ x₂ → refl (x₂ , refl x₂)) (pr₁ yp) x₁ (pr₂ yp)))) X Y x) y)} (λ c →
(x : Σ {U ′} {U} {Id {U ′} {U ̇} X Y} (λ x₁ → Id {U} {Σ {U} {U} {X → Y}
(λ f → (y₁ : Y) → Σ {U} {U} {Σ {U} {U} {X} (λ x₂ → Id {U} {Y} (f x₂) y₁)}
(λ c₁ → (x₂ : Σ {U} {U} {X} (λ x₃ → Id {U} {Y} (f x₃) y₁)) → Id {U}
{Σ {U} {U} {X} (λ x₃ → Id {U} {Y} (f x₃) y₁)} c₁ x₂))} (J {U ′} {U} {U ̇}
(λ X₁ Y₁ p → Σ {U} {U} {X₁ → Y₁} (λ f → (y₁ : Y₁) → Σ {U} {U} {Σ {U} {U}
{X₁} (λ x₂ → Id {U} {Y₁} (f x₂) y₁)} (λ c₁ → (x₂ : Σ {U} {U} {X₁} (λ x₃ →
Id {U} {Y₁} (f x₃) y₁)) → Id {U} {Σ {U} {U} {X₁} (λ x₃ → Id {U} {Y₁} (f x₃)
y₁)} c₁ x₂))) (λ X₁ → (λ x₂ → x₂) , (λ x₂ → (x₂ , refl x₂) , (λ yp → J {U}
{U} {X₁} (λ y₁ x₃ p → Id {U} {Σ {U} {U} {X₁} (λ y₂ → Id {U} {X₁} y₂ x₃)}
(x₃ , refl x₃) (y₁ , p)) (λ x₃ → refl (x₃ , refl x₃)) (pr₁ yp) x₂ (pr₂ yp))))
X Y x₁) y)) → Id {U ′} {Σ {U ′} {U} {Id {U ′} {U ̇} X Y} (λ x₁ → Id {U}
{Σ {U} {U} {X → Y} (λ f → (y₁ : Y) → Σ {U} {U} {Σ {U} {U} {X} (λ x₂ →
Id {U} {Y} (f x₂) y₁)} (λ c₁ → (x₂ : Σ {U} {U} {X} (λ x₃ → Id {U} {Y} (f x₃)
y₁)) → Id {U} {Σ {U} {U} {X} (λ x₃ → Id {U} {Y} (f x₃) y₁)} c₁ x₂))}
(J {U ′} {U} {U ̇} (λ X₁ Y₁ p → Σ {U} {U} {X₁ → Y₁} (λ f → (y₁ : Y₁) →
Σ {U} {U} {Σ {U} {U} {X₁} (λ x₂ → Id {U} {Y₁} (f x₂) y₁)} (λ c₁ →
(x₂ : Σ {U} {U} {X₁} (λ x₃ → Id {U} {Y₁} (f x₃) y₁)) → Id {U} {Σ {U} {U} {X₁}
(λ x₃ → Id {U} {Y₁} (f x₃) y₁)} c₁ x₂))) (λ X₁ → (λ x₂ → x₂) , (λ x₂ → (x₂ ,
refl x₂) , (λ yp → J {U} {U} {X₁} (λ y₁ x₃ p → Id {U} {Σ {U} {U} {X₁}
(λ y₂ → Id {U} {X₁} y₂ x₃)} (x₃ , refl x₃) (y₁ , p)) (λ x₃ → refl (x₃ ,
refl x₃)) (pr₁ yp) x₂ (pr₂ yp)))) X Y x₁) y)} c x)
