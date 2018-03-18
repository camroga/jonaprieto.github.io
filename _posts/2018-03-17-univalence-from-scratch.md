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
     <a id="727" class="Symbol">:</a> <a id="729" class="PrimitiveType">Set</a> <a id="733" class="Symbol">(</a><a id="734" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#664" class="Bound">U</a> <a id="736" href="Agda.Primitive.html#_%E2%8A%94_" class="Primitive Operator">⊔</a> <a id="738" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#666" class="Bound">V</a><a id="739" class="Symbol">)</a> <a id="741" class="Keyword">where</a>
  <a id="Σ._,_" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#%CE%A3._%2C_" class="InductiveConstructor Operator">_,_</a> <a id="753" class="Symbol">:</a> <a id="755" class="Symbol">(</a><a id="756" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#756" class="Bound">x</a> <a id="758" class="Symbol">:</a> <a id="760" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#688" class="Bound">X</a><a id="761" class="Symbol">)</a> <a id="763" class="Symbol">(</a><a id="764" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#764" class="Bound">y</a> <a id="766" class="Symbol">:</a> <a id="768" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#707" class="Bound">Y</a> <a id="770" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#756" class="Bound">x</a><a id="771" class="Symbol">)</a> <a id="773" class="Symbol">→</a> <a id="775" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#%CE%A3" class="Datatype">Σ</a> <a id="777" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#707" class="Bound">Y</a>

<a id="780" class="Keyword">data</a> <a id="Id" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="788" class="Symbol">{</a><a id="789" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#789" class="Bound">U</a> <a id="791" class="Symbol">:</a> <a id="793" href="Agda.Primitive.html#Universe" class="Postulate">Universe</a><a id="801" class="Symbol">}</a> <a id="803" class="Symbol">{</a><a id="804" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#804" class="Bound">X</a> <a id="806" class="Symbol">:</a> <a id="808" class="PrimitiveType">Set</a> <a id="812" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#789" class="Bound">U</a><a id="813" class="Symbol">}</a> <a id="815" class="Symbol">:</a> <a id="817" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#804" class="Bound">X</a> <a id="819" class="Symbol">→</a> <a id="821" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#804" class="Bound">X</a> <a id="823" class="Symbol">→</a> <a id="825" class="PrimitiveType">Set</a> <a id="829" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#789" class="Bound">U</a>  <a id="832" class="Keyword">where</a>
  <a id="Id.refl" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id.refl" class="InductiveConstructor">refl</a> <a id="845" class="Symbol">:</a> <a id="847" class="Symbol">(</a><a id="848" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#848" class="Bound">x</a> <a id="850" class="Symbol">:</a> <a id="852" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#804" class="Bound">X</a><a id="853" class="Symbol">)</a> <a id="855" class="Symbol">→</a> <a id="857" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="860" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#848" class="Bound">x</a> <a id="862" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#848" class="Bound">x</a>{% endraw %}</pre>

### J eliminator

<pre class="Agda">{% raw %}<a id="J" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#J" class="Function">J</a> <a id="909" class="Symbol">:</a> <a id="911" class="Symbol">{</a><a id="912" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#912" class="Bound">U</a> <a id="914" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#914" class="Bound">V</a> <a id="916" class="Symbol">:</a> <a id="918" href="Agda.Primitive.html#Universe" class="Postulate">Universe</a><a id="926" class="Symbol">}</a> <a id="928" class="Symbol">{</a><a id="929" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#929" class="Bound">X</a> <a id="931" class="Symbol">:</a> <a id="933" class="PrimitiveType">Set</a> <a id="937" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#912" class="Bound">U</a><a id="938" class="Symbol">}</a>
  <a id="942" class="Symbol">→</a> <a id="944" class="Symbol">(</a><a id="945" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#945" class="Bound">A</a> <a id="947" class="Symbol">:</a> <a id="949" class="Symbol">(</a><a id="950" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#950" class="Bound">x</a> <a id="952" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#952" class="Bound">y</a> <a id="954" class="Symbol">:</a> <a id="956" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#929" class="Bound">X</a><a id="957" class="Symbol">)</a> <a id="959" class="Symbol">→</a> <a id="961" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="964" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#950" class="Bound">x</a> <a id="966" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#952" class="Bound">y</a> <a id="968" class="Symbol">→</a> <a id="970" class="PrimitiveType">Set</a> <a id="974" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#914" class="Bound">V</a><a id="975" class="Symbol">)</a>  <a id="978" class="Comment">-- type former</a>
  <a id="995" class="Symbol">→</a> <a id="997" class="Symbol">((</a><a id="999" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#999" class="Bound">x</a> <a id="1001" class="Symbol">:</a> <a id="1003" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#929" class="Bound">X</a><a id="1004" class="Symbol">)</a> <a id="1006" class="Symbol">→</a> <a id="1008" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#945" class="Bound">A</a> <a id="1010" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#999" class="Bound">x</a> <a id="1012" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#999" class="Bound">x</a> <a id="1014" class="Symbol">(</a><a id="1015" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id.refl" class="InductiveConstructor">refl</a> <a id="1020" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#999" class="Bound">x</a><a id="1021" class="Symbol">))</a>        <a id="1031" class="Comment">-- diagonal proof</a>
  <a id="1051" class="Symbol">→</a> <a id="1053" class="Symbol">(</a><a id="1054" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1054" class="Bound">x</a> <a id="1056" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1056" class="Bound">y</a> <a id="1058" class="Symbol">:</a> <a id="1060" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#929" class="Bound">X</a><a id="1061" class="Symbol">)</a> <a id="1063" class="Symbol">(</a><a id="1064" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1064" class="Bound">p</a> <a id="1066" class="Symbol">:</a> <a id="1068" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="1071" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1054" class="Bound">x</a> <a id="1073" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1056" class="Bound">y</a><a id="1074" class="Symbol">)</a> <a id="1076" class="Symbol">→</a> <a id="1078" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#945" class="Bound">A</a> <a id="1080" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1054" class="Bound">x</a> <a id="1082" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1056" class="Bound">y</a> <a id="1084" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1064" class="Bound">p</a>
<a id="1086" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#J" class="Function">J</a> <a id="1088" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1088" class="Bound">A</a> <a id="1090" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1090" class="Bound">f</a> <a id="1092" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1092" class="Bound">x</a> <a id="1094" class="DottedPattern Symbol">.</a><a id="1095" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1092" class="DottedPattern Bound">x</a> <a id="1097" class="Symbol">(</a><a id="1098" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id.refl" class="InductiveConstructor">refl</a> <a id="1103" class="DottedPattern Symbol">.</a><a id="1104" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1092" class="DottedPattern Bound">x</a><a id="1105" class="Symbol">)</a> <a id="1107" class="Symbol">=</a> <a id="1109" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1090" class="Bound">f</a> <a id="1111" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1092" class="Bound">x</a>{% endraw %}</pre>

### Singleton

A type X is a *singleton* if we have
an element c : X with Id(c,x) for all x : X.

![path](/assets/images/issinglenton.png)

<pre class="Agda">{% raw %}<a id="isSingleton" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#isSingleton" class="Function">isSingleton</a> <a id="1290" class="Symbol">:</a> <a id="1292" class="Symbol">{</a><a id="1293" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1293" class="Bound">U</a> <a id="1295" class="Symbol">:</a> <a id="1297" href="Agda.Primitive.html#Universe" class="Postulate">Universe</a><a id="1305" class="Symbol">}</a> <a id="1307" class="Symbol">→</a> <a id="1309" class="PrimitiveType">Set</a> <a id="1313" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1293" class="Bound">U</a> <a id="1315" class="Symbol">→</a> <a id="1317" class="PrimitiveType">Set</a> <a id="1321" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1293" class="Bound">U</a>
<a id="1323" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#isSingleton" class="Function">isSingleton</a> <a id="1335" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1335" class="Bound">X</a> <a id="1337" class="Symbol">=</a> <a id="1339" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#%CE%A3" class="Datatype">Σ</a> <a id="1341" class="Symbol">\(</a><a id="1343" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1343" class="Bound">c</a> <a id="1345" class="Symbol">:</a> <a id="1347" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1335" class="Bound">X</a><a id="1348" class="Symbol">)</a> <a id="1350" class="Symbol">→</a> <a id="1352" class="Symbol">(</a><a id="1353" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1353" class="Bound">x</a> <a id="1355" class="Symbol">:</a> <a id="1357" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1335" class="Bound">X</a><a id="1358" class="Symbol">)</a> <a id="1360" class="Symbol">→</a> <a id="1362" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="1365" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1343" class="Bound">c</a> <a id="1367" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1353" class="Bound">x</a>{% endraw %}</pre>

### Fiber

<pre class="Agda">{% raw %}<a id="fiber" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#fiber" class="Function">fiber</a> <a id="1411" class="Symbol">:</a> <a id="1413" class="Symbol">{</a><a id="1414" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1414" class="Bound">U</a> <a id="1416" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1416" class="Bound">V</a> <a id="1418" class="Symbol">:</a> <a id="1420" href="Agda.Primitive.html#Universe" class="Postulate">Universe</a><a id="1428" class="Symbol">}</a> <a id="1430" class="Symbol">{</a><a id="1431" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1431" class="Bound">X</a> <a id="1433" class="Symbol">:</a> <a id="1435" class="PrimitiveType">Set</a> <a id="1439" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1414" class="Bound">U</a><a id="1440" class="Symbol">}</a> <a id="1442" class="Symbol">{</a><a id="1443" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1443" class="Bound">Y</a> <a id="1445" class="Symbol">:</a> <a id="1447" class="PrimitiveType">Set</a> <a id="1451" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1416" class="Bound">V</a><a id="1452" class="Symbol">}</a> <a id="1454" class="Symbol">→</a> <a id="1456" class="Symbol">(</a><a id="1457" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1431" class="Bound">X</a> <a id="1459" class="Symbol">→</a> <a id="1461" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1443" class="Bound">Y</a><a id="1462" class="Symbol">)</a> <a id="1464" class="Symbol">→</a> <a id="1466" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1443" class="Bound">Y</a> <a id="1468" class="Symbol">→</a> <a id="1470" class="PrimitiveType">Set</a> <a id="1474" class="Symbol">(</a><a id="1475" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1414" class="Bound">U</a> <a id="1477" href="Agda.Primitive.html#_%E2%8A%94_" class="Primitive Operator">⊔</a> <a id="1479" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1416" class="Bound">V</a><a id="1480" class="Symbol">)</a>
<a id="1482" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#fiber" class="Function">fiber</a> <a id="1488" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1488" class="Bound">f</a> <a id="1490" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1490" class="Bound">y</a> <a id="1492" class="Symbol">=</a> <a id="1494" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#%CE%A3" class="Datatype">Σ</a> <a id="1496" class="Symbol">\</a><a id="1497" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1497" class="Bound">x</a> <a id="1499" class="Symbol">→</a> <a id="1501" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="1504" class="Symbol">(</a><a id="1505" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1488" class="Bound">f</a> <a id="1507" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1497" class="Bound">x</a><a id="1508" class="Symbol">)</a> <a id="1510" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1490" class="Bound">y</a>{% endraw %}</pre>

### Equivalence

<pre class="Agda">{% raw %}<a id="isEquiv" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#isEquiv" class="Function">isEquiv</a> <a id="1562" class="Symbol">:</a> <a id="1564" class="Symbol">{</a><a id="1565" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1565" class="Bound">U</a> <a id="1567" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1567" class="Bound">V</a> <a id="1569" class="Symbol">:</a> <a id="1571" href="Agda.Primitive.html#Universe" class="Postulate">Universe</a><a id="1579" class="Symbol">}</a> <a id="1581" class="Symbol">{</a><a id="1582" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1582" class="Bound">X</a> <a id="1584" class="Symbol">:</a> <a id="1586" class="PrimitiveType">Set</a> <a id="1590" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1565" class="Bound">U</a><a id="1591" class="Symbol">}</a> <a id="1593" class="Symbol">{</a><a id="1594" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1594" class="Bound">Y</a> <a id="1596" class="Symbol">:</a> <a id="1598" class="PrimitiveType">Set</a> <a id="1602" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1567" class="Bound">V</a><a id="1603" class="Symbol">}</a> <a id="1605" class="Symbol">→</a> <a id="1607" class="Symbol">(</a><a id="1608" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1582" class="Bound">X</a> <a id="1610" class="Symbol">→</a> <a id="1612" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1594" class="Bound">Y</a><a id="1613" class="Symbol">)</a> <a id="1615" class="Symbol">→</a> <a id="1617" class="PrimitiveType">Set</a> <a id="1621" class="Symbol">(</a><a id="1622" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1565" class="Bound">U</a> <a id="1624" href="Agda.Primitive.html#_%E2%8A%94_" class="Primitive Operator">⊔</a> <a id="1626" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1567" class="Bound">V</a><a id="1627" class="Symbol">)</a>
<a id="1629" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#isEquiv" class="Function">isEquiv</a> <a id="1637" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1637" class="Bound">f</a> <a id="1639" class="Symbol">=</a> <a id="1641" class="Symbol">(</a><a id="1642" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1642" class="Bound">y</a> <a id="1644" class="Symbol">:</a> <a id="1646" class="Symbol">_)</a> <a id="1649" class="Symbol">→</a> <a id="1651" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#isSingleton" class="Function">isSingleton</a><a id="1662" class="Symbol">(</a><a id="1663" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#fiber" class="Function">fiber</a> <a id="1669" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1637" class="Bound">f</a> <a id="1671" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1642" class="Bound">y</a><a id="1672" class="Symbol">)</a>

<a id="1675" class="Comment">-- Eq : {U V : Universe} → U ̇ → V ̇ → U ⊔ V ̇</a>
<a id="1722" class="Comment">-- Eq X Y = Σ \(f : X → Y) → isEquiv f</a>
<a id="1761" class="Comment">--</a>
<a id="1764" class="Comment">-- singletonType : {U : Universe} {X : U ̇} → X → U ̇</a>
<a id="1818" class="Comment">-- singletonType x = Σ \y → Id y x</a>
<a id="1853" class="Comment">--</a>
<a id="1856" class="Comment">-- η : {U : Universe} {X : U ̇} (x : X) → singletonType x</a>
<a id="1914" class="Comment">-- η x = (x , refl x)</a>
<a id="1936" class="Comment">--</a>
<a id="1939" class="Comment">-- singletonTypesAreSingletons : {U : Universe} {X : U ̇} (x : X) → isSingleton(singletonType x)</a>
<a id="2036" class="Comment">-- singletonTypesAreSingletons {U} {X} = h</a>
<a id="2079" class="Comment">--  where</a>
<a id="2089" class="Comment">--   A : (y x : X) → Id y x → U ̇</a>
<a id="2123" class="Comment">--   A y x p = Id (η x) (y , p)</a>
<a id="2155" class="Comment">--   f : (x : X) → A x x (refl x)</a>
<a id="2189" class="Comment">--   f x = refl (η x)</a>
<a id="2211" class="Comment">--   φ : (y x : X) (p : Id y x) → Id (η x) (y , p)</a>
<a id="2262" class="Comment">--   φ = J A f</a>
<a id="2277" class="Comment">--   g : (x : X) (σ : singletonType x) → Id (η x) σ</a>
<a id="2329" class="Comment">--   g x (y , p) = φ y x p</a>
<a id="2356" class="Comment">--   h : (x : X) → Σ \(c : singletonType x) → (σ : singletonType x) → Id c σ</a>
<a id="2433" class="Comment">--   h x = (η x , g x)</a>
<a id="2456" class="Comment">--</a>
<a id="2459" class="Comment">-- id : {U : Universe} (X : U ̇) → X → X</a>
<a id="2500" class="Comment">-- id X x = x</a>
<a id="2514" class="Comment">--</a>
<a id="2517" class="Comment">-- idIsEquiv : {U : Universe} (X : U ̇) → isEquiv(id X)</a>
<a id="2573" class="Comment">-- idIsEquiv X = g</a>
<a id="2592" class="Comment">--  where</a>
<a id="2602" class="Comment">--   g : (x : X) → isSingleton (fiber (id X) x)</a>
<a id="2650" class="Comment">--   g = singletonTypesAreSingletons</a>
<a id="2687" class="Comment">--</a>
<a id="2690" class="Comment">-- IdToEq : {U : Universe} (X Y : U ̇) → Id X Y → Eq X Y</a>
<a id="2747" class="Comment">-- IdToEq {U} = J A f</a>
<a id="2769" class="Comment">--  where</a>
<a id="2779" class="Comment">--   A : (X Y : U ̇) → Id X Y → U ̇</a>
<a id="2815" class="Comment">--   A X Y p = Eq X Y</a>
<a id="2837" class="Comment">--   f : (X : U ̇) → A X X (refl X)</a>
<a id="2873" class="Comment">--   f X = (id X , idIsEquiv X)</a>
<a id="2905" class="Comment">--</a>
<a id="2908" class="Comment">-- isUnivalent : (U : Universe) → U ′ ̇</a>
<a id="2948" class="Comment">-- isUnivalent U = (X Y : U ̇) → isEquiv(IdToEq X Y)</a>{% endraw %}</pre>

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
