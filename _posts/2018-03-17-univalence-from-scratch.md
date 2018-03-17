---
layout: "post"
title: "Univalence From Scratch"
date: "2018-03-17"
categories: type-theory
---

M.H. Escardo. [*A self-contained, brief and complete formulation of Voevodsky's
Univalence Axiom*](https://arxiv.org/abs/1803.02294), March 2018, arXiv:1803.02294.

The author of the following code is the same author's paper, Martín Hötzel
Escardó. I put the code here for me but I modified it a little for my own
convenience. For the original version, review the link of the paper.

Basic imports:

<pre class="Agda">{% raw %}<a id="514" class="Symbol">{-#</a> <a id="518" class="Keyword">OPTIONS</a> <a id="526" class="Option">--without-K</a> <a id="538" class="Symbol">#-}</a>

<a id="543" class="Keyword">open</a> <a id="548" class="Keyword">import</a> <a id="555" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>
  <a id="572" class="Keyword">using</a>    <a id="581" class="Symbol">(</a><a id="582" href="Agda.Primitive.html#_%E2%8A%94_" class="Primitive Operator">_⊔_</a><a id="585" class="Symbol">)</a>
  <a id="589" class="Keyword">renaming</a> <a id="598" class="Symbol">(</a><a id="599" href="Agda.Primitive.html#lzero" class="Primitive">lzero</a> <a id="605" class="Symbol">to</a> <a id="608" href="Agda.Primitive.html#lzero" class="Primitive">U₀</a> <a id="611" class="Symbol">;</a> <a id="613" href="Agda.Primitive.html#lsuc" class="Primitive">lsuc</a> <a id="618" class="Symbol">to</a> <a id="621" href="Agda.Primitive.html#lsuc" class="Primitive">_′</a> <a id="624" class="Symbol">;</a> <a id="626" href="Agda.Primitive.html#Level" class="Postulate">Level</a> <a id="632" class="Symbol">to</a> <a id="635" href="Agda.Primitive.html#Level" class="Postulate">Universe</a><a id="643" class="Symbol">)</a>{% endraw %}</pre>

### Σ-type and Identity type

<pre class="Agda">{% raw %}<a id="700" class="Keyword">data</a> <a id="Σ" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#%CE%A3" class="Datatype">Σ</a> <a id="707" class="Symbol">{</a><a id="708" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#708" class="Bound">U</a> <a id="710" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#710" class="Bound">V</a> <a id="712" class="Symbol">:</a> <a id="714" href="Agda.Primitive.html#Universe" class="Postulate">Universe</a><a id="722" class="Symbol">}</a>
       <a id="731" class="Symbol">{</a><a id="732" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#732" class="Bound">X</a> <a id="734" class="Symbol">:</a> <a id="736" class="PrimitiveType">Set</a> <a id="740" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#708" class="Bound">U</a><a id="741" class="Symbol">}</a>
       <a id="750" class="Symbol">(</a><a id="751" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#751" class="Bound">Y</a> <a id="753" class="Symbol">:</a> <a id="755" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#732" class="Bound">X</a> <a id="757" class="Symbol">→</a> <a id="759" class="PrimitiveType">Set</a> <a id="763" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#710" class="Bound">V</a><a id="764" class="Symbol">)</a>
     <a id="771" class="Symbol">:</a> <a id="773" class="PrimitiveType">Set</a> <a id="777" class="Symbol">(</a><a id="778" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#708" class="Bound">U</a> <a id="780" href="Agda.Primitive.html#_%E2%8A%94_" class="Primitive Operator">⊔</a> <a id="782" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#710" class="Bound">V</a><a id="783" class="Symbol">)</a> <a id="785" class="Keyword">where</a>
  <a id="Σ._,_" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#%CE%A3._%2C_" class="InductiveConstructor Operator">_,_</a> <a id="797" class="Symbol">:</a> <a id="799" class="Symbol">(</a><a id="800" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#800" class="Bound">x</a> <a id="802" class="Symbol">:</a> <a id="804" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#732" class="Bound">X</a><a id="805" class="Symbol">)</a> <a id="807" class="Symbol">(</a><a id="808" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#808" class="Bound">y</a> <a id="810" class="Symbol">:</a> <a id="812" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#751" class="Bound">Y</a> <a id="814" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#800" class="Bound">x</a><a id="815" class="Symbol">)</a> <a id="817" class="Symbol">→</a> <a id="819" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#%CE%A3" class="Datatype">Σ</a> <a id="821" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#751" class="Bound">Y</a>

<a id="824" class="Keyword">data</a> <a id="Id" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="832" class="Symbol">{</a><a id="833" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#833" class="Bound">U</a> <a id="835" class="Symbol">:</a> <a id="837" href="Agda.Primitive.html#Universe" class="Postulate">Universe</a><a id="845" class="Symbol">}</a> <a id="847" class="Symbol">{</a><a id="848" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#848" class="Bound">X</a> <a id="850" class="Symbol">:</a> <a id="852" class="PrimitiveType">Set</a> <a id="856" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#833" class="Bound">U</a><a id="857" class="Symbol">}</a> <a id="859" class="Symbol">:</a> <a id="861" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#848" class="Bound">X</a> <a id="863" class="Symbol">→</a> <a id="865" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#848" class="Bound">X</a> <a id="867" class="Symbol">→</a> <a id="869" class="PrimitiveType">Set</a> <a id="873" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#833" class="Bound">U</a>  <a id="876" class="Keyword">where</a>
  <a id="Id.refl" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id.refl" class="InductiveConstructor">refl</a> <a id="889" class="Symbol">:</a> <a id="891" class="Symbol">(</a><a id="892" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#892" class="Bound">x</a> <a id="894" class="Symbol">:</a> <a id="896" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#848" class="Bound">X</a><a id="897" class="Symbol">)</a> <a id="899" class="Symbol">→</a> <a id="901" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="904" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#892" class="Bound">x</a> <a id="906" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#892" class="Bound">x</a>{% endraw %}</pre>

### J eliminator

<pre class="Agda">{% raw %}<a id="J" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#J" class="Function">J</a> <a id="953" class="Symbol">:</a> <a id="955" class="Symbol">{</a><a id="956" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#956" class="Bound">U</a> <a id="958" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#958" class="Bound">V</a> <a id="960" class="Symbol">:</a> <a id="962" href="Agda.Primitive.html#Universe" class="Postulate">Universe</a><a id="970" class="Symbol">}</a> <a id="972" class="Symbol">{</a><a id="973" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#973" class="Bound">X</a> <a id="975" class="Symbol">:</a> <a id="977" class="PrimitiveType">Set</a> <a id="981" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#956" class="Bound">U</a><a id="982" class="Symbol">}</a>
  <a id="986" class="Symbol">→</a> <a id="988" class="Symbol">(</a><a id="989" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#989" class="Bound">A</a> <a id="991" class="Symbol">:</a> <a id="993" class="Symbol">(</a><a id="994" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#994" class="Bound">x</a> <a id="996" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#996" class="Bound">y</a> <a id="998" class="Symbol">:</a> <a id="1000" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#973" class="Bound">X</a><a id="1001" class="Symbol">)</a> <a id="1003" class="Symbol">→</a> <a id="1005" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="1008" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#994" class="Bound">x</a> <a id="1010" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#996" class="Bound">y</a> <a id="1012" class="Symbol">→</a> <a id="1014" class="PrimitiveType">Set</a> <a id="1018" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#958" class="Bound">V</a><a id="1019" class="Symbol">)</a>  <a id="1022" class="Comment">-- type former</a>
  <a id="1039" class="Symbol">→</a> <a id="1041" class="Symbol">((</a><a id="1043" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1043" class="Bound">x</a> <a id="1045" class="Symbol">:</a> <a id="1047" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#973" class="Bound">X</a><a id="1048" class="Symbol">)</a> <a id="1050" class="Symbol">→</a> <a id="1052" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#989" class="Bound">A</a> <a id="1054" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1043" class="Bound">x</a> <a id="1056" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1043" class="Bound">x</a> <a id="1058" class="Symbol">(</a><a id="1059" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id.refl" class="InductiveConstructor">refl</a> <a id="1064" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1043" class="Bound">x</a><a id="1065" class="Symbol">))</a>        <a id="1075" class="Comment">-- diagonal proof</a>
  <a id="1095" class="Symbol">→</a> <a id="1097" class="Symbol">(</a><a id="1098" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1098" class="Bound">x</a> <a id="1100" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1100" class="Bound">y</a> <a id="1102" class="Symbol">:</a> <a id="1104" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#973" class="Bound">X</a><a id="1105" class="Symbol">)</a> <a id="1107" class="Symbol">(</a><a id="1108" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1108" class="Bound">p</a> <a id="1110" class="Symbol">:</a> <a id="1112" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="1115" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1098" class="Bound">x</a> <a id="1117" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1100" class="Bound">y</a><a id="1118" class="Symbol">)</a> <a id="1120" class="Symbol">→</a> <a id="1122" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#989" class="Bound">A</a> <a id="1124" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1098" class="Bound">x</a> <a id="1126" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1100" class="Bound">y</a> <a id="1128" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1108" class="Bound">p</a>
<a id="1130" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#J" class="Function">J</a> <a id="1132" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1132" class="Bound">A</a> <a id="1134" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1134" class="Bound">f</a> <a id="1136" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1136" class="Bound">x</a> <a id="1138" class="DottedPattern Symbol">.</a><a id="1139" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1136" class="DottedPattern Bound">x</a> <a id="1141" class="Symbol">(</a><a id="1142" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id.refl" class="InductiveConstructor">refl</a> <a id="1147" class="DottedPattern Symbol">.</a><a id="1148" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1136" class="DottedPattern Bound">x</a><a id="1149" class="Symbol">)</a> <a id="1151" class="Symbol">=</a> <a id="1153" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1134" class="Bound">f</a> <a id="1155" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1136" class="Bound">x</a>{% endraw %}</pre>

### Singleton

A type X is a *singleton* if we have
an element c : X with Id(c,x) for all x : X.

![path](/assets/images/issinglenton.png)

<pre class="Agda">{% raw %}<a id="isSingleton" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#isSingleton" class="Function">isSingleton</a> <a id="1334" class="Symbol">:</a> <a id="1336" class="Symbol">{</a><a id="1337" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1337" class="Bound">U</a> <a id="1339" class="Symbol">:</a> <a id="1341" href="Agda.Primitive.html#Universe" class="Postulate">Universe</a><a id="1349" class="Symbol">}</a> <a id="1351" class="Symbol">→</a> <a id="1353" class="PrimitiveType">Set</a> <a id="1357" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1337" class="Bound">U</a> <a id="1359" class="Symbol">→</a> <a id="1361" class="PrimitiveType">Set</a> <a id="1365" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1337" class="Bound">U</a>
<a id="1367" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#isSingleton" class="Function">isSingleton</a> <a id="1379" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1379" class="Bound">X</a> <a id="1381" class="Symbol">=</a> <a id="1383" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#%CE%A3" class="Datatype">Σ</a> <a id="1385" class="Symbol">\(</a><a id="1387" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1387" class="Bound">c</a> <a id="1389" class="Symbol">:</a> <a id="1391" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1379" class="Bound">X</a><a id="1392" class="Symbol">)</a> <a id="1394" class="Symbol">→</a> <a id="1396" class="Symbol">(</a><a id="1397" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1397" class="Bound">x</a> <a id="1399" class="Symbol">:</a> <a id="1401" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1379" class="Bound">X</a><a id="1402" class="Symbol">)</a> <a id="1404" class="Symbol">→</a> <a id="1406" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="1409" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1387" class="Bound">c</a> <a id="1411" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1397" class="Bound">x</a>{% endraw %}</pre>

### Fiber

<pre class="Agda">{% raw %}<a id="fiber" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#fiber" class="Function">fiber</a> <a id="1455" class="Symbol">:</a> <a id="1457" class="Symbol">{</a><a id="1458" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1458" class="Bound">U</a> <a id="1460" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1460" class="Bound">V</a> <a id="1462" class="Symbol">:</a> <a id="1464" href="Agda.Primitive.html#Universe" class="Postulate">Universe</a><a id="1472" class="Symbol">}</a> <a id="1474" class="Symbol">{</a><a id="1475" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1475" class="Bound">X</a> <a id="1477" class="Symbol">:</a> <a id="1479" class="PrimitiveType">Set</a> <a id="1483" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1458" class="Bound">U</a><a id="1484" class="Symbol">}</a> <a id="1486" class="Symbol">{</a><a id="1487" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1487" class="Bound">Y</a> <a id="1489" class="Symbol">:</a> <a id="1491" class="PrimitiveType">Set</a> <a id="1495" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1460" class="Bound">V</a><a id="1496" class="Symbol">}</a> <a id="1498" class="Symbol">→</a> <a id="1500" class="Symbol">(</a><a id="1501" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1475" class="Bound">X</a> <a id="1503" class="Symbol">→</a> <a id="1505" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1487" class="Bound">Y</a><a id="1506" class="Symbol">)</a> <a id="1508" class="Symbol">→</a> <a id="1510" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1487" class="Bound">Y</a> <a id="1512" class="Symbol">→</a> <a id="1514" class="PrimitiveType">Set</a> <a id="1518" class="Symbol">(</a><a id="1519" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1458" class="Bound">U</a> <a id="1521" href="Agda.Primitive.html#_%E2%8A%94_" class="Primitive Operator">⊔</a> <a id="1523" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1460" class="Bound">V</a><a id="1524" class="Symbol">)</a>
<a id="1526" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#fiber" class="Function">fiber</a> <a id="1532" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1532" class="Bound">f</a> <a id="1534" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1534" class="Bound">y</a> <a id="1536" class="Symbol">=</a> <a id="1538" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#%CE%A3" class="Datatype">Σ</a> <a id="1540" class="Symbol">\</a><a id="1541" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1541" class="Bound">x</a> <a id="1543" class="Symbol">→</a> <a id="1545" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="1548" class="Symbol">(</a><a id="1549" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1532" class="Bound">f</a> <a id="1551" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1541" class="Bound">x</a><a id="1552" class="Symbol">)</a> <a id="1554" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1534" class="Bound">y</a>{% endraw %}</pre>

### Equivalence

<pre class="Agda">{% raw %}<a id="isEquiv" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#isEquiv" class="Function">isEquiv</a> <a id="1606" class="Symbol">:</a> <a id="1608" class="Symbol">{</a><a id="1609" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1609" class="Bound">U</a> <a id="1611" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1611" class="Bound">V</a> <a id="1613" class="Symbol">:</a> <a id="1615" href="Agda.Primitive.html#Universe" class="Postulate">Universe</a><a id="1623" class="Symbol">}</a> <a id="1625" class="Symbol">{</a><a id="1626" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1626" class="Bound">X</a> <a id="1628" class="Symbol">:</a> <a id="1630" class="PrimitiveType">Set</a> <a id="1634" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1609" class="Bound">U</a><a id="1635" class="Symbol">}</a> <a id="1637" class="Symbol">{</a><a id="1638" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1638" class="Bound">Y</a> <a id="1640" class="Symbol">:</a> <a id="1642" class="PrimitiveType">Set</a> <a id="1646" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1611" class="Bound">V</a><a id="1647" class="Symbol">}</a> <a id="1649" class="Symbol">→</a> <a id="1651" class="Symbol">(</a><a id="1652" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1626" class="Bound">X</a> <a id="1654" class="Symbol">→</a> <a id="1656" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1638" class="Bound">Y</a><a id="1657" class="Symbol">)</a> <a id="1659" class="Symbol">→</a> <a id="1661" class="PrimitiveType">Set</a> <a id="1665" class="Symbol">(</a><a id="1666" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1609" class="Bound">U</a> <a id="1668" href="Agda.Primitive.html#_%E2%8A%94_" class="Primitive Operator">⊔</a> <a id="1670" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1611" class="Bound">V</a><a id="1671" class="Symbol">)</a>
<a id="1673" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#isEquiv" class="Function">isEquiv</a> <a id="1681" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1681" class="Bound">f</a> <a id="1683" class="Symbol">=</a> <a id="1685" class="Symbol">(</a><a id="1686" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1686" class="Bound">y</a> <a id="1688" class="Symbol">:</a> <a id="1690" class="Symbol">_)</a> <a id="1693" class="Symbol">→</a> <a id="1695" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#isSingleton" class="Function">isSingleton</a><a id="1706" class="Symbol">(</a><a id="1707" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#fiber" class="Function">fiber</a> <a id="1713" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1681" class="Bound">f</a> <a id="1715" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1686" class="Bound">y</a><a id="1716" class="Symbol">)</a>

<a id="1719" class="Comment">-- Eq : {U V : Universe} → U ̇ → V ̇ → U ⊔ V ̇</a>
<a id="1766" class="Comment">-- Eq X Y = Σ \(f : X → Y) → isEquiv f</a>
<a id="1805" class="Comment">--</a>
<a id="1808" class="Comment">-- singletonType : {U : Universe} {X : U ̇} → X → U ̇</a>
<a id="1862" class="Comment">-- singletonType x = Σ \y → Id y x</a>
<a id="1897" class="Comment">--</a>
<a id="1900" class="Comment">-- η : {U : Universe} {X : U ̇} (x : X) → singletonType x</a>
<a id="1958" class="Comment">-- η x = (x , refl x)</a>
<a id="1980" class="Comment">--</a>
<a id="1983" class="Comment">-- singletonTypesAreSingletons : {U : Universe} {X : U ̇} (x : X) → isSingleton(singletonType x)</a>
<a id="2080" class="Comment">-- singletonTypesAreSingletons {U} {X} = h</a>
<a id="2123" class="Comment">--  where</a>
<a id="2133" class="Comment">--   A : (y x : X) → Id y x → U ̇</a>
<a id="2167" class="Comment">--   A y x p = Id (η x) (y , p)</a>
<a id="2199" class="Comment">--   f : (x : X) → A x x (refl x)</a>
<a id="2233" class="Comment">--   f x = refl (η x)</a>
<a id="2255" class="Comment">--   φ : (y x : X) (p : Id y x) → Id (η x) (y , p)</a>
<a id="2306" class="Comment">--   φ = J A f</a>
<a id="2321" class="Comment">--   g : (x : X) (σ : singletonType x) → Id (η x) σ</a>
<a id="2373" class="Comment">--   g x (y , p) = φ y x p</a>
<a id="2400" class="Comment">--   h : (x : X) → Σ \(c : singletonType x) → (σ : singletonType x) → Id c σ</a>
<a id="2477" class="Comment">--   h x = (η x , g x)</a>
<a id="2500" class="Comment">--</a>
<a id="2503" class="Comment">-- id : {U : Universe} (X : U ̇) → X → X</a>
<a id="2544" class="Comment">-- id X x = x</a>
<a id="2558" class="Comment">--</a>
<a id="2561" class="Comment">-- idIsEquiv : {U : Universe} (X : U ̇) → isEquiv(id X)</a>
<a id="2617" class="Comment">-- idIsEquiv X = g</a>
<a id="2636" class="Comment">--  where</a>
<a id="2646" class="Comment">--   g : (x : X) → isSingleton (fiber (id X) x)</a>
<a id="2694" class="Comment">--   g = singletonTypesAreSingletons</a>
<a id="2731" class="Comment">--</a>
<a id="2734" class="Comment">-- IdToEq : {U : Universe} (X Y : U ̇) → Id X Y → Eq X Y</a>
<a id="2791" class="Comment">-- IdToEq {U} = J A f</a>
<a id="2813" class="Comment">--  where</a>
<a id="2823" class="Comment">--   A : (X Y : U ̇) → Id X Y → U ̇</a>
<a id="2859" class="Comment">--   A X Y p = Eq X Y</a>
<a id="2881" class="Comment">--   f : (X : U ̇) → A X X (refl X)</a>
<a id="2917" class="Comment">--   f X = (id X , idIsEquiv X)</a>
<a id="2949" class="Comment">--</a>
<a id="2952" class="Comment">-- isUnivalent : (U : Universe) → U ′ ̇</a>
<a id="2992" class="Comment">-- isUnivalent U = (X Y : U ̇) → isEquiv(IdToEq X Y)</a>{% endraw %}</pre>

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
