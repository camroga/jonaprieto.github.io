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

### Basic definitions

<pre class="Agda">{% raw %}<a id="521" class="Symbol">{-#</a> <a id="525" class="Keyword">OPTIONS</a> <a id="533" class="Option">--without-K</a> <a id="545" class="Symbol">#-}</a>
<a id="549" class="Keyword">open</a> <a id="554" class="Keyword">import</a> <a id="561" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>
  <a id="578" class="Keyword">using</a>    <a id="587" class="Symbol">(</a><a id="588" href="Agda.Primitive.html#_%E2%8A%94_" class="Primitive Operator">_⊔_</a><a id="591" class="Symbol">)</a>
  <a id="595" class="Keyword">renaming</a> <a id="604" class="Symbol">(</a><a id="605" href="Agda.Primitive.html#lzero" class="Primitive">lzero</a> <a id="611" class="Symbol">to</a> <a id="614" href="Agda.Primitive.html#lzero" class="Primitive">U₀</a> <a id="617" class="Symbol">;</a> <a id="619" href="Agda.Primitive.html#lsuc" class="Primitive">lsuc</a> <a id="624" class="Symbol">to</a> <a id="627" href="Agda.Primitive.html#lsuc" class="Primitive">_′</a> <a id="630" class="Symbol">;</a> <a id="632" href="Agda.Primitive.html#Level" class="Postulate">Level</a> <a id="638" class="Symbol">to</a> <a id="641" href="Agda.Primitive.html#Level" class="Postulate">Universe</a><a id="649" class="Symbol">)</a>

<a id="652" class="Keyword">data</a> <a id="Σ" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#%CE%A3" class="Datatype">Σ</a> <a id="659" class="Symbol">{</a><a id="660" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#660" class="Bound">U</a> <a id="662" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#662" class="Bound">V</a> <a id="664" class="Symbol">:</a> <a id="666" href="Agda.Primitive.html#Universe" class="Postulate">Universe</a><a id="674" class="Symbol">}</a>
      <a id="682" class="Symbol">{</a><a id="683" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#683" class="Bound">X</a> <a id="685" class="Symbol">:</a> <a id="687" class="PrimitiveType">Set</a> <a id="691" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#660" class="Bound">U</a><a id="692" class="Symbol">}</a>
      <a id="700" class="Symbol">(</a><a id="701" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#701" class="Bound">Y</a> <a id="703" class="Symbol">:</a> <a id="705" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#683" class="Bound">X</a> <a id="707" class="Symbol">→</a> <a id="709" class="PrimitiveType">Set</a> <a id="713" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#662" class="Bound">V</a><a id="714" class="Symbol">)</a>
    <a id="720" class="Symbol">:</a> <a id="722" class="PrimitiveType">Set</a> <a id="726" class="Symbol">(</a><a id="727" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#660" class="Bound">U</a> <a id="729" href="Agda.Primitive.html#_%E2%8A%94_" class="Primitive Operator">⊔</a> <a id="731" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#662" class="Bound">V</a><a id="732" class="Symbol">)</a> <a id="734" class="Keyword">where</a>
  <a id="Σ._,_" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#%CE%A3._%2C_" class="InductiveConstructor Operator">_,_</a> <a id="746" class="Symbol">:</a> <a id="748" class="Symbol">(</a><a id="749" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#749" class="Bound">x</a> <a id="751" class="Symbol">:</a> <a id="753" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#683" class="Bound">X</a><a id="754" class="Symbol">)</a> <a id="756" class="Symbol">(</a><a id="757" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#757" class="Bound">y</a> <a id="759" class="Symbol">:</a> <a id="761" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#701" class="Bound">Y</a> <a id="763" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#749" class="Bound">x</a><a id="764" class="Symbol">)</a> <a id="766" class="Symbol">→</a> <a id="768" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#%CE%A3" class="Datatype">Σ</a> <a id="770" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#701" class="Bound">Y</a>

<a id="773" class="Keyword">data</a> <a id="Id" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="781" class="Symbol">{</a><a id="782" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#782" class="Bound">U</a> <a id="784" class="Symbol">:</a> <a id="786" href="Agda.Primitive.html#Universe" class="Postulate">Universe</a><a id="794" class="Symbol">}</a> <a id="796" class="Symbol">{</a><a id="797" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#797" class="Bound">X</a> <a id="799" class="Symbol">:</a> <a id="801" class="PrimitiveType">Set</a> <a id="805" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#782" class="Bound">U</a><a id="806" class="Symbol">}</a> <a id="808" class="Symbol">:</a> <a id="810" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#797" class="Bound">X</a> <a id="812" class="Symbol">→</a> <a id="814" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#797" class="Bound">X</a> <a id="816" class="Symbol">→</a> <a id="818" class="PrimitiveType">Set</a> <a id="822" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#782" class="Bound">U</a>  <a id="825" class="Keyword">where</a>
  <a id="Id.refl" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id.refl" class="InductiveConstructor">refl</a> <a id="838" class="Symbol">:</a> <a id="840" class="Symbol">(</a><a id="841" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#841" class="Bound">x</a> <a id="843" class="Symbol">:</a> <a id="845" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#797" class="Bound">X</a><a id="846" class="Symbol">)</a> <a id="848" class="Symbol">→</a> <a id="850" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="853" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#841" class="Bound">x</a> <a id="855" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#841" class="Bound">x</a>

<a id="J" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#J" class="Function">J</a> <a id="860" class="Symbol">:</a> <a id="862" class="Symbol">{</a><a id="863" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#863" class="Bound">U</a> <a id="865" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#865" class="Bound">V</a> <a id="867" class="Symbol">:</a> <a id="869" href="Agda.Primitive.html#Universe" class="Postulate">Universe</a><a id="877" class="Symbol">}</a> <a id="879" class="Symbol">{</a><a id="880" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#880" class="Bound">X</a> <a id="882" class="Symbol">:</a> <a id="884" class="PrimitiveType">Set</a> <a id="888" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#863" class="Bound">U</a><a id="889" class="Symbol">}</a>
  <a id="893" class="Symbol">→</a> <a id="895" class="Symbol">(</a><a id="896" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#896" class="Bound">A</a> <a id="898" class="Symbol">:</a> <a id="900" class="Symbol">(</a><a id="901" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#901" class="Bound">x</a> <a id="903" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#903" class="Bound">y</a> <a id="905" class="Symbol">:</a> <a id="907" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#880" class="Bound">X</a><a id="908" class="Symbol">)</a> <a id="910" class="Symbol">→</a> <a id="912" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="915" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#901" class="Bound">x</a> <a id="917" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#903" class="Bound">y</a> <a id="919" class="Symbol">→</a> <a id="921" class="PrimitiveType">Set</a> <a id="925" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#865" class="Bound">V</a><a id="926" class="Symbol">)</a>  <a id="929" class="Comment">-- type former</a>
  <a id="946" class="Symbol">→</a> <a id="948" class="Symbol">((</a><a id="950" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#950" class="Bound">x</a> <a id="952" class="Symbol">:</a> <a id="954" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#880" class="Bound">X</a><a id="955" class="Symbol">)</a> <a id="957" class="Symbol">→</a> <a id="959" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#896" class="Bound">A</a> <a id="961" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#950" class="Bound">x</a> <a id="963" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#950" class="Bound">x</a> <a id="965" class="Symbol">(</a><a id="966" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id.refl" class="InductiveConstructor">refl</a> <a id="971" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#950" class="Bound">x</a><a id="972" class="Symbol">))</a>        <a id="982" class="Comment">-- diagonal proof</a>
  <a id="1002" class="Symbol">→</a> <a id="1004" class="Symbol">(</a><a id="1005" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1005" class="Bound">x</a> <a id="1007" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1007" class="Bound">y</a> <a id="1009" class="Symbol">:</a> <a id="1011" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#880" class="Bound">X</a><a id="1012" class="Symbol">)</a> <a id="1014" class="Symbol">(</a><a id="1015" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1015" class="Bound">p</a> <a id="1017" class="Symbol">:</a> <a id="1019" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="1022" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1005" class="Bound">x</a> <a id="1024" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1007" class="Bound">y</a><a id="1025" class="Symbol">)</a> <a id="1027" class="Symbol">→</a> <a id="1029" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#896" class="Bound">A</a> <a id="1031" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1005" class="Bound">x</a> <a id="1033" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1007" class="Bound">y</a> <a id="1035" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1015" class="Bound">p</a>
<a id="1037" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#J" class="Function">J</a> <a id="1039" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1039" class="Bound">A</a> <a id="1041" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1041" class="Bound">f</a> <a id="1043" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1043" class="Bound">x</a> <a id="1045" class="DottedPattern Symbol">.</a><a id="1046" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1043" class="DottedPattern Bound">x</a> <a id="1048" class="Symbol">(</a><a id="1049" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id.refl" class="InductiveConstructor">refl</a> <a id="1054" class="DottedPattern Symbol">.</a><a id="1055" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1043" class="DottedPattern Bound">x</a><a id="1056" class="Symbol">)</a> <a id="1058" class="Symbol">=</a> <a id="1060" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1041" class="Bound">f</a> <a id="1062" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1043" class="Bound">x</a>{% endraw %}</pre>

### Fibrations

<pre class="Agda">{% raw %}<a id="isSingleton" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#isSingleton" class="Function">isSingleton</a> <a id="1117" class="Symbol">:</a> <a id="1119" class="Symbol">{</a><a id="1120" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1120" class="Bound">U</a> <a id="1122" class="Symbol">:</a> <a id="1124" href="Agda.Primitive.html#Universe" class="Postulate">Universe</a><a id="1132" class="Symbol">}</a> <a id="1134" class="Symbol">→</a> <a id="1136" class="PrimitiveType">Set</a> <a id="1140" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1120" class="Bound">U</a> <a id="1142" class="Symbol">→</a> <a id="1144" class="PrimitiveType">Set</a> <a id="1148" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1120" class="Bound">U</a>
<a id="1150" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#isSingleton" class="Function">isSingleton</a> <a id="1162" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1162" class="Bound">X</a> <a id="1164" class="Symbol">=</a> <a id="1166" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#%CE%A3" class="Datatype">Σ</a> <a id="1168" class="Symbol">\(</a><a id="1170" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1170" class="Bound">c</a> <a id="1172" class="Symbol">:</a> <a id="1174" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1162" class="Bound">X</a><a id="1175" class="Symbol">)</a> <a id="1177" class="Symbol">→</a> <a id="1179" class="Symbol">(</a><a id="1180" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1180" class="Bound">x</a> <a id="1182" class="Symbol">:</a> <a id="1184" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1162" class="Bound">X</a><a id="1185" class="Symbol">)</a> <a id="1187" class="Symbol">→</a> <a id="1189" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#Id" class="Datatype">Id</a> <a id="1192" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1170" class="Bound">c</a> <a id="1194" href="{% endraw %}{% link _posts/2018-03-17-univalence-from-scratch.md %}{% raw %}#1180" class="Bound">x</a>
<a id="1196" class="Comment">--</a>
<a id="1199" class="Comment">-- fiber : {U V : Universe} {X : U ̇} {Y : V ̇} → (X → Y) → Y → U ⊔ V ̇</a>
<a id="1271" class="Comment">-- fiber f y = Σ \x → Id (f x) y</a>
<a id="1304" class="Comment">--</a>
<a id="1307" class="Comment">-- isEquiv : {U V : Universe} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇</a>
<a id="1377" class="Comment">-- isEquiv f = (y : _) → isSingleton(fiber f y)</a>
<a id="1425" class="Comment">--</a>
<a id="1428" class="Comment">-- Eq : {U V : Universe} → U ̇ → V ̇ → U ⊔ V ̇</a>
<a id="1475" class="Comment">-- Eq X Y = Σ \(f : X → Y) → isEquiv f</a>
<a id="1514" class="Comment">--</a>
<a id="1517" class="Comment">-- singletonType : {U : Universe} {X : U ̇} → X → U ̇</a>
<a id="1571" class="Comment">-- singletonType x = Σ \y → Id y x</a>
<a id="1606" class="Comment">--</a>
<a id="1609" class="Comment">-- η : {U : Universe} {X : U ̇} (x : X) → singletonType x</a>
<a id="1667" class="Comment">-- η x = (x , refl x)</a>
<a id="1689" class="Comment">--</a>
<a id="1692" class="Comment">-- singletonTypesAreSingletons : {U : Universe} {X : U ̇} (x : X) → isSingleton(singletonType x)</a>
<a id="1789" class="Comment">-- singletonTypesAreSingletons {U} {X} = h</a>
<a id="1832" class="Comment">--  where</a>
<a id="1842" class="Comment">--   A : (y x : X) → Id y x → U ̇</a>
<a id="1876" class="Comment">--   A y x p = Id (η x) (y , p)</a>
<a id="1908" class="Comment">--   f : (x : X) → A x x (refl x)</a>
<a id="1942" class="Comment">--   f x = refl (η x)</a>
<a id="1964" class="Comment">--   φ : (y x : X) (p : Id y x) → Id (η x) (y , p)</a>
<a id="2015" class="Comment">--   φ = J A f</a>
<a id="2030" class="Comment">--   g : (x : X) (σ : singletonType x) → Id (η x) σ</a>
<a id="2082" class="Comment">--   g x (y , p) = φ y x p</a>
<a id="2109" class="Comment">--   h : (x : X) → Σ \(c : singletonType x) → (σ : singletonType x) → Id c σ</a>
<a id="2186" class="Comment">--   h x = (η x , g x)</a>
<a id="2209" class="Comment">--</a>
<a id="2212" class="Comment">-- id : {U : Universe} (X : U ̇) → X → X</a>
<a id="2253" class="Comment">-- id X x = x</a>
<a id="2267" class="Comment">--</a>
<a id="2270" class="Comment">-- idIsEquiv : {U : Universe} (X : U ̇) → isEquiv(id X)</a>
<a id="2326" class="Comment">-- idIsEquiv X = g</a>
<a id="2345" class="Comment">--  where</a>
<a id="2355" class="Comment">--   g : (x : X) → isSingleton (fiber (id X) x)</a>
<a id="2403" class="Comment">--   g = singletonTypesAreSingletons</a>
<a id="2440" class="Comment">--</a>
<a id="2443" class="Comment">-- IdToEq : {U : Universe} (X Y : U ̇) → Id X Y → Eq X Y</a>
<a id="2500" class="Comment">-- IdToEq {U} = J A f</a>
<a id="2522" class="Comment">--  where</a>
<a id="2532" class="Comment">--   A : (X Y : U ̇) → Id X Y → U ̇</a>
<a id="2568" class="Comment">--   A X Y p = Eq X Y</a>
<a id="2590" class="Comment">--   f : (X : U ̇) → A X X (refl X)</a>
<a id="2626" class="Comment">--   f X = (id X , idIsEquiv X)</a>
<a id="2658" class="Comment">--</a>
<a id="2661" class="Comment">-- isUnivalent : (U : Universe) → U ′ ̇</a>
<a id="2701" class="Comment">-- isUnivalent U = (X Y : U ̇) → isEquiv(IdToEq X Y)</a>{% endraw %}</pre>

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
