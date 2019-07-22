---
src: ./src/plfa/Decidable.lagda.md
title     : "Decidable: 布尔值与判定过程"
layout    : page
prev      : /Quantifiers/
permalink : /Decidable/
next      : /Lists/
translators : ["Fangyi Zhou"]
progress  : 100
---

{% raw %}<pre class="Agda"><a id="181" class="Keyword">module</a> <a id="188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}" class="Module">plfa.Decidable</a> <a id="203" class="Keyword">where</a>
</pre>{% endraw %}
{::comment}
We have a choice as to how to represent relations:
as an inductive data type of _evidence_ that the relation holds,
or as a function that _computes_ whether the relation holds.
Here we explore the relation between these choices.
We first explore the familiar notion of _booleans_,
but later discover that these are best avoided in favour
of a new notion of _decidable_.
{:/}

我们在如何表示关系上可以有所选择：表示为其成立的*证明*（Evidence）的数据类型，
或者表示为一个*计算*（Compute）其是否成立的函数。我们在此探讨这两个选择直接的关系。
我们首先研究大家熟悉的*布尔值*（Boolean）记法，但是我们之后会发现，我们最好避免布尔值的记法，
而使用一种新的*可判定性*（Decidable）记法。

{::comment}
## Imports
{:/}

## 导入

{% raw %}<pre class="Agda"><a id="815" class="Keyword">import</a> <a id="822" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="860" class="Symbol">as</a> <a id="863" class="Module">Eq</a>
<a id="866" class="Keyword">open</a> <a id="871" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="874" class="Keyword">using</a> <a id="880" class="Symbol">(</a><a id="881" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="884" class="Symbol">;</a> <a id="886" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="890" class="Symbol">)</a>
<a id="892" class="Keyword">open</a> <a id="897" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a>
<a id="912" class="Keyword">open</a> <a id="917" class="Keyword">import</a> <a id="924" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="933" class="Keyword">using</a> <a id="939" class="Symbol">(</a><a id="940" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="941" class="Symbol">;</a> <a id="943" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="947" class="Symbol">;</a> <a id="949" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="952" class="Symbol">)</a>
<a id="954" class="Keyword">open</a> <a id="959" class="Keyword">import</a> <a id="966" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="979" class="Keyword">using</a> <a id="985" class="Symbol">(</a><a id="986" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="989" class="Symbol">)</a> <a id="991" class="Keyword">renaming</a> <a id="1000" class="Symbol">(</a><a id="1001" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="1005" class="Symbol">to</a> <a id="1008" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="1013" class="Symbol">)</a>
<a id="1015" class="Keyword">open</a> <a id="1020" class="Keyword">import</a> <a id="1027" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="1036" class="Keyword">using</a> <a id="1042" class="Symbol">(</a><a id="1043" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="1046" class="Symbol">;</a> <a id="1048" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a><a id="1052" class="Symbol">;</a> <a id="1054" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a><a id="1058" class="Symbol">)</a>
<a id="1060" class="Keyword">open</a> <a id="1065" class="Keyword">import</a> <a id="1072" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="1089" class="Keyword">using</a> <a id="1095" class="Symbol">(</a><a id="1096" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="1098" class="Symbol">)</a>
<a id="1100" class="Keyword">open</a> <a id="1105" class="Keyword">import</a> <a id="1112" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="1138" class="Keyword">using</a> <a id="1144" class="Symbol">()</a>
  <a id="1149" class="Keyword">renaming</a> <a id="1158" class="Symbol">(</a><a id="1159" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#809" class="Function">contradiction</a> <a id="1173" class="Symbol">to</a> <a id="1176" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#809" class="Function">¬¬-intro</a><a id="1184" class="Symbol">)</a>
<a id="1186" class="Keyword">open</a> <a id="1191" class="Keyword">import</a> <a id="1198" href="https://agda.github.io/agda-stdlib/v1.1/Data.Unit.html" class="Module">Data.Unit</a> <a id="1208" class="Keyword">using</a> <a id="1214" class="Symbol">(</a><a id="1215" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Unit.html#137" class="Record">⊤</a><a id="1216" class="Symbol">;</a> <a id="1218" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a><a id="1220" class="Symbol">)</a>
<a id="1222" class="Keyword">open</a> <a id="1227" class="Keyword">import</a> <a id="1234" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="1245" class="Keyword">using</a> <a id="1251" class="Symbol">(</a><a id="1252" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="1253" class="Symbol">;</a> <a id="1255" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="1261" class="Symbol">)</a>
<a id="1263" class="Keyword">open</a> <a id="1268" class="Keyword">import</a> <a id="1275" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}" class="Module">plfa.Relations</a> <a id="1290" class="Keyword">using</a> <a id="1296" class="Symbol">(</a><a id="1297" href="plfa.Relations.html#26126" class="Datatype Operator">_&lt;_</a><a id="1300" class="Symbol">;</a> <a id="1302" href="plfa.Relations.html#26153" class="InductiveConstructor">z&lt;s</a><a id="1305" class="Symbol">;</a> <a id="1307" href="plfa.Relations.html#26210" class="InductiveConstructor">s&lt;s</a><a id="1310" class="Symbol">)</a>
<a id="1312" class="Keyword">open</a> <a id="1317" class="Keyword">import</a> <a id="1324" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}" class="Module">plfa.Isomorphism</a> <a id="1341" class="Keyword">using</a> <a id="1347" class="Symbol">(</a><a id="1348" href="plfa.Isomorphism.html#14837" class="Record Operator">_⇔_</a><a id="1351" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
## Evidence vs Computation
{:/}

## 证据 vs 计算

{::comment}
Recall that Chapter [Relations][plfa.Relations]
defined comparison as an inductive datatype,
which provides _evidence_ that one number
is less than or equal to another:
{:/}

回忆我们在 [Relations][plfa.Relations] 章节中将比较定义为一个归纳数据类型，
其提供了一个数小于或等于另外一个数的证明：

{% raw %}<pre class="Agda"><a id="1683" class="Keyword">infix</a> <a id="1689" class="Number">4</a> <a id="1691" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#1701" class="Datatype Operator">_≤_</a>

<a id="1696" class="Keyword">data</a> <a id="_≤_"></a><a id="1701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#1701" class="Datatype Operator">_≤_</a> <a id="1705" class="Symbol">:</a> <a id="1707" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="1709" class="Symbol">→</a> <a id="1711" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="1713" class="Symbol">→</a> <a id="1715" class="PrimitiveType">Set</a> <a id="1719" class="Keyword">where</a>

  <a id="_≤_.z≤n"></a><a id="1728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#1728" class="InductiveConstructor">z≤n</a> <a id="1732" class="Symbol">:</a> <a id="1734" class="Symbol">∀</a> <a id="1736" class="Symbol">{</a><a id="1737" href="plfa.Decidable.html#1737" class="Bound">n</a> <a id="1739" class="Symbol">:</a> <a id="1741" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1742" class="Symbol">}</a>
      <a id="1750" class="Comment">--------</a>
    <a id="1763" class="Symbol">→</a> <a id="1765" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="1770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#1701" class="Datatype Operator">≤</a> <a id="1772" href="plfa.Decidable.html#1737" class="Bound">n</a>

  <a id="_≤_.s≤s"></a><a id="1777" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#1777" class="InductiveConstructor">s≤s</a> <a id="1781" class="Symbol">:</a> <a id="1783" class="Symbol">∀</a> <a id="1785" class="Symbol">{</a><a id="1786" href="plfa.Decidable.html#1786" class="Bound">m</a> <a id="1788" href="plfa.Decidable.html#1788" class="Bound">n</a> <a id="1790" class="Symbol">:</a> <a id="1792" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1793" class="Symbol">}</a>
    <a id="1799" class="Symbol">→</a> <a id="1801" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#1786" class="Bound">m</a> <a id="1803" href="plfa.Decidable.html#1701" class="Datatype Operator">≤</a> <a id="1805" href="plfa.Decidable.html#1788" class="Bound">n</a>
      <a id="1813" class="Comment">-------------</a>
    <a id="1831" class="Symbol">→</a> <a id="1833" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1837" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#1786" class="Bound">m</a> <a id="1839" href="plfa.Decidable.html#1701" class="Datatype Operator">≤</a> <a id="1841" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1845" href="plfa.Decidable.html#1788" class="Bound">n</a>
</pre>{% endraw %}
{::comment}
For example, we can provide evidence that `2 ≤ 4`,
and show there is no possible evidence that `4 ≤ 2`:
{:/}

举例来说，我们提供 `2 ≤ 4` 成立的证明，也可以证明没有 `4 ≤ 2` 成立的证明。

{% raw %}<pre class="Agda"><a id="2≤4"></a><a id="2026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2026" class="Function">2≤4</a> <a id="2030" class="Symbol">:</a> <a id="2032" class="Number">2</a> <a id="2034" href="plfa.Decidable.html#1701" class="Datatype Operator">≤</a> <a id="2036" class="Number">4</a>
<a id="2038" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2026" class="Function">2≤4</a> <a id="2042" class="Symbol">=</a> <a id="2044" href="plfa.Decidable.html#1777" class="InductiveConstructor">s≤s</a> <a id="2048" class="Symbol">(</a><a id="2049" href="plfa.Decidable.html#1777" class="InductiveConstructor">s≤s</a> <a id="2053" href="plfa.Decidable.html#1728" class="InductiveConstructor">z≤n</a><a id="2056" class="Symbol">)</a>

<a id="¬4≤2"></a><a id="2059" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2059" class="Function">¬4≤2</a> <a id="2064" class="Symbol">:</a> <a id="2066" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="2068" class="Symbol">(</a><a id="2069" class="Number">4</a> <a id="2071" href="plfa.Decidable.html#1701" class="Datatype Operator">≤</a> <a id="2073" class="Number">2</a><a id="2074" class="Symbol">)</a>
<a id="2076" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2059" class="Function">¬4≤2</a> <a id="2081" class="Symbol">(</a><a id="2082" href="plfa.Decidable.html#1777" class="InductiveConstructor">s≤s</a> <a id="2086" class="Symbol">(</a><a id="2087" href="plfa.Decidable.html#1777" class="InductiveConstructor">s≤s</a> <a id="2091" class="Symbol">()))</a>
</pre>{% endraw %}
{::comment}
The occurrence of `()` attests to the fact that there is
no possible evidence for `2 ≤ 0`, which `z≤n` cannot match
(because `2` is not `zero`) and `s≤s` cannot match
(because `0` cannot match `suc n`).
{:/}

`()` 的出现表明了没有 `2 ≤ 0` 成立的证明：`z≤n` 不能匹配（因为 `2` 不是
`zero`），`s≤s` 也不能匹配（因为 `0` 不能匹配 `suc n`）。

{::comment}
An alternative, which may seem more familiar, is to define a
type of booleans:
{:/}

作为替代的定义，我们可以定义一个大家可能比较熟悉的布尔类型：

{% raw %}<pre class="Agda"><a id="2547" class="Keyword">data</a> <a id="Bool"></a><a id="2552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2552" class="Datatype">Bool</a> <a id="2557" class="Symbol">:</a> <a id="2559" class="PrimitiveType">Set</a> <a id="2563" class="Keyword">where</a>
  <a id="Bool.true"></a><a id="2571" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2571" class="InductiveConstructor">true</a>  <a id="2577" class="Symbol">:</a> <a id="2579" href="plfa.Decidable.html#2552" class="Datatype">Bool</a>
  <a id="Bool.false"></a><a id="2586" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2586" class="InductiveConstructor">false</a> <a id="2592" class="Symbol">:</a> <a id="2594" href="plfa.Decidable.html#2552" class="Datatype">Bool</a>
</pre>{% endraw %}
{::comment}
Given booleans, we can define a function of two numbers that
_computes_ to `true` if the comparison holds and to `false` otherwise:
{:/}

给定了布尔类型，我们可以定义一个两个数的函数在比较关系成立时来*计算*出 `true`，
否则计算出 `false`：

{% raw %}<pre class="Agda"><a id="2819" class="Keyword">infix</a> <a id="2825" class="Number">4</a> <a id="2827" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2833" class="Function Operator">_≤ᵇ_</a>

<a id="_≤ᵇ_"></a><a id="2833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2833" class="Function Operator">_≤ᵇ_</a> <a id="2838" class="Symbol">:</a> <a id="2840" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="2842" class="Symbol">→</a> <a id="2844" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="2846" class="Symbol">→</a> <a id="2848" href="plfa.Decidable.html#2552" class="Datatype">Bool</a>
<a id="2853" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="2858" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2833" class="Function Operator">≤ᵇ</a> <a id="2861" href="plfa.Decidable.html#2861" class="Bound">n</a>       <a id="2869" class="Symbol">=</a>  <a id="2872" href="plfa.Decidable.html#2571" class="InductiveConstructor">true</a>
<a id="2877" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="2881" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2881" class="Bound">m</a> <a id="2883" href="plfa.Decidable.html#2833" class="Function Operator">≤ᵇ</a> <a id="2886" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>   <a id="2893" class="Symbol">=</a>  <a id="2896" href="plfa.Decidable.html#2586" class="InductiveConstructor">false</a>
<a id="2902" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="2906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2906" class="Bound">m</a> <a id="2908" href="plfa.Decidable.html#2833" class="Function Operator">≤ᵇ</a> <a id="2911" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="2915" href="plfa.Decidable.html#2915" class="Bound">n</a>  <a id="2918" class="Symbol">=</a>  <a id="2921" href="plfa.Decidable.html#2906" class="Bound">m</a> <a id="2923" href="plfa.Decidable.html#2833" class="Function Operator">≤ᵇ</a> <a id="2926" href="plfa.Decidable.html#2915" class="Bound">n</a>
</pre>{% endraw %}
{::comment}
The first and last clauses of this definition resemble the two
constructors of the corresponding inductive datatype, while the
middle clause arises because there is no possible evidence that
`suc m ≤ zero` for any `m`.
For example, we can compute that `2 ≤ᵇ 4` holds,
and we can compute that `4 ≤ᵇ 2` does not hold:
{:/}

定义中的第一条与最后一条与归纳数据类型中的两个构造器相对应。因为对于任意的 `m`，不可能出现
`suc m ≤ zero` 的证明，我们使用中间一条定义来表示。
举个例子，我们可以计算 `2 ≤ᵇ 4` 成立，也可以计算 `4 ≤ᵇ 2` 不成立：

{% raw %}<pre class="Agda"><a id="3398" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#3398" class="Function">_</a> <a id="3400" class="Symbol">:</a> <a id="3402" class="Symbol">(</a><a id="3403" class="Number">2</a> <a id="3405" href="plfa.Decidable.html#2833" class="Function Operator">≤ᵇ</a> <a id="3408" class="Number">4</a><a id="3409" class="Symbol">)</a> <a id="3411" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="3413" href="plfa.Decidable.html#2571" class="InductiveConstructor">true</a>
<a id="3418" class="Symbol">_</a> <a id="3420" class="Symbol">=</a>
  <a id="3424" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="3434" class="Number">2</a> <a id="3436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2833" class="Function Operator">≤ᵇ</a> <a id="3439" class="Number">4</a>
  <a id="3443" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3451" class="Number">1</a> <a id="3453" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2833" class="Function Operator">≤ᵇ</a> <a id="3456" class="Number">3</a>
  <a id="3460" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3468" class="Number">0</a> <a id="3470" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2833" class="Function Operator">≤ᵇ</a> <a id="3473" class="Number">2</a>
  <a id="3477" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2571" class="InductiveConstructor">true</a>
  <a id="3492" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>

<a id="3495" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#3495" class="Function">_</a> <a id="3497" class="Symbol">:</a> <a id="3499" class="Symbol">(</a><a id="3500" class="Number">4</a> <a id="3502" href="plfa.Decidable.html#2833" class="Function Operator">≤ᵇ</a> <a id="3505" class="Number">2</a><a id="3506" class="Symbol">)</a> <a id="3508" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="3510" href="plfa.Decidable.html#2586" class="InductiveConstructor">false</a>
<a id="3516" class="Symbol">_</a> <a id="3518" class="Symbol">=</a>
  <a id="3522" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="3532" class="Number">4</a> <a id="3534" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2833" class="Function Operator">≤ᵇ</a> <a id="3537" class="Number">2</a>
  <a id="3541" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3549" class="Number">3</a> <a id="3551" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2833" class="Function Operator">≤ᵇ</a> <a id="3554" class="Number">1</a>
  <a id="3558" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3566" class="Number">2</a> <a id="3568" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2833" class="Function Operator">≤ᵇ</a> <a id="3571" class="Number">0</a>
  <a id="3575" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3583" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2586" class="InductiveConstructor">false</a>
  <a id="3591" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}
{::comment}
In the first case, it takes two steps to reduce the first argument to zero,
and one more step to compute true, corresponding to the two uses of `s≤s`
and the one use of `z≤n` when providing evidence that `2 ≤ 4`.
In the second case, it takes two steps to reduce the second argument to zero,
and one more step to compute false, corresponding to the two uses of `s≤s`
and the one use of `()` when showing there can be no evidence that `4 ≤ 2`.
{:/}

在第一种情况中，我们需要两步来将第一个参数降低到 0，再用一步来计算出真，这对应着我们需要
使用两次 `s≤s` 和一次 `z≤n` 来证明 `2 ≤ 4`。
在第二种情况中，我们需要两步来将第二个参数降低到 0，再用一步来计算出假，这对应着我们需要
使用两次 `s≤s` 和一次 `()` 来说明没有 `4 ≤ 2` 的证明。

{::comment}
## Relating evidence and computation
{:/}

## 将证明与计算相联系

{::comment}
We would hope to be able to show these two approaches are related, and
indeed we can.  First, we define a function that lets us map from the
computation world to the evidence world:
{:/}

我们希望能够证明这两种方法是有联系的，而我们的确可以。
首先，我们定义一个函数来把计算世界映射到证明世界：

{% raw %}<pre class="Agda"><a id="T"></a><a id="4552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#4552" class="Function">T</a> <a id="4554" class="Symbol">:</a> <a id="4556" href="plfa.Decidable.html#2552" class="Datatype">Bool</a> <a id="4561" class="Symbol">→</a> <a id="4563" class="PrimitiveType">Set</a>
<a id="4567" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#4552" class="Function">T</a> <a id="4569" href="plfa.Decidable.html#2571" class="InductiveConstructor">true</a>   <a id="4576" class="Symbol">=</a>  <a id="4579" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Unit.html#137" class="Record">⊤</a>
<a id="4581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#4552" class="Function">T</a> <a id="4583" href="plfa.Decidable.html#2586" class="InductiveConstructor">false</a>  <a id="4590" class="Symbol">=</a>  <a id="4593" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
</pre>{% endraw %}
{::comment}
Recall that `⊤` is the unit type which contains the single element `tt`,
and the `⊥` is the empty type which contains no values.  (Also note that
`T` is a capital letter t, and distinct from `⊤`.)  If `b` is of type `Bool`,
then `tt` provides evidence that `T b` holds if `b` is true, while there is
no possible evidence that `T b` holds if `b` is false.
{:/}

回忆到 `⊤` 是只有一个元素 `tt` 的单元类型，`⊥` 是没有值的空类型。（注意 `T` 是大写字母 `t`，
与 `⊤` 不同。）如果 `b` 是 `Bool` 类型的，那么如果 `b` 为真，`tt` 可以提供 `T b` 成立的证明；
如果 `b` 为假，则不可能有 `T b` 成立的证明。

{::comment}
Another way to put this is that `T b` is inhabited exactly when `b ≡ true`
is inhabited.
In the forward direction, we need to do a case analysis on the boolean `b`:
{:/}

换句话说，`T b` 当且仅当 `b ≡ true` 成立时成立。在向前的方向，我们需要针对 `b` 进行情况分析：

{% raw %}<pre class="Agda"><a id="T→≡"></a><a id="5374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#5374" class="Function">T→≡</a> <a id="5378" class="Symbol">:</a> <a id="5380" class="Symbol">∀</a> <a id="5382" class="Symbol">(</a><a id="5383" href="plfa.Decidable.html#5383" class="Bound">b</a> <a id="5385" class="Symbol">:</a> <a id="5387" href="plfa.Decidable.html#2552" class="Datatype">Bool</a><a id="5391" class="Symbol">)</a> <a id="5393" class="Symbol">→</a> <a id="5395" href="plfa.Decidable.html#4552" class="Function">T</a> <a id="5397" href="plfa.Decidable.html#5383" class="Bound">b</a> <a id="5399" class="Symbol">→</a> <a id="5401" href="plfa.Decidable.html#5383" class="Bound">b</a> <a id="5403" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5405" href="plfa.Decidable.html#2571" class="InductiveConstructor">true</a>
<a id="5410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#5374" class="Function">T→≡</a> <a id="5414" href="plfa.Decidable.html#2571" class="InductiveConstructor">true</a> <a id="5419" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a>   <a id="5424" class="Symbol">=</a>  <a id="5427" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="5432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#5374" class="Function">T→≡</a> <a id="5436" href="plfa.Decidable.html#2586" class="InductiveConstructor">false</a> <a id="5442" class="Symbol">()</a>
</pre>{% endraw %}
{::comment}
If `b` is true then `T b` is inhabited by `tt` and `b ≡ true` is inhabited
by `refl`, while if `b` is false then `T b` in uninhabited.
{:/}

如果 `b` 为真，那么 `T b` 由 `tt` 证明，`b ≡ true` 由 `refl` 证明。
当 `b` 为假，那么 `T b` 无法证明。

{::comment}
In the reverse direction, there is no need for a case analysis on the boolean `b`:
{:/}

在向后的方向，不需要针对布尔值 `b` 的情况分析：

{% raw %}<pre class="Agda"><a id="≡→T"></a><a id="5814" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#5814" class="Function">≡→T</a> <a id="5818" class="Symbol">:</a> <a id="5820" class="Symbol">∀</a> <a id="5822" class="Symbol">{</a><a id="5823" href="plfa.Decidable.html#5823" class="Bound">b</a> <a id="5825" class="Symbol">:</a> <a id="5827" href="plfa.Decidable.html#2552" class="Datatype">Bool</a><a id="5831" class="Symbol">}</a> <a id="5833" class="Symbol">→</a> <a id="5835" href="plfa.Decidable.html#5823" class="Bound">b</a> <a id="5837" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5839" href="plfa.Decidable.html#2571" class="InductiveConstructor">true</a> <a id="5844" class="Symbol">→</a> <a id="5846" href="plfa.Decidable.html#4552" class="Function">T</a> <a id="5848" href="plfa.Decidable.html#5823" class="Bound">b</a>
<a id="5850" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#5814" class="Function">≡→T</a> <a id="5854" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>  <a id="5860" class="Symbol">=</a>  <a id="5863" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a>
</pre>{% endraw %}
{::comment}
If `b ≡ true` is inhabited by `refl` we know that `b` is `true` and
hence `T b` is inhabited by `tt`.
{:/}

如果 `b ≡ true` 由 `refl` 证明，我们知道 `b` 是 `true`，因此 `T b` 由 `tt` 证明。

{::comment}
Now we can show that `T (m ≤ᵇ n)` is inhabited exactly when `m ≤ n` is inhabited.
{:/}

现在我们可以证明 `T (m ≤ᵇ n)` 当且仅当 `m ≤ n` 成立时成立。

{::comment}
In the forward direction, we consider the three clauses in the definition
of `_≤ᵇ_`:
{:/}

在向前的方向，我们考虑 `_≤ᵇ_` 定义中的三条语句：

{% raw %}<pre class="Agda"><a id="≤ᵇ→≤"></a><a id="6336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#6336" class="Function">≤ᵇ→≤</a> <a id="6341" class="Symbol">:</a> <a id="6343" class="Symbol">∀</a> <a id="6345" class="Symbol">(</a><a id="6346" href="plfa.Decidable.html#6346" class="Bound">m</a> <a id="6348" href="plfa.Decidable.html#6348" class="Bound">n</a> <a id="6350" class="Symbol">:</a> <a id="6352" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="6353" class="Symbol">)</a> <a id="6355" class="Symbol">→</a> <a id="6357" href="plfa.Decidable.html#4552" class="Function">T</a> <a id="6359" class="Symbol">(</a><a id="6360" href="plfa.Decidable.html#6346" class="Bound">m</a> <a id="6362" href="plfa.Decidable.html#2833" class="Function Operator">≤ᵇ</a> <a id="6365" href="plfa.Decidable.html#6348" class="Bound">n</a><a id="6366" class="Symbol">)</a> <a id="6368" class="Symbol">→</a> <a id="6370" href="plfa.Decidable.html#6346" class="Bound">m</a> <a id="6372" href="plfa.Decidable.html#1701" class="Datatype Operator">≤</a> <a id="6374" href="plfa.Decidable.html#6348" class="Bound">n</a>
<a id="6376" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#6336" class="Function">≤ᵇ→≤</a> <a id="6381" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="6389" href="plfa.Decidable.html#6389" class="Bound">n</a>       <a id="6397" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a>  <a id="6401" class="Symbol">=</a>  <a id="6404" href="plfa.Decidable.html#1728" class="InductiveConstructor">z≤n</a>
<a id="6408" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#6336" class="Function">≤ᵇ→≤</a> <a id="6413" class="Symbol">(</a><a id="6414" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="6418" href="plfa.Decidable.html#6418" class="Bound">m</a><a id="6419" class="Symbol">)</a> <a id="6421" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="6429" class="Symbol">()</a>
<a id="6432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#6336" class="Function">≤ᵇ→≤</a> <a id="6437" class="Symbol">(</a><a id="6438" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="6442" href="plfa.Decidable.html#6442" class="Bound">m</a><a id="6443" class="Symbol">)</a> <a id="6445" class="Symbol">(</a><a id="6446" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="6450" href="plfa.Decidable.html#6450" class="Bound">n</a><a id="6451" class="Symbol">)</a> <a id="6453" href="plfa.Decidable.html#6453" class="Bound">t</a>   <a id="6457" class="Symbol">=</a>  <a id="6460" href="plfa.Decidable.html#1777" class="InductiveConstructor">s≤s</a> <a id="6464" class="Symbol">(</a><a id="6465" href="plfa.Decidable.html#6336" class="Function">≤ᵇ→≤</a> <a id="6470" href="plfa.Decidable.html#6442" class="Bound">m</a> <a id="6472" href="plfa.Decidable.html#6450" class="Bound">n</a> <a id="6474" href="plfa.Decidable.html#6453" class="Bound">t</a><a id="6475" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
In the first clause, we immediately have that `zero ≤ᵇ n` is
true, so `T (m ≤ᵇ n)` is evidenced by `tt`, and correspondingly `m ≤ n` is
evidenced by `z≤n`. In the middle clause, we immediately have that
`suc m ≤ᵇ zero` is false, and hence `T (m ≤ᵇ n)` is empty, so we need
not provide evidence that `m ≤ n`, which is just as well since there is no
such evidence.  In the last clause, we have that `suc m ≤ᵇ suc n` recurses
to `m ≤ᵇ n`.  We let `t` be the evidence of `T (suc m ≤ᵇ suc n)` if it exists,
which, by definition of `_≤ᵇ_`, will also be evidence of `T (m ≤ᵇ n)`.
We recursively invoke the function to get evidence that `m ≤ n`, which
`s≤s` converts to evidence that `suc m ≤ suc n`.
{:/}

第一条语句中，我们立即可以得出 `zero ≤ᵇ n` 为真，所以 `T (m ≤ᵇ n)` 由 `tt` 而得，
相对应地 `m ≤ n` 由 `z≤n` 而证明。在中间的语句中，我们立刻得出 `suc m ≤ᵇ zero` 为假，则
`T (m ≤ᵇ n)` 为空，因此我们无需证明 `m ≤ n`，同时也不存在这样的证明。在最后的语句中，我们对于
`suc m ≤ᵇ suc n` 递归至 `m ≤ᵇ n`。令 `t` 为 `T (suc m ≤ᵇ suc n)` 的证明，如果其存在。
根据 `_≤ᵇ_` 的定义，这也是 `T (m ≤ᵇ n)` 的证明。我们递归地应用函数来获得 `m ≤ n` 的证明，再使用
`s≤s` 将其转换成为 `suc m ≤ suc n` 的证明。

{::comment}
In the reverse direction, we consider the possible forms of evidence
that `m ≤ n`:
{:/}

在向后的方向，我们考虑 `m ≤ n` 成立证明的可能形式：

{% raw %}<pre class="Agda"><a id="≤→≤ᵇ"></a><a id="7676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#7676" class="Function">≤→≤ᵇ</a> <a id="7681" class="Symbol">:</a> <a id="7683" class="Symbol">∀</a> <a id="7685" class="Symbol">{</a><a id="7686" href="plfa.Decidable.html#7686" class="Bound">m</a> <a id="7688" href="plfa.Decidable.html#7688" class="Bound">n</a> <a id="7690" class="Symbol">:</a> <a id="7692" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="7693" class="Symbol">}</a> <a id="7695" class="Symbol">→</a> <a id="7697" href="plfa.Decidable.html#7686" class="Bound">m</a> <a id="7699" href="plfa.Decidable.html#1701" class="Datatype Operator">≤</a> <a id="7701" href="plfa.Decidable.html#7688" class="Bound">n</a> <a id="7703" class="Symbol">→</a> <a id="7705" href="plfa.Decidable.html#4552" class="Function">T</a> <a id="7707" class="Symbol">(</a><a id="7708" href="plfa.Decidable.html#7686" class="Bound">m</a> <a id="7710" href="plfa.Decidable.html#2833" class="Function Operator">≤ᵇ</a> <a id="7713" href="plfa.Decidable.html#7688" class="Bound">n</a><a id="7714" class="Symbol">)</a>
<a id="7716" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#7676" class="Function">≤→≤ᵇ</a> <a id="7721" href="plfa.Decidable.html#1728" class="InductiveConstructor">z≤n</a>        <a id="7732" class="Symbol">=</a>  <a id="7735" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a>
<a id="7738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#7676" class="Function">≤→≤ᵇ</a> <a id="7743" class="Symbol">(</a><a id="7744" href="plfa.Decidable.html#1777" class="InductiveConstructor">s≤s</a> <a id="7748" href="plfa.Decidable.html#7748" class="Bound">m≤n</a><a id="7751" class="Symbol">)</a>  <a id="7754" class="Symbol">=</a>  <a id="7757" href="plfa.Decidable.html#7676" class="Function">≤→≤ᵇ</a> <a id="7762" href="plfa.Decidable.html#7748" class="Bound">m≤n</a>
</pre>{% endraw %}
{::comment}
If the evidence is `z≤n` then we immediately have that `zero ≤ᵇ n` is
true, so `T (m ≤ᵇ n)` is evidenced by `tt`. If the evidence is `s≤s`
applied to `m≤n`, then `suc m ≤ᵇ suc n` reduces to `m ≤ᵇ n`, and we
may recursively invoke the function to produce evidence that `T (m ≤ᵇ n)`.
{:/}

如果证明是 `z≤n`，我们立即可以得到 `zero ≤ᵇ n` 为真，所以 `T (m ≤ᵇ n)` 由 `tt` 证明。
如果证明是 `s≤s` 作用于 `m≤n`，那么 `suc m ≤ᵇ suc n` 规约到 `m ≤ᵇ n`，我们可以递归地使用函数
来获得 `T (m ≤ᵇ n)` 的证明。

{::comment}
The forward proof has one more clause than the reverse proof,
precisely because in the forward proof we need clauses corresponding to
the comparison yielding both true and false, while in the reverse proof
we only need clauses corresponding to the case where there is evidence
that the comparison holds.  This is exactly why we tend to prefer the
evidence formulation to the computation formulation, because it allows
us to do less work: we consider only cases where the relation holds,
and can ignore those where it does not.
{:/}

向前方向的证明比向后方向的证明多一条语句，因为在向前方向的证明中我们需要考虑比较结果为真和假
的语句，而向后方向的证明只需要考虑比较成立的语句。这也是为什么我们比起计算的形式，更加偏爱证明的形式，
因为这样让我们做更少的工作：我们只需要考虑关系成立时的情况，而可以忽略不成立的情况。

{::comment}
On the other hand, sometimes the computation formulation may be just what
we want.  Given a non-obvious relation over large values, it might be
handy to have the computer work out the answer for us.  Fortunately,
rather than choosing between _evidence_ and _computation_,
there is a way to get the benefits of both.
{:/}

从另一个角度来说，有时计算的性质可能是我们所需要的。给定一个在很多值之上的不显然的关系，
可能使用电脑来计算出答案会更加方便。幸运的是，比起需要自行选择*证明*和*计算*，我们有一种方法来获得
两种方法的优点。

{::comment}
## The best of both worlds
{:/}

## 取二者之精华

{::comment}
A function that returns a boolean returns exactly a single bit of information:
does the relation hold or does it not? Conversely, the evidence approach tells
us exactly why the relation holds, but we are responsible for generating the
evidence.  But it is easy to define a type that combines the benefits of
both approaches.  It is called `Dec A`, where `Dec` is short for _decidable_:
{:/}

一个返回布尔值的函数提供恰好一比特的信息：这个关系成立或是不成立。相反地，证明的形式告诉我们
为什么这个关系成立，但是我们需要自行完成这样的证明。但是我们可以简单地来定义一个类型来取二者之精华。
我们把它叫做：`Dec A`，其中 `Dec` 是*可判定的*（Decidable）的意思。

{% raw %}<pre class="Agda"><a id="9963" class="Keyword">data</a> <a id="Dec"></a><a id="9968" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#9968" class="Datatype">Dec</a> <a id="9972" class="Symbol">(</a><a id="9973" href="plfa.Decidable.html#9973" class="Bound">A</a> <a id="9975" class="Symbol">:</a> <a id="9977" class="PrimitiveType">Set</a><a id="9980" class="Symbol">)</a> <a id="9982" class="Symbol">:</a> <a id="9984" class="PrimitiveType">Set</a> <a id="9988" class="Keyword">where</a>
  <a id="Dec.yes"></a><a id="9996" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#9996" class="InductiveConstructor">yes</a> <a id="10000" class="Symbol">:</a>   <a id="10004" href="plfa.Decidable.html#9973" class="Bound">A</a> <a id="10006" class="Symbol">→</a> <a id="10008" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="10012" href="plfa.Decidable.html#9973" class="Bound">A</a>
  <a id="Dec.no"></a><a id="10016" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10016" class="InductiveConstructor">no</a>  <a id="10020" class="Symbol">:</a> <a id="10022" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="10024" href="plfa.Decidable.html#9973" class="Bound">A</a> <a id="10026" class="Symbol">→</a> <a id="10028" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="10032" href="plfa.Decidable.html#9973" class="Bound">A</a>
</pre>{% endraw %}
{::comment}
Like booleans, the type has two constructors.  A value of type `Dec A`
is either of the form `yes x`, where `x` provides evidence that `A` holds,
or of the form `no ¬x`, where `¬x` provides evidence that `A` cannot hold
(that is, `¬x` is a function which given evidence of `A` yields a contradiction).
{:/}

如果布尔值，这个类型有两个构造器。一个 `Dec A` 类型的值要么是以 `yes x` 的形式，其中 `x` 提供 `A`
成立的证明，或者是以 `no ¬x` 的形式，其中 `x` 提供了 `A` 无法成立的证明。（也就是说，`¬x` 是一个给定
`A` 成立的证据，返回矛盾的函数）

{::comment}
For example, we define a function `_≤?_` which given two numbers decides whether one
is less than or equal to the other, and provides evidence to justify its conclusion.
{:/}

比如说，我们定义一个函数 `_≤?_`，给定两个数，判定是否一个数小于等于另一个，并提供证明来说明结论。

{::comment}
First, we introduce two functions useful for constructing evidence that
an inequality does not hold:
{:/}

首先，我们使用两个有用的函数，用于构造不等式不成立的证明：

{% raw %}<pre class="Agda"><a id="¬s≤z"></a><a id="10901" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10901" class="Function">¬s≤z</a> <a id="10906" class="Symbol">:</a> <a id="10908" class="Symbol">∀</a> <a id="10910" class="Symbol">{</a><a id="10911" href="plfa.Decidable.html#10911" class="Bound">m</a> <a id="10913" class="Symbol">:</a> <a id="10915" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10916" class="Symbol">}</a> <a id="10918" class="Symbol">→</a> <a id="10920" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="10922" class="Symbol">(</a><a id="10923" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="10927" href="plfa.Decidable.html#10911" class="Bound">m</a> <a id="10929" href="plfa.Decidable.html#1701" class="Datatype Operator">≤</a> <a id="10931" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="10935" class="Symbol">)</a>
<a id="10937" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10901" class="Function">¬s≤z</a> <a id="10942" class="Symbol">()</a>

<a id="¬s≤s"></a><a id="10946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10946" class="Function">¬s≤s</a> <a id="10951" class="Symbol">:</a> <a id="10953" class="Symbol">∀</a> <a id="10955" class="Symbol">{</a><a id="10956" href="plfa.Decidable.html#10956" class="Bound">m</a> <a id="10958" href="plfa.Decidable.html#10958" class="Bound">n</a> <a id="10960" class="Symbol">:</a> <a id="10962" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10963" class="Symbol">}</a> <a id="10965" class="Symbol">→</a> <a id="10967" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="10969" class="Symbol">(</a><a id="10970" href="plfa.Decidable.html#10956" class="Bound">m</a> <a id="10972" href="plfa.Decidable.html#1701" class="Datatype Operator">≤</a> <a id="10974" href="plfa.Decidable.html#10958" class="Bound">n</a><a id="10975" class="Symbol">)</a> <a id="10977" class="Symbol">→</a> <a id="10979" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="10981" class="Symbol">(</a><a id="10982" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="10986" href="plfa.Decidable.html#10956" class="Bound">m</a> <a id="10988" href="plfa.Decidable.html#1701" class="Datatype Operator">≤</a> <a id="10990" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="10994" href="plfa.Decidable.html#10958" class="Bound">n</a><a id="10995" class="Symbol">)</a>
<a id="10997" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10946" class="Function">¬s≤s</a> <a id="11002" href="plfa.Decidable.html#11002" class="Bound">¬m≤n</a> <a id="11007" class="Symbol">(</a><a id="11008" href="plfa.Decidable.html#1777" class="InductiveConstructor">s≤s</a> <a id="11012" href="plfa.Decidable.html#11012" class="Bound">m≤n</a><a id="11015" class="Symbol">)</a> <a id="11017" class="Symbol">=</a> <a id="11019" href="plfa.Decidable.html#11002" class="Bound">¬m≤n</a> <a id="11024" href="plfa.Decidable.html#11012" class="Bound">m≤n</a>
</pre>{% endraw %}
{::comment}
The first of these asserts that `¬ (suc m ≤ zero)`, and follows by
absurdity, since any evidence of inequality has the form `zero ≤ n`
or `suc m ≤ suc n`, neither of which match `suc m ≤ zero`. The second
of these takes evidence `¬m≤n` of `¬ (m ≤ n)` and returns a proof of
`¬ (suc m ≤ suc n)`.  Any evidence of `suc m ≤ suc n` must have the
form `s≤s m≤n` where `m≤n` is evidence that `m ≤ n`.  Hence, we have
a contradiction, evidenced by `¬m≤n m≤n`.
{:/}

第一个函数断言了 `¬ (suc m ≤ zero)`，由荒谬可得。因为每个不等式的成立证明必须是
`zero ≤ n` 或者 `suc m ≤ suc n` 的形式，两者都无法匹配 `suc m ≤ zero`。
第二个函数取 `¬ (m ≤ n)` 的证明 `¬m≤n`，返回 `¬ (suc m ≤ suc n)` 的证明。
所有形如 `suc m ≤ suc n` 的证明必须是以 `s≤s m≤n` 的形式给出。因此我们可以构造一个
矛盾，以 `¬m≤n m≤n` 来证明。

{::comment}
Using these, it is straightforward to decide an inequality:
{:/}

使用这些，我们可以直接的判定不等关系：

{% raw %}<pre class="Agda"><a id="_≤?_"></a><a id="11851" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#11851" class="Function Operator">_≤?_</a> <a id="11856" class="Symbol">:</a> <a id="11858" class="Symbol">∀</a> <a id="11860" class="Symbol">(</a><a id="11861" href="plfa.Decidable.html#11861" class="Bound">m</a> <a id="11863" href="plfa.Decidable.html#11863" class="Bound">n</a> <a id="11865" class="Symbol">:</a> <a id="11867" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11868" class="Symbol">)</a> <a id="11870" class="Symbol">→</a> <a id="11872" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="11876" class="Symbol">(</a><a id="11877" href="plfa.Decidable.html#11861" class="Bound">m</a> <a id="11879" href="plfa.Decidable.html#1701" class="Datatype Operator">≤</a> <a id="11881" href="plfa.Decidable.html#11863" class="Bound">n</a><a id="11882" class="Symbol">)</a>
<a id="11884" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>  <a id="11890" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#11851" class="Function Operator">≤?</a> <a id="11893" href="plfa.Decidable.html#11893" class="Bound">n</a>                   <a id="11913" class="Symbol">=</a>  <a id="11916" href="plfa.Decidable.html#9996" class="InductiveConstructor">yes</a> <a id="11920" href="plfa.Decidable.html#1728" class="InductiveConstructor">z≤n</a>
<a id="11924" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#11928" class="Bound">m</a> <a id="11930" href="plfa.Decidable.html#11851" class="Function Operator">≤?</a> <a id="11933" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>                <a id="11953" class="Symbol">=</a>  <a id="11956" href="plfa.Decidable.html#10016" class="InductiveConstructor">no</a> <a id="11959" href="plfa.Decidable.html#10901" class="Function">¬s≤z</a>
<a id="11964" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11968" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#11968" class="Bound">m</a> <a id="11970" href="plfa.Decidable.html#11851" class="Function Operator">≤?</a> <a id="11973" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11977" href="plfa.Decidable.html#11977" class="Bound">n</a> <a id="11979" class="Keyword">with</a> <a id="11984" href="plfa.Decidable.html#11968" class="Bound">m</a> <a id="11986" href="plfa.Decidable.html#11851" class="Function Operator">≤?</a> <a id="11989" href="plfa.Decidable.html#11977" class="Bound">n</a>
<a id="11991" class="Symbol">...</a>               <a id="12009" class="Symbol">|</a> <a id="12011" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#9996" class="InductiveConstructor">yes</a> <a id="12015" href="plfa.Decidable.html#12015" class="Bound">m≤n</a>  <a id="12020" class="Symbol">=</a>  <a id="12023" href="plfa.Decidable.html#9996" class="InductiveConstructor">yes</a> <a id="12027" class="Symbol">(</a><a id="12028" href="plfa.Decidable.html#1777" class="InductiveConstructor">s≤s</a> <a id="12032" href="plfa.Decidable.html#12015" class="Bound">m≤n</a><a id="12035" class="Symbol">)</a>
<a id="12037" class="Symbol">...</a>               <a id="12055" class="Symbol">|</a> <a id="12057" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10016" class="InductiveConstructor">no</a> <a id="12060" href="plfa.Decidable.html#12060" class="Bound">¬m≤n</a>  <a id="12066" class="Symbol">=</a>  <a id="12069" href="plfa.Decidable.html#10016" class="InductiveConstructor">no</a> <a id="12072" class="Symbol">(</a><a id="12073" href="plfa.Decidable.html#10946" class="Function">¬s≤s</a> <a id="12078" href="plfa.Decidable.html#12060" class="Bound">¬m≤n</a><a id="12082" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
As with `_≤ᵇ_`, the definition has three clauses.  In the first
clause, it is immediate that `zero ≤ n` holds, and it is evidenced by
`z≤n`.  In the second clause, it is immediate that `suc m ≤ zero` does
not hold, and it is evidenced by `¬s≤z`.
In the third clause, to decide whether `suc m ≤ suc n` holds we
recursively invoke `m ≤? n`.  There are two possibilities.  In the
`yes` case it returns evidence `m≤n` that `m ≤ n`, and `s≤s m≤n`
provides evidence that `suc m ≤ suc n`.  In the `no` case it returns
evidence `¬m≤n` that `¬ (m ≤ n)`, and `¬s≤s ¬m≤n` provides evidence
that `¬ (suc m ≤ suc n)`.
{:/}

与 `_≤ᵇ_` 一样，定义有三条语句。第一条语句中，`zero ≤ n` 立即成立，由 `z≤n` 证明。
第二条语句中，`suc m ≤ zero` 立即不成立，由 `¬s≤z` 证明。
第三条语句中，我们需要递归地应用 `m ≤? n`。有两种可能性，在 `yes` 的情况中，它会返回
`m ≤ n` 的证明 `m≤n`，所以 `s≤s m≤n` 即可作为 `suc m ≤ suc n` 的证明；在 `no` 的情况中，
它会返回 `¬ (m ≤ n)` 的证明 `¬m≤n`，所以 `¬s≤s ¬m≤n` 即可作为 `¬ (suc m ≤ suc n)` 的证明。

{::comment}
When we wrote `_≤ᵇ_`, we had to write two other functions, `≤ᵇ→≤` and `≤→≤ᵇ`,
in order to show that it was correct.  In contrast, the definition of `_≤?_`
proves itself correct, as attested to by its type.  The code of `_≤?_`
is far more compact than the combined code of `_≤ᵇ_`, `≤ᵇ→≤`, and `≤→≤ᵇ`.
As we will later show, if you really want the latter three, it is easy
to derive them from `_≤?_`.
{:/}

当我们写 `_≤ᵇ_` 时，我们必须写两个其他的函数 `≤ᵇ→≤` 和 `≤→≤ᵇ` 来证明其正确性。
作为对比，`_≤?_` 的定义自身就证明了其正确性，由类型即可得知。`_≤?_` 的代码也比
`_≤ᵇ_`、`≤ᵇ→≤` 和 `≤→≤ᵇ` 加起来要简洁的多。我们稍后将会证明，如果我们需要后三者，
我们亦可简单地从 `_≤?_` 中派生出来。

{::comment}
We can use our new function to _compute_ the _evidence_ that earlier we had to
think up on our own:
{:/}

我们可以使用我们新的函数来*计算*出我们之前需要自己想出来的*证明*。

{% raw %}<pre class="Agda"><a id="13753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#13753" class="Function">_</a> <a id="13755" class="Symbol">:</a> <a id="13757" class="Number">2</a> <a id="13759" href="plfa.Decidable.html#11851" class="Function Operator">≤?</a> <a id="13762" class="Number">4</a> <a id="13764" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="13766" href="plfa.Decidable.html#9996" class="InductiveConstructor">yes</a> <a id="13770" class="Symbol">(</a><a id="13771" href="plfa.Decidable.html#1777" class="InductiveConstructor">s≤s</a> <a id="13775" class="Symbol">(</a><a id="13776" href="plfa.Decidable.html#1777" class="InductiveConstructor">s≤s</a> <a id="13780" href="plfa.Decidable.html#1728" class="InductiveConstructor">z≤n</a><a id="13783" class="Symbol">))</a>
<a id="13786" class="Symbol">_</a> <a id="13788" class="Symbol">=</a> <a id="13790" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="13796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#13796" class="Function">_</a> <a id="13798" class="Symbol">:</a> <a id="13800" class="Number">4</a> <a id="13802" href="plfa.Decidable.html#11851" class="Function Operator">≤?</a> <a id="13805" class="Number">2</a> <a id="13807" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="13809" href="plfa.Decidable.html#10016" class="InductiveConstructor">no</a> <a id="13812" class="Symbol">(</a><a id="13813" href="plfa.Decidable.html#10946" class="Function">¬s≤s</a> <a id="13818" class="Symbol">(</a><a id="13819" href="plfa.Decidable.html#10946" class="Function">¬s≤s</a> <a id="13824" href="plfa.Decidable.html#10901" class="Function">¬s≤z</a><a id="13828" class="Symbol">))</a>
<a id="13831" class="Symbol">_</a> <a id="13833" class="Symbol">=</a> <a id="13835" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
You can check that Agda will indeed compute these values.  Typing
`C-c C-n` and providing `2 ≤? 4` or `4 ≤? 2` as the requested expression
causes Agda to print the values given above.
{:/}

你可以验证 Agda 的确计算出了这些值。输入 `C-c C-n` 并给出 `2 ≤? 4` 或者 `4 ≤? 2` 作为
需要的表达式，Agda 会输出如上的值。

{::comment}
(A subtlety: if we do not define `¬s≤z` and `¬s≤s` as top-level functions,
but instead use inline anonymous functions then Agda may have
trouble normalising evidence of negation.)
{:/}

（小细节：如果我们不把 `¬s≤z` 和 `¬s≤s` 作为顶层函数来定义，而是使用内嵌的匿名函数，
Agda 可能会在规范化否定的证明中出现问题。）


{::comment}
#### Exercise `_<?_` (recommended)
{:/}

#### 练习 `_<?_` （推荐）

{::comment}
Analogous to the function above, define a function to decide strict inequality:
{:/}

与上面的函数相似，定义一个判定严格不等性的函数：

{% raw %}<pre class="Agda"><a id="14609" class="Keyword">postulate</a>
  <a id="_&lt;?_"></a><a id="14621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#14621" class="Postulate Operator">_&lt;?_</a> <a id="14626" class="Symbol">:</a> <a id="14628" class="Symbol">∀</a> <a id="14630" class="Symbol">(</a><a id="14631" href="plfa.Decidable.html#14631" class="Bound">m</a> <a id="14633" href="plfa.Decidable.html#14633" class="Bound">n</a> <a id="14635" class="Symbol">:</a> <a id="14637" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="14638" class="Symbol">)</a> <a id="14640" class="Symbol">→</a> <a id="14642" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="14646" class="Symbol">(</a><a id="14647" href="plfa.Decidable.html#14631" class="Bound">m</a> <a id="14649" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26126" class="Datatype Operator">&lt;</a> <a id="14651" href="plfa.Decidable.html#14633" class="Bound">n</a><a id="14652" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
{% raw %}<pre class="Agda"><a id="14675" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="14712" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `_≡ℕ?_`
{:/}

#### 练习 `_≡ℕ?_`

{::comment}
Define a function to decide whether two naturals are equal:
{:/}

定义一个函数来判定两个自然数是否相等。

{% raw %}<pre class="Agda"><a id="14890" class="Keyword">postulate</a>
  <a id="_≡ℕ?_"></a><a id="14902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#14902" class="Postulate Operator">_≡ℕ?_</a> <a id="14908" class="Symbol">:</a> <a id="14910" class="Symbol">∀</a> <a id="14912" class="Symbol">(</a><a id="14913" href="plfa.Decidable.html#14913" class="Bound">m</a> <a id="14915" href="plfa.Decidable.html#14915" class="Bound">n</a> <a id="14917" class="Symbol">:</a> <a id="14919" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="14920" class="Symbol">)</a> <a id="14922" class="Symbol">→</a> <a id="14924" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="14928" class="Symbol">(</a><a id="14929" href="plfa.Decidable.html#14913" class="Bound">m</a> <a id="14931" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="14933" href="plfa.Decidable.html#14915" class="Bound">n</a><a id="14934" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
{% raw %}<pre class="Agda"><a id="14957" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="14994" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
## Decidables from booleans, and booleans from decidables
{:/}

## 从可判定的值到布尔值，从布尔值到可判定的值

{::comment}
Curious readers might wonder if we could reuse the definition of
`m ≤ᵇ n`, together with the proofs that it is equivalent to `m ≤ n`, to show
decidability.  Indeed, we can do so as follows:
{:/}

好奇的读者可能会思考能不能重用 `m ≤ᵇ n` 的定义，加上它与 `m ≤ n` 等价的证明，
来证明可判定性。的确，我们是可以做到的：

{% raw %}<pre class="Agda"><a id="_≤?′_"></a><a id="15398" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#15398" class="Function Operator">_≤?′_</a> <a id="15404" class="Symbol">:</a> <a id="15406" class="Symbol">∀</a> <a id="15408" class="Symbol">(</a><a id="15409" href="plfa.Decidable.html#15409" class="Bound">m</a> <a id="15411" href="plfa.Decidable.html#15411" class="Bound">n</a> <a id="15413" class="Symbol">:</a> <a id="15415" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="15416" class="Symbol">)</a> <a id="15418" class="Symbol">→</a> <a id="15420" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="15424" class="Symbol">(</a><a id="15425" href="plfa.Decidable.html#15409" class="Bound">m</a> <a id="15427" href="plfa.Decidable.html#1701" class="Datatype Operator">≤</a> <a id="15429" href="plfa.Decidable.html#15411" class="Bound">n</a><a id="15430" class="Symbol">)</a>
<a id="15432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#15432" class="Bound">m</a> <a id="15434" href="plfa.Decidable.html#15398" class="Function Operator">≤?′</a> <a id="15438" href="plfa.Decidable.html#15438" class="Bound">n</a> <a id="15440" class="Keyword">with</a> <a id="15445" href="plfa.Decidable.html#15432" class="Bound">m</a> <a id="15447" href="plfa.Decidable.html#2833" class="Function Operator">≤ᵇ</a> <a id="15450" href="plfa.Decidable.html#15438" class="Bound">n</a> <a id="15452" class="Symbol">|</a> <a id="15454" href="plfa.Decidable.html#6336" class="Function">≤ᵇ→≤</a> <a id="15459" href="plfa.Decidable.html#15432" class="Bound">m</a> <a id="15461" href="plfa.Decidable.html#15438" class="Bound">n</a> <a id="15463" class="Symbol">|</a> <a id="15465" href="plfa.Decidable.html#7676" class="Function">≤→≤ᵇ</a> <a id="15470" class="Symbol">{</a><a id="15471" href="plfa.Decidable.html#15432" class="Bound">m</a><a id="15472" class="Symbol">}</a> <a id="15474" class="Symbol">{</a><a id="15475" href="plfa.Decidable.html#15438" class="Bound">n</a><a id="15476" class="Symbol">}</a>
<a id="15478" class="Symbol">...</a>        <a id="15489" class="Symbol">|</a> <a id="15491" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2571" class="InductiveConstructor">true</a>   <a id="15498" class="Symbol">|</a> <a id="15500" href="plfa.Decidable.html#15500" class="Bound">p</a>        <a id="15509" class="Symbol">|</a> <a id="15511" class="Symbol">_</a>            <a id="15524" class="Symbol">=</a> <a id="15526" href="plfa.Decidable.html#9996" class="InductiveConstructor">yes</a> <a id="15530" class="Symbol">(</a><a id="15531" href="plfa.Decidable.html#15500" class="Bound">p</a> <a id="15533" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a><a id="15535" class="Symbol">)</a>
<a id="15537" class="Symbol">...</a>        <a id="15548" class="Symbol">|</a> <a id="15550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2586" class="InductiveConstructor">false</a>  <a id="15557" class="Symbol">|</a> <a id="15559" class="Symbol">_</a>        <a id="15568" class="Symbol">|</a> <a id="15570" href="plfa.Decidable.html#15570" class="Bound">¬p</a>           <a id="15583" class="Symbol">=</a> <a id="15585" href="plfa.Decidable.html#10016" class="InductiveConstructor">no</a> <a id="15588" href="plfa.Decidable.html#15570" class="Bound">¬p</a>
</pre>{% endraw %}
{::comment}
If `m ≤ᵇ n` is true then `≤ᵇ→≤` yields a proof that `m ≤ n` holds,
while if it is false then `≤→≤ᵇ` takes a proof that `m ≤ n` holds into a contradiction.
{:/}

如果 `m ≤ᵇ n` 为真，那么 `≤ᵇ→≤` 会返回一个 `m ≤ n` 成立的证明。
如果 `m ≤ᵇ n` 为假，那么 `≤→≤ᵇ` 会取一个 `m ≤ n` 成立的证明，将其转换为一个矛盾。

{::comment}
The triple binding of the `with` clause in this proof is essential.
If instead we wrote:
{:/}

在这个证明中，`with` 语句的三重约束是必须的。如果我们取而代之的写：

    _≤?″_ : ∀ (m n : ℕ) → Dec (m ≤ n)
    m ≤?″ n with m ≤ᵇ n
    ... | true   =  yes (≤ᵇ→≤ m n tt)
    ... | false  =  no (≤→≤ᵇ {m} {n})

{::comment}
then Agda would make two complaints, one for each clause:
{:/}

那么 Agda 对于每条语句会有一个抱怨：

    ⊤ !=< (T (m ≤ᵇ n)) of type Set
    when checking that the expression tt has type T (m ≤ᵇ n)

    T (m ≤ᵇ n) !=< ⊥ of type Set
    when checking that the expression ≤→≤ᵇ {m} {n} has type ¬ m ≤ n

{::comment}
Putting the expressions into the `with` clause permits Agda to exploit
the fact that `T (m ≤ᵇ n)` is `⊤` when `m ≤ᵇ n` is true, and that
`T (m ≤ᵇ n)` is `⊥` when `m ≤ᵇ n` is false.
{:/}

将表达式放在 `with` 语句中能让 Agda 利用下列事实：当 `m ≤ᵇ n` 为真时，`T (m ≤ᵇ n)` 是
`⊤`；当 `m ≤ᵇ n` 为假时，`T (m ≤ᵇ n)` 是 `⊥`。

{::comment}
However, overall it is simpler to just define `_≤?_` directly, as in the previous
section.  If one really wants `_≤ᵇ_`, then it and its properties are easily derived
from `_≤?_`, as we will now show.
{:/}

然而，总体来说还是直接定义 `_≤?_` 比较方便，正如之前部分中那样。如果有人真的很需要 `_≤ᵇ_`，
那么它和它的性质可以简单地从 `_≤?_` 中派生出来，正如我们接下来要展示的一样。

{::comment}
Erasure takes a decidable value to a boolean:
{:/}

擦除（Erasure）将一个可判定的值转换为一个布尔值：

{% raw %}<pre class="Agda"><a id="⌊_⌋"></a><a id="17169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17169" class="Function Operator">⌊_⌋</a> <a id="17173" class="Symbol">:</a> <a id="17175" class="Symbol">∀</a> <a id="17177" class="Symbol">{</a><a id="17178" href="plfa.Decidable.html#17178" class="Bound">A</a> <a id="17180" class="Symbol">:</a> <a id="17182" class="PrimitiveType">Set</a><a id="17185" class="Symbol">}</a> <a id="17187" class="Symbol">→</a> <a id="17189" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="17193" href="plfa.Decidable.html#17178" class="Bound">A</a> <a id="17195" class="Symbol">→</a> <a id="17197" href="plfa.Decidable.html#2552" class="Datatype">Bool</a>
<a id="17202" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17169" class="Function Operator">⌊</a> <a id="17204" href="plfa.Decidable.html#9996" class="InductiveConstructor">yes</a> <a id="17208" href="plfa.Decidable.html#17208" class="Bound">x</a> <a id="17210" href="plfa.Decidable.html#17169" class="Function Operator">⌋</a>  <a id="17213" class="Symbol">=</a>  <a id="17216" href="plfa.Decidable.html#2571" class="InductiveConstructor">true</a>
<a id="17221" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17169" class="Function Operator">⌊</a> <a id="17223" href="plfa.Decidable.html#10016" class="InductiveConstructor">no</a> <a id="17226" href="plfa.Decidable.html#17226" class="Bound">¬x</a> <a id="17229" href="plfa.Decidable.html#17169" class="Function Operator">⌋</a>  <a id="17232" class="Symbol">=</a>  <a id="17235" href="plfa.Decidable.html#2586" class="InductiveConstructor">false</a>
</pre>{% endraw %}
{::comment}
Using erasure, we can easily derive `_≤ᵇ_` from `_≤?_`:
{:/}

使用擦除，我们可以简单地从 `_≤?_` 中派生出 `_≤ᵇ_`：

{% raw %}<pre class="Agda"><a id="_≤ᵇ′_"></a><a id="17359" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17359" class="Function Operator">_≤ᵇ′_</a> <a id="17365" class="Symbol">:</a> <a id="17367" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="17369" class="Symbol">→</a> <a id="17371" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="17373" class="Symbol">→</a> <a id="17375" href="plfa.Decidable.html#2552" class="Datatype">Bool</a>
<a id="17380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17380" class="Bound">m</a> <a id="17382" href="plfa.Decidable.html#17359" class="Function Operator">≤ᵇ′</a> <a id="17386" href="plfa.Decidable.html#17386" class="Bound">n</a>  <a id="17389" class="Symbol">=</a>  <a id="17392" href="plfa.Decidable.html#17169" class="Function Operator">⌊</a> <a id="17394" href="plfa.Decidable.html#17380" class="Bound">m</a> <a id="17396" href="plfa.Decidable.html#11851" class="Function Operator">≤?</a> <a id="17399" href="plfa.Decidable.html#17386" class="Bound">n</a> <a id="17401" href="plfa.Decidable.html#17169" class="Function Operator">⌋</a>
</pre>{% endraw %}
{::comment}
Further, if `D` is a value of type `Dec A`, then `T ⌊ D ⌋` is
inhabited exactly when `A` is inhabited:
{:/}

更进一步来说，如果 `D` 是一个类型为 `Dec A` 的值，那么 `T ⌊ D ⌋`
当且仅当 `A` 成立时成立：
{% raw %}<pre class="Agda"><a id="toWitness"></a><a id="17594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17594" class="Function">toWitness</a> <a id="17604" class="Symbol">:</a> <a id="17606" class="Symbol">∀</a> <a id="17608" class="Symbol">{</a><a id="17609" href="plfa.Decidable.html#17609" class="Bound">A</a> <a id="17611" class="Symbol">:</a> <a id="17613" class="PrimitiveType">Set</a><a id="17616" class="Symbol">}</a> <a id="17618" class="Symbol">{</a><a id="17619" href="plfa.Decidable.html#17619" class="Bound">D</a> <a id="17621" class="Symbol">:</a> <a id="17623" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="17627" href="plfa.Decidable.html#17609" class="Bound">A</a><a id="17628" class="Symbol">}</a> <a id="17630" class="Symbol">→</a> <a id="17632" href="plfa.Decidable.html#4552" class="Function">T</a> <a id="17634" href="plfa.Decidable.html#17169" class="Function Operator">⌊</a> <a id="17636" href="plfa.Decidable.html#17619" class="Bound">D</a> <a id="17638" href="plfa.Decidable.html#17169" class="Function Operator">⌋</a> <a id="17640" class="Symbol">→</a> <a id="17642" href="plfa.Decidable.html#17609" class="Bound">A</a>
<a id="17644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17594" class="Function">toWitness</a> <a id="17654" class="Symbol">{</a><a id="17655" href="plfa.Decidable.html#17655" class="Bound">A</a><a id="17656" class="Symbol">}</a> <a id="17658" class="Symbol">{</a><a id="17659" href="plfa.Decidable.html#9996" class="InductiveConstructor">yes</a> <a id="17663" href="plfa.Decidable.html#17663" class="Bound">x</a><a id="17664" class="Symbol">}</a> <a id="17666" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a>  <a id="17670" class="Symbol">=</a>  <a id="17673" href="plfa.Decidable.html#17663" class="Bound">x</a>
<a id="17675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17594" class="Function">toWitness</a> <a id="17685" class="Symbol">{</a><a id="17686" href="plfa.Decidable.html#17686" class="Bound">A</a><a id="17687" class="Symbol">}</a> <a id="17689" class="Symbol">{</a><a id="17690" href="plfa.Decidable.html#10016" class="InductiveConstructor">no</a> <a id="17693" href="plfa.Decidable.html#17693" class="Bound">¬x</a><a id="17695" class="Symbol">}</a> <a id="17697" class="Symbol">()</a>

<a id="fromWitness"></a><a id="17701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17701" class="Function">fromWitness</a> <a id="17713" class="Symbol">:</a> <a id="17715" class="Symbol">∀</a> <a id="17717" class="Symbol">{</a><a id="17718" href="plfa.Decidable.html#17718" class="Bound">A</a> <a id="17720" class="Symbol">:</a> <a id="17722" class="PrimitiveType">Set</a><a id="17725" class="Symbol">}</a> <a id="17727" class="Symbol">{</a><a id="17728" href="plfa.Decidable.html#17728" class="Bound">D</a> <a id="17730" class="Symbol">:</a> <a id="17732" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="17736" href="plfa.Decidable.html#17718" class="Bound">A</a><a id="17737" class="Symbol">}</a> <a id="17739" class="Symbol">→</a> <a id="17741" href="plfa.Decidable.html#17718" class="Bound">A</a> <a id="17743" class="Symbol">→</a> <a id="17745" href="plfa.Decidable.html#4552" class="Function">T</a> <a id="17747" href="plfa.Decidable.html#17169" class="Function Operator">⌊</a> <a id="17749" href="plfa.Decidable.html#17728" class="Bound">D</a> <a id="17751" href="plfa.Decidable.html#17169" class="Function Operator">⌋</a>
<a id="17753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17701" class="Function">fromWitness</a> <a id="17765" class="Symbol">{</a><a id="17766" href="plfa.Decidable.html#17766" class="Bound">A</a><a id="17767" class="Symbol">}</a> <a id="17769" class="Symbol">{</a><a id="17770" href="plfa.Decidable.html#9996" class="InductiveConstructor">yes</a> <a id="17774" href="plfa.Decidable.html#17774" class="Bound">x</a><a id="17775" class="Symbol">}</a> <a id="17777" class="Symbol">_</a>  <a id="17780" class="Symbol">=</a>  <a id="17783" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a>
<a id="17786" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#17701" class="Function">fromWitness</a> <a id="17798" class="Symbol">{</a><a id="17799" href="plfa.Decidable.html#17799" class="Bound">A</a><a id="17800" class="Symbol">}</a> <a id="17802" class="Symbol">{</a><a id="17803" href="plfa.Decidable.html#10016" class="InductiveConstructor">no</a> <a id="17806" href="plfa.Decidable.html#17806" class="Bound">¬x</a><a id="17808" class="Symbol">}</a> <a id="17810" href="plfa.Decidable.html#17810" class="Bound">x</a>  <a id="17813" class="Symbol">=</a>  <a id="17816" href="plfa.Decidable.html#17806" class="Bound">¬x</a> <a id="17819" href="plfa.Decidable.html#17810" class="Bound">x</a>
</pre>{% endraw %}
{::comment}
Using these, we can easily derive that `T (m ≤ᵇ′ n)` is inhabited
exactly when `m ≤ n` is inhabited:
{:/}

使用这些，我们可以简单地派生出 `T (m ≤ᵇ′ n)` 当且仅当 `m ≤ n` 成立时成立。

{% raw %}<pre class="Agda"><a id="≤ᵇ′→≤"></a><a id="18000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#18000" class="Function">≤ᵇ′→≤</a> <a id="18006" class="Symbol">:</a> <a id="18008" class="Symbol">∀</a> <a id="18010" class="Symbol">{</a><a id="18011" href="plfa.Decidable.html#18011" class="Bound">m</a> <a id="18013" href="plfa.Decidable.html#18013" class="Bound">n</a> <a id="18015" class="Symbol">:</a> <a id="18017" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18018" class="Symbol">}</a> <a id="18020" class="Symbol">→</a> <a id="18022" href="plfa.Decidable.html#4552" class="Function">T</a> <a id="18024" class="Symbol">(</a><a id="18025" href="plfa.Decidable.html#18011" class="Bound">m</a> <a id="18027" href="plfa.Decidable.html#17359" class="Function Operator">≤ᵇ′</a> <a id="18031" href="plfa.Decidable.html#18013" class="Bound">n</a><a id="18032" class="Symbol">)</a> <a id="18034" class="Symbol">→</a> <a id="18036" href="plfa.Decidable.html#18011" class="Bound">m</a> <a id="18038" href="plfa.Decidable.html#1701" class="Datatype Operator">≤</a> <a id="18040" href="plfa.Decidable.html#18013" class="Bound">n</a>
<a id="18042" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#18000" class="Function">≤ᵇ′→≤</a>  <a id="18049" class="Symbol">=</a>  <a id="18052" href="plfa.Decidable.html#17594" class="Function">toWitness</a>

<a id="≤→≤ᵇ′"></a><a id="18063" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#18063" class="Function">≤→≤ᵇ′</a> <a id="18069" class="Symbol">:</a> <a id="18071" class="Symbol">∀</a> <a id="18073" class="Symbol">{</a><a id="18074" href="plfa.Decidable.html#18074" class="Bound">m</a> <a id="18076" href="plfa.Decidable.html#18076" class="Bound">n</a> <a id="18078" class="Symbol">:</a> <a id="18080" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18081" class="Symbol">}</a> <a id="18083" class="Symbol">→</a> <a id="18085" href="plfa.Decidable.html#18074" class="Bound">m</a> <a id="18087" href="plfa.Decidable.html#1701" class="Datatype Operator">≤</a> <a id="18089" href="plfa.Decidable.html#18076" class="Bound">n</a> <a id="18091" class="Symbol">→</a> <a id="18093" href="plfa.Decidable.html#4552" class="Function">T</a> <a id="18095" class="Symbol">(</a><a id="18096" href="plfa.Decidable.html#18074" class="Bound">m</a> <a id="18098" href="plfa.Decidable.html#17359" class="Function Operator">≤ᵇ′</a> <a id="18102" href="plfa.Decidable.html#18076" class="Bound">n</a><a id="18103" class="Symbol">)</a>
<a id="18105" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#18063" class="Function">≤→≤ᵇ′</a>  <a id="18112" class="Symbol">=</a>  <a id="18115" href="plfa.Decidable.html#17701" class="Function">fromWitness</a>
</pre>{% endraw %}
{::comment}
In summary, it is usually best to eschew booleans and rely on decidables.
If you need booleans, they and their properties are easily derived from the
corresponding decidables.
{:/}

总结来说，最好避免直接使用布尔值，而使用可判定的值。如果有需要布尔值的时候，它们和它们的性质
可以简单地从对应的可判定的值中派生而来。


{::comment}
## Logical connectives
{:/}

{::comment}
Most readers will be familiar with the logical connectives for booleans.
Each of these extends to decidables.
{:/}

大多数读者对于布尔值的逻辑运算符很熟悉了。每个逻辑运算符都可以被延伸至可判定的值。

{::comment}
The conjunction of two booleans is true if both are true,
and false if either is false:
{:/}

两个布尔值的合取当两者都为真时为真，当任一为假时为假：

{% raw %}<pre class="Agda"><a id="18747" class="Keyword">infixr</a> <a id="18754" class="Number">6</a> <a id="18756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#18761" class="Function Operator">_∧_</a>

<a id="_∧_"></a><a id="18761" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#18761" class="Function Operator">_∧_</a> <a id="18765" class="Symbol">:</a> <a id="18767" href="plfa.Decidable.html#2552" class="Datatype">Bool</a> <a id="18772" class="Symbol">→</a> <a id="18774" href="plfa.Decidable.html#2552" class="Datatype">Bool</a> <a id="18779" class="Symbol">→</a> <a id="18781" href="plfa.Decidable.html#2552" class="Datatype">Bool</a>
<a id="18786" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2571" class="InductiveConstructor">true</a>  <a id="18792" href="plfa.Decidable.html#18761" class="Function Operator">∧</a> <a id="18794" href="plfa.Decidable.html#2571" class="InductiveConstructor">true</a>  <a id="18800" class="Symbol">=</a> <a id="18802" href="plfa.Decidable.html#2571" class="InductiveConstructor">true</a>
<a id="18807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2586" class="InductiveConstructor">false</a> <a id="18813" href="plfa.Decidable.html#18761" class="Function Operator">∧</a> <a id="18815" class="Symbol">_</a>     <a id="18821" class="Symbol">=</a> <a id="18823" href="plfa.Decidable.html#2586" class="InductiveConstructor">false</a>
<a id="18829" class="CatchallClause Symbol">_</a><a id="18830" class="CatchallClause">     </a><a id="18835" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#18761" class="CatchallClause Function Operator">∧</a><a id="18836" class="CatchallClause"> </a><a id="18837" href="plfa.Decidable.html#2586" class="CatchallClause InductiveConstructor">false</a> <a id="18843" class="Symbol">=</a> <a id="18845" href="plfa.Decidable.html#2586" class="InductiveConstructor">false</a>
</pre>{% endraw %}
{::comment}
In Emacs, the left-hand side of the third equation displays in grey,
indicating that the order of the equations determines which of the
second or the third can match.  However, regardless of which matches
the answer is the same.
{:/}

在 Emacs 中，第三个等式的左手边显示为灰色，表示这些等式出现的顺序决定了是第二条还是第三条
会被匹配到。然而，不管是哪一条被匹配到，结果都是一样的。

{::comment}
Correspondingly, given two decidable propositions, we can
decide their conjunction:
{:/}

相应地，给定两个可判定的命题，我们可以判定它们的合取：

{% raw %}<pre class="Agda"><a id="19317" class="Keyword">infixr</a> <a id="19324" class="Number">6</a> <a id="19326" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#19335" class="Function Operator">_×-dec_</a>

<a id="_×-dec_"></a><a id="19335" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#19335" class="Function Operator">_×-dec_</a> <a id="19343" class="Symbol">:</a> <a id="19345" class="Symbol">∀</a> <a id="19347" class="Symbol">{</a><a id="19348" href="plfa.Decidable.html#19348" class="Bound">A</a> <a id="19350" href="plfa.Decidable.html#19350" class="Bound">B</a> <a id="19352" class="Symbol">:</a> <a id="19354" class="PrimitiveType">Set</a><a id="19357" class="Symbol">}</a> <a id="19359" class="Symbol">→</a> <a id="19361" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="19365" href="plfa.Decidable.html#19348" class="Bound">A</a> <a id="19367" class="Symbol">→</a> <a id="19369" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="19373" href="plfa.Decidable.html#19350" class="Bound">B</a> <a id="19375" class="Symbol">→</a> <a id="19377" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="19381" class="Symbol">(</a><a id="19382" href="plfa.Decidable.html#19348" class="Bound">A</a> <a id="19384" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="19386" href="plfa.Decidable.html#19350" class="Bound">B</a><a id="19387" class="Symbol">)</a>
<a id="19389" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#9996" class="InductiveConstructor">yes</a> <a id="19393" href="plfa.Decidable.html#19393" class="Bound">x</a> <a id="19395" href="plfa.Decidable.html#19335" class="Function Operator">×-dec</a> <a id="19401" href="plfa.Decidable.html#9996" class="InductiveConstructor">yes</a> <a id="19405" href="plfa.Decidable.html#19405" class="Bound">y</a> <a id="19407" class="Symbol">=</a> <a id="19409" href="plfa.Decidable.html#9996" class="InductiveConstructor">yes</a> <a id="19413" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨</a> <a id="19415" href="plfa.Decidable.html#19393" class="Bound">x</a> <a id="19417" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">,</a> <a id="19419" href="plfa.Decidable.html#19405" class="Bound">y</a> <a id="19421" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟩</a>
<a id="19423" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10016" class="InductiveConstructor">no</a> <a id="19426" href="plfa.Decidable.html#19426" class="Bound">¬x</a> <a id="19429" href="plfa.Decidable.html#19335" class="Function Operator">×-dec</a> <a id="19435" class="Symbol">_</a>     <a id="19441" class="Symbol">=</a> <a id="19443" href="plfa.Decidable.html#10016" class="InductiveConstructor">no</a> <a id="19446" class="Symbol">λ{</a> <a id="19449" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨</a> <a id="19451" href="plfa.Decidable.html#19451" class="Bound">x</a> <a id="19453" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">,</a> <a id="19455" href="plfa.Decidable.html#19455" class="Bound">y</a> <a id="19457" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟩</a> <a id="19459" class="Symbol">→</a> <a id="19461" href="plfa.Decidable.html#19426" class="Bound">¬x</a> <a id="19464" href="plfa.Decidable.html#19451" class="Bound">x</a> <a id="19466" class="Symbol">}</a>
<a id="19468" class="CatchallClause Symbol">_</a><a id="19469" class="CatchallClause">     </a><a id="19474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#19335" class="CatchallClause Function Operator">×-dec</a><a id="19479" class="CatchallClause"> </a><a id="19480" href="plfa.Decidable.html#10016" class="CatchallClause InductiveConstructor">no</a><a id="19482" class="CatchallClause"> </a><a id="19483" href="plfa.Decidable.html#19483" class="CatchallClause Bound">¬y</a> <a id="19486" class="Symbol">=</a> <a id="19488" href="plfa.Decidable.html#10016" class="InductiveConstructor">no</a> <a id="19491" class="Symbol">λ{</a> <a id="19494" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨</a> <a id="19496" href="plfa.Decidable.html#19496" class="Bound">x</a> <a id="19498" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">,</a> <a id="19500" href="plfa.Decidable.html#19500" class="Bound">y</a> <a id="19502" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟩</a> <a id="19504" class="Symbol">→</a> <a id="19506" href="plfa.Decidable.html#19483" class="Bound">¬y</a> <a id="19509" href="plfa.Decidable.html#19500" class="Bound">y</a> <a id="19511" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
The conjunction of two propositions holds if they both hold,
and its negation holds if the negation of either holds.
If both hold, then we pair the evidence for each to yield
evidence of the conjunct.  If the negation of either holds,
assuming the conjunct will lead to a contradiction.
{:/}

两个命题的合取当两者都成立时成立，其否定则当任意一者否定成立时成立。如果两个都成立，
我们将每一证明放入数据对中，作为合取的证明。如果任意一者的否定成立，假设整个合取将会引入一个矛盾。

{::comment}
Again in Emacs, the left-hand side of the third equation displays in grey,
indicating that the order of the equations determines which of the
second or the third can match.  This time the answer is different depending
on which matches; if both conjuncts fail to hold we pick the first to
yield the contradiction, but it would be equally valid to pick the second.
{:/}

同样地，在 Emacs 中，第三条等式在左手边以灰色显示，说明等式的顺序决定了第二条还是第三条会被匹配。
这一次，我们给出的结果会因为是第二条还是第三条而不一样。如果两个命题都不成立，我们选择第一个来构造矛盾，
但选择第二个也是同样正确的。

{::comment}
The disjunction of two booleans is true if either is true,
and false if both are false:
{:/}

两个布尔值的析取当任意为真时为真，当两者为假时为假：

{% raw %}<pre class="Agda"><a id="20558" class="Keyword">infixr</a> <a id="20565" class="Number">5</a> <a id="20567" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#20572" class="Function Operator">_∨_</a>

<a id="_∨_"></a><a id="20572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#20572" class="Function Operator">_∨_</a> <a id="20576" class="Symbol">:</a> <a id="20578" href="plfa.Decidable.html#2552" class="Datatype">Bool</a> <a id="20583" class="Symbol">→</a> <a id="20585" href="plfa.Decidable.html#2552" class="Datatype">Bool</a> <a id="20590" class="Symbol">→</a> <a id="20592" href="plfa.Decidable.html#2552" class="Datatype">Bool</a>
<a id="20597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2571" class="InductiveConstructor">true</a>  <a id="20603" href="plfa.Decidable.html#20572" class="Function Operator">∨</a> <a id="20605" class="Symbol">_</a>      <a id="20612" class="Symbol">=</a> <a id="20614" href="plfa.Decidable.html#2571" class="InductiveConstructor">true</a>
<a id="20619" class="CatchallClause Symbol">_</a><a id="20620" class="CatchallClause">     </a><a id="20625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#20572" class="CatchallClause Function Operator">∨</a><a id="20626" class="CatchallClause"> </a><a id="20627" href="plfa.Decidable.html#2571" class="CatchallClause InductiveConstructor">true</a>   <a id="20634" class="Symbol">=</a> <a id="20636" href="plfa.Decidable.html#2571" class="InductiveConstructor">true</a>
<a id="20641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2586" class="InductiveConstructor">false</a> <a id="20647" href="plfa.Decidable.html#20572" class="Function Operator">∨</a> <a id="20649" href="plfa.Decidable.html#2586" class="InductiveConstructor">false</a>  <a id="20656" class="Symbol">=</a> <a id="20658" href="plfa.Decidable.html#2586" class="InductiveConstructor">false</a>
</pre>{% endraw %}
{::comment}
In Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  However, regardless of which matches
the answer is the same.
{:/}

在 Emacs 中，第二个等式的左手边显示为灰色，表示这些等式出现的顺序决定了是第一条还是第二条
会被匹配到。然而，不管是哪一条被匹配到，结果都是一样的。

{::comment}
Correspondingly, given two decidable propositions, we can
decide their disjunction:
{:/}

相应地，给定两个可判定的命题，我们可以判定它们的析取：

{% raw %}<pre class="Agda"><a id="21131" class="Keyword">infixr</a> <a id="21138" class="Number">5</a> <a id="21140" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#21149" class="Function Operator">_⊎-dec_</a>

<a id="_⊎-dec_"></a><a id="21149" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#21149" class="Function Operator">_⊎-dec_</a> <a id="21157" class="Symbol">:</a> <a id="21159" class="Symbol">∀</a> <a id="21161" class="Symbol">{</a><a id="21162" href="plfa.Decidable.html#21162" class="Bound">A</a> <a id="21164" href="plfa.Decidable.html#21164" class="Bound">B</a> <a id="21166" class="Symbol">:</a> <a id="21168" class="PrimitiveType">Set</a><a id="21171" class="Symbol">}</a> <a id="21173" class="Symbol">→</a> <a id="21175" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="21179" href="plfa.Decidable.html#21162" class="Bound">A</a> <a id="21181" class="Symbol">→</a> <a id="21183" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="21187" href="plfa.Decidable.html#21164" class="Bound">B</a> <a id="21189" class="Symbol">→</a> <a id="21191" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="21195" class="Symbol">(</a><a id="21196" href="plfa.Decidable.html#21162" class="Bound">A</a> <a id="21198" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="21200" href="plfa.Decidable.html#21164" class="Bound">B</a><a id="21201" class="Symbol">)</a>
<a id="21203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#9996" class="InductiveConstructor">yes</a> <a id="21207" href="plfa.Decidable.html#21207" class="Bound">x</a> <a id="21209" href="plfa.Decidable.html#21149" class="Function Operator">⊎-dec</a> <a id="21215" class="Symbol">_</a>     <a id="21221" class="Symbol">=</a> <a id="21223" href="plfa.Decidable.html#9996" class="InductiveConstructor">yes</a> <a id="21227" class="Symbol">(</a><a id="21228" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a> <a id="21233" href="plfa.Decidable.html#21207" class="Bound">x</a><a id="21234" class="Symbol">)</a>
<a id="21236" class="CatchallClause Symbol">_</a><a id="21237" class="CatchallClause">     </a><a id="21242" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#21149" class="CatchallClause Function Operator">⊎-dec</a><a id="21247" class="CatchallClause"> </a><a id="21248" href="plfa.Decidable.html#9996" class="CatchallClause InductiveConstructor">yes</a><a id="21251" class="CatchallClause"> </a><a id="21252" href="plfa.Decidable.html#21252" class="CatchallClause Bound">y</a> <a id="21254" class="Symbol">=</a> <a id="21256" href="plfa.Decidable.html#9996" class="InductiveConstructor">yes</a> <a id="21260" class="Symbol">(</a><a id="21261" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a> <a id="21266" href="plfa.Decidable.html#21252" class="Bound">y</a><a id="21267" class="Symbol">)</a>
<a id="21269" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10016" class="InductiveConstructor">no</a> <a id="21272" href="plfa.Decidable.html#21272" class="Bound">¬x</a> <a id="21275" href="plfa.Decidable.html#21149" class="Function Operator">⊎-dec</a> <a id="21281" href="plfa.Decidable.html#10016" class="InductiveConstructor">no</a> <a id="21284" href="plfa.Decidable.html#21284" class="Bound">¬y</a> <a id="21287" class="Symbol">=</a> <a id="21289" href="plfa.Decidable.html#10016" class="InductiveConstructor">no</a> <a id="21292" class="Symbol">λ{</a> <a id="21295" class="Symbol">(</a><a id="21296" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a> <a id="21301" href="plfa.Decidable.html#21301" class="Bound">x</a><a id="21302" class="Symbol">)</a> <a id="21304" class="Symbol">→</a> <a id="21306" href="plfa.Decidable.html#21272" class="Bound">¬x</a> <a id="21309" href="plfa.Decidable.html#21301" class="Bound">x</a> <a id="21311" class="Symbol">;</a> <a id="21313" class="Symbol">(</a><a id="21314" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a> <a id="21319" href="plfa.Decidable.html#21319" class="Bound">y</a><a id="21320" class="Symbol">)</a> <a id="21322" class="Symbol">→</a> <a id="21324" href="plfa.Decidable.html#21284" class="Bound">¬y</a> <a id="21327" href="plfa.Decidable.html#21319" class="Bound">y</a> <a id="21329" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
The disjunction of two propositions holds if either holds,
and its negation holds if the negation of both hold.
If either holds, we inject the evidence to yield
evidence of the disjunct.  If the negation of both hold,
assuming either disjunct will lead to a contradiction.
{:/}

两个命题的析取当任意一者成立时成立，其否定则当两者的否定成立时成立。如果任意一者成立，
我们使用其证明来作为析取的证明。如果两个的否定都成立，假设任意一者都会引入一个矛盾。

{::comment}
Again in Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  This time the answer is different depending
on which matches; if both disjuncts hold we pick the first,
but it would be equally valid to pick the second.
{:/}

同样地，在 Emacs 中，第二条等式在左手边以灰色显示，说明等式的顺序决定了第一条还是第二条会被匹配。
这一次，我们给出的结果会因为是第二条还是第三条而不一样。如果两个命题都成立，我们选择第一个来构造析取，
但选择第二个也是同样正确的。

{::comment}
The negation of a boolean is false if its argument is true,
and vice versa:
{:/}

一个布尔值的否定当值为真时为假，反之亦然：

{% raw %}<pre class="Agda"><a id="not"></a><a id="22304" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#22304" class="Function">not</a> <a id="22308" class="Symbol">:</a> <a id="22310" href="plfa.Decidable.html#2552" class="Datatype">Bool</a> <a id="22315" class="Symbol">→</a> <a id="22317" href="plfa.Decidable.html#2552" class="Datatype">Bool</a>
<a id="22322" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#22304" class="Function">not</a> <a id="22326" href="plfa.Decidable.html#2571" class="InductiveConstructor">true</a>  <a id="22332" class="Symbol">=</a> <a id="22334" href="plfa.Decidable.html#2586" class="InductiveConstructor">false</a>
<a id="22340" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#22304" class="Function">not</a> <a id="22344" href="plfa.Decidable.html#2586" class="InductiveConstructor">false</a> <a id="22350" class="Symbol">=</a> <a id="22352" href="plfa.Decidable.html#2571" class="InductiveConstructor">true</a>
</pre>{% endraw %}
{::comment}
Correspondingly, given a decidable proposition, we
can decide its negation:
{:/}

相应地，给定一个可判定的命题，我们可以判定它的否定：

{% raw %}<pre class="Agda"><a id="¬?"></a><a id="22488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#22488" class="Function">¬?</a> <a id="22491" class="Symbol">:</a> <a id="22493" class="Symbol">∀</a> <a id="22495" class="Symbol">{</a><a id="22496" href="plfa.Decidable.html#22496" class="Bound">A</a> <a id="22498" class="Symbol">:</a> <a id="22500" class="PrimitiveType">Set</a><a id="22503" class="Symbol">}</a> <a id="22505" class="Symbol">→</a> <a id="22507" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="22511" href="plfa.Decidable.html#22496" class="Bound">A</a> <a id="22513" class="Symbol">→</a> <a id="22515" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="22519" class="Symbol">(</a><a id="22520" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="22522" href="plfa.Decidable.html#22496" class="Bound">A</a><a id="22523" class="Symbol">)</a>
<a id="22525" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#22488" class="Function">¬?</a> <a id="22528" class="Symbol">(</a><a id="22529" href="plfa.Decidable.html#9996" class="InductiveConstructor">yes</a> <a id="22533" href="plfa.Decidable.html#22533" class="Bound">x</a><a id="22534" class="Symbol">)</a>  <a id="22537" class="Symbol">=</a>  <a id="22540" href="plfa.Decidable.html#10016" class="InductiveConstructor">no</a> <a id="22543" class="Symbol">(</a><a id="22544" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#809" class="Function">¬¬-intro</a> <a id="22553" href="plfa.Decidable.html#22533" class="Bound">x</a><a id="22554" class="Symbol">)</a>
<a id="22556" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#22488" class="Function">¬?</a> <a id="22559" class="Symbol">(</a><a id="22560" href="plfa.Decidable.html#10016" class="InductiveConstructor">no</a> <a id="22563" href="plfa.Decidable.html#22563" class="Bound">¬x</a><a id="22565" class="Symbol">)</a>  <a id="22568" class="Symbol">=</a>  <a id="22571" href="plfa.Decidable.html#9996" class="InductiveConstructor">yes</a> <a id="22575" href="plfa.Decidable.html#22563" class="Bound">¬x</a>
</pre>{% endraw %}
{::comment}
We simply swap yes and no.  In the first equation,
the right-hand side asserts that the negation of `¬ A` holds,
in other words, that `¬ ¬ A` holds, which is an easy consequence
of the fact that `A` holds.
{:/}

我们直接把 yes 和 no 交换。在第一个等式中，右手边断言了 `¬ A` 的否定成立，也就是说
`¬ ¬ A` 成立——这是一个 `A` 成立时可以简单得到的推论。

{::comment}
There is also a slightly less familiar connective,
corresponding to implication:
{:/}

还有一个与蕴涵相对应，但是稍微不那么知名的运算符：

{% raw %}<pre class="Agda"><a id="_⊃_"></a><a id="23023" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#23023" class="Function Operator">_⊃_</a> <a id="23027" class="Symbol">:</a> <a id="23029" href="plfa.Decidable.html#2552" class="Datatype">Bool</a> <a id="23034" class="Symbol">→</a> <a id="23036" href="plfa.Decidable.html#2552" class="Datatype">Bool</a> <a id="23041" class="Symbol">→</a> <a id="23043" href="plfa.Decidable.html#2552" class="Datatype">Bool</a>
<a id="23048" class="Symbol">_</a>     <a id="23054" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#23023" class="Function Operator">⊃</a> <a id="23056" href="plfa.Decidable.html#2571" class="InductiveConstructor">true</a>   <a id="23063" class="Symbol">=</a>  <a id="23066" href="plfa.Decidable.html#2571" class="InductiveConstructor">true</a>
<a id="23071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2586" class="CatchallClause InductiveConstructor">false</a><a id="23076" class="CatchallClause"> </a><a id="23077" href="plfa.Decidable.html#23023" class="CatchallClause Function Operator">⊃</a><a id="23078" class="CatchallClause"> </a><a id="23079" class="CatchallClause Symbol">_</a>      <a id="23086" class="Symbol">=</a>  <a id="23089" href="plfa.Decidable.html#2571" class="InductiveConstructor">true</a>
<a id="23094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#2571" class="InductiveConstructor">true</a>  <a id="23100" href="plfa.Decidable.html#23023" class="Function Operator">⊃</a> <a id="23102" href="plfa.Decidable.html#2586" class="InductiveConstructor">false</a>  <a id="23109" class="Symbol">=</a>  <a id="23112" href="plfa.Decidable.html#2586" class="InductiveConstructor">false</a>
</pre>{% endraw %}
{::comment}
One boolean implies another if
whenever the first is true then the second is true.
Hence, the implication of two booleans is true if
the second is true or the first is false,
and false if the first is true and the second is false.
In Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  However, regardless of which matches
the answer is the same.
{:/}

当任何一个布尔值为真的时候，另一个布尔值恒为真，我们成为第一个布尔值蕴涵第二个布尔值。
因此，两者的蕴涵在第二个为真或者第一个为假时为真，在第一个为真而第二个为假时为假。
在 Emacs 中，第二个等式的左手边显示为灰色，表示这些等式出现的顺序决定了是第一条还是第二条
会被匹配到。然而，不管是哪一条被匹配到，结果都是一样的。

{::comment}
Correspondingly, given two decidable propositions,
we can decide if the first implies the second:
{:/}

相应地，给定两个可判定的命题，我们可以判定它们的析取：

{% raw %}<pre class="Agda"><a id="_→-dec_"></a><a id="23916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#23916" class="Function Operator">_→-dec_</a> <a id="23924" class="Symbol">:</a> <a id="23926" class="Symbol">∀</a> <a id="23928" class="Symbol">{</a><a id="23929" href="plfa.Decidable.html#23929" class="Bound">A</a> <a id="23931" href="plfa.Decidable.html#23931" class="Bound">B</a> <a id="23933" class="Symbol">:</a> <a id="23935" class="PrimitiveType">Set</a><a id="23938" class="Symbol">}</a> <a id="23940" class="Symbol">→</a> <a id="23942" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="23946" href="plfa.Decidable.html#23929" class="Bound">A</a> <a id="23948" class="Symbol">→</a> <a id="23950" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="23954" href="plfa.Decidable.html#23931" class="Bound">B</a> <a id="23956" class="Symbol">→</a> <a id="23958" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="23962" class="Symbol">(</a><a id="23963" href="plfa.Decidable.html#23929" class="Bound">A</a> <a id="23965" class="Symbol">→</a> <a id="23967" href="plfa.Decidable.html#23931" class="Bound">B</a><a id="23968" class="Symbol">)</a>
<a id="23970" class="Symbol">_</a>     <a id="23976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#23916" class="Function Operator">→-dec</a> <a id="23982" href="plfa.Decidable.html#9996" class="InductiveConstructor">yes</a> <a id="23986" href="plfa.Decidable.html#23986" class="Bound">y</a>  <a id="23989" class="Symbol">=</a>  <a id="23992" href="plfa.Decidable.html#9996" class="InductiveConstructor">yes</a> <a id="23996" class="Symbol">(λ</a> <a id="23999" href="plfa.Decidable.html#23999" class="Bound">_</a> <a id="24001" class="Symbol">→</a> <a id="24003" href="plfa.Decidable.html#23986" class="Bound">y</a><a id="24004" class="Symbol">)</a>
<a id="24006" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#10016" class="CatchallClause InductiveConstructor">no</a><a id="24008" class="CatchallClause"> </a><a id="24009" href="plfa.Decidable.html#24009" class="CatchallClause Bound">¬x</a><a id="24011" class="CatchallClause"> </a><a id="24012" href="plfa.Decidable.html#23916" class="CatchallClause Function Operator">→-dec</a><a id="24017" class="CatchallClause"> </a><a id="24018" class="CatchallClause Symbol">_</a>      <a id="24025" class="Symbol">=</a>  <a id="24028" href="plfa.Decidable.html#9996" class="InductiveConstructor">yes</a> <a id="24032" class="Symbol">(λ</a> <a id="24035" href="plfa.Decidable.html#24035" class="Bound">x</a> <a id="24037" class="Symbol">→</a> <a id="24039" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="24046" class="Symbol">(</a><a id="24047" href="plfa.Decidable.html#24009" class="Bound">¬x</a> <a id="24050" href="plfa.Decidable.html#24035" class="Bound">x</a><a id="24051" class="Symbol">))</a>
<a id="24054" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#9996" class="InductiveConstructor">yes</a> <a id="24058" href="plfa.Decidable.html#24058" class="Bound">x</a> <a id="24060" href="plfa.Decidable.html#23916" class="Function Operator">→-dec</a> <a id="24066" href="plfa.Decidable.html#10016" class="InductiveConstructor">no</a> <a id="24069" href="plfa.Decidable.html#24069" class="Bound">¬y</a>  <a id="24073" class="Symbol">=</a>  <a id="24076" href="plfa.Decidable.html#10016" class="InductiveConstructor">no</a> <a id="24079" class="Symbol">(λ</a> <a id="24082" href="plfa.Decidable.html#24082" class="Bound">f</a> <a id="24084" class="Symbol">→</a> <a id="24086" href="plfa.Decidable.html#24069" class="Bound">¬y</a> <a id="24089" class="Symbol">(</a><a id="24090" href="plfa.Decidable.html#24082" class="Bound">f</a> <a id="24092" href="plfa.Decidable.html#24058" class="Bound">x</a><a id="24093" class="Symbol">))</a>
</pre>{% endraw %}
{::comment}
The implication holds if either the second holds or
the negation of the first holds, and its negation
holds if the first holds and the negation of the second holds.
Evidence for the implication is a function from evidence
of the first to evidence of the second.
If the second holds, the function returns the evidence for it.
If the negation of the first holds, the function takes the
evidence of the first and derives a contradiction.
If the first holds and the negation of the second holds,
given evidence of the implication we must derive a contradiction;
we apply the evidence of the implication `f` to the evidence of the
first `x`, yielding a contradiction with the evidence `¬y` of
the negation of the second.
{:/}

两者的蕴涵在第二者成立或者第一者的否定成立时成立，其否定在第一者成立而第二者否定成立时成立。
蕴涵成立的证明是一个从第一者成立的证明到第二者成立的证明的函数。如果第二者成立，那么这个函数
直接返回第二者的证明。如果第一者的否定成立，那么使用第一者成立的证明，构造一个矛盾。
如果第一者成立，第二者不成立，给定蕴涵成立的证明，我们必须构造一个矛盾：我们将成立的证明 `f`
应用于第一者成立的证明 `x`，再加以第二者否定成立的证明 `¬y` 来构造矛盾。

{::comment}
Again in Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  This time the answer is different depending
on which matches; but either is equally valid.
{:/}

同样地，在 Emacs 中，第二条等式在左手边以灰色显示，说明等式的顺序决定了第一条还是第二条会被匹配。
这一次，我们给出的结果会因为是哪一条被匹配而不一样，但两者都是同样正确的。

{::comment}
#### Exercise `erasure`
{:/}

#### 练习 `erasure`

{::comment}
Show that erasure relates corresponding boolean and decidable operations:
{:/}

证明擦除将对应的布尔值和可判定的值的操作联系了起来：

{% raw %}<pre class="Agda"><a id="25625" class="Keyword">postulate</a>
  <a id="∧-×"></a><a id="25637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#25637" class="Postulate">∧-×</a> <a id="25641" class="Symbol">:</a> <a id="25643" class="Symbol">∀</a> <a id="25645" class="Symbol">{</a><a id="25646" href="plfa.Decidable.html#25646" class="Bound">A</a> <a id="25648" href="plfa.Decidable.html#25648" class="Bound">B</a> <a id="25650" class="Symbol">:</a> <a id="25652" class="PrimitiveType">Set</a><a id="25655" class="Symbol">}</a> <a id="25657" class="Symbol">(</a><a id="25658" href="plfa.Decidable.html#25658" class="Bound">x</a> <a id="25660" class="Symbol">:</a> <a id="25662" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="25666" href="plfa.Decidable.html#25646" class="Bound">A</a><a id="25667" class="Symbol">)</a> <a id="25669" class="Symbol">(</a><a id="25670" href="plfa.Decidable.html#25670" class="Bound">y</a> <a id="25672" class="Symbol">:</a> <a id="25674" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="25678" href="plfa.Decidable.html#25648" class="Bound">B</a><a id="25679" class="Symbol">)</a> <a id="25681" class="Symbol">→</a> <a id="25683" href="plfa.Decidable.html#17169" class="Function Operator">⌊</a> <a id="25685" href="plfa.Decidable.html#25658" class="Bound">x</a> <a id="25687" href="plfa.Decidable.html#17169" class="Function Operator">⌋</a> <a id="25689" href="plfa.Decidable.html#18761" class="Function Operator">∧</a> <a id="25691" href="plfa.Decidable.html#17169" class="Function Operator">⌊</a> <a id="25693" href="plfa.Decidable.html#25670" class="Bound">y</a> <a id="25695" href="plfa.Decidable.html#17169" class="Function Operator">⌋</a> <a id="25697" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="25699" href="plfa.Decidable.html#17169" class="Function Operator">⌊</a> <a id="25701" href="plfa.Decidable.html#25658" class="Bound">x</a> <a id="25703" href="plfa.Decidable.html#19335" class="Function Operator">×-dec</a> <a id="25709" href="plfa.Decidable.html#25670" class="Bound">y</a> <a id="25711" href="plfa.Decidable.html#17169" class="Function Operator">⌋</a>
  <a id="∨-⊎"></a><a id="25715" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#25715" class="Postulate">∨-⊎</a> <a id="25719" class="Symbol">:</a> <a id="25721" class="Symbol">∀</a> <a id="25723" class="Symbol">{</a><a id="25724" href="plfa.Decidable.html#25724" class="Bound">A</a> <a id="25726" href="plfa.Decidable.html#25726" class="Bound">B</a> <a id="25728" class="Symbol">:</a> <a id="25730" class="PrimitiveType">Set</a><a id="25733" class="Symbol">}</a> <a id="25735" class="Symbol">(</a><a id="25736" href="plfa.Decidable.html#25736" class="Bound">x</a> <a id="25738" class="Symbol">:</a> <a id="25740" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="25744" href="plfa.Decidable.html#25724" class="Bound">A</a><a id="25745" class="Symbol">)</a> <a id="25747" class="Symbol">(</a><a id="25748" href="plfa.Decidable.html#25748" class="Bound">y</a> <a id="25750" class="Symbol">:</a> <a id="25752" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="25756" href="plfa.Decidable.html#25726" class="Bound">B</a><a id="25757" class="Symbol">)</a> <a id="25759" class="Symbol">→</a> <a id="25761" href="plfa.Decidable.html#17169" class="Function Operator">⌊</a> <a id="25763" href="plfa.Decidable.html#25736" class="Bound">x</a> <a id="25765" href="plfa.Decidable.html#17169" class="Function Operator">⌋</a> <a id="25767" href="plfa.Decidable.html#20572" class="Function Operator">∨</a> <a id="25769" href="plfa.Decidable.html#17169" class="Function Operator">⌊</a> <a id="25771" href="plfa.Decidable.html#25748" class="Bound">y</a> <a id="25773" href="plfa.Decidable.html#17169" class="Function Operator">⌋</a> <a id="25775" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="25777" href="plfa.Decidable.html#17169" class="Function Operator">⌊</a> <a id="25779" href="plfa.Decidable.html#25736" class="Bound">x</a> <a id="25781" href="plfa.Decidable.html#21149" class="Function Operator">⊎-dec</a> <a id="25787" href="plfa.Decidable.html#25748" class="Bound">y</a> <a id="25789" href="plfa.Decidable.html#17169" class="Function Operator">⌋</a>
  <a id="not-¬"></a><a id="25793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#25793" class="Postulate">not-¬</a> <a id="25799" class="Symbol">:</a> <a id="25801" class="Symbol">∀</a> <a id="25803" class="Symbol">{</a><a id="25804" href="plfa.Decidable.html#25804" class="Bound">A</a> <a id="25806" class="Symbol">:</a> <a id="25808" class="PrimitiveType">Set</a><a id="25811" class="Symbol">}</a> <a id="25813" class="Symbol">(</a><a id="25814" href="plfa.Decidable.html#25814" class="Bound">x</a> <a id="25816" class="Symbol">:</a> <a id="25818" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="25822" href="plfa.Decidable.html#25804" class="Bound">A</a><a id="25823" class="Symbol">)</a> <a id="25825" class="Symbol">→</a> <a id="25827" href="plfa.Decidable.html#22304" class="Function">not</a> <a id="25831" href="plfa.Decidable.html#17169" class="Function Operator">⌊</a> <a id="25833" href="plfa.Decidable.html#25814" class="Bound">x</a> <a id="25835" href="plfa.Decidable.html#17169" class="Function Operator">⌋</a> <a id="25837" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="25839" href="plfa.Decidable.html#17169" class="Function Operator">⌊</a> <a id="25841" href="plfa.Decidable.html#22488" class="Function">¬?</a> <a id="25844" href="plfa.Decidable.html#25814" class="Bound">x</a> <a id="25846" href="plfa.Decidable.html#17169" class="Function Operator">⌋</a>
</pre>{% endraw %}
{::comment}
#### Exercise `iff-erasure` (recommended)
{:/}

#### 练习 `iff-erasure` （推荐）

{::comment}
Give analogues of the `_⇔_` operation from
Chapter [Isomorphism][plfa.Isomorphism#iff],
operation on booleans and decidables, and also show the corresponding erasure:
{:/}

给出与 [Isomorphism][plfa.Isomorphism#iff] 章节中 `_↔_` 相对应的布尔值与可判定的值的操作，
并证明其对应的擦除：

{% raw %}<pre class="Agda"><a id="26210" class="Keyword">postulate</a>
  <a id="_iff_"></a><a id="26222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#26222" class="Postulate Operator">_iff_</a> <a id="26228" class="Symbol">:</a> <a id="26230" href="plfa.Decidable.html#2552" class="Datatype">Bool</a> <a id="26235" class="Symbol">→</a> <a id="26237" href="plfa.Decidable.html#2552" class="Datatype">Bool</a> <a id="26242" class="Symbol">→</a> <a id="26244" href="plfa.Decidable.html#2552" class="Datatype">Bool</a>
  <a id="_⇔-dec_"></a><a id="26251" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#26251" class="Postulate Operator">_⇔-dec_</a> <a id="26259" class="Symbol">:</a> <a id="26261" class="Symbol">∀</a> <a id="26263" class="Symbol">{</a><a id="26264" href="plfa.Decidable.html#26264" class="Bound">A</a> <a id="26266" href="plfa.Decidable.html#26266" class="Bound">B</a> <a id="26268" class="Symbol">:</a> <a id="26270" class="PrimitiveType">Set</a><a id="26273" class="Symbol">}</a> <a id="26275" class="Symbol">→</a> <a id="26277" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="26281" href="plfa.Decidable.html#26264" class="Bound">A</a> <a id="26283" class="Symbol">→</a> <a id="26285" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="26289" href="plfa.Decidable.html#26266" class="Bound">B</a> <a id="26291" class="Symbol">→</a> <a id="26293" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="26297" class="Symbol">(</a><a id="26298" href="plfa.Decidable.html#26264" class="Bound">A</a> <a id="26300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14837" class="Record Operator">⇔</a> <a id="26302" href="plfa.Decidable.html#26266" class="Bound">B</a><a id="26303" class="Symbol">)</a>
  <a id="iff-⇔"></a><a id="26307" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Decidable.md %}{% raw %}#26307" class="Postulate">iff-⇔</a> <a id="26313" class="Symbol">:</a> <a id="26315" class="Symbol">∀</a> <a id="26317" class="Symbol">{</a><a id="26318" href="plfa.Decidable.html#26318" class="Bound">A</a> <a id="26320" href="plfa.Decidable.html#26320" class="Bound">B</a> <a id="26322" class="Symbol">:</a> <a id="26324" class="PrimitiveType">Set</a><a id="26327" class="Symbol">}</a> <a id="26329" class="Symbol">(</a><a id="26330" href="plfa.Decidable.html#26330" class="Bound">x</a> <a id="26332" class="Symbol">:</a> <a id="26334" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="26338" href="plfa.Decidable.html#26318" class="Bound">A</a><a id="26339" class="Symbol">)</a> <a id="26341" class="Symbol">(</a><a id="26342" href="plfa.Decidable.html#26342" class="Bound">y</a> <a id="26344" class="Symbol">:</a> <a id="26346" href="plfa.Decidable.html#9968" class="Datatype">Dec</a> <a id="26350" href="plfa.Decidable.html#26320" class="Bound">B</a><a id="26351" class="Symbol">)</a> <a id="26353" class="Symbol">→</a> <a id="26355" href="plfa.Decidable.html#17169" class="Function Operator">⌊</a> <a id="26357" href="plfa.Decidable.html#26330" class="Bound">x</a> <a id="26359" href="plfa.Decidable.html#17169" class="Function Operator">⌋</a> <a id="26361" href="plfa.Decidable.html#26222" class="Postulate Operator">iff</a> <a id="26365" href="plfa.Decidable.html#17169" class="Function Operator">⌊</a> <a id="26367" href="plfa.Decidable.html#26342" class="Bound">y</a> <a id="26369" href="plfa.Decidable.html#17169" class="Function Operator">⌋</a> <a id="26371" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="26373" href="plfa.Decidable.html#17169" class="Function Operator">⌊</a> <a id="26375" href="plfa.Decidable.html#26330" class="Bound">x</a> <a id="26377" href="plfa.Decidable.html#26251" class="Postulate Operator">⇔-dec</a> <a id="26383" href="plfa.Decidable.html#26342" class="Bound">y</a> <a id="26385" href="plfa.Decidable.html#17169" class="Function Operator">⌋</a>
</pre>{% endraw %}
{::comment}
{% raw %}<pre class="Agda"><a id="26408" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="26445" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## Standard Library
{:/}

## 标准库

{% raw %}<pre class="Agda"><a id="26513" class="Keyword">import</a> <a id="26520" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html" class="Module">Data.Bool.Base</a> <a id="26535" class="Keyword">using</a> <a id="26541" class="Symbol">(</a><a id="26542" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Bool.html#135" class="Datatype">Bool</a><a id="26546" class="Symbol">;</a> <a id="26548" href="Agda.Builtin.Bool.html#160" class="InductiveConstructor">true</a><a id="26552" class="Symbol">;</a> <a id="26554" href="Agda.Builtin.Bool.html#154" class="InductiveConstructor">false</a><a id="26559" class="Symbol">;</a> <a id="26561" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1480" class="Function">T</a><a id="26562" class="Symbol">;</a> <a id="26564" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1015" class="Function Operator">_∧_</a><a id="26567" class="Symbol">;</a> <a id="26569" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#1073" class="Function Operator">_∨_</a><a id="26572" class="Symbol">;</a> <a id="26574" href="https://agda.github.io/agda-stdlib/v1.1/Data.Bool.Base.html#961" class="Function">not</a><a id="26577" class="Symbol">)</a>
<a id="26579" class="Keyword">import</a> <a id="26586" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="26595" class="Keyword">using</a> <a id="26601" class="Symbol">(</a><a id="26602" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#4585" class="Function Operator">_≤?_</a><a id="26606" class="Symbol">)</a>
<a id="26608" class="Keyword">import</a> <a id="26615" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="26632" class="Keyword">using</a> <a id="26638" class="Symbol">(</a><a id="26639" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a><a id="26642" class="Symbol">;</a> <a id="26644" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a><a id="26647" class="Symbol">;</a> <a id="26649" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a><a id="26651" class="Symbol">)</a>
<a id="26653" class="Keyword">import</a> <a id="26660" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.html" class="Module">Relation.Nullary.Decidable</a> <a id="26687" class="Keyword">using</a> <a id="26693" class="Symbol">(</a><a id="26694" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#753" class="Function Operator">⌊_⌋</a><a id="26697" class="Symbol">;</a> <a id="26699" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#926" class="Function">toWitness</a><a id="26708" class="Symbol">;</a> <a id="26710" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Decidable.Core.html#1062" class="Function">fromWitness</a><a id="26721" class="Symbol">)</a>
<a id="26723" class="Keyword">import</a> <a id="26730" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="26756" class="Keyword">using</a> <a id="26762" class="Symbol">(</a><a id="26763" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Negation.html#1115" class="Function">¬?</a><a id="26765" class="Symbol">)</a>
<a id="26767" class="Keyword">import</a> <a id="26774" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html" class="Module">Relation.Nullary.Product</a> <a id="26799" class="Keyword">using</a> <a id="26805" class="Symbol">(</a><a id="26806" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Product.html#585" class="Function Operator">_×-dec_</a><a id="26813" class="Symbol">)</a>
<a id="26815" class="Keyword">import</a> <a id="26822" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html" class="Module">Relation.Nullary.Sum</a> <a id="26843" class="Keyword">using</a> <a id="26849" class="Symbol">(</a><a id="26850" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.Sum.html#668" class="Function Operator">_⊎-dec_</a><a id="26857" class="Symbol">)</a>
<a id="26859" class="Keyword">import</a> <a id="26866" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.html" class="Module">Relation.Binary</a> <a id="26882" class="Keyword">using</a> <a id="26888" class="Symbol">(</a><a id="26889" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.Core.html#5557" class="Function">Decidable</a><a id="26898" class="Symbol">)</a>
</pre>{% endraw %}

## Unicode

{::comment}
    ∧  U+2227  LOGICAL AND (\and, \wedge)
    ∨  U+2228  LOGICAL OR (\or, \vee)
    ⊃  U+2283  SUPERSET OF (\sup)
    ᵇ  U+1D47  MODIFIER LETTER SMALL B  (\^b)
    ⌊  U+230A  LEFT FLOOR (\cll)
    ⌋  U+230B  RIGHT FLOOR (\clr)
{:/}

    ∧  U+2227  逻辑和 (\and, \wedge)
    ∨  U+2228  逻辑或 (\or, \vee)
    ⊃  U+2283  超集 (\sup)
    ᵇ  U+1D47  修饰符小写 B  (\^b)
    ⌊  U+230A  左向下取整 (\cll)
    ⌋  U+230B  右向下取整 (\clr)
