---
src: ./src/plfa/Connectives.lagda.md
title     : "Connectives: 合取、析取与蕴涵"
layout    : page
prev      : /Isomorphism/
permalink : /Connectives/
next      : /Negation/
translators : ["Fangyi Zhou"]
progress  : 100
---

{% raw %}<pre class="Agda"><a id="188" class="Keyword">module</a> <a id="195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}" class="Module">plfa.Connectives</a> <a id="212" class="Keyword">where</a>
</pre>{% endraw %}
<!-- The ⊥ ⊎ A ≅ A exercise requires a (inj₁ ()) pattern,
     which the reader will not have seen. Restore this
     exercise, and possibly also associativity? Take the
     exercises from the final sections on distributivity
     and exponentials? -->

{::comment}
This chapter introduces the basic logical connectives, by observing a
correspondence between connectives of logic and data types, a
principle known as _Propositions as Types_:
{:/}

本章节介绍基础的逻辑运算符。我们使用逻辑运算符与数据类型之间的对应关系，
即*命题即类型*原理（Propositions as Types）。

{::comment}
  * _conjunction_ is _product_,
  * _disjunction_ is _sum_,
  * _true_ is _unit type_,
  * _false_ is _empty type_,
  * _implication_ is _function space_.
{:/}

  * *合取*（Conjunction）即是*积*（Product）
  * *析取*（Disjunction）即是*和*（Sum）
  * *真*（True）即是*单元类型*（Unit Type）
  * *假*（False）即是*空类型*（Empty Type）
  * *蕴涵*（Implication）即是*函数空间*（Function Space）

{::comment}
## Imports
{:/}

## 导入

{% raw %}<pre class="Agda"><a id="1140" class="Keyword">import</a> <a id="1147" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="1185" class="Symbol">as</a> <a id="1188" class="Module">Eq</a>
<a id="1191" class="Keyword">open</a> <a id="1196" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="1199" class="Keyword">using</a> <a id="1205" class="Symbol">(</a><a id="1206" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="1209" class="Symbol">;</a> <a id="1211" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="1215" class="Symbol">)</a>
<a id="1217" class="Keyword">open</a> <a id="1222" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a>
<a id="1237" class="Keyword">open</a> <a id="1242" class="Keyword">import</a> <a id="1249" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="1258" class="Keyword">using</a> <a id="1264" class="Symbol">(</a><a id="1265" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1266" class="Symbol">)</a>
<a id="1268" class="Keyword">open</a> <a id="1273" class="Keyword">import</a> <a id="1280" href="https://agda.github.io/agda-stdlib/v1.1/Function.html" class="Module">Function</a> <a id="1289" class="Keyword">using</a> <a id="1295" class="Symbol">(</a><a id="1296" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">_∘_</a><a id="1299" class="Symbol">)</a>
<a id="1301" class="Keyword">open</a> <a id="1306" class="Keyword">import</a> <a id="1313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}" class="Module">plfa.Isomorphism</a> <a id="1330" class="Keyword">using</a> <a id="1336" class="Symbol">(</a><a id="1337" href="plfa.Isomorphism.html#5424" class="Record Operator">_≃_</a><a id="1340" class="Symbol">;</a> <a id="1342" href="plfa.Isomorphism.html#11500" class="Record Operator">_≲_</a><a id="1345" class="Symbol">;</a> <a id="1347" href="plfa.Isomorphism.html#3728" class="Postulate">extensionality</a><a id="1361" class="Symbol">)</a>
<a id="1363" class="Keyword">open</a> <a id="1368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10568" class="Module">plfa.Isomorphism.≃-Reasoning</a>
</pre>{% endraw %}

{::comment}
## Conjunction is product
{:/}

## 合取即是积

{::comment}
Given two propositions `A` and `B`, the conjunction `A × B` holds
if both `A` holds and `B` holds.  We formalise this idea by
declaring a suitable inductive type:
{:/}

给定两个命题 `A` 和 `B`，其合取 `A × B` 成立当 `A` 成立和 `B` 成立。
我们将这样的概念形式化，使用如下的归纳类型：

{% raw %}<pre class="Agda"><a id="1715" class="Keyword">data</a> <a id="_×_"></a><a id="1720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1720" class="Datatype Operator">_×_</a> <a id="1724" class="Symbol">(</a><a id="1725" href="plfa.Connectives.html#1725" class="Bound">A</a> <a id="1727" href="plfa.Connectives.html#1727" class="Bound">B</a> <a id="1729" class="Symbol">:</a> <a id="1731" class="PrimitiveType">Set</a><a id="1734" class="Symbol">)</a> <a id="1736" class="Symbol">:</a> <a id="1738" class="PrimitiveType">Set</a> <a id="1742" class="Keyword">where</a>

  <a id="_×_.⟨_,_⟩"></a><a id="1751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨_,_⟩</a> <a id="1757" class="Symbol">:</a>
      <a id="1765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1725" class="Bound">A</a>
    <a id="1771" class="Symbol">→</a> <a id="1773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1727" class="Bound">B</a>
      <a id="1781" class="Comment">-----</a>
    <a id="1791" class="Symbol">→</a> <a id="1793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1725" class="Bound">A</a> <a id="1795" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="1797" href="plfa.Connectives.html#1727" class="Bound">B</a>
</pre>{% endraw %}
{::comment}
Evidence that `A × B` holds is of the form `⟨ M , N ⟩`, where `M`
provides evidence that `A` holds and `N` provides evidence that `B`
holds.
{:/}

`A × B` 成立的证明由 `⟨ M , N ⟩` 的形式表现，其中 `M` 是 `A` 成立的证明，
`N` 是 `B` 成立的证明。

{::comment}
Given evidence that `A × B` holds, we can conclude that either
`A` holds or `B` holds:
{:/}

给定 `A × B` 成立的证明，我们可以得出 `A` 成立或者 `B` 成立。

{% raw %}<pre class="Agda"><a id="proj₁"></a><a id="2185" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2185" class="Function">proj₁</a> <a id="2191" class="Symbol">:</a> <a id="2193" class="Symbol">∀</a> <a id="2195" class="Symbol">{</a><a id="2196" href="plfa.Connectives.html#2196" class="Bound">A</a> <a id="2198" href="plfa.Connectives.html#2198" class="Bound">B</a> <a id="2200" class="Symbol">:</a> <a id="2202" class="PrimitiveType">Set</a><a id="2205" class="Symbol">}</a>
  <a id="2209" class="Symbol">→</a> <a id="2211" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2196" class="Bound">A</a> <a id="2213" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="2215" href="plfa.Connectives.html#2198" class="Bound">B</a>
    <a id="2221" class="Comment">-----</a>
  <a id="2229" class="Symbol">→</a> <a id="2231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2196" class="Bound">A</a>
<a id="2233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2185" class="Function">proj₁</a> <a id="2239" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="2241" href="plfa.Connectives.html#2241" class="Bound">x</a> <a id="2243" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="2245" href="plfa.Connectives.html#2245" class="Bound">y</a> <a id="2247" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="2249" class="Symbol">=</a> <a id="2251" href="plfa.Connectives.html#2241" class="Bound">x</a>

<a id="proj₂"></a><a id="2254" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2254" class="Function">proj₂</a> <a id="2260" class="Symbol">:</a> <a id="2262" class="Symbol">∀</a> <a id="2264" class="Symbol">{</a><a id="2265" href="plfa.Connectives.html#2265" class="Bound">A</a> <a id="2267" href="plfa.Connectives.html#2267" class="Bound">B</a> <a id="2269" class="Symbol">:</a> <a id="2271" class="PrimitiveType">Set</a><a id="2274" class="Symbol">}</a>
  <a id="2278" class="Symbol">→</a> <a id="2280" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2265" class="Bound">A</a> <a id="2282" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="2284" href="plfa.Connectives.html#2267" class="Bound">B</a>
    <a id="2290" class="Comment">-----</a>
  <a id="2298" class="Symbol">→</a> <a id="2300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2267" class="Bound">B</a>
<a id="2302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2254" class="Function">proj₂</a> <a id="2308" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="2310" href="plfa.Connectives.html#2310" class="Bound">x</a> <a id="2312" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="2314" href="plfa.Connectives.html#2314" class="Bound">y</a> <a id="2316" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="2318" class="Symbol">=</a> <a id="2320" href="plfa.Connectives.html#2314" class="Bound">y</a>
</pre>{% endraw %}
{::comment}
If `L` provides evidence that `A × B` holds, then `proj₁ L` provides evidence
that `A` holds, and `proj₂ L` provides evidence that `B` holds.
{:/}

如果 `L` 是 `A × B` 成立的证据, 那么 `proj₁ L` 是 `A` 成立的证据，
`proj₂ L` 是 `B` 成立的证据。

{::comment}
Equivalently, we could also declare conjunction as a record type:
{:/}

等价地，我们亦可以将合取定义为一个记录类型：

{% raw %}<pre class="Agda"><a id="2673" class="Keyword">record</a> <a id="_×′_"></a><a id="2680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2680" class="Record Operator">_×′_</a> <a id="2685" class="Symbol">(</a><a id="2686" href="plfa.Connectives.html#2686" class="Bound">A</a> <a id="2688" href="plfa.Connectives.html#2688" class="Bound">B</a> <a id="2690" class="Symbol">:</a> <a id="2692" class="PrimitiveType">Set</a><a id="2695" class="Symbol">)</a> <a id="2697" class="Symbol">:</a> <a id="2699" class="PrimitiveType">Set</a> <a id="2703" class="Keyword">where</a>
  <a id="2711" class="Keyword">field</a>
    <a id="_×′_.proj₁′"></a><a id="2721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2721" class="Field">proj₁′</a> <a id="2728" class="Symbol">:</a> <a id="2730" href="plfa.Connectives.html#2686" class="Bound">A</a>
    <a id="_×′_.proj₂′"></a><a id="2736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2736" class="Field">proj₂′</a> <a id="2743" class="Symbol">:</a> <a id="2745" href="plfa.Connectives.html#2688" class="Bound">B</a>
<a id="2747" class="Keyword">open</a> <a id="2752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#2680" class="Module Operator">_×′_</a>
</pre>{% endraw %}
{::comment}
Here record construction
{:/}

在这里，记录的构造

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

{::comment}
corresponds to the term
{:/}

对应

    ⟨ M , N ⟩

{::comment}
where `M` is a term of type `A` and `N` is a term of type `B`.
{:/}

其中 `M` 是 `A` 类型的项，`N` 是 `B` 类型的项。

{::comment}
When `⟨_,_⟩` appears in a term on the right-hand side of an equation
we refer to it as a _constructor_, and when it appears in a pattern on
the left-hand side of an equation we refer to it as a _destructor_.
We may also refer to `proj₁` and `proj₂` as destructors, since they
play a similar role.
{:/}

当 `⟨_,_⟩` 在等式右手边的项中出现的时候，我们将其称作*构造器*（Constructor），
当它出现在等式左边时，我们将其称作*析构器*（Destructor）。我们亦可将 `proj₁` 和 `proj₂`
称作析构器，因为它们起到相似的效果。

{::comment}
Other terminology refers to `⟨_,_⟩` as _introducing_ a conjunction, and
to `proj₁` and `proj₂` as _eliminating_ a conjunction; indeed, the
former is sometimes given the name `×-I` and the latter two the names
`×-E₁` and `×-E₂`.  As we read the rules from top to bottom,
introduction and elimination do what they say on the tin: the first
_introduces_ a formula for the connective, which appears in the
conclusion but not in the hypotheses; the second _eliminates_ a
formula for the connective, which appears in a hypothesis but not in
the conclusion. An introduction rule describes under what conditions
we say the connective holds---how to _define_ the connective. An
elimination rule describes what we may conclude when the connective
holds---how to _use_ the connective.
{:/}

其他的术语将 `⟨_,_⟩` 称作*引入*（Introduce）合取，将 `proj₁` 和 `proj₂` 称作*消去*（Eliminate）合取。
前者亦记作 `×-I`，后者 `×-E₁` 和 `×-E₂`。如果我们从上到下来阅读这些规则，引入和消去
正如其名字所说的那样：第一条*引入*一个运算符，所以运算符出现在结论中，而不是假设中；
第二条*消去*一个带有运算符的式子，而运算符出现在假设中，而不是结论中。引入规则描述了
运算符在什么情况下成立——即怎么样*定义*一个运算符。消去规则描述了运算符成立时，可以得出
什么样的结论——即怎么样*使用*一个运算符。

{::comment}
(The paragraph above was adopted from "Propositions as Types", Philip Wadler,
_Communications of the ACM_, December 2015.)
{:/}

（上面一段内容由此处改编得来：*Propositions as Types*，作者：Philip Wadler，
发表于 《ACM 通讯》，2015 年 9 月）

{::comment}
In this case, applying each destructor and reassembling the results with the
constructor is the identity over products:
{:/}

在这样的情况下，先使用析构器，再使用构造器将结果重组，得到还是原来的积。

{% raw %}<pre class="Agda"><a id="η-×"></a><a id="4979" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4979" class="Function">η-×</a> <a id="4983" class="Symbol">:</a> <a id="4985" class="Symbol">∀</a> <a id="4987" class="Symbol">{</a><a id="4988" href="plfa.Connectives.html#4988" class="Bound">A</a> <a id="4990" href="plfa.Connectives.html#4990" class="Bound">B</a> <a id="4992" class="Symbol">:</a> <a id="4994" class="PrimitiveType">Set</a><a id="4997" class="Symbol">}</a> <a id="4999" class="Symbol">(</a><a id="5000" href="plfa.Connectives.html#5000" class="Bound">w</a> <a id="5002" class="Symbol">:</a> <a id="5004" href="plfa.Connectives.html#4988" class="Bound">A</a> <a id="5006" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="5008" href="plfa.Connectives.html#4990" class="Bound">B</a><a id="5009" class="Symbol">)</a> <a id="5011" class="Symbol">→</a> <a id="5013" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="5015" href="plfa.Connectives.html#2185" class="Function">proj₁</a> <a id="5021" href="plfa.Connectives.html#5000" class="Bound">w</a> <a id="5023" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="5025" href="plfa.Connectives.html#2254" class="Function">proj₂</a> <a id="5031" href="plfa.Connectives.html#5000" class="Bound">w</a> <a id="5033" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="5035" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5037" href="plfa.Connectives.html#5000" class="Bound">w</a>
<a id="5039" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#4979" class="Function">η-×</a> <a id="5043" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="5045" href="plfa.Connectives.html#5045" class="Bound">x</a> <a id="5047" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="5049" href="plfa.Connectives.html#5049" class="Bound">y</a> <a id="5051" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="5053" class="Symbol">=</a> <a id="5055" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
The pattern matching on the left-hand side is essential, since
replacing `w` by `⟨ x , y ⟩` allows both sides of the
propositional equality to simplify to the same term.
{:/}

左手边的模式匹配是必要的。用 `⟨ x , y ⟩` 来替换 `w` 让等式的两边可以化简成相同的项。

{::comment}
We set the precedence of conjunction so that it binds less
tightly than anything save disjunction:
{:/}

我们设置合取的优先级，使它与除了析取之外结合的都不紧密：

{% raw %}<pre class="Agda"><a id="5457" class="Keyword">infixr</a> <a id="5464" class="Number">2</a> <a id="5466" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1720" class="Datatype Operator">_×_</a>
</pre>{% endraw %}
{::comment}
Thus, `m ≤ n × n ≤ p` parses as `(m ≤ n) × (n ≤ p)`.
{:/}

因此，`m ≤ n × n ≤ p` 解析为 `(m ≤ n) × (n ≤ p)`。

{::comment}
Given two types `A` and `B`, we refer to `A × B` as the
_product_ of `A` and `B`.  In set theory, it is also sometimes
called the _Cartesian product_, and in computing it corresponds
to a _record_ type. Among other reasons for
calling it the product, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A × B` has `m * n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members:
{:/}

给定两个类型 `A` 和 `B`，我们将 `A × B` 称为 `A` 与 `B` 的*积*。
在集合论中它也被称作*笛卡尔积*（Cartesian Product），在计算机科学中它对应*记录*类型。
如果类型 `A` 有 `m` 个不同的成员，类型 `B` 有 `n` 个不同的成员，
那么类型 `A × B` 有 `m * n` 个不同的成员。这也是它被称为积的原因之一。
例如，考虑有两个成员的 `Bool` 类型，和有三个成员的 `Tri` 类型：

{% raw %}<pre class="Agda"><a id="6326" class="Keyword">data</a> <a id="Bool"></a><a id="6331" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6331" class="Datatype">Bool</a> <a id="6336" class="Symbol">:</a> <a id="6338" class="PrimitiveType">Set</a> <a id="6342" class="Keyword">where</a>
  <a id="Bool.true"></a><a id="6350" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6350" class="InductiveConstructor">true</a>  <a id="6356" class="Symbol">:</a> <a id="6358" href="plfa.Connectives.html#6331" class="Datatype">Bool</a>
  <a id="Bool.false"></a><a id="6365" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6365" class="InductiveConstructor">false</a> <a id="6371" class="Symbol">:</a> <a id="6373" href="plfa.Connectives.html#6331" class="Datatype">Bool</a>

<a id="6379" class="Keyword">data</a> <a id="Tri"></a><a id="6384" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6384" class="Datatype">Tri</a> <a id="6388" class="Symbol">:</a> <a id="6390" class="PrimitiveType">Set</a> <a id="6394" class="Keyword">where</a>
  <a id="Tri.aa"></a><a id="6402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6402" class="InductiveConstructor">aa</a> <a id="6405" class="Symbol">:</a> <a id="6407" href="plfa.Connectives.html#6384" class="Datatype">Tri</a>
  <a id="Tri.bb"></a><a id="6413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6413" class="InductiveConstructor">bb</a> <a id="6416" class="Symbol">:</a> <a id="6418" href="plfa.Connectives.html#6384" class="Datatype">Tri</a>
  <a id="Tri.cc"></a><a id="6424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6424" class="InductiveConstructor">cc</a> <a id="6427" class="Symbol">:</a> <a id="6429" href="plfa.Connectives.html#6384" class="Datatype">Tri</a>
</pre>{% endraw %}
{::comment}
Then the type `Bool × Tri` has six members:
{:/}

那么，`Bool × Tri` 类型有如下的六个成员：

    ⟨ true  , aa ⟩    ⟨ true  , bb ⟩    ⟨ true ,  cc ⟩
    ⟨ false , aa ⟩    ⟨ false , bb ⟩    ⟨ false , cc ⟩

{::comment}
For example, the following function enumerates all
possible arguments of type `Bool × Tri`:
{:/}

下面的函数枚举了所有类型为 `Bool × Tri` 的参数：

{% raw %}<pre class="Agda"><a id="×-count"></a><a id="6787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6787" class="Function">×-count</a> <a id="6795" class="Symbol">:</a> <a id="6797" href="plfa.Connectives.html#6331" class="Datatype">Bool</a> <a id="6802" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="6804" href="plfa.Connectives.html#6384" class="Datatype">Tri</a> <a id="6808" class="Symbol">→</a> <a id="6810" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="6812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6787" class="Function">×-count</a> <a id="6820" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="6822" href="plfa.Connectives.html#6350" class="InductiveConstructor">true</a>  <a id="6828" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="6830" href="plfa.Connectives.html#6402" class="InductiveConstructor">aa</a> <a id="6833" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a>  <a id="6836" class="Symbol">=</a>  <a id="6839" class="Number">1</a>
<a id="6841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6787" class="Function">×-count</a> <a id="6849" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="6851" href="plfa.Connectives.html#6350" class="InductiveConstructor">true</a>  <a id="6857" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="6859" href="plfa.Connectives.html#6413" class="InductiveConstructor">bb</a> <a id="6862" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a>  <a id="6865" class="Symbol">=</a>  <a id="6868" class="Number">2</a>
<a id="6870" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6787" class="Function">×-count</a> <a id="6878" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="6880" href="plfa.Connectives.html#6350" class="InductiveConstructor">true</a>  <a id="6886" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="6888" href="plfa.Connectives.html#6424" class="InductiveConstructor">cc</a> <a id="6891" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a>  <a id="6894" class="Symbol">=</a>  <a id="6897" class="Number">3</a>
<a id="6899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6787" class="Function">×-count</a> <a id="6907" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="6909" href="plfa.Connectives.html#6365" class="InductiveConstructor">false</a> <a id="6915" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="6917" href="plfa.Connectives.html#6402" class="InductiveConstructor">aa</a> <a id="6920" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a>  <a id="6923" class="Symbol">=</a>  <a id="6926" class="Number">4</a>
<a id="6928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6787" class="Function">×-count</a> <a id="6936" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="6938" href="plfa.Connectives.html#6365" class="InductiveConstructor">false</a> <a id="6944" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="6946" href="plfa.Connectives.html#6413" class="InductiveConstructor">bb</a> <a id="6949" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a>  <a id="6952" class="Symbol">=</a>  <a id="6955" class="Number">5</a>
<a id="6957" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6787" class="Function">×-count</a> <a id="6965" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="6967" href="plfa.Connectives.html#6365" class="InductiveConstructor">false</a> <a id="6973" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="6975" href="plfa.Connectives.html#6424" class="InductiveConstructor">cc</a> <a id="6978" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a>  <a id="6981" class="Symbol">=</a>  <a id="6984" class="Number">6</a>
</pre>{% endraw %}
{::comment}
Product on types also shares a property with product on numbers in
that there is a sense in which it is commutative and associative.  In
particular, product is commutative and associative _up to
isomorphism_.
{:/}

类型上的积与数的积有相似的性质——它们满足交换律和结合律。
更确切地说，积在*在同构意义下*满足交换律和结合率。

{::comment}
For commutativity, the `to` function swaps a pair, taking `⟨ x , y ⟩` to
`⟨ y , x ⟩`, and the `from` function does the same (up to renaming).
Instantiating the patterns correctly in `from∘to` and `to∘from` is essential.
Replacing the definition of `from∘to` by `λ w → refl` will not work;
and similarly for `to∘from`:
{:/}

对于交换律，`to` 函数将有序对交换，将 `⟨ x , y ⟩` 变为 `⟨ y , x ⟩`，`from`
函数亦是如此（忽略命名）。
在 `from∘to` 和 `to∘from` 中正确地实例化要匹配的模式是很重要的。
使用 `λ w → refl` 作为 `from∘to` 的定义是不可行的，`to∘from` 同理。

{% raw %}<pre class="Agda"><a id="×-comm"></a><a id="7783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#7783" class="Function">×-comm</a> <a id="7790" class="Symbol">:</a> <a id="7792" class="Symbol">∀</a> <a id="7794" class="Symbol">{</a><a id="7795" href="plfa.Connectives.html#7795" class="Bound">A</a> <a id="7797" href="plfa.Connectives.html#7797" class="Bound">B</a> <a id="7799" class="Symbol">:</a> <a id="7801" class="PrimitiveType">Set</a><a id="7804" class="Symbol">}</a> <a id="7806" class="Symbol">→</a> <a id="7808" href="plfa.Connectives.html#7795" class="Bound">A</a> <a id="7810" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="7812" href="plfa.Connectives.html#7797" class="Bound">B</a> <a id="7814" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5424" class="Record Operator">≃</a> <a id="7816" href="plfa.Connectives.html#7797" class="Bound">B</a> <a id="7818" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="7820" href="plfa.Connectives.html#7795" class="Bound">A</a>
<a id="7822" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#7783" class="Function">×-comm</a> <a id="7829" class="Symbol">=</a>
  <a id="7833" class="Keyword">record</a>
    <a id="7844" class="Symbol">{</a> <a id="7846" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5464" class="Field">to</a>       <a id="7855" class="Symbol">=</a>  <a id="7858" class="Symbol">λ{</a> <a id="7861" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="7863" href="plfa.Connectives.html#7863" class="Bound">x</a> <a id="7865" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="7867" href="plfa.Connectives.html#7867" class="Bound">y</a> <a id="7869" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="7871" class="Symbol">→</a> <a id="7873" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="7875" href="plfa.Connectives.html#7867" class="Bound">y</a> <a id="7877" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="7879" href="plfa.Connectives.html#7863" class="Bound">x</a> <a id="7881" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="7883" class="Symbol">}</a>
    <a id="7889" class="Symbol">;</a> <a id="7891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5481" class="Field">from</a>     <a id="7900" class="Symbol">=</a>  <a id="7903" class="Symbol">λ{</a> <a id="7906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="7908" href="plfa.Connectives.html#7908" class="Bound">y</a> <a id="7910" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="7912" href="plfa.Connectives.html#7912" class="Bound">x</a> <a id="7914" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="7916" class="Symbol">→</a> <a id="7918" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="7920" href="plfa.Connectives.html#7912" class="Bound">x</a> <a id="7922" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="7924" href="plfa.Connectives.html#7908" class="Bound">y</a> <a id="7926" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="7928" class="Symbol">}</a>
    <a id="7934" class="Symbol">;</a> <a id="7936" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5498" class="Field">from∘to</a>  <a id="7945" class="Symbol">=</a>  <a id="7948" class="Symbol">λ{</a> <a id="7951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="7953" href="plfa.Connectives.html#7953" class="Bound">x</a> <a id="7955" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="7957" href="plfa.Connectives.html#7957" class="Bound">y</a> <a id="7959" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="7961" class="Symbol">→</a> <a id="7963" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="7968" class="Symbol">}</a>
    <a id="7974" class="Symbol">;</a> <a id="7976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5540" class="Field">to∘from</a>  <a id="7985" class="Symbol">=</a>  <a id="7988" class="Symbol">λ{</a> <a id="7991" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="7993" href="plfa.Connectives.html#7993" class="Bound">y</a> <a id="7995" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="7997" href="plfa.Connectives.html#7997" class="Bound">x</a> <a id="7999" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="8001" class="Symbol">→</a> <a id="8003" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="8008" class="Symbol">}</a>
    <a id="8014" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Being _commutative_ is different from being _commutative up to
isomorphism_.  Compare the two statements:
{:/}

满足*交换律*和*在同构意义下满足交换律*是不一样的。比较下列两个命题：

    m * n ≡ n * m
    A × B ≃ B × A

{::comment}
In the first case, we might have that `m` is `2` and `n` is `3`, and
both `m * n` and `n * m` are equal to `6`.  In the second case, we
might have that `A` is `Bool` and `B` is `Tri`, and `Bool × Tri` is
_not_ the same as `Tri × Bool`.  But there is an isomorphism between
the two types.  For instance, `⟨ true , aa ⟩`, which is a member of the
former, corresponds to `⟨ aa , true ⟩`, which is a member of the latter.
{:/}

在第一个情况下，我们可能有 `m` 是 `2`、`n` 是 `3`，那么 `m * n` 和 `n * m` 都是 `6`。
在第二个情况下，我们可能有 `A` 是 `Bool` 和 `B` 是 `Tri`，但是 `Bool × Tri` 和
`Tri × Bool` *不是*一样的。但是存在一个两者之间的同构。例如：`⟨ true , aa ⟩` 是前者的成员，
其对应后者的成员 `⟨ aa , true ⟩`。

{::comment}
For associativity, the `to` function reassociates two uses of pairing,
taking `⟨ ⟨ x , y ⟩ , z ⟩` to `⟨ x , ⟨ y , z ⟩ ⟩`, and the `from` function does
the inverse.  Again, the evidence of left and right inverse requires
matching against a suitable pattern to enable simplification:
{:/}

对于结合律来说，`to` 函数将两个有序对进行重组：将 `⟨ ⟨ x , y ⟩ , z ⟩` 转换为 `⟨ x , ⟨ y , z ⟩ ⟩`，
`from` 函数则为其逆。同样，左逆和右逆的证明需要在一个合适的模式来匹配，从而可以直接化简：

{% raw %}<pre class="Agda"><a id="×-assoc"></a><a id="9294" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#9294" class="Function">×-assoc</a> <a id="9302" class="Symbol">:</a> <a id="9304" class="Symbol">∀</a> <a id="9306" class="Symbol">{</a><a id="9307" href="plfa.Connectives.html#9307" class="Bound">A</a> <a id="9309" href="plfa.Connectives.html#9309" class="Bound">B</a> <a id="9311" href="plfa.Connectives.html#9311" class="Bound">C</a> <a id="9313" class="Symbol">:</a> <a id="9315" class="PrimitiveType">Set</a><a id="9318" class="Symbol">}</a> <a id="9320" class="Symbol">→</a> <a id="9322" class="Symbol">(</a><a id="9323" href="plfa.Connectives.html#9307" class="Bound">A</a> <a id="9325" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="9327" href="plfa.Connectives.html#9309" class="Bound">B</a><a id="9328" class="Symbol">)</a> <a id="9330" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="9332" href="plfa.Connectives.html#9311" class="Bound">C</a> <a id="9334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5424" class="Record Operator">≃</a> <a id="9336" href="plfa.Connectives.html#9307" class="Bound">A</a> <a id="9338" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="9340" class="Symbol">(</a><a id="9341" href="plfa.Connectives.html#9309" class="Bound">B</a> <a id="9343" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="9345" href="plfa.Connectives.html#9311" class="Bound">C</a><a id="9346" class="Symbol">)</a>
<a id="9348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#9294" class="Function">×-assoc</a> <a id="9356" class="Symbol">=</a>
  <a id="9360" class="Keyword">record</a>
    <a id="9371" class="Symbol">{</a> <a id="9373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5464" class="Field">to</a>      <a id="9381" class="Symbol">=</a> <a id="9383" class="Symbol">λ{</a> <a id="9386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="9388" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="9390" href="plfa.Connectives.html#9390" class="Bound">x</a> <a id="9392" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9394" href="plfa.Connectives.html#9394" class="Bound">y</a> <a id="9396" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9398" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9400" href="plfa.Connectives.html#9400" class="Bound">z</a> <a id="9402" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9404" class="Symbol">→</a> <a id="9406" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="9408" href="plfa.Connectives.html#9390" class="Bound">x</a> <a id="9410" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9412" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="9414" href="plfa.Connectives.html#9394" class="Bound">y</a> <a id="9416" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9418" href="plfa.Connectives.html#9400" class="Bound">z</a> <a id="9420" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9422" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9424" class="Symbol">}</a>
    <a id="9430" class="Symbol">;</a> <a id="9432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5481" class="Field">from</a>    <a id="9440" class="Symbol">=</a> <a id="9442" class="Symbol">λ{</a> <a id="9445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="9447" href="plfa.Connectives.html#9447" class="Bound">x</a> <a id="9449" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9451" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="9453" href="plfa.Connectives.html#9453" class="Bound">y</a> <a id="9455" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9457" href="plfa.Connectives.html#9457" class="Bound">z</a> <a id="9459" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9461" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9463" class="Symbol">→</a> <a id="9465" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="9467" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="9469" href="plfa.Connectives.html#9447" class="Bound">x</a> <a id="9471" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9473" href="plfa.Connectives.html#9453" class="Bound">y</a> <a id="9475" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9477" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9479" href="plfa.Connectives.html#9457" class="Bound">z</a> <a id="9481" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9483" class="Symbol">}</a>
    <a id="9489" class="Symbol">;</a> <a id="9491" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5498" class="Field">from∘to</a> <a id="9499" class="Symbol">=</a> <a id="9501" class="Symbol">λ{</a> <a id="9504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="9506" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="9508" href="plfa.Connectives.html#9508" class="Bound">x</a> <a id="9510" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9512" href="plfa.Connectives.html#9512" class="Bound">y</a> <a id="9514" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9516" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9518" href="plfa.Connectives.html#9518" class="Bound">z</a> <a id="9520" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9522" class="Symbol">→</a> <a id="9524" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="9529" class="Symbol">}</a>
    <a id="9535" class="Symbol">;</a> <a id="9537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5540" class="Field">to∘from</a> <a id="9545" class="Symbol">=</a> <a id="9547" class="Symbol">λ{</a> <a id="9550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="9552" href="plfa.Connectives.html#9552" class="Bound">x</a> <a id="9554" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9556" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="9558" href="plfa.Connectives.html#9558" class="Bound">y</a> <a id="9560" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="9562" href="plfa.Connectives.html#9562" class="Bound">z</a> <a id="9564" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9566" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="9568" class="Symbol">→</a> <a id="9570" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="9575" class="Symbol">}</a>
    <a id="9581" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Being _associative_ is not the same as being _associative
up to isomorphism_.  Compare the two statements:
{:/}

满足*结合律*和*在同构意义下满足结合律*是不一样的。比较下列两个命题：

    (m * n) * p ≡ m * (n * p)
    (A × B) × C ≃ A × (B × C)

{::comment}
For example, the type `(ℕ × Bool) × Tri` is _not_ the same as `ℕ ×
(Bool × Tri)`. But there is an isomorphism between the two types. For
instance `⟨ ⟨ 1 , true ⟩ , aa ⟩`, which is a member of the former,
corresponds to `⟨ 1 , ⟨ true , aa ⟩ ⟩`, which is a member of the latter.
{:/}

举个例子，`(ℕ × Bool) × Tri` 与 `ℕ × (Bool × Tri)` *不同*，但是两个类型之间
存在同构。例如 `⟨ ⟨ 1 , true ⟩ , aa ⟩`，一个前者的成员，与 `⟨ 1 , ⟨ true , aa ⟩ ⟩`，
一个后者的成员，相对应。

{::comment}
#### Exercise `⇔≃×` (recommended)
{:/}

#### 练习 `⇔≃×` （推荐）

{::comment}
Show that `A ⇔ B` as defined [earlier][plfa.Isomorphism#iff]
is isomorphic to `(A → B) × (B → A)`.
{:/}

证明[之前][plfa.Isomorphism#iff]定义的 `A ⇔ B` 与 `(A → B) × (B → A)` 同构。

{::comment}
{% raw %}<pre class="Agda"><a id="10519" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="10556" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## Truth is unit
{:/}

## 真即是单元类型

{::comment}
Truth `⊤` always holds. We formalise this idea by
declaring a suitable inductive type:
{:/}

恒真 `⊤` 恒成立。我们将这个概念用合适的归纳类型来形式化：

{% raw %}<pre class="Agda"><a id="10763" class="Keyword">data</a> <a id="⊤"></a><a id="10768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10768" class="Datatype">⊤</a> <a id="10770" class="Symbol">:</a> <a id="10772" class="PrimitiveType">Set</a> <a id="10776" class="Keyword">where</a>

  <a id="⊤.tt"></a><a id="10785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10785" class="InductiveConstructor">tt</a> <a id="10788" class="Symbol">:</a>
    <a id="10794" class="Comment">--</a>
    <a id="10801" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10768" class="Datatype">⊤</a>
</pre>{% endraw %}
{::comment}
Evidence that `⊤` holds is of the form `tt`.
{:/}

`⊤` 成立的证明由 `tt` 的形式构成。

{::comment}
There is an introduction rule, but no elimination rule.
Given evidence that `⊤` holds, there is nothing more of interest we
can conclude.  Since truth always holds, knowing that it holds tells
us nothing new.
{:/}

恒真有引入规则，但没有消去规则。给定一个 `⊤` 成立的证明，我们不能得出任何有趣的结论。
因为恒真恒成立，知道恒真成立不会给我们带来新的知识。

{::comment}
The nullary case of `η-×` is `η-⊤`, which asserts that any
value of type `⊤` must be equal to `tt`:
{:/}

`η-×` 的 零元形式是 `η-⊤`，其断言了任何 `⊤` 类型的值一定等于 `tt`：

{% raw %}<pre class="Agda"><a id="η-⊤"></a><a id="11365" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#11365" class="Function">η-⊤</a> <a id="11369" class="Symbol">:</a> <a id="11371" class="Symbol">∀</a> <a id="11373" class="Symbol">(</a><a id="11374" href="plfa.Connectives.html#11374" class="Bound">w</a> <a id="11376" class="Symbol">:</a> <a id="11378" href="plfa.Connectives.html#10768" class="Datatype">⊤</a><a id="11379" class="Symbol">)</a> <a id="11381" class="Symbol">→</a> <a id="11383" href="plfa.Connectives.html#10785" class="InductiveConstructor">tt</a> <a id="11386" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11388" href="plfa.Connectives.html#11374" class="Bound">w</a>
<a id="11390" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#11365" class="Function">η-⊤</a> <a id="11394" href="plfa.Connectives.html#10785" class="InductiveConstructor">tt</a> <a id="11397" class="Symbol">=</a> <a id="11399" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
The pattern matching on the left-hand side is essential.  Replacing
`w` by `tt` allows both sides of the propositional equality to
simplify to the same term.
{:/}

左手边的模式匹配是必要的。将 `w` 替换为 `tt` 让等式两边可以化简为相同的值。

{::comment}
We refer to `⊤` as the _unit_ type. And, indeed,
type `⊤` has exactly one member, `tt`.  For example, the following
function enumerates all possible arguments of type `⊤`:

我们将 `⊤` 称为*单元*类型（Unit Type）。实际上，`⊤` 类型只有一个成员 `tt`。
例如，下面的函数枚举了所有 `⊤` 类型的参数：

{:/}
{% raw %}<pre class="Agda"><a id="⊤-count"></a><a id="11901" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#11901" class="Function">⊤-count</a> <a id="11909" class="Symbol">:</a> <a id="11911" href="plfa.Connectives.html#10768" class="Datatype">⊤</a> <a id="11913" class="Symbol">→</a> <a id="11915" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="11917" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#11901" class="Function">⊤-count</a> <a id="11925" href="plfa.Connectives.html#10785" class="InductiveConstructor">tt</a> <a id="11928" class="Symbol">=</a> <a id="11930" class="Number">1</a>
</pre>{% endraw %}
{::comment}
For numbers, one is the identity of multiplication. Correspondingly,
unit is the identity of product _up to isomorphism_.  For left
identity, the `to` function takes `⟨ tt , x ⟩` to `x`, and the `from`
function does the inverse.  The evidence of left inverse requires
matching against a suitable pattern to enable simplification:
{:/}

对于数来说，1 是乘法的幺元。对应地，单元是积的幺元（*在同构意义下*）。对于左幺元来说，
`to` 函数将 `⟨ tt , x ⟩` 转换成 `x`， `from` 函数则是其反函数。左逆的证明需要
匹配一个合适的模式来化简：

{% raw %}<pre class="Agda"><a id="⊤-identityˡ"></a><a id="12405" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#12405" class="Function">⊤-identityˡ</a> <a id="12417" class="Symbol">:</a> <a id="12419" class="Symbol">∀</a> <a id="12421" class="Symbol">{</a><a id="12422" href="plfa.Connectives.html#12422" class="Bound">A</a> <a id="12424" class="Symbol">:</a> <a id="12426" class="PrimitiveType">Set</a><a id="12429" class="Symbol">}</a> <a id="12431" class="Symbol">→</a> <a id="12433" href="plfa.Connectives.html#10768" class="Datatype">⊤</a> <a id="12435" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="12437" href="plfa.Connectives.html#12422" class="Bound">A</a> <a id="12439" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5424" class="Record Operator">≃</a> <a id="12441" href="plfa.Connectives.html#12422" class="Bound">A</a>
<a id="12443" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#12405" class="Function">⊤-identityˡ</a> <a id="12455" class="Symbol">=</a>
  <a id="12459" class="Keyword">record</a>
    <a id="12470" class="Symbol">{</a> <a id="12472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5464" class="Field">to</a>      <a id="12480" class="Symbol">=</a> <a id="12482" class="Symbol">λ{</a> <a id="12485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="12487" href="plfa.Connectives.html#10785" class="InductiveConstructor">tt</a> <a id="12490" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="12492" href="plfa.Connectives.html#12492" class="Bound">x</a> <a id="12494" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="12496" class="Symbol">→</a> <a id="12498" href="plfa.Connectives.html#12492" class="Bound">x</a> <a id="12500" class="Symbol">}</a>
    <a id="12506" class="Symbol">;</a> <a id="12508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5481" class="Field">from</a>    <a id="12516" class="Symbol">=</a> <a id="12518" class="Symbol">λ{</a> <a id="12521" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#12521" class="Bound">x</a> <a id="12523" class="Symbol">→</a> <a id="12525" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="12527" href="plfa.Connectives.html#10785" class="InductiveConstructor">tt</a> <a id="12530" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="12532" href="plfa.Connectives.html#12521" class="Bound">x</a> <a id="12534" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="12536" class="Symbol">}</a>
    <a id="12542" class="Symbol">;</a> <a id="12544" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5498" class="Field">from∘to</a> <a id="12552" class="Symbol">=</a> <a id="12554" class="Symbol">λ{</a> <a id="12557" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="12559" href="plfa.Connectives.html#10785" class="InductiveConstructor">tt</a> <a id="12562" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="12564" href="plfa.Connectives.html#12564" class="Bound">x</a> <a id="12566" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="12568" class="Symbol">→</a> <a id="12570" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="12575" class="Symbol">}</a>
    <a id="12581" class="Symbol">;</a> <a id="12583" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5540" class="Field">to∘from</a> <a id="12591" class="Symbol">=</a> <a id="12593" class="Symbol">λ{</a> <a id="12596" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#12596" class="Bound">x</a> <a id="12598" class="Symbol">→</a> <a id="12600" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="12605" class="Symbol">}</a>
    <a id="12611" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Having an _identity_ is different from having an identity
_up to isomorphism_.  Compare the two statements:
{:/}

*幺元*和*在同构意义下的幺元*是不一样的。比较下列两个命题：

    1 * m ≡ m
    ⊤ × A ≃ A

{::comment}
In the first case, we might have that `m` is `2`, and both
`1 * m` and `m` are equal to `2`.  In the second
case, we might have that `A` is `Bool`, and `⊤ × Bool` is _not_ the
same as `Bool`.  But there is an isomorphism between the two types.
For instance, `⟨ tt , true ⟩`, which is a member of the former,
corresponds to `true`, which is a member of the latter.
{:/}

在第一种情况下，我们可能有 `m` 是 `2`，那么 `1 * m` 和 `m` 都为 `2`。
在第二种情况下，我们可能有 `A` 是 `Bool`，但是 `⊤ × Bool` 和 `Bool` 是不同的。
例如：`⟨ tt , true ⟩` 是前者的成员，其对应后者的成员 `true`。

{::comment}
Right identity follows from commutativity of product and left identity:
{:/}

右幺元可以由积的交换律得来：

{% raw %}<pre class="Agda"><a id="⊤-identityʳ"></a><a id="13447" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#13447" class="Function">⊤-identityʳ</a> <a id="13459" class="Symbol">:</a> <a id="13461" class="Symbol">∀</a> <a id="13463" class="Symbol">{</a><a id="13464" href="plfa.Connectives.html#13464" class="Bound">A</a> <a id="13466" class="Symbol">:</a> <a id="13468" class="PrimitiveType">Set</a><a id="13471" class="Symbol">}</a> <a id="13473" class="Symbol">→</a> <a id="13475" class="Symbol">(</a><a id="13476" href="plfa.Connectives.html#13464" class="Bound">A</a> <a id="13478" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="13480" href="plfa.Connectives.html#10768" class="Datatype">⊤</a><a id="13481" class="Symbol">)</a> <a id="13483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5424" class="Record Operator">≃</a> <a id="13485" href="plfa.Connectives.html#13464" class="Bound">A</a>
<a id="13487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#13447" class="Function">⊤-identityʳ</a> <a id="13499" class="Symbol">{</a><a id="13500" href="plfa.Connectives.html#13500" class="Bound">A</a><a id="13501" class="Symbol">}</a> <a id="13503" class="Symbol">=</a>
  <a id="13507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10644" class="Function Operator">≃-begin</a>
    <a id="13519" class="Symbol">(</a><a id="13520" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#13500" class="Bound">A</a> <a id="13522" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="13524" href="plfa.Connectives.html#10768" class="Datatype">⊤</a><a id="13525" class="Symbol">)</a>
  <a id="13529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10728" class="Function Operator">≃⟨</a> <a id="13532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#7783" class="Function">×-comm</a> <a id="13539" href="plfa.Isomorphism.html#10728" class="Function Operator">⟩</a>
    <a id="13545" class="Symbol">(</a><a id="13546" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#10768" class="Datatype">⊤</a> <a id="13548" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="13550" href="plfa.Connectives.html#13500" class="Bound">A</a><a id="13551" class="Symbol">)</a>
  <a id="13555" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10728" class="Function Operator">≃⟨</a> <a id="13558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#12405" class="Function">⊤-identityˡ</a> <a id="13570" href="plfa.Isomorphism.html#10728" class="Function Operator">⟩</a>
    <a id="13576" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#13500" class="Bound">A</a>
  <a id="13580" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10847" class="Function Operator">≃-∎</a>
</pre>{% endraw %}
{::comment}
Here we have used a chain of isomorphisms, analogous to that used for
equality.
{:/}

我们在此使用了同构链，与等式链相似。

{::comment}
## Disjunction is sum
{:/}

## 析取即是和

{::comment}
Given two propositions `A` and `B`, the disjunction `A ⊎ B` holds
if either `A` holds or `B` holds.  We formalise this idea by
declaring a suitable inductive type:
{:/}

给定两个命题 `A` 和 `B`，析取 `A ⊎ B` 在 `A` 成立或者 `B` 成立时成立。
我们将这个概念用合适的归纳类型来形式化：

{% raw %}<pre class="Agda"><a id="14015" class="Keyword">data</a> <a id="_⊎_"></a><a id="14020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14020" class="Datatype Operator">_⊎_</a> <a id="14024" class="Symbol">(</a><a id="14025" href="plfa.Connectives.html#14025" class="Bound">A</a> <a id="14027" href="plfa.Connectives.html#14027" class="Bound">B</a> <a id="14029" class="Symbol">:</a> <a id="14031" class="PrimitiveType">Set</a><a id="14034" class="Symbol">)</a> <a id="14036" class="Symbol">:</a> <a id="14038" class="PrimitiveType">Set</a> <a id="14042" class="Keyword">where</a>

  <a id="_⊎_.inj₁"></a><a id="14051" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14051" class="InductiveConstructor">inj₁</a> <a id="14056" class="Symbol">:</a>
      <a id="14064" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14025" class="Bound">A</a>
      <a id="14072" class="Comment">-----</a>
    <a id="14082" class="Symbol">→</a> <a id="14084" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14025" class="Bound">A</a> <a id="14086" href="plfa.Connectives.html#14020" class="Datatype Operator">⊎</a> <a id="14088" href="plfa.Connectives.html#14027" class="Bound">B</a>

  <a id="_⊎_.inj₂"></a><a id="14093" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14093" class="InductiveConstructor">inj₂</a> <a id="14098" class="Symbol">:</a>
      <a id="14106" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14027" class="Bound">B</a>
      <a id="14114" class="Comment">-----</a>
    <a id="14124" class="Symbol">→</a> <a id="14126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14025" class="Bound">A</a> <a id="14128" href="plfa.Connectives.html#14020" class="Datatype Operator">⊎</a> <a id="14130" href="plfa.Connectives.html#14027" class="Bound">B</a>
</pre>{% endraw %}
{::comment}
Evidence that `A ⊎ B` holds is either of the form `inj₁ M`, where `M`
provides evidence that `A` holds, or `inj₂ N`, where `N` provides
evidence that `B` holds.
{:/}

`A ⊎ B` 成立的证明有两个形式： `inj₁ M`，其中 `M` 是 `A` 成立的证明，或者
`inj₂ N`，其中 `N` 是 `B` 成立的证明。

{::comment}
Given evidence that `A → C` and `B → C` both hold, then given
evidence that `A ⊎ B` holds we can conclude that `C` holds:
{:/}

给定 `A → C` 和 `B → C` 成立的证明，那么给定一个 `A ⊎ B` 的证明，我们可以得出 `C` 成立：

{% raw %}<pre class="Agda"><a id="case-⊎"></a><a id="14603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14603" class="Function">case-⊎</a> <a id="14610" class="Symbol">:</a> <a id="14612" class="Symbol">∀</a> <a id="14614" class="Symbol">{</a><a id="14615" href="plfa.Connectives.html#14615" class="Bound">A</a> <a id="14617" href="plfa.Connectives.html#14617" class="Bound">B</a> <a id="14619" href="plfa.Connectives.html#14619" class="Bound">C</a> <a id="14621" class="Symbol">:</a> <a id="14623" class="PrimitiveType">Set</a><a id="14626" class="Symbol">}</a>
  <a id="14630" class="Symbol">→</a> <a id="14632" class="Symbol">(</a><a id="14633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14615" class="Bound">A</a> <a id="14635" class="Symbol">→</a> <a id="14637" href="plfa.Connectives.html#14619" class="Bound">C</a><a id="14638" class="Symbol">)</a>
  <a id="14642" class="Symbol">→</a> <a id="14644" class="Symbol">(</a><a id="14645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14617" class="Bound">B</a> <a id="14647" class="Symbol">→</a> <a id="14649" href="plfa.Connectives.html#14619" class="Bound">C</a><a id="14650" class="Symbol">)</a>
  <a id="14654" class="Symbol">→</a> <a id="14656" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14615" class="Bound">A</a> <a id="14658" href="plfa.Connectives.html#14020" class="Datatype Operator">⊎</a> <a id="14660" href="plfa.Connectives.html#14617" class="Bound">B</a>
    <a id="14666" class="Comment">-----------</a>
  <a id="14680" class="Symbol">→</a> <a id="14682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14619" class="Bound">C</a>
<a id="14684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14603" class="Function">case-⊎</a> <a id="14691" href="plfa.Connectives.html#14691" class="Bound">f</a> <a id="14693" href="plfa.Connectives.html#14693" class="Bound">g</a> <a id="14695" class="Symbol">(</a><a id="14696" href="plfa.Connectives.html#14051" class="InductiveConstructor">inj₁</a> <a id="14701" href="plfa.Connectives.html#14701" class="Bound">x</a><a id="14702" class="Symbol">)</a> <a id="14704" class="Symbol">=</a> <a id="14706" href="plfa.Connectives.html#14691" class="Bound">f</a> <a id="14708" href="plfa.Connectives.html#14701" class="Bound">x</a>
<a id="14710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14603" class="Function">case-⊎</a> <a id="14717" href="plfa.Connectives.html#14717" class="Bound">f</a> <a id="14719" href="plfa.Connectives.html#14719" class="Bound">g</a> <a id="14721" class="Symbol">(</a><a id="14722" href="plfa.Connectives.html#14093" class="InductiveConstructor">inj₂</a> <a id="14727" href="plfa.Connectives.html#14727" class="Bound">y</a><a id="14728" class="Symbol">)</a> <a id="14730" class="Symbol">=</a> <a id="14732" href="plfa.Connectives.html#14719" class="Bound">g</a> <a id="14734" href="plfa.Connectives.html#14727" class="Bound">y</a>
</pre>{% endraw %}
{::comment}
Pattern matching against `inj₁` and `inj₂` is typical of how we exploit
evidence that a disjunction holds.
{:/}

对 `inj₁` 和 `inj₂` 进行模式匹配，是我们使用析取成立的证明的常见方法。

{::comment}
When `inj₁` and `inj₂` appear on the right-hand side of an equation we
refer to them as _constructors_, and when they appear on the
left-hand side we refer to them as _destructors_.  We also refer to
`case-⊎` as a destructor, since it plays a similar role.  Other
terminology refers to `inj₁` and `inj₂` as _introducing_ a
disjunction, and to `case-⊎` as _eliminating_ a disjunction; indeed
the former are sometimes given the names `⊎-I₁` and `⊎-I₂` and the
latter the name `⊎-E`.
{:/}

当 `inj₁` 和 `inj₂` 在等式右手边出现的时候，我们将其称作*构造器*，
当它出现在等式左边时，我们将其称作*析构器*。我们亦可将 `case-⊎`
称作析构器，因为它们起到相似的效果。其他术语将 `inj₁` 和 `inj₂` 称为*引入*析取，
将 `case-⊎` 称为*消去*析取。前者亦被称为 `⊎-I₁` 和 `⊎-I₂`，后者 `⊎-E`。

{::comment}
Applying the destructor to each of the constructors is the identity:
{:/}

对每个构造器使用析构器得到的是原来的值：

{% raw %}<pre class="Agda"><a id="η-⊎"></a><a id="15708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#15708" class="Function">η-⊎</a> <a id="15712" class="Symbol">:</a> <a id="15714" class="Symbol">∀</a> <a id="15716" class="Symbol">{</a><a id="15717" href="plfa.Connectives.html#15717" class="Bound">A</a> <a id="15719" href="plfa.Connectives.html#15719" class="Bound">B</a> <a id="15721" class="Symbol">:</a> <a id="15723" class="PrimitiveType">Set</a><a id="15726" class="Symbol">}</a> <a id="15728" class="Symbol">(</a><a id="15729" href="plfa.Connectives.html#15729" class="Bound">w</a> <a id="15731" class="Symbol">:</a> <a id="15733" href="plfa.Connectives.html#15717" class="Bound">A</a> <a id="15735" href="plfa.Connectives.html#14020" class="Datatype Operator">⊎</a> <a id="15737" href="plfa.Connectives.html#15719" class="Bound">B</a><a id="15738" class="Symbol">)</a> <a id="15740" class="Symbol">→</a> <a id="15742" href="plfa.Connectives.html#14603" class="Function">case-⊎</a> <a id="15749" href="plfa.Connectives.html#14051" class="InductiveConstructor">inj₁</a> <a id="15754" href="plfa.Connectives.html#14093" class="InductiveConstructor">inj₂</a> <a id="15759" href="plfa.Connectives.html#15729" class="Bound">w</a> <a id="15761" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="15763" href="plfa.Connectives.html#15729" class="Bound">w</a>
<a id="15765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#15708" class="Function">η-⊎</a> <a id="15769" class="Symbol">(</a><a id="15770" href="plfa.Connectives.html#14051" class="InductiveConstructor">inj₁</a> <a id="15775" href="plfa.Connectives.html#15775" class="Bound">x</a><a id="15776" class="Symbol">)</a> <a id="15778" class="Symbol">=</a> <a id="15780" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="15785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#15708" class="Function">η-⊎</a> <a id="15789" class="Symbol">(</a><a id="15790" href="plfa.Connectives.html#14093" class="InductiveConstructor">inj₂</a> <a id="15795" href="plfa.Connectives.html#15795" class="Bound">y</a><a id="15796" class="Symbol">)</a> <a id="15798" class="Symbol">=</a> <a id="15800" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
More generally, we can also throw in an arbitrary function from a disjunction:
{:/}

更普遍地来说，我们亦可对于析取使用一个任意的函数：

{% raw %}<pre class="Agda"><a id="uniq-⊎"></a><a id="15938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#15938" class="Function">uniq-⊎</a> <a id="15945" class="Symbol">:</a> <a id="15947" class="Symbol">∀</a> <a id="15949" class="Symbol">{</a><a id="15950" href="plfa.Connectives.html#15950" class="Bound">A</a> <a id="15952" href="plfa.Connectives.html#15952" class="Bound">B</a> <a id="15954" href="plfa.Connectives.html#15954" class="Bound">C</a> <a id="15956" class="Symbol">:</a> <a id="15958" class="PrimitiveType">Set</a><a id="15961" class="Symbol">}</a> <a id="15963" class="Symbol">(</a><a id="15964" href="plfa.Connectives.html#15964" class="Bound">h</a> <a id="15966" class="Symbol">:</a> <a id="15968" href="plfa.Connectives.html#15950" class="Bound">A</a> <a id="15970" href="plfa.Connectives.html#14020" class="Datatype Operator">⊎</a> <a id="15972" href="plfa.Connectives.html#15952" class="Bound">B</a> <a id="15974" class="Symbol">→</a> <a id="15976" href="plfa.Connectives.html#15954" class="Bound">C</a><a id="15977" class="Symbol">)</a> <a id="15979" class="Symbol">(</a><a id="15980" href="plfa.Connectives.html#15980" class="Bound">w</a> <a id="15982" class="Symbol">:</a> <a id="15984" href="plfa.Connectives.html#15950" class="Bound">A</a> <a id="15986" href="plfa.Connectives.html#14020" class="Datatype Operator">⊎</a> <a id="15988" href="plfa.Connectives.html#15952" class="Bound">B</a><a id="15989" class="Symbol">)</a> <a id="15991" class="Symbol">→</a>
  <a id="15995" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14603" class="Function">case-⊎</a> <a id="16002" class="Symbol">(</a><a id="16003" href="plfa.Connectives.html#15964" class="Bound">h</a> <a id="16005" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="16007" href="plfa.Connectives.html#14051" class="InductiveConstructor">inj₁</a><a id="16011" class="Symbol">)</a> <a id="16013" class="Symbol">(</a><a id="16014" href="plfa.Connectives.html#15964" class="Bound">h</a> <a id="16016" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="16018" href="plfa.Connectives.html#14093" class="InductiveConstructor">inj₂</a><a id="16022" class="Symbol">)</a> <a id="16024" href="plfa.Connectives.html#15980" class="Bound">w</a> <a id="16026" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16028" href="plfa.Connectives.html#15964" class="Bound">h</a> <a id="16030" href="plfa.Connectives.html#15980" class="Bound">w</a>
<a id="16032" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#15938" class="Function">uniq-⊎</a> <a id="16039" href="plfa.Connectives.html#16039" class="Bound">h</a> <a id="16041" class="Symbol">(</a><a id="16042" href="plfa.Connectives.html#14051" class="InductiveConstructor">inj₁</a> <a id="16047" href="plfa.Connectives.html#16047" class="Bound">x</a><a id="16048" class="Symbol">)</a> <a id="16050" class="Symbol">=</a> <a id="16052" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="16057" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#15938" class="Function">uniq-⊎</a> <a id="16064" href="plfa.Connectives.html#16064" class="Bound">h</a> <a id="16066" class="Symbol">(</a><a id="16067" href="plfa.Connectives.html#14093" class="InductiveConstructor">inj₂</a> <a id="16072" href="plfa.Connectives.html#16072" class="Bound">y</a><a id="16073" class="Symbol">)</a> <a id="16075" class="Symbol">=</a> <a id="16077" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
The pattern matching on the left-hand side is essential.  Replacing
`w` by `inj₁ x` allows both sides of the propositional equality to
simplify to the same term, and similarly for `inj₂ y`.
{:/}

左手边的模式匹配是必要的。用 `inj₁ x` 来替换 `w` 让等式的两边可以化简成相同的项，
`inj₂ y` 同理。

{::comment}
We set the precedence of disjunction so that it binds less tightly
than any other declared operator:
{:/}

我们设置析取的优先级，使它与任何已经定义的运算符都结合的不紧密：

{% raw %}<pre class="Agda"><a id="16515" class="Keyword">infix</a> <a id="16521" class="Number">1</a> <a id="16523" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14020" class="Datatype Operator">_⊎_</a>
</pre>{% endraw %}
{::comment}
Thus, `A × C ⊎ B × C` parses as `(A × C) ⊎ (B × C)`.
{:/}

因此 `A × C ⊎ B × C` 解析为 `(A × C) ⊎ (B × C)`。

{::comment}
Given two types `A` and `B`, we refer to `A ⊎ B` as the
_sum_ of `A` and `B`.  In set theory, it is also sometimes
called the _disjoint union_, and in computing it corresponds
to a _variant record_ type. Among other reasons for
calling it the sum, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A ⊎ B` has `m + n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members, as defined earlier.
Then the type `Bool ⊎ Tri` has five
members:
{:/}

给定两个类型 `A` 和 `B`，我们将 `A ⊎ B` 称为 `A` 与 `B` 的*和*。
在集合论中它也被称作*不交并*（Disjoint Union），在计算机科学中它对应*变体记录*类型。
如果类型 `A` 有 `m` 个不同的成员，类型 `B` 有 `n` 个不同的成员，
那么类型 `A ⊎ B` 有 `m + n` 个不同的成员。这也是它被称为和的原因之一。
例如，考虑有两个成员的 `Bool` 类型，和有三个成员的 `Tri` 类型，如之前的定义。
那么，`Bool ⊎ Tri` 类型有如下的五个成员：

    inj₁ true     inj₂ aa
    inj₁ false    inj₂ bb
                  inj₂ cc

{::comment}
For example, the following function enumerates all
possible arguments of type `Bool ⊎ Tri`:
{:/}

下面的函数枚举了所有类型为 `Bool ⊎ Tri` 的参数：

{% raw %}<pre class="Agda"><a id="⊎-count"></a><a id="17700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#17700" class="Function">⊎-count</a> <a id="17708" class="Symbol">:</a> <a id="17710" href="plfa.Connectives.html#6331" class="Datatype">Bool</a> <a id="17715" href="plfa.Connectives.html#14020" class="Datatype Operator">⊎</a> <a id="17717" href="plfa.Connectives.html#6384" class="Datatype">Tri</a> <a id="17721" class="Symbol">→</a> <a id="17723" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="17725" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#17700" class="Function">⊎-count</a> <a id="17733" class="Symbol">(</a><a id="17734" href="plfa.Connectives.html#14051" class="InductiveConstructor">inj₁</a> <a id="17739" href="plfa.Connectives.html#6350" class="InductiveConstructor">true</a><a id="17743" class="Symbol">)</a>   <a id="17747" class="Symbol">=</a>  <a id="17750" class="Number">1</a>
<a id="17752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#17700" class="Function">⊎-count</a> <a id="17760" class="Symbol">(</a><a id="17761" href="plfa.Connectives.html#14051" class="InductiveConstructor">inj₁</a> <a id="17766" href="plfa.Connectives.html#6365" class="InductiveConstructor">false</a><a id="17771" class="Symbol">)</a>  <a id="17774" class="Symbol">=</a>  <a id="17777" class="Number">2</a>
<a id="17779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#17700" class="Function">⊎-count</a> <a id="17787" class="Symbol">(</a><a id="17788" href="plfa.Connectives.html#14093" class="InductiveConstructor">inj₂</a> <a id="17793" href="plfa.Connectives.html#6402" class="InductiveConstructor">aa</a><a id="17795" class="Symbol">)</a>     <a id="17801" class="Symbol">=</a>  <a id="17804" class="Number">3</a>
<a id="17806" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#17700" class="Function">⊎-count</a> <a id="17814" class="Symbol">(</a><a id="17815" href="plfa.Connectives.html#14093" class="InductiveConstructor">inj₂</a> <a id="17820" href="plfa.Connectives.html#6413" class="InductiveConstructor">bb</a><a id="17822" class="Symbol">)</a>     <a id="17828" class="Symbol">=</a>  <a id="17831" class="Number">4</a>
<a id="17833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#17700" class="Function">⊎-count</a> <a id="17841" class="Symbol">(</a><a id="17842" href="plfa.Connectives.html#14093" class="InductiveConstructor">inj₂</a> <a id="17847" href="plfa.Connectives.html#6424" class="InductiveConstructor">cc</a><a id="17849" class="Symbol">)</a>     <a id="17855" class="Symbol">=</a>  <a id="17858" class="Number">5</a>
</pre>{% endraw %}
{::comment}
Sum on types also shares a property with sum on numbers in that it is
commutative and associative _up to isomorphism_.
{:/}

类型上的和与数的和有相似的性质——它们满足交换律和结合律。
更确切地说，和在*在同构意义下*是交换和结合的。

{::comment}
#### Exercise `⊎-comm` (recommended)
{:/}

#### 练习 `⊎-comm` （推荐）

{::comment}
Show sum is commutative up to isomorphism.
{:/}

证明和类型在同构意义下满足交换律。

{::comment}
{% raw %}<pre class="Agda"><a id="18232" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="18269" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `⊎-assoc`
{:/}

#### 练习 `⊎-assoc`

{::comment}
Show sum is associative up to isomorphism.
{:/}

证明和类型在同构意义下满足结合律。

{::comment}
{% raw %}<pre class="Agda"><a id="18444" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="18481" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## False is empty
{:/}

## 假即是空类型

{::comment}
False `⊥` never holds.  We formalise this idea by declaring
a suitable inductive type:
{:/}

恒假 `⊥` 从不成立。我们将这个概念用合适的归纳类型来形式化：

{::comment}
FIXME: the code block is removed to make Agda not recognise this as code.
data ⊥ : Set where
  -- no clauses!
{:/}

{% raw %}<pre class="Agda"><a id="18817" class="Keyword">data</a> <a id="⊥"></a><a id="18822" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#18822" class="Datatype">⊥</a> <a id="18824" class="Symbol">:</a> <a id="18826" class="PrimitiveType">Set</a> <a id="18830" class="Keyword">where</a>
  <a id="18838" class="Comment">-- 没有语句！</a>
</pre>{% endraw %}
{::comment}
There is no possible evidence that `⊥` holds.
{:/}

没有 `⊥` 成立的证明。

{::comment}
Dual to `⊤`, for `⊥` there is no introduction rule but an elimination rule.
Since false never holds, knowing that it holds tells us we are in a
paradoxical situation.  Given evidence that `⊥` holds, we might
conclude anything!  This is a basic principle of logic, known in
medieval times by the Latin phrase _ex falso_, and known to children
through phrases such as "if pigs had wings, then I'd be the Queen of
Sheba".  We formalise it as follows:
{:/}

与 `⊤` 相对偶，`⊥` 没有引入规则，但是有消去规则。因为恒假从不成立，
如果它一旦成立，我们就进入了矛盾之中。给定 `⊥` 成立的证明，我们可以得出任何结论！
这是逻辑学的基本原理，又由中世纪的拉丁文词组 _ex falso_ 为名。小孩子也由诸如
“如果猪有翅膀，那我就是示巴女王”的词组中知晓。我们如下将它形式化：

{% raw %}<pre class="Agda"><a id="⊥-elim"></a><a id="19565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#19565" class="Function">⊥-elim</a> <a id="19572" class="Symbol">:</a> <a id="19574" class="Symbol">∀</a> <a id="19576" class="Symbol">{</a><a id="19577" href="plfa.Connectives.html#19577" class="Bound">A</a> <a id="19579" class="Symbol">:</a> <a id="19581" class="PrimitiveType">Set</a><a id="19584" class="Symbol">}</a>
  <a id="19588" class="Symbol">→</a> <a id="19590" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#18822" class="Datatype">⊥</a>
    <a id="19596" class="Comment">--</a>
  <a id="19601" class="Symbol">→</a> <a id="19603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#19577" class="Bound">A</a>
<a id="19605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#19565" class="Function">⊥-elim</a> <a id="19612" class="Symbol">()</a>
</pre>{% endraw %}
{::comment}
This is our first use of the _absurd pattern_ `()`.
Here since `⊥` is a type with no members, we indicate that it is
_never_ possible to match against a value of this type by using
the pattern `()`.
{:/}

这是我们第一次使用*荒谬模式*（Absurd Pattern） `()`。在这里，因为 `⊥`
是一个没有成员的类型，我们用 `()` 模式来指明这里不可能匹配任何这个类型的值。

{::comment}
The nullary case of `case-⊎` is `⊥-elim`.  By analogy,
we might have called it `case-⊥`, but chose to stick with the name
in the standard library.
{:/}

`case-⊎` 的零元形式是 `⊥-elim`。类比的来说，它应该叫做 `case-⊥`，
但是我们在此使用标准库中使用的名字。

{::comment}
The nullary case of `uniq-⊎` is `uniq-⊥`, which asserts that `⊥-elim`
is equal to any arbitrary function from `⊥`:
{:/}

`uniq-⊎` 的零元形式是 `uniq-⊥`，其断言了 `⊥-elim` 和任何取 `⊥` 的函数是等价的。

{% raw %}<pre class="Agda"><a id="uniq-⊥"></a><a id="20355" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#20355" class="Function">uniq-⊥</a> <a id="20362" class="Symbol">:</a> <a id="20364" class="Symbol">∀</a> <a id="20366" class="Symbol">{</a><a id="20367" href="plfa.Connectives.html#20367" class="Bound">C</a> <a id="20369" class="Symbol">:</a> <a id="20371" class="PrimitiveType">Set</a><a id="20374" class="Symbol">}</a> <a id="20376" class="Symbol">(</a><a id="20377" href="plfa.Connectives.html#20377" class="Bound">h</a> <a id="20379" class="Symbol">:</a> <a id="20381" href="plfa.Connectives.html#18822" class="Datatype">⊥</a> <a id="20383" class="Symbol">→</a> <a id="20385" href="plfa.Connectives.html#20367" class="Bound">C</a><a id="20386" class="Symbol">)</a> <a id="20388" class="Symbol">(</a><a id="20389" href="plfa.Connectives.html#20389" class="Bound">w</a> <a id="20391" class="Symbol">:</a> <a id="20393" href="plfa.Connectives.html#18822" class="Datatype">⊥</a><a id="20394" class="Symbol">)</a> <a id="20396" class="Symbol">→</a> <a id="20398" href="plfa.Connectives.html#19565" class="Function">⊥-elim</a> <a id="20405" href="plfa.Connectives.html#20389" class="Bound">w</a> <a id="20407" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="20409" href="plfa.Connectives.html#20377" class="Bound">h</a> <a id="20411" href="plfa.Connectives.html#20389" class="Bound">w</a>
<a id="20413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#20355" class="Function">uniq-⊥</a> <a id="20420" href="plfa.Connectives.html#20420" class="Bound">h</a> <a id="20422" class="Symbol">()</a>
</pre>{% endraw %}
{::comment}
Using the absurd pattern asserts there are no possible values for `w`,
so the equation holds trivially.
{:/}

使用荒谬模式断言了 `w` 没有任何可能的值，因此等式显然成立。

{::comment}
We refer to `⊥` as the _empty_ type. And, indeed,
type `⊥` has no members. For example, the following function
enumerates all possible arguments of type `⊥`:

我们将 `⊥` 成为*空*类型（Empty Type）。实际上，`⊥` 类型没有成员。
例如，下面的函数枚举了所有 `⊥` 类型的参数：

{:/}
{% raw %}<pre class="Agda"><a id="⊥-count"></a><a id="20836" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#20836" class="Function">⊥-count</a> <a id="20844" class="Symbol">:</a> <a id="20846" href="plfa.Connectives.html#18822" class="Datatype">⊥</a> <a id="20848" class="Symbol">→</a> <a id="20850" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="20852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#20836" class="Function">⊥-count</a> <a id="20860" class="Symbol">()</a>
</pre>{% endraw %}
{::comment}
Here again the absurd pattern `()` indicates that no value can match
type `⊥`.
{:/}

同样，荒谬模式告诉我们没有值可以来匹配类型 `⊥`。

{::comment}
For numbers, zero is the identity of addition. Correspondingly, empty
is the identity of sums _up to isomorphism_.
{:/}

对于数来说，0 是加法的幺元。对应地，空是和的幺元（*在同构意义下*）。

{::comment}
#### Exercise `⊥-identityˡ` (recommended)
{:/}

#### 练习 `⊥-identityˡ` （推荐）

{::comment}
Show empty is the left identity of sums up to isomorphism.
{:/}

证明空在同构意义下是和的左幺元。

{::comment}
{% raw %}<pre class="Agda"><a id="21363" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="21400" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `⊥-identityʳ`
{:/}

#### 练习 `⊥-identityʳ`

{::comment}
Show empty is the right identity of sums up to isomorphism.
{:/}

证明空在同构意义下是和的右幺元。

{::comment}
{% raw %}<pre class="Agda"><a id="21599" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="21636" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## Implication is function {#implication}
{:/}

## 蕴涵即是函数 {#implication}

{::comment}
Given two propositions `A` and `B`, the implication `A → B` holds if
whenever `A` holds then `B` must also hold.  We formalise implication using
the function type, which has appeared throughout this book.
{:/}

给定两个命题 `A` 和 `B`，其蕴涵 `A → B` 在任何 `A` 成立的时候，`B` 也成立时成立。
我们用函数类型来形式化蕴涵，如本书中通篇出现的那样。


{::comment}
Evidence that `A → B` holds is of the form
{:/}

`A → B` 成立的证据由下面的形式组成：

    λ (x : A) → N

{::comment}
where `N` is a term of type `B` containing as a free variable `x` of type `A`.
Given a term `L` providing evidence that `A → B` holds, and a term `M`
providing evidence that `A` holds, the term `L M` provides evidence that
`B` holds.  In other words, evidence that `A → B` holds is a function that
converts evidence that `A` holds into evidence that `B` holds.
{:/}

其中 `N` 是一个类型为 `B` 的项，其包括了一个类型为 `A` 的自由变量 `x`。
给定一个 `A → B` 成立的证明 `L`，和一个 `A` 成立的证明 `M`，那么 `L M` 是 `B` 成立的证明。
也就是说，`A → B` 成立的证明是一个函数，将 `A` 成立的证明转换成 `B` 成立的证明。

{::comment}
Put another way, if we know that `A → B` and `A` both hold,
then we may conclude that `B` holds:
{:/}

换句话说，如果知道 `A → B` 和 `A` 同时成立，那么我们可以推出 `B` 成立：

{% raw %}<pre class="Agda"><a id="→-elim"></a><a id="22856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#22856" class="Function">→-elim</a> <a id="22863" class="Symbol">:</a> <a id="22865" class="Symbol">∀</a> <a id="22867" class="Symbol">{</a><a id="22868" href="plfa.Connectives.html#22868" class="Bound">A</a> <a id="22870" href="plfa.Connectives.html#22870" class="Bound">B</a> <a id="22872" class="Symbol">:</a> <a id="22874" class="PrimitiveType">Set</a><a id="22877" class="Symbol">}</a>
  <a id="22881" class="Symbol">→</a> <a id="22883" class="Symbol">(</a><a id="22884" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#22868" class="Bound">A</a> <a id="22886" class="Symbol">→</a> <a id="22888" href="plfa.Connectives.html#22870" class="Bound">B</a><a id="22889" class="Symbol">)</a>
  <a id="22893" class="Symbol">→</a> <a id="22895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#22868" class="Bound">A</a>
    <a id="22901" class="Comment">-------</a>
  <a id="22911" class="Symbol">→</a> <a id="22913" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#22870" class="Bound">B</a>
<a id="22915" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#22856" class="Function">→-elim</a> <a id="22922" href="plfa.Connectives.html#22922" class="Bound">L</a> <a id="22924" href="plfa.Connectives.html#22924" class="Bound">M</a> <a id="22926" class="Symbol">=</a> <a id="22928" href="plfa.Connectives.html#22922" class="Bound">L</a> <a id="22930" href="plfa.Connectives.html#22924" class="Bound">M</a>
</pre>{% endraw %}
{::comment}
In medieval times, this rule was known by the name _modus ponens_.
It corresponds to function application.
{:/}

在中世纪，这条规则被叫做 _modus ponens_，它与函数应用相对应。

{::comment}
Defining a function, with a named definition or a lambda abstraction,
is referred to as _introducing_ a function,
while applying a function is referred to as _eliminating_ the function.
{:/}

定义一个函数，不管是带名字的定义或是使用 Lambda 抽象，被称为*引入*一个函数，
使用一个函数被称为*消去*一个函数。

{::comment}
Elimination followed by introduction is the identity:
{:/}

引入后接着消去，得到的还是原来的值：

{% raw %}<pre class="Agda"><a id="η-→"></a><a id="23466" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#23466" class="Function">η-→</a> <a id="23470" class="Symbol">:</a> <a id="23472" class="Symbol">∀</a> <a id="23474" class="Symbol">{</a><a id="23475" href="plfa.Connectives.html#23475" class="Bound">A</a> <a id="23477" href="plfa.Connectives.html#23477" class="Bound">B</a> <a id="23479" class="Symbol">:</a> <a id="23481" class="PrimitiveType">Set</a><a id="23484" class="Symbol">}</a> <a id="23486" class="Symbol">(</a><a id="23487" href="plfa.Connectives.html#23487" class="Bound">f</a> <a id="23489" class="Symbol">:</a> <a id="23491" href="plfa.Connectives.html#23475" class="Bound">A</a> <a id="23493" class="Symbol">→</a> <a id="23495" href="plfa.Connectives.html#23477" class="Bound">B</a><a id="23496" class="Symbol">)</a> <a id="23498" class="Symbol">→</a> <a id="23500" class="Symbol">(λ</a> <a id="23503" class="Symbol">(</a><a id="23504" href="plfa.Connectives.html#23504" class="Bound">x</a> <a id="23506" class="Symbol">:</a> <a id="23508" href="plfa.Connectives.html#23475" class="Bound">A</a><a id="23509" class="Symbol">)</a> <a id="23511" class="Symbol">→</a> <a id="23513" href="plfa.Connectives.html#23487" class="Bound">f</a> <a id="23515" href="plfa.Connectives.html#23504" class="Bound">x</a><a id="23516" class="Symbol">)</a> <a id="23518" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="23520" href="plfa.Connectives.html#23487" class="Bound">f</a>
<a id="23522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#23466" class="Function">η-→</a> <a id="23526" href="plfa.Connectives.html#23526" class="Bound">f</a> <a id="23528" class="Symbol">=</a> <a id="23530" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
Implication binds less tightly than any other operator. Thus, `A ⊎ B →
B ⊎ A` parses as `(A ⊎ B) → (B ⊎ A)`.
{:/}

蕴涵比其他的运算符结合得都不紧密。因此 `A ⊎ B → B ⊎ A` 被解析为 `(A ⊎ B) → (B ⊎ A)`。

{::comment}
Given two types `A` and `B`, we refer to `A → B` as the _function_
space from `A` to `B`.  It is also sometimes called the _exponential_,
with `B` raised to the `A` power.  Among other reasons for calling
it the exponential, note that if type `A` has `m` distinct
members, and type `B` has `n` distinct members, then the type
`A → B` has `nᵐ` distinct members.  For instance, consider a
type `Bool` with two members and a type `Tri` with three members,
as defined earlier. Then the type `Bool → Tri` has nine (that is,
three squared) members:
{:/}

给定两个类型 `A` 和 `B`，我们将 `A → B` 称为从 `A` 到 `B` 的*函数*空间。
它有时也被称作以 `B` 为底，`A` 为次数的*幂*。如果类型 `A` 有 `m` 个不同的成员，
类型 `B` 有 `n` 个不同的成员，那么类型 `A → B` 有 `nᵐ` 个不同的成员。
这也是它被称为幂的原因之一。例如，考虑有两个成员的 `Bool` 类型，和有三个成员的 `Tri` 类型，
如之前的定义。那么，`Bool → Tri` 类型有如下的九个成员（三的平方）：

    λ{true → aa; false → aa}  λ{true → aa; false → bb}  λ{true → aa; false → cc}
    λ{true → bb; false → aa}  λ{true → bb; false → bb}  λ{true → bb; false → cc}
    λ{true → cc; false → aa}  λ{true → cc; false → bb}  λ{true → cc; false → cc}

{::comment}
For example, the following function enumerates all possible
arguments of the type `Bool → Tri`:
{:/}

下面的函数枚举了所有类型为 `Bool → Tri` 的参数：

{% raw %}<pre class="Agda"><a id="→-count"></a><a id="24933" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#24933" class="Function">→-count</a> <a id="24941" class="Symbol">:</a> <a id="24943" class="Symbol">(</a><a id="24944" href="plfa.Connectives.html#6331" class="Datatype">Bool</a> <a id="24949" class="Symbol">→</a> <a id="24951" href="plfa.Connectives.html#6384" class="Datatype">Tri</a><a id="24954" class="Symbol">)</a> <a id="24956" class="Symbol">→</a> <a id="24958" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="24960" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#24933" class="Function">→-count</a> <a id="24968" href="plfa.Connectives.html#24968" class="Bound">f</a> <a id="24970" class="Keyword">with</a> <a id="24975" href="plfa.Connectives.html#24968" class="Bound">f</a> <a id="24977" href="plfa.Connectives.html#6350" class="InductiveConstructor">true</a> <a id="24982" class="Symbol">|</a> <a id="24984" href="plfa.Connectives.html#24968" class="Bound">f</a> <a id="24986" href="plfa.Connectives.html#6365" class="InductiveConstructor">false</a>
<a id="24992" class="Symbol">...</a>          <a id="25005" class="Symbol">|</a> <a id="25007" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6402" class="InductiveConstructor">aa</a>     <a id="25014" class="Symbol">|</a> <a id="25016" href="plfa.Connectives.html#6402" class="InductiveConstructor">aa</a>      <a id="25024" class="Symbol">=</a>   <a id="25028" class="Number">1</a>
<a id="25030" class="Symbol">...</a>          <a id="25043" class="Symbol">|</a> <a id="25045" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6402" class="InductiveConstructor">aa</a>     <a id="25052" class="Symbol">|</a> <a id="25054" href="plfa.Connectives.html#6413" class="InductiveConstructor">bb</a>      <a id="25062" class="Symbol">=</a>   <a id="25066" class="Number">2</a>
<a id="25068" class="Symbol">...</a>          <a id="25081" class="Symbol">|</a> <a id="25083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6402" class="InductiveConstructor">aa</a>     <a id="25090" class="Symbol">|</a> <a id="25092" href="plfa.Connectives.html#6424" class="InductiveConstructor">cc</a>      <a id="25100" class="Symbol">=</a>   <a id="25104" class="Number">3</a>
<a id="25106" class="Symbol">...</a>          <a id="25119" class="Symbol">|</a> <a id="25121" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6413" class="InductiveConstructor">bb</a>     <a id="25128" class="Symbol">|</a> <a id="25130" href="plfa.Connectives.html#6402" class="InductiveConstructor">aa</a>      <a id="25138" class="Symbol">=</a>   <a id="25142" class="Number">4</a>
<a id="25144" class="Symbol">...</a>          <a id="25157" class="Symbol">|</a> <a id="25159" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6413" class="InductiveConstructor">bb</a>     <a id="25166" class="Symbol">|</a> <a id="25168" href="plfa.Connectives.html#6413" class="InductiveConstructor">bb</a>      <a id="25176" class="Symbol">=</a>   <a id="25180" class="Number">5</a>
<a id="25182" class="Symbol">...</a>          <a id="25195" class="Symbol">|</a> <a id="25197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6413" class="InductiveConstructor">bb</a>     <a id="25204" class="Symbol">|</a> <a id="25206" href="plfa.Connectives.html#6424" class="InductiveConstructor">cc</a>      <a id="25214" class="Symbol">=</a>   <a id="25218" class="Number">6</a>
<a id="25220" class="Symbol">...</a>          <a id="25233" class="Symbol">|</a> <a id="25235" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6424" class="InductiveConstructor">cc</a>     <a id="25242" class="Symbol">|</a> <a id="25244" href="plfa.Connectives.html#6402" class="InductiveConstructor">aa</a>      <a id="25252" class="Symbol">=</a>   <a id="25256" class="Number">7</a>
<a id="25258" class="Symbol">...</a>          <a id="25271" class="Symbol">|</a> <a id="25273" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6424" class="InductiveConstructor">cc</a>     <a id="25280" class="Symbol">|</a> <a id="25282" href="plfa.Connectives.html#6413" class="InductiveConstructor">bb</a>      <a id="25290" class="Symbol">=</a>   <a id="25294" class="Number">8</a>
<a id="25296" class="Symbol">...</a>          <a id="25309" class="Symbol">|</a> <a id="25311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#6424" class="InductiveConstructor">cc</a>     <a id="25318" class="Symbol">|</a> <a id="25320" href="plfa.Connectives.html#6424" class="InductiveConstructor">cc</a>      <a id="25328" class="Symbol">=</a>   <a id="25332" class="Number">9</a>
</pre>{% endraw %}
{::comment}
Exponential on types also share a property with exponential on
numbers in that many of the standard identities for numbers carry
over to the types.
{:/}

类型上的幂与数的幂有相似的性质，很多数上成立的关系式也可以在类型上成立。

{::comment}
Corresponding to the law
{:/}

对应如下的定律：

    (p ^ n) ^ m  ≡  p ^ (n * m)

{::comment}
we have the isomorphism
{:/}

我们有如下的同构：

    A → (B → C)  ≃  (A × B) → C

{::comment}
Both types can be viewed as functions that given evidence that `A` holds
and evidence that `B` holds can return evidence that `C` holds.
This isomorphism sometimes goes by the name *currying*.
The proof of the right inverse requires extensionality:
{:/}

两个类型可以被看作给定 `A` 成立的证据和 `B` 成立的证据，返回 `C` 成立的证据。
这个同构有时也被称作*柯里化*（Currying）。右逆的证明需要外延性：

{% raw %}<pre class="Agda"><a id="currying"></a><a id="26072" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#26072" class="Function">currying</a> <a id="26081" class="Symbol">:</a> <a id="26083" class="Symbol">∀</a> <a id="26085" class="Symbol">{</a><a id="26086" href="plfa.Connectives.html#26086" class="Bound">A</a> <a id="26088" href="plfa.Connectives.html#26088" class="Bound">B</a> <a id="26090" href="plfa.Connectives.html#26090" class="Bound">C</a> <a id="26092" class="Symbol">:</a> <a id="26094" class="PrimitiveType">Set</a><a id="26097" class="Symbol">}</a> <a id="26099" class="Symbol">→</a> <a id="26101" class="Symbol">(</a><a id="26102" href="plfa.Connectives.html#26086" class="Bound">A</a> <a id="26104" class="Symbol">→</a> <a id="26106" href="plfa.Connectives.html#26088" class="Bound">B</a> <a id="26108" class="Symbol">→</a> <a id="26110" href="plfa.Connectives.html#26090" class="Bound">C</a><a id="26111" class="Symbol">)</a> <a id="26113" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5424" class="Record Operator">≃</a> <a id="26115" class="Symbol">(</a><a id="26116" href="plfa.Connectives.html#26086" class="Bound">A</a> <a id="26118" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="26120" href="plfa.Connectives.html#26088" class="Bound">B</a> <a id="26122" class="Symbol">→</a> <a id="26124" href="plfa.Connectives.html#26090" class="Bound">C</a><a id="26125" class="Symbol">)</a>
<a id="26127" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#26072" class="Function">currying</a> <a id="26136" class="Symbol">=</a>
  <a id="26140" class="Keyword">record</a>
    <a id="26151" class="Symbol">{</a> <a id="26153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5464" class="Field">to</a>      <a id="26161" class="Symbol">=</a>  <a id="26164" class="Symbol">λ{</a> <a id="26167" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#26167" class="Bound">f</a> <a id="26169" class="Symbol">→</a> <a id="26171" class="Symbol">λ{</a> <a id="26174" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="26176" href="plfa.Connectives.html#26176" class="Bound">x</a> <a id="26178" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="26180" href="plfa.Connectives.html#26180" class="Bound">y</a> <a id="26182" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="26184" class="Symbol">→</a> <a id="26186" href="plfa.Connectives.html#26167" class="Bound">f</a> <a id="26188" href="plfa.Connectives.html#26176" class="Bound">x</a> <a id="26190" href="plfa.Connectives.html#26180" class="Bound">y</a> <a id="26192" class="Symbol">}}</a>
    <a id="26199" class="Symbol">;</a> <a id="26201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5481" class="Field">from</a>    <a id="26209" class="Symbol">=</a>  <a id="26212" class="Symbol">λ{</a> <a id="26215" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#26215" class="Bound">g</a> <a id="26217" class="Symbol">→</a> <a id="26219" class="Symbol">λ{</a> <a id="26222" href="plfa.Connectives.html#26222" class="Bound">x</a> <a id="26224" class="Symbol">→</a> <a id="26226" class="Symbol">λ{</a> <a id="26229" href="plfa.Connectives.html#26229" class="Bound">y</a> <a id="26231" class="Symbol">→</a> <a id="26233" href="plfa.Connectives.html#26215" class="Bound">g</a> <a id="26235" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="26237" href="plfa.Connectives.html#26222" class="Bound">x</a> <a id="26239" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="26241" href="plfa.Connectives.html#26229" class="Bound">y</a> <a id="26243" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="26245" class="Symbol">}}}</a>
    <a id="26253" class="Symbol">;</a> <a id="26255" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5498" class="Field">from∘to</a> <a id="26263" class="Symbol">=</a>  <a id="26266" class="Symbol">λ{</a> <a id="26269" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#26269" class="Bound">f</a> <a id="26271" class="Symbol">→</a> <a id="26273" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="26278" class="Symbol">}</a>
    <a id="26284" class="Symbol">;</a> <a id="26286" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5540" class="Field">to∘from</a> <a id="26294" class="Symbol">=</a>  <a id="26297" class="Symbol">λ{</a> <a id="26300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#26300" class="Bound">g</a> <a id="26302" class="Symbol">→</a> <a id="26304" href="plfa.Isomorphism.html#3728" class="Postulate">extensionality</a> <a id="26319" class="Symbol">λ{</a> <a id="26322" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="26324" href="plfa.Connectives.html#26324" class="Bound">x</a> <a id="26326" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="26328" href="plfa.Connectives.html#26328" class="Bound">y</a> <a id="26330" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="26332" class="Symbol">→</a> <a id="26334" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="26339" class="Symbol">}}</a>
    <a id="26346" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Currying tells us that instead of a function that takes a pair of arguments,
we can have a function that takes the first argument and returns a function that
expects the second argument.  Thus, for instance, our way of writing addition
{:/}

柯里化告诉我们，如果一个函数有取一个数据对作为参数，
那么我们可以构造一个函数，取第一个参数，返回一个取第二个参数，返回最终结果的函数。
因此，举例来说，下面表示加法的形式：

    _+_ : ℕ → ℕ → ℕ

{::comment}
is isomorphic to a function that accepts a pair of arguments:
{:/}

和下面的一个带有一个数据对作为参数的函数是同构的：

    _+′_ : (ℕ × ℕ) → ℕ

{::comment}
Agda is optimised for currying, so `2 + 3` abbreviates `_+_ 2 3`.
In a language optimised for pairing, we would instead take `2 +′ 3` as
an abbreviation for `_+′_ ⟨ 2 , 3 ⟩`.
{:/}

Agda 对柯里化进行了优化，因此 `2 + 3` 是 `_+_ 2 3` 的简写。在一个对有序对进行优化的语言里，
`2 +′ 3` 可能是 `_+′_ ⟨ 2 , 3 ⟩` 的简写。

{::comment}
Corresponding to the law
{:/}

对应如下的定律：

    p ^ (n + m) = (p ^ n) * (p ^ m)

{::comment}
we have the isomorphism:
{:/}

我们有如下的同构：

    (A ⊎ B) → C  ≃  (A → C) × (B → C)

{::comment}
That is, the assertion that if either `A` holds or `B` holds then `C` holds
is the same as the assertion that if `A` holds then `C` holds and if
`B` holds then `C` holds.  The proof of the left inverse requires extensionality:
{:/}

命题如果 `A` 成立或者 `B` 成立，那么 `C` 成立，和命题如果 `A` 成立，那么 `C` 成立以及
如果 `B` 成立，那么 `C` 成立，是一样的。左逆的证明需要外延性：

{% raw %}<pre class="Agda"><a id="→-distrib-⊎"></a><a id="27662" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#27662" class="Function">→-distrib-⊎</a> <a id="27674" class="Symbol">:</a> <a id="27676" class="Symbol">∀</a> <a id="27678" class="Symbol">{</a><a id="27679" href="plfa.Connectives.html#27679" class="Bound">A</a> <a id="27681" href="plfa.Connectives.html#27681" class="Bound">B</a> <a id="27683" href="plfa.Connectives.html#27683" class="Bound">C</a> <a id="27685" class="Symbol">:</a> <a id="27687" class="PrimitiveType">Set</a><a id="27690" class="Symbol">}</a> <a id="27692" class="Symbol">→</a> <a id="27694" class="Symbol">(</a><a id="27695" href="plfa.Connectives.html#27679" class="Bound">A</a> <a id="27697" href="plfa.Connectives.html#14020" class="Datatype Operator">⊎</a> <a id="27699" href="plfa.Connectives.html#27681" class="Bound">B</a> <a id="27701" class="Symbol">→</a> <a id="27703" href="plfa.Connectives.html#27683" class="Bound">C</a><a id="27704" class="Symbol">)</a> <a id="27706" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5424" class="Record Operator">≃</a> <a id="27708" class="Symbol">((</a><a id="27710" href="plfa.Connectives.html#27679" class="Bound">A</a> <a id="27712" class="Symbol">→</a> <a id="27714" href="plfa.Connectives.html#27683" class="Bound">C</a><a id="27715" class="Symbol">)</a> <a id="27717" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="27719" class="Symbol">(</a><a id="27720" href="plfa.Connectives.html#27681" class="Bound">B</a> <a id="27722" class="Symbol">→</a> <a id="27724" href="plfa.Connectives.html#27683" class="Bound">C</a><a id="27725" class="Symbol">))</a>
<a id="27728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#27662" class="Function">→-distrib-⊎</a> <a id="27740" class="Symbol">=</a>
  <a id="27744" class="Keyword">record</a>
    <a id="27755" class="Symbol">{</a> <a id="27757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5464" class="Field">to</a>      <a id="27765" class="Symbol">=</a> <a id="27767" class="Symbol">λ{</a> <a id="27770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#27770" class="Bound">f</a> <a id="27772" class="Symbol">→</a> <a id="27774" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="27776" href="plfa.Connectives.html#27770" class="Bound">f</a> <a id="27778" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="27780" href="plfa.Connectives.html#14051" class="InductiveConstructor">inj₁</a> <a id="27785" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="27787" href="plfa.Connectives.html#27770" class="Bound">f</a> <a id="27789" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="27791" href="plfa.Connectives.html#14093" class="InductiveConstructor">inj₂</a> <a id="27796" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="27798" class="Symbol">}</a>
    <a id="27804" class="Symbol">;</a> <a id="27806" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5481" class="Field">from</a>    <a id="27814" class="Symbol">=</a> <a id="27816" class="Symbol">λ{</a> <a id="27819" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="27821" href="plfa.Connectives.html#27821" class="Bound">g</a> <a id="27823" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="27825" href="plfa.Connectives.html#27825" class="Bound">h</a> <a id="27827" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="27829" class="Symbol">→</a> <a id="27831" class="Symbol">λ{</a> <a id="27834" class="Symbol">(</a><a id="27835" href="plfa.Connectives.html#14051" class="InductiveConstructor">inj₁</a> <a id="27840" href="plfa.Connectives.html#27840" class="Bound">x</a><a id="27841" class="Symbol">)</a> <a id="27843" class="Symbol">→</a> <a id="27845" href="plfa.Connectives.html#27821" class="Bound">g</a> <a id="27847" href="plfa.Connectives.html#27840" class="Bound">x</a> <a id="27849" class="Symbol">;</a> <a id="27851" class="Symbol">(</a><a id="27852" href="plfa.Connectives.html#14093" class="InductiveConstructor">inj₂</a> <a id="27857" href="plfa.Connectives.html#27857" class="Bound">y</a><a id="27858" class="Symbol">)</a> <a id="27860" class="Symbol">→</a> <a id="27862" href="plfa.Connectives.html#27825" class="Bound">h</a> <a id="27864" href="plfa.Connectives.html#27857" class="Bound">y</a> <a id="27866" class="Symbol">}</a> <a id="27868" class="Symbol">}</a>
    <a id="27874" class="Symbol">;</a> <a id="27876" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5498" class="Field">from∘to</a> <a id="27884" class="Symbol">=</a> <a id="27886" class="Symbol">λ{</a> <a id="27889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#27889" class="Bound">f</a> <a id="27891" class="Symbol">→</a> <a id="27893" href="plfa.Isomorphism.html#3728" class="Postulate">extensionality</a> <a id="27908" class="Symbol">λ{</a> <a id="27911" class="Symbol">(</a><a id="27912" href="plfa.Connectives.html#14051" class="InductiveConstructor">inj₁</a> <a id="27917" href="plfa.Connectives.html#27917" class="Bound">x</a><a id="27918" class="Symbol">)</a> <a id="27920" class="Symbol">→</a> <a id="27922" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="27927" class="Symbol">;</a> <a id="27929" class="Symbol">(</a><a id="27930" href="plfa.Connectives.html#14093" class="InductiveConstructor">inj₂</a> <a id="27935" href="plfa.Connectives.html#27935" class="Bound">y</a><a id="27936" class="Symbol">)</a> <a id="27938" class="Symbol">→</a> <a id="27940" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="27945" class="Symbol">}</a> <a id="27947" class="Symbol">}</a>
    <a id="27953" class="Symbol">;</a> <a id="27955" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5540" class="Field">to∘from</a> <a id="27963" class="Symbol">=</a> <a id="27965" class="Symbol">λ{</a> <a id="27968" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="27970" href="plfa.Connectives.html#27970" class="Bound">g</a> <a id="27972" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="27974" href="plfa.Connectives.html#27974" class="Bound">h</a> <a id="27976" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="27978" class="Symbol">→</a> <a id="27980" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="27985" class="Symbol">}</a>
    <a id="27991" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Corresponding to the law
{:/}

对应如下的定律：

    (p * n) ^ m = (p ^ m) * (n ^ m)

{::comment}
we have the isomorphism:
{:/}

我们有如下的同构：

    A → B × C  ≃  (A → B) × (A → C)

{::comment}
That is, the assertion that if `A` holds then `B` holds and `C` holds
is the same as the assertion that if `A` holds then `B` holds and if
`A` holds then `C` holds.  The proof of left inverse requires both extensionality
and the rule `η-×` for products:
{:/}

命题如果 `A` 成立，那么 `B` 成立和 `C` 成立，和命题如果 `A` 成立，那么 `B` 成立以及
如果 `A` 成立，那么 `C` 成立，是一样的。左逆的证明需要外延性和积的 `η-×` 规则：

{% raw %}<pre class="Agda"><a id="→-distrib-×"></a><a id="28560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#28560" class="Function">→-distrib-×</a> <a id="28572" class="Symbol">:</a> <a id="28574" class="Symbol">∀</a> <a id="28576" class="Symbol">{</a><a id="28577" href="plfa.Connectives.html#28577" class="Bound">A</a> <a id="28579" href="plfa.Connectives.html#28579" class="Bound">B</a> <a id="28581" href="plfa.Connectives.html#28581" class="Bound">C</a> <a id="28583" class="Symbol">:</a> <a id="28585" class="PrimitiveType">Set</a><a id="28588" class="Symbol">}</a> <a id="28590" class="Symbol">→</a> <a id="28592" class="Symbol">(</a><a id="28593" href="plfa.Connectives.html#28577" class="Bound">A</a> <a id="28595" class="Symbol">→</a> <a id="28597" href="plfa.Connectives.html#28579" class="Bound">B</a> <a id="28599" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="28601" href="plfa.Connectives.html#28581" class="Bound">C</a><a id="28602" class="Symbol">)</a> <a id="28604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5424" class="Record Operator">≃</a> <a id="28606" class="Symbol">(</a><a id="28607" href="plfa.Connectives.html#28577" class="Bound">A</a> <a id="28609" class="Symbol">→</a> <a id="28611" href="plfa.Connectives.html#28579" class="Bound">B</a><a id="28612" class="Symbol">)</a> <a id="28614" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="28616" class="Symbol">(</a><a id="28617" href="plfa.Connectives.html#28577" class="Bound">A</a> <a id="28619" class="Symbol">→</a> <a id="28621" href="plfa.Connectives.html#28581" class="Bound">C</a><a id="28622" class="Symbol">)</a>
<a id="28624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#28560" class="Function">→-distrib-×</a> <a id="28636" class="Symbol">=</a>
  <a id="28640" class="Keyword">record</a>
    <a id="28651" class="Symbol">{</a> <a id="28653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5464" class="Field">to</a>      <a id="28661" class="Symbol">=</a> <a id="28663" class="Symbol">λ{</a> <a id="28666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#28666" class="Bound">f</a> <a id="28668" class="Symbol">→</a> <a id="28670" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="28672" href="plfa.Connectives.html#2185" class="Function">proj₁</a> <a id="28678" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="28680" href="plfa.Connectives.html#28666" class="Bound">f</a> <a id="28682" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="28684" href="plfa.Connectives.html#2254" class="Function">proj₂</a> <a id="28690" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">∘</a> <a id="28692" href="plfa.Connectives.html#28666" class="Bound">f</a> <a id="28694" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="28696" class="Symbol">}</a>
    <a id="28702" class="Symbol">;</a> <a id="28704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5481" class="Field">from</a>    <a id="28712" class="Symbol">=</a> <a id="28714" class="Symbol">λ{</a> <a id="28717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="28719" href="plfa.Connectives.html#28719" class="Bound">g</a> <a id="28721" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="28723" href="plfa.Connectives.html#28723" class="Bound">h</a> <a id="28725" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="28727" class="Symbol">→</a> <a id="28729" class="Symbol">λ</a> <a id="28731" href="plfa.Connectives.html#28731" class="Bound">x</a> <a id="28733" class="Symbol">→</a> <a id="28735" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="28737" href="plfa.Connectives.html#28719" class="Bound">g</a> <a id="28739" href="plfa.Connectives.html#28731" class="Bound">x</a> <a id="28741" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="28743" href="plfa.Connectives.html#28723" class="Bound">h</a> <a id="28745" href="plfa.Connectives.html#28731" class="Bound">x</a> <a id="28747" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="28749" class="Symbol">}</a>
    <a id="28755" class="Symbol">;</a> <a id="28757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5498" class="Field">from∘to</a> <a id="28765" class="Symbol">=</a> <a id="28767" class="Symbol">λ{</a> <a id="28770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#28770" class="Bound">f</a> <a id="28772" class="Symbol">→</a> <a id="28774" href="plfa.Isomorphism.html#3728" class="Postulate">extensionality</a> <a id="28789" class="Symbol">λ{</a> <a id="28792" href="plfa.Connectives.html#28792" class="Bound">x</a> <a id="28794" class="Symbol">→</a> <a id="28796" href="plfa.Connectives.html#4979" class="Function">η-×</a> <a id="28800" class="Symbol">(</a><a id="28801" href="plfa.Connectives.html#28770" class="Bound">f</a> <a id="28803" href="plfa.Connectives.html#28792" class="Bound">x</a><a id="28804" class="Symbol">)</a> <a id="28806" class="Symbol">}</a> <a id="28808" class="Symbol">}</a>
    <a id="28814" class="Symbol">;</a> <a id="28816" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5540" class="Field">to∘from</a> <a id="28824" class="Symbol">=</a> <a id="28826" class="Symbol">λ{</a> <a id="28829" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="28831" href="plfa.Connectives.html#28831" class="Bound">g</a> <a id="28833" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="28835" href="plfa.Connectives.html#28835" class="Bound">h</a> <a id="28837" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="28839" class="Symbol">→</a> <a id="28841" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="28846" class="Symbol">}</a>
    <a id="28852" class="Symbol">}</a>
</pre>{% endraw %}

{::comment}
## Distribution
{:/}

## 分配律

{::comment}
Products distribute over sum, up to isomorphism.  The code to validate
this fact is similar in structure to our previous results:
{:/}

在同构意义下，积对于和满足分配律。验证这条形式的代码和之前的证明相似：

{% raw %}<pre class="Agda"><a id="×-distrib-⊎"></a><a id="29091" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#29091" class="Function">×-distrib-⊎</a> <a id="29103" class="Symbol">:</a> <a id="29105" class="Symbol">∀</a> <a id="29107" class="Symbol">{</a><a id="29108" href="plfa.Connectives.html#29108" class="Bound">A</a> <a id="29110" href="plfa.Connectives.html#29110" class="Bound">B</a> <a id="29112" href="plfa.Connectives.html#29112" class="Bound">C</a> <a id="29114" class="Symbol">:</a> <a id="29116" class="PrimitiveType">Set</a><a id="29119" class="Symbol">}</a> <a id="29121" class="Symbol">→</a> <a id="29123" class="Symbol">(</a><a id="29124" href="plfa.Connectives.html#29108" class="Bound">A</a> <a id="29126" href="plfa.Connectives.html#14020" class="Datatype Operator">⊎</a> <a id="29128" href="plfa.Connectives.html#29110" class="Bound">B</a><a id="29129" class="Symbol">)</a> <a id="29131" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="29133" href="plfa.Connectives.html#29112" class="Bound">C</a> <a id="29135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5424" class="Record Operator">≃</a> <a id="29137" class="Symbol">(</a><a id="29138" href="plfa.Connectives.html#29108" class="Bound">A</a> <a id="29140" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="29142" href="plfa.Connectives.html#29112" class="Bound">C</a><a id="29143" class="Symbol">)</a> <a id="29145" href="plfa.Connectives.html#14020" class="Datatype Operator">⊎</a> <a id="29147" class="Symbol">(</a><a id="29148" href="plfa.Connectives.html#29110" class="Bound">B</a> <a id="29150" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="29152" href="plfa.Connectives.html#29112" class="Bound">C</a><a id="29153" class="Symbol">)</a>
<a id="29155" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#29091" class="Function">×-distrib-⊎</a> <a id="29167" class="Symbol">=</a>
  <a id="29171" class="Keyword">record</a>
    <a id="29182" class="Symbol">{</a> <a id="29184" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5464" class="Field">to</a>      <a id="29192" class="Symbol">=</a> <a id="29194" class="Symbol">λ{</a> <a id="29197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="29199" href="plfa.Connectives.html#14051" class="InductiveConstructor">inj₁</a> <a id="29204" href="plfa.Connectives.html#29204" class="Bound">x</a> <a id="29206" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29208" href="plfa.Connectives.html#29208" class="Bound">z</a> <a id="29210" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="29212" class="Symbol">→</a> <a id="29214" class="Symbol">(</a><a id="29215" href="plfa.Connectives.html#14051" class="InductiveConstructor">inj₁</a> <a id="29220" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29222" href="plfa.Connectives.html#29204" class="Bound">x</a> <a id="29224" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29226" href="plfa.Connectives.html#29208" class="Bound">z</a> <a id="29228" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a><a id="29229" class="Symbol">)</a>
                 <a id="29248" class="Symbol">;</a> <a id="29250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="29252" href="plfa.Connectives.html#14093" class="InductiveConstructor">inj₂</a> <a id="29257" href="plfa.Connectives.html#29257" class="Bound">y</a> <a id="29259" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29261" href="plfa.Connectives.html#29261" class="Bound">z</a> <a id="29263" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="29265" class="Symbol">→</a> <a id="29267" class="Symbol">(</a><a id="29268" href="plfa.Connectives.html#14093" class="InductiveConstructor">inj₂</a> <a id="29273" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29275" href="plfa.Connectives.html#29257" class="Bound">y</a> <a id="29277" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29279" href="plfa.Connectives.html#29261" class="Bound">z</a> <a id="29281" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a><a id="29282" class="Symbol">)</a>
                 <a id="29301" class="Symbol">}</a>
    <a id="29307" class="Symbol">;</a> <a id="29309" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5481" class="Field">from</a>    <a id="29317" class="Symbol">=</a> <a id="29319" class="Symbol">λ{</a> <a id="29322" class="Symbol">(</a><a id="29323" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14051" class="InductiveConstructor">inj₁</a> <a id="29328" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29330" href="plfa.Connectives.html#29330" class="Bound">x</a> <a id="29332" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29334" href="plfa.Connectives.html#29334" class="Bound">z</a> <a id="29336" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a><a id="29337" class="Symbol">)</a> <a id="29339" class="Symbol">→</a> <a id="29341" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29343" href="plfa.Connectives.html#14051" class="InductiveConstructor">inj₁</a> <a id="29348" href="plfa.Connectives.html#29330" class="Bound">x</a> <a id="29350" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29352" href="plfa.Connectives.html#29334" class="Bound">z</a> <a id="29354" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a>
                 <a id="29373" class="Symbol">;</a> <a id="29375" class="Symbol">(</a><a id="29376" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14093" class="InductiveConstructor">inj₂</a> <a id="29381" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29383" href="plfa.Connectives.html#29383" class="Bound">y</a> <a id="29385" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29387" href="plfa.Connectives.html#29387" class="Bound">z</a> <a id="29389" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a><a id="29390" class="Symbol">)</a> <a id="29392" class="Symbol">→</a> <a id="29394" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29396" href="plfa.Connectives.html#14093" class="InductiveConstructor">inj₂</a> <a id="29401" href="plfa.Connectives.html#29383" class="Bound">y</a> <a id="29403" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29405" href="plfa.Connectives.html#29387" class="Bound">z</a> <a id="29407" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a>
                 <a id="29426" class="Symbol">}</a>
    <a id="29432" class="Symbol">;</a> <a id="29434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5498" class="Field">from∘to</a> <a id="29442" class="Symbol">=</a> <a id="29444" class="Symbol">λ{</a> <a id="29447" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="29449" href="plfa.Connectives.html#14051" class="InductiveConstructor">inj₁</a> <a id="29454" href="plfa.Connectives.html#29454" class="Bound">x</a> <a id="29456" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29458" href="plfa.Connectives.html#29458" class="Bound">z</a> <a id="29460" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="29462" class="Symbol">→</a> <a id="29464" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="29486" class="Symbol">;</a> <a id="29488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="29490" href="plfa.Connectives.html#14093" class="InductiveConstructor">inj₂</a> <a id="29495" href="plfa.Connectives.html#29495" class="Bound">y</a> <a id="29497" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29499" href="plfa.Connectives.html#29499" class="Bound">z</a> <a id="29501" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="29503" class="Symbol">→</a> <a id="29505" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="29527" class="Symbol">}</a>
    <a id="29533" class="Symbol">;</a> <a id="29535" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5540" class="Field">to∘from</a> <a id="29543" class="Symbol">=</a> <a id="29545" class="Symbol">λ{</a> <a id="29548" class="Symbol">(</a><a id="29549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14051" class="InductiveConstructor">inj₁</a> <a id="29554" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29556" href="plfa.Connectives.html#29556" class="Bound">x</a> <a id="29558" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29560" href="plfa.Connectives.html#29560" class="Bound">z</a> <a id="29562" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a><a id="29563" class="Symbol">)</a> <a id="29565" class="Symbol">→</a> <a id="29567" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="29589" class="Symbol">;</a> <a id="29591" class="Symbol">(</a><a id="29592" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14093" class="InductiveConstructor">inj₂</a> <a id="29597" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29599" href="plfa.Connectives.html#29599" class="Bound">y</a> <a id="29601" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29603" href="plfa.Connectives.html#29603" class="Bound">z</a> <a id="29605" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a><a id="29606" class="Symbol">)</a> <a id="29608" class="Symbol">→</a> <a id="29610" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="29632" class="Symbol">}</a>
    <a id="29638" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Sums do not distribute over products up to isomorphism, but it is an embedding:
{:/}

和对于积不满足分配律，但满足嵌入：

{% raw %}<pre class="Agda"><a id="⊎-distrib-×"></a><a id="29766" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#29766" class="Function">⊎-distrib-×</a> <a id="29778" class="Symbol">:</a> <a id="29780" class="Symbol">∀</a> <a id="29782" class="Symbol">{</a><a id="29783" href="plfa.Connectives.html#29783" class="Bound">A</a> <a id="29785" href="plfa.Connectives.html#29785" class="Bound">B</a> <a id="29787" href="plfa.Connectives.html#29787" class="Bound">C</a> <a id="29789" class="Symbol">:</a> <a id="29791" class="PrimitiveType">Set</a><a id="29794" class="Symbol">}</a> <a id="29796" class="Symbol">→</a> <a id="29798" class="Symbol">(</a><a id="29799" href="plfa.Connectives.html#29783" class="Bound">A</a> <a id="29801" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="29803" href="plfa.Connectives.html#29785" class="Bound">B</a><a id="29804" class="Symbol">)</a> <a id="29806" href="plfa.Connectives.html#14020" class="Datatype Operator">⊎</a> <a id="29808" href="plfa.Connectives.html#29787" class="Bound">C</a> <a id="29810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11500" class="Record Operator">≲</a> <a id="29812" class="Symbol">(</a><a id="29813" href="plfa.Connectives.html#29783" class="Bound">A</a> <a id="29815" href="plfa.Connectives.html#14020" class="Datatype Operator">⊎</a> <a id="29817" href="plfa.Connectives.html#29787" class="Bound">C</a><a id="29818" class="Symbol">)</a> <a id="29820" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="29822" class="Symbol">(</a><a id="29823" href="plfa.Connectives.html#29785" class="Bound">B</a> <a id="29825" href="plfa.Connectives.html#14020" class="Datatype Operator">⊎</a> <a id="29827" href="plfa.Connectives.html#29787" class="Bound">C</a><a id="29828" class="Symbol">)</a>
<a id="29830" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#29766" class="Function">⊎-distrib-×</a> <a id="29842" class="Symbol">=</a>
  <a id="29846" class="Keyword">record</a>
    <a id="29857" class="Symbol">{</a> <a id="29859" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11540" class="Field">to</a>      <a id="29867" class="Symbol">=</a> <a id="29869" class="Symbol">λ{</a> <a id="29872" class="Symbol">(</a><a id="29873" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14051" class="InductiveConstructor">inj₁</a> <a id="29878" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29880" href="plfa.Connectives.html#29880" class="Bound">x</a> <a id="29882" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29884" href="plfa.Connectives.html#29884" class="Bound">y</a> <a id="29886" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a><a id="29887" class="Symbol">)</a> <a id="29889" class="Symbol">→</a> <a id="29891" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29893" href="plfa.Connectives.html#14051" class="InductiveConstructor">inj₁</a> <a id="29898" href="plfa.Connectives.html#29880" class="Bound">x</a> <a id="29900" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29902" href="plfa.Connectives.html#14051" class="InductiveConstructor">inj₁</a> <a id="29907" href="plfa.Connectives.html#29884" class="Bound">y</a> <a id="29909" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a>
                 <a id="29928" class="Symbol">;</a> <a id="29930" class="Symbol">(</a><a id="29931" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14093" class="InductiveConstructor">inj₂</a> <a id="29936" href="plfa.Connectives.html#29936" class="Bound">z</a><a id="29937" class="Symbol">)</a>         <a id="29947" class="Symbol">→</a> <a id="29949" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="29951" href="plfa.Connectives.html#14093" class="InductiveConstructor">inj₂</a> <a id="29956" href="plfa.Connectives.html#29936" class="Bound">z</a> <a id="29958" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="29960" href="plfa.Connectives.html#14093" class="InductiveConstructor">inj₂</a> <a id="29965" href="plfa.Connectives.html#29936" class="Bound">z</a> <a id="29967" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a>
                 <a id="29986" class="Symbol">}</a>
    <a id="29992" class="Symbol">;</a> <a id="29994" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11560" class="Field">from</a>    <a id="30002" class="Symbol">=</a> <a id="30004" class="Symbol">λ{</a> <a id="30007" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="30009" href="plfa.Connectives.html#14051" class="InductiveConstructor">inj₁</a> <a id="30014" href="plfa.Connectives.html#30014" class="Bound">x</a> <a id="30016" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="30018" href="plfa.Connectives.html#14051" class="InductiveConstructor">inj₁</a> <a id="30023" href="plfa.Connectives.html#30023" class="Bound">y</a> <a id="30025" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="30027" class="Symbol">→</a> <a id="30029" class="Symbol">(</a><a id="30030" href="plfa.Connectives.html#14051" class="InductiveConstructor">inj₁</a> <a id="30035" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="30037" href="plfa.Connectives.html#30014" class="Bound">x</a> <a id="30039" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="30041" href="plfa.Connectives.html#30023" class="Bound">y</a> <a id="30043" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a><a id="30044" class="Symbol">)</a>
                 <a id="30063" class="Symbol">;</a> <a id="30065" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="30067" href="plfa.Connectives.html#14051" class="InductiveConstructor">inj₁</a> <a id="30072" href="plfa.Connectives.html#30072" class="Bound">x</a> <a id="30074" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="30076" href="plfa.Connectives.html#14093" class="InductiveConstructor">inj₂</a> <a id="30081" href="plfa.Connectives.html#30081" class="Bound">z</a> <a id="30083" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="30085" class="Symbol">→</a> <a id="30087" class="Symbol">(</a><a id="30088" href="plfa.Connectives.html#14093" class="InductiveConstructor">inj₂</a> <a id="30093" href="plfa.Connectives.html#30081" class="Bound">z</a><a id="30094" class="Symbol">)</a>
                 <a id="30113" class="Symbol">;</a> <a id="30115" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#1751" class="InductiveConstructor Operator">⟨</a> <a id="30117" href="plfa.Connectives.html#14093" class="InductiveConstructor">inj₂</a> <a id="30122" href="plfa.Connectives.html#30122" class="Bound">z</a> <a id="30124" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="30126" class="Symbol">_</a>      <a id="30133" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a> <a id="30135" class="Symbol">→</a> <a id="30137" class="Symbol">(</a><a id="30138" href="plfa.Connectives.html#14093" class="InductiveConstructor">inj₂</a> <a id="30143" href="plfa.Connectives.html#30122" class="Bound">z</a><a id="30144" class="Symbol">)</a>
                 <a id="30163" class="Symbol">}</a>
    <a id="30169" class="Symbol">;</a> <a id="30171" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11580" class="Field">from∘to</a> <a id="30179" class="Symbol">=</a> <a id="30181" class="Symbol">λ{</a> <a id="30184" class="Symbol">(</a><a id="30185" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14051" class="InductiveConstructor">inj₁</a> <a id="30190" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟨</a> <a id="30192" href="plfa.Connectives.html#30192" class="Bound">x</a> <a id="30194" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">,</a> <a id="30196" href="plfa.Connectives.html#30196" class="Bound">y</a> <a id="30198" href="plfa.Connectives.html#1751" class="InductiveConstructor Operator">⟩</a><a id="30199" class="Symbol">)</a> <a id="30201" class="Symbol">→</a> <a id="30203" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="30225" class="Symbol">;</a> <a id="30227" class="Symbol">(</a><a id="30228" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#14093" class="InductiveConstructor">inj₂</a> <a id="30233" href="plfa.Connectives.html#30233" class="Bound">z</a><a id="30234" class="Symbol">)</a>         <a id="30244" class="Symbol">→</a> <a id="30246" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
                 <a id="30268" class="Symbol">}</a>
    <a id="30274" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
Note that there is a choice in how we write the `from` function.
As given, it takes `⟨ inj₂ z , inj₂ z′ ⟩` to `inj₂ z`, but it is
easy to write a variant that instead returns `inj₂ z′`.  We have
an embedding rather than an isomorphism because the
`from` function must discard either `z` or `z′` in this case.
{:/}

我们在定义 `from` 函数的时候可以有选择。给定的定义中，它将 `⟨ inj₂ z , inj₂ z′ ⟩`
转换为 `inj₂ z`，但我们也可以返回 `inj₂ z′` 作为嵌入证明的变种。我们在这里只能证明嵌入，
而不能证明同构，因为 `from` 函数必须丢弃 `z` 或者 `z′` 其中的一个。

{::comment}
In the usual approach to logic, both of the distribution laws
are given as equivalences, where each side implies the other:
{:/}

在一般的逻辑学方法中，两条分配律都以等价的形式给出，每一边都蕴涵了另一边：

    A × (B ⊎ C) ⇔ (A × B) ⊎ (A × C)
    A ⊎ (B × C) ⇔ (A ⊎ B) × (A ⊎ C)

{::comment}
But when we consider the functions that provide evidence for these
implications, then the first corresponds to an isomorphism while the
second only corresponds to an embedding, revealing a sense in which
one of these laws is "more true" than the other.
{:/}

但当我们考虑提供上述蕴涵证明的函数时，第一条对应同构而第二条只能对应嵌入，
揭示了有些定理比另一个更加的”正确“。


{::comment}
#### Exercise `⊎-weak-×` (recommended)
{:/}

#### 练习 `⊎-weak-×` （推荐）

{::comment}
Show that the following property holds:
{:/}

证明如下性质成立：

{% raw %}<pre class="Agda"><a id="31505" class="Keyword">postulate</a>
  <a id="⊎-weak-×"></a><a id="31517" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#31517" class="Postulate">⊎-weak-×</a> <a id="31526" class="Symbol">:</a> <a id="31528" class="Symbol">∀</a> <a id="31530" class="Symbol">{</a><a id="31531" href="plfa.Connectives.html#31531" class="Bound">A</a> <a id="31533" href="plfa.Connectives.html#31533" class="Bound">B</a> <a id="31535" href="plfa.Connectives.html#31535" class="Bound">C</a> <a id="31537" class="Symbol">:</a> <a id="31539" class="PrimitiveType">Set</a><a id="31542" class="Symbol">}</a> <a id="31544" class="Symbol">→</a> <a id="31546" class="Symbol">(</a><a id="31547" href="plfa.Connectives.html#31531" class="Bound">A</a> <a id="31549" href="plfa.Connectives.html#14020" class="Datatype Operator">⊎</a> <a id="31551" href="plfa.Connectives.html#31533" class="Bound">B</a><a id="31552" class="Symbol">)</a> <a id="31554" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="31556" href="plfa.Connectives.html#31535" class="Bound">C</a> <a id="31558" class="Symbol">→</a> <a id="31560" href="plfa.Connectives.html#31531" class="Bound">A</a> <a id="31562" href="plfa.Connectives.html#14020" class="Datatype Operator">⊎</a> <a id="31564" class="Symbol">(</a><a id="31565" href="plfa.Connectives.html#31533" class="Bound">B</a> <a id="31567" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="31569" href="plfa.Connectives.html#31535" class="Bound">C</a><a id="31570" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
This is called a _weak distributive law_. Give the corresponding
distributive law, and explain how it relates to the weak version.
{:/}

这被称为*弱分配律*。给出相对应的分配律，并解释分配律与弱分配律的关系。

{::comment}
{% raw %}<pre class="Agda"><a id="31780" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="31817" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}


{::comment}
#### Exercise `⊎×-implies-×⊎`
{:/}

#### 练习 `⊎×-implies-×⊎`

{::comment}
Show that a disjunct of conjuncts implies a conjunct of disjuncts:
{:/}

证明合取的析取蕴涵了析取的合取：

{% raw %}<pre class="Agda"><a id="32017" class="Keyword">postulate</a>
  <a id="⊎×-implies-×⊎"></a><a id="32029" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Connectives.md %}{% raw %}#32029" class="Postulate">⊎×-implies-×⊎</a> <a id="32043" class="Symbol">:</a> <a id="32045" class="Symbol">∀</a> <a id="32047" class="Symbol">{</a><a id="32048" href="plfa.Connectives.html#32048" class="Bound">A</a> <a id="32050" href="plfa.Connectives.html#32050" class="Bound">B</a> <a id="32052" href="plfa.Connectives.html#32052" class="Bound">C</a> <a id="32054" href="plfa.Connectives.html#32054" class="Bound">D</a> <a id="32056" class="Symbol">:</a> <a id="32058" class="PrimitiveType">Set</a><a id="32061" class="Symbol">}</a> <a id="32063" class="Symbol">→</a> <a id="32065" class="Symbol">(</a><a id="32066" href="plfa.Connectives.html#32048" class="Bound">A</a> <a id="32068" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="32070" href="plfa.Connectives.html#32050" class="Bound">B</a><a id="32071" class="Symbol">)</a> <a id="32073" href="plfa.Connectives.html#14020" class="Datatype Operator">⊎</a> <a id="32075" class="Symbol">(</a><a id="32076" href="plfa.Connectives.html#32052" class="Bound">C</a> <a id="32078" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="32080" href="plfa.Connectives.html#32054" class="Bound">D</a><a id="32081" class="Symbol">)</a> <a id="32083" class="Symbol">→</a> <a id="32085" class="Symbol">(</a><a id="32086" href="plfa.Connectives.html#32048" class="Bound">A</a> <a id="32088" href="plfa.Connectives.html#14020" class="Datatype Operator">⊎</a> <a id="32090" href="plfa.Connectives.html#32052" class="Bound">C</a><a id="32091" class="Symbol">)</a> <a id="32093" href="plfa.Connectives.html#1720" class="Datatype Operator">×</a> <a id="32095" class="Symbol">(</a><a id="32096" href="plfa.Connectives.html#32050" class="Bound">B</a> <a id="32098" href="plfa.Connectives.html#14020" class="Datatype Operator">⊎</a> <a id="32100" href="plfa.Connectives.html#32054" class="Bound">D</a><a id="32101" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Does the converse hold? If so, prove; if not, give a counterexample.
{:/}

反命题成立吗？如果成立，给出证明；如果不成立，给出反例。

{::comment}
{% raw %}<pre class="Agda"><a id="32241" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="32278" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

标准库中可以找到与本章节中相似的定义：

{% raw %}<pre class="Agda"><a id="32468" class="Keyword">import</a> <a id="32475" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="32488" class="Keyword">using</a> <a id="32494" class="Symbol">(</a><a id="32495" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="32498" class="Symbol">;</a> <a id="32500" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Sigma.html#225" class="Field">proj₁</a><a id="32505" class="Symbol">;</a> <a id="32507" href="Agda.Builtin.Sigma.html#237" class="Field">proj₂</a><a id="32512" class="Symbol">)</a> <a id="32514" class="Keyword">renaming</a> <a id="32523" class="Symbol">(</a><a id="32524" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="32528" class="Symbol">to</a> <a id="32531" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="32536" class="Symbol">)</a>
<a id="32538" class="Keyword">import</a> <a id="32545" href="https://agda.github.io/agda-stdlib/v1.1/Data.Unit.html" class="Module">Data.Unit</a> <a id="32555" class="Keyword">using</a> <a id="32561" class="Symbol">(</a><a id="32562" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Unit.html#137" class="Record">⊤</a><a id="32563" class="Symbol">;</a> <a id="32565" href="Agda.Builtin.Unit.html#174" class="InductiveConstructor">tt</a><a id="32567" class="Symbol">)</a>
<a id="32569" class="Keyword">import</a> <a id="32576" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="32585" class="Keyword">using</a> <a id="32591" class="Symbol">(</a><a id="32592" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="32595" class="Symbol">;</a> <a id="32597" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#662" class="InductiveConstructor">inj₁</a><a id="32601" class="Symbol">;</a> <a id="32603" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#687" class="InductiveConstructor">inj₂</a><a id="32607" class="Symbol">)</a> <a id="32609" class="Keyword">renaming</a> <a id="32618" class="Symbol">(</a><a id="32619" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">[_,_]</a> <a id="32625" class="Symbol">to</a> <a id="32628" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#798" class="Function Operator">case-⊎</a><a id="32634" class="Symbol">)</a>
<a id="32636" class="Keyword">import</a> <a id="32643" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="32654" class="Keyword">using</a> <a id="32660" class="Symbol">(</a><a id="32661" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="32662" class="Symbol">;</a> <a id="32664" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="32670" class="Symbol">)</a>
<a id="32672" class="Keyword">import</a> <a id="32679" href="https://agda.github.io/agda-stdlib/v1.1/Function.Equivalence.html" class="Module">Function.Equivalence</a> <a id="32700" class="Keyword">using</a> <a id="32706" class="Symbol">(</a><a id="32707" href="https://agda.github.io/agda-stdlib/v1.1/Function.Equivalence.html#971" class="Function Operator">_⇔_</a><a id="32710" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
The standard library constructs pairs with `_,_` whereas we use `⟨_,_⟩`.
The former makes it convenient to build triples or larger tuples from pairs,
permitting `a , b , c` to stand for `(a , (b , c))`.  But it conflicts with
other useful notations, such as `[_,_]` to construct a list of two elements in
Chapter [Lists][plfa.Lists]
and `Γ , A` to extend environments in
Chapter [DeBruijn][plfa.DeBruijn].
The standard library `_⇔_` is similar to ours, but the one in the
standard library is less convenient, since it is parameterised with
respect to an arbitrary notion of equivalence.
{:/}

标准库中使用 `_,_` 构造数据对，而我们使用 `⟨_,_⟩`。前者在从数据对构造三元对或者更大的
元组时更加的方便，允许 `a , b , c` 作为 `(a, (b , c))` 的记法。但它与其他有用的记法相冲突，
比如说 [Lists][plfa.Lists] 中的 `[_,_]` 记法表示两个元素的列表，
或者 [DeBruijn][plfa.DeBruijn] 章节中的 `Γ , A` 来表示环境的扩展。
标准库中的 `_⇔_` 和我们的相似，但使用起来比较不便，
因为它可以根据任意的相等性定义进行参数化。

## Unicode

{::comment}
This chapter uses the following unicode:

    ×  U+00D7  MULTIPLICATION SIGN (\x)
    ⊎  U+228E  MULTISET UNION (\u+)
    ⊤  U+22A4  DOWN TACK (\top)
    ⊥  U+22A5  UP TACK (\bot)
    η  U+03B7  GREEK SMALL LETTER ETA (\eta)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)
{:/}

本章节使用下列 Unicode：

    ×  U+00D7  乘法符号 (\x)
    ⊎  U+228E  多重集并集 (\u+)
    ⊤  U+22A4  向下图钉 (\top)
    ⊥  U+22A5  向上图钉 (\bot)
    η  U+03B7  希腊小写字母 ETA (\eta)
    ₁  U+2081  下标 1 (\_1)
    ₂  U+2082  下标 2 (\_2)
    ⇔  U+21D4  左右双箭头 (\<=>)
