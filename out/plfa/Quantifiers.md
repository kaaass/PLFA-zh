---
src: ./src/plfa/Quantifiers.lagda.md
title     : "Quantifiers: 全称量词与存在量词"
layout    : page
prev      : /Negation/
permalink : /Quantifiers/
next      : /Decidable/
translators: ["Fangyi Zhou"]
progress  : 100
---

{% raw %}<pre class="Agda"><a id="186" class="Keyword">module</a> <a id="193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}" class="Module">plfa.Quantifiers</a> <a id="210" class="Keyword">where</a>
</pre>{% endraw %}
{::comment}
This chapter introduces universal and existential quantification.
{:/}

本章节介绍全称量化（Universal Quantification）和存在量化（Existential Quantification）。

{::comment}
## Imports
{:/}

## 导入

{% raw %}<pre class="Agda"><a id="416" class="Keyword">import</a> <a id="423" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="461" class="Symbol">as</a> <a id="464" class="Module">Eq</a>
<a id="467" class="Keyword">open</a> <a id="472" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="475" class="Keyword">using</a> <a id="481" class="Symbol">(</a><a id="482" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="485" class="Symbol">;</a> <a id="487" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="491" class="Symbol">)</a>
<a id="493" class="Keyword">open</a> <a id="498" class="Keyword">import</a> <a id="505" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="514" class="Keyword">using</a> <a id="520" class="Symbol">(</a><a id="521" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="522" class="Symbol">;</a> <a id="524" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="528" class="Symbol">;</a> <a id="530" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="533" class="Symbol">;</a> <a id="535" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="538" class="Symbol">;</a> <a id="540" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="543" class="Symbol">)</a>
<a id="545" class="Keyword">open</a> <a id="550" class="Keyword">import</a> <a id="557" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="574" class="Keyword">using</a> <a id="580" class="Symbol">(</a><a id="581" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="583" class="Symbol">)</a>
<a id="585" class="Keyword">open</a> <a id="590" class="Keyword">import</a> <a id="597" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="610" class="Keyword">using</a> <a id="616" class="Symbol">(</a><a id="617" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">_×_</a><a id="620" class="Symbol">;</a> <a id="622" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Sigma.html#225" class="Field">proj₁</a><a id="627" class="Symbol">)</a> <a id="629" class="Keyword">renaming</a> <a id="638" class="Symbol">(</a><a id="639" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="643" class="Symbol">to</a> <a id="646" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="651" class="Symbol">)</a>
<a id="653" class="Keyword">open</a> <a id="658" class="Keyword">import</a> <a id="665" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.html" class="Module">Data.Sum</a> <a id="674" class="Keyword">using</a> <a id="680" class="Symbol">(</a><a id="681" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">_⊎_</a><a id="684" class="Symbol">)</a>
<a id="686" class="Keyword">open</a> <a id="691" class="Keyword">import</a> <a id="698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}" class="Module">plfa.Isomorphism</a> <a id="715" class="Keyword">using</a> <a id="721" class="Symbol">(</a><a id="722" href="plfa.Isomorphism.html#5424" class="Record Operator">_≃_</a><a id="725" class="Symbol">;</a> <a id="727" href="plfa.Isomorphism.html#3728" class="Postulate">extensionality</a><a id="741" class="Symbol">)</a>
</pre>{% endraw %}

{::comment}
## Universals
{:/}

## 全称量化

{::comment}
We formalise universal quantification using the
dependent function type, which has appeared throughout this book.
{:/}

我们用依赖函数类型（Dependent Function Type）来形式化全称量化。
这样的形式贯穿全书地出现。


{::comment}
Given a variable `x` of type `A` and a proposition `B x` which
contains `x` as a free variable, the universally quantified
proposition `∀ (x : A) → B x` holds if for every term `M` of type
`A` the proposition `B M` holds.  Here `B M` stands for
the proposition `B x` with each free occurrence of `x` replaced by
`M`.  Variable `x` appears free in `B x` but bound in
`∀ (x : A) → B x`.
{:/}

给定一个 `A` 类型的变量 `x` 和一个带有 `x` 自由变量的命题 `B x`，全称量化
的命题 `∀ (x : A) → B x` 当对于所有类型为 `A` 的项 `M`，命题 `B M` 成立时成立。
在这里，`B M` 代表了将 `B x` 中自由出现的变量 `x` 替换成 `M` 以后的命题。
变量 `x` 在 `B x` 中以自由变量形式出现，但是在 `∀ (x : A) → B x` 中是约束的。

{::comment}
Evidence that `∀ (x : A) → B x` holds is of the form
{:/}

`∀ (x : A) → B x` 成立的证明由以下形式构成：

    λ (x : A) → N x

{::comment}
where `N x` is a term of type `B x`, and `N x` and `B x` both contain
a free variable `x` of type `A`.  Given a term `L` providing evidence
that `∀ (x : A) → B x` holds, and a term `M` of type `A`, the term `L
M` provides evidence that `B M` holds.  In other words, evidence that
`∀ (x : A) → B x` holds is a function that converts a term `M` of type
`A` into evidence that `B M` holds.
{:/}

其中 `N x` 是一个 `B x` 类型的项，`N x` 和 `B x` 都包含了一个 `A` 类型的自由变量 `x`。
给定一个项 `L`， 其提供 `∀ (x : A) → B x` 成立的证明，和一个类型为 `A` 的项 `M`，
`L M` 这一项则是 `B M` 成立的证明。换句话说，`∀ (x : A) → B x` 成立的证明是一个函数，
将类型为 `A` 的项 `M` 转换成 `B M` 成立的证明。

{::comment}
Put another way, if we know that `∀ (x : A) → B x` holds and that `M`
is a term of type `A` then we may conclude that `B M` holds:
{:/}

再换句话说，如果我们知道 `∀ (x : A) → B x` 成立，又知道 `M` 是一个类型为 `A` 的项，
那么我们可以推导出 `B M` 成立：
{% raw %}<pre class="Agda"><a id="∀-elim"></a><a id="2569" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2569" class="Function">∀-elim</a> <a id="2576" class="Symbol">:</a> <a id="2578" class="Symbol">∀</a> <a id="2580" class="Symbol">{</a><a id="2581" href="plfa.Quantifiers.html#2581" class="Bound">A</a> <a id="2583" class="Symbol">:</a> <a id="2585" class="PrimitiveType">Set</a><a id="2588" class="Symbol">}</a> <a id="2590" class="Symbol">{</a><a id="2591" href="plfa.Quantifiers.html#2591" class="Bound">B</a> <a id="2593" class="Symbol">:</a> <a id="2595" href="plfa.Quantifiers.html#2581" class="Bound">A</a> <a id="2597" class="Symbol">→</a> <a id="2599" class="PrimitiveType">Set</a><a id="2602" class="Symbol">}</a>
  <a id="2606" class="Symbol">→</a> <a id="2608" class="Symbol">(</a><a id="2609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2609" class="Bound">L</a> <a id="2611" class="Symbol">:</a> <a id="2613" class="Symbol">∀</a> <a id="2615" class="Symbol">(</a><a id="2616" href="plfa.Quantifiers.html#2616" class="Bound">x</a> <a id="2618" class="Symbol">:</a> <a id="2620" href="plfa.Quantifiers.html#2581" class="Bound">A</a><a id="2621" class="Symbol">)</a> <a id="2623" class="Symbol">→</a> <a id="2625" href="plfa.Quantifiers.html#2591" class="Bound">B</a> <a id="2627" href="plfa.Quantifiers.html#2616" class="Bound">x</a><a id="2628" class="Symbol">)</a>
  <a id="2632" class="Symbol">→</a> <a id="2634" class="Symbol">(</a><a id="2635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2635" class="Bound">M</a> <a id="2637" class="Symbol">:</a> <a id="2639" href="plfa.Quantifiers.html#2581" class="Bound">A</a><a id="2640" class="Symbol">)</a>
    <a id="2646" class="Comment">-----------------</a>
  <a id="2666" class="Symbol">→</a> <a id="2668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2591" class="Bound">B</a> <a id="2670" href="plfa.Quantifiers.html#2635" class="Bound">M</a>
<a id="2672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#2569" class="Function">∀-elim</a> <a id="2679" href="plfa.Quantifiers.html#2679" class="Bound">L</a> <a id="2681" href="plfa.Quantifiers.html#2681" class="Bound">M</a> <a id="2683" class="Symbol">=</a> <a id="2685" href="plfa.Quantifiers.html#2679" class="Bound">L</a> <a id="2687" href="plfa.Quantifiers.html#2681" class="Bound">M</a>
</pre>{% endraw %}
{::comment}
As with `→-elim`, the rule corresponds to function application.
{:/}

如 `→-elim` 那样，这条规则对应了函数应用。

{::comment}
Functions arise as a special case of dependent functions,
where the range does not depend on a variable drawn from the domain.
When a function is viewed as evidence of implication, both its
argument and result are viewed as evidence, whereas when a dependent
function is viewed as evidence of a universal, its argument is viewed
as an element of a data type and its result is viewed as evidence of
a proposition that depends on the argument. This difference is largely
a matter of interpretation, since in Agda a value of a type and
evidence of a proposition are indistinguishable.
{:/}

函数是依赖函数的一种特殊形式，其值域不取决于定义域中的变量。当一个函数被视为
蕴涵的证明时，它的参数和结果都是证明，而当一个依赖函数被视为全称量词的证明时，
它的参数被视为数据类型中的一个元素，而结果是一个依赖于参数的命题的证明。因为在
Agda 中，一个数据类型中的一个值和一个命题的证明是无法区别的，这样的区别很大程度上
取决于如何来诠释。

{::comment}
Dependent function types are sometimes referred to as dependent
products, because if `A` is a finite type with values `x₁ , ⋯ , xₙ`,
and if each of the types `B x₁ , ⋯ , B xₙ` has `m₁ , ⋯ , mₙ` distinct
members, then `∀ (x : A) → B x` has `m₁ * ⋯ * mₙ` members.  Indeed,
sometimes the notation `∀ (x : A) → B x` is replaced by a notation
such as `Π[ x ∈ A ] (B x)`, where `Π` stands for product.  However, we
will stick with the name dependent function, because (as we will see)
dependent product is ambiguous.
{:/}

依赖函数类型也被叫做依赖积（Dependent Product），因为如果 `A` 是一个有限的数据类型，
有值 `x₁ , ⋯ , xₙ`，如果每个类型 `B x₁ , ⋯ , B xₙ` 有 `m₁ , ⋯ , mₙ` 个不同的成员，
那么 `∀ (x : A) → B x` 有 `m₁ * ⋯ * mₙ` 个成员。的确，`∀ (x : A) → B x` 的记法有时
也被 `Π[ x ∈ A ] (B x)` 取代，其中 `Π` 代表积。然而，我们还是使用依赖函数这个名称，
因为依赖积这个名称是有歧义的，我们后续会体会到歧义所在。

{::comment}
#### Exercise `∀-distrib-×` (recommended)
{:/}

#### 练习 `∀-distrib-×` （推荐）

{::comment}
Show that universals distribute over conjunction:
{:/}

证明全称量词对于合取满足分配律：

{% raw %}<pre class="Agda"><a id="4558" class="Keyword">postulate</a>
  <a id="∀-distrib-×"></a><a id="4570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4570" class="Postulate">∀-distrib-×</a> <a id="4582" class="Symbol">:</a> <a id="4584" class="Symbol">∀</a> <a id="4586" class="Symbol">{</a><a id="4587" href="plfa.Quantifiers.html#4587" class="Bound">A</a> <a id="4589" class="Symbol">:</a> <a id="4591" class="PrimitiveType">Set</a><a id="4594" class="Symbol">}</a> <a id="4596" class="Symbol">{</a><a id="4597" href="plfa.Quantifiers.html#4597" class="Bound">B</a> <a id="4599" href="plfa.Quantifiers.html#4599" class="Bound">C</a> <a id="4601" class="Symbol">:</a> <a id="4603" href="plfa.Quantifiers.html#4587" class="Bound">A</a> <a id="4605" class="Symbol">→</a> <a id="4607" class="PrimitiveType">Set</a><a id="4610" class="Symbol">}</a> <a id="4612" class="Symbol">→</a>
    <a id="4618" class="Symbol">(∀</a> <a id="4621" class="Symbol">(</a><a id="4622" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#4622" class="Bound">x</a> <a id="4624" class="Symbol">:</a> <a id="4626" href="plfa.Quantifiers.html#4587" class="Bound">A</a><a id="4627" class="Symbol">)</a> <a id="4629" class="Symbol">→</a> <a id="4631" href="plfa.Quantifiers.html#4597" class="Bound">B</a> <a id="4633" href="plfa.Quantifiers.html#4622" class="Bound">x</a> <a id="4635" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4637" href="plfa.Quantifiers.html#4599" class="Bound">C</a> <a id="4639" href="plfa.Quantifiers.html#4622" class="Bound">x</a><a id="4640" class="Symbol">)</a> <a id="4642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5424" class="Record Operator">≃</a> <a id="4644" class="Symbol">(∀</a> <a id="4647" class="Symbol">(</a><a id="4648" href="plfa.Quantifiers.html#4648" class="Bound">x</a> <a id="4650" class="Symbol">:</a> <a id="4652" href="plfa.Quantifiers.html#4587" class="Bound">A</a><a id="4653" class="Symbol">)</a> <a id="4655" class="Symbol">→</a> <a id="4657" href="plfa.Quantifiers.html#4597" class="Bound">B</a> <a id="4659" href="plfa.Quantifiers.html#4648" class="Bound">x</a><a id="4660" class="Symbol">)</a> <a id="4662" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="4664" class="Symbol">(∀</a> <a id="4667" class="Symbol">(</a><a id="4668" href="plfa.Quantifiers.html#4668" class="Bound">x</a> <a id="4670" class="Symbol">:</a> <a id="4672" href="plfa.Quantifiers.html#4587" class="Bound">A</a><a id="4673" class="Symbol">)</a> <a id="4675" class="Symbol">→</a> <a id="4677" href="plfa.Quantifiers.html#4599" class="Bound">C</a> <a id="4679" href="plfa.Quantifiers.html#4668" class="Bound">x</a><a id="4680" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Compare this with the result (`→-distrib-×`) in
Chapter [Connectives][plfa.Connectives].
{:/

将这个结果与 [Connectives][plfa.Connectives] 章节中的 (`→-distrib-×`) 结果对比。

{::comment}
#### Exercise `⊎∀-implies-∀⊎`
{:/}

#### 练习 `⊎∀-implies-∀⊎`

{::comment}
Show that a disjunction of universals implies a universal of disjunctions:
{:/}

证明全称命题的析取蕴涵了析取的全称命题：

{% raw %}<pre class="Agda"><a id="5052" class="Keyword">postulate</a>
  <a id="⊎∀-implies-∀⊎"></a><a id="5064" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5064" class="Postulate">⊎∀-implies-∀⊎</a> <a id="5078" class="Symbol">:</a> <a id="5080" class="Symbol">∀</a> <a id="5082" class="Symbol">{</a><a id="5083" href="plfa.Quantifiers.html#5083" class="Bound">A</a> <a id="5085" class="Symbol">:</a> <a id="5087" class="PrimitiveType">Set</a><a id="5090" class="Symbol">}</a> <a id="5092" class="Symbol">{</a><a id="5093" href="plfa.Quantifiers.html#5093" class="Bound">B</a> <a id="5095" href="plfa.Quantifiers.html#5095" class="Bound">C</a> <a id="5097" class="Symbol">:</a> <a id="5099" href="plfa.Quantifiers.html#5083" class="Bound">A</a> <a id="5101" class="Symbol">→</a> <a id="5103" class="PrimitiveType">Set</a><a id="5106" class="Symbol">}</a> <a id="5108" class="Symbol">→</a>
    <a id="5114" class="Symbol">(∀</a> <a id="5117" class="Symbol">(</a><a id="5118" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5118" class="Bound">x</a> <a id="5120" class="Symbol">:</a> <a id="5122" href="plfa.Quantifiers.html#5083" class="Bound">A</a><a id="5123" class="Symbol">)</a> <a id="5125" class="Symbol">→</a> <a id="5127" href="plfa.Quantifiers.html#5093" class="Bound">B</a> <a id="5129" href="plfa.Quantifiers.html#5118" class="Bound">x</a><a id="5130" class="Symbol">)</a> <a id="5132" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="5134" class="Symbol">(∀</a> <a id="5137" class="Symbol">(</a><a id="5138" href="plfa.Quantifiers.html#5138" class="Bound">x</a> <a id="5140" class="Symbol">:</a> <a id="5142" href="plfa.Quantifiers.html#5083" class="Bound">A</a><a id="5143" class="Symbol">)</a> <a id="5145" class="Symbol">→</a> <a id="5147" href="plfa.Quantifiers.html#5095" class="Bound">C</a> <a id="5149" href="plfa.Quantifiers.html#5138" class="Bound">x</a><a id="5150" class="Symbol">)</a>  <a id="5153" class="Symbol">→</a>  <a id="5156" class="Symbol">∀</a> <a id="5158" class="Symbol">(</a><a id="5159" href="plfa.Quantifiers.html#5159" class="Bound">x</a> <a id="5161" class="Symbol">:</a> <a id="5163" href="plfa.Quantifiers.html#5083" class="Bound">A</a><a id="5164" class="Symbol">)</a> <a id="5166" class="Symbol">→</a> <a id="5168" href="plfa.Quantifiers.html#5093" class="Bound">B</a> <a id="5170" href="plfa.Quantifiers.html#5159" class="Bound">x</a> <a id="5172" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="5174" href="plfa.Quantifiers.html#5095" class="Bound">C</a> <a id="5176" href="plfa.Quantifiers.html#5159" class="Bound">x</a>
</pre>{% endraw %}
{::comment}
Does the converse hold? If so, prove; if not, explain why.
{:/}

逆命题成立么？如果成立，给出证明。如果不成立，解释为什么。


{::comment}
#### Exercise `∀-×`
{:/}

#### 练习 `∀-×`

{::comment}
Consider the following type.
{:/}

参考下面的类型：

{% raw %}<pre class="Agda"><a id="5406" class="Keyword">data</a> <a id="Tri"></a><a id="5411" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5411" class="Datatype">Tri</a> <a id="5415" class="Symbol">:</a> <a id="5417" class="PrimitiveType">Set</a> <a id="5421" class="Keyword">where</a>
  <a id="Tri.aa"></a><a id="5429" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5429" class="InductiveConstructor">aa</a> <a id="5432" class="Symbol">:</a> <a id="5434" href="plfa.Quantifiers.html#5411" class="Datatype">Tri</a>
  <a id="Tri.bb"></a><a id="5440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5440" class="InductiveConstructor">bb</a> <a id="5443" class="Symbol">:</a> <a id="5445" href="plfa.Quantifiers.html#5411" class="Datatype">Tri</a>
  <a id="Tri.cc"></a><a id="5451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#5451" class="InductiveConstructor">cc</a> <a id="5454" class="Symbol">:</a> <a id="5456" href="plfa.Quantifiers.html#5411" class="Datatype">Tri</a>
</pre>{% endraw %}
{::comment}
Let `B` be a type indexed by `Tri`, that is `B : Tri → Set`.
Show that `∀ (x : Tri) → B x` is isomorphic to `B aa × B bb × B cc`.
{:/}

令 `B` 作为由 `Tri` 索引的一个类型，也就是说 `B : Tri → Set`。
证明 `∀ (x : Tri) → B x` 和 `B aa × B bb × B cc` 是同构的。


{::comment}
## Existentials
{:/}

## 存在量化

{::comment}
Given a variable `x` of type `A` and a proposition `B x` which
contains `x` as a free variable, the existentially quantified
proposition `Σ[ x ∈ A ] B x` holds if for some term `M` of type
`A` the proposition `B M` holds.  Here `B M` stands for
the proposition `B x` with each free occurrence of `x` replaced by
`M`.  Variable `x` appears free in `B x` but bound in
`Σ[ x ∈ A ] B x`.
{:/}

给定一个 `A` 类型的变量 `x` 和一个带有 `x` 自由变量的命题 `B x`，存在量化
的命题 `Σ[ x ∈ A ] B x` 当对于一些类型为 `A` 的项 `M`，命题 `B M` 成立时成立。
在这里，`B M` 代表了将 `B x` 中自由出现的变量 `x` 替换成 `M` 以后的命题。
变量 `x` 在 `B x` 中以自由变量形式出现，但是在 `Σ[ x ∈ A ] B x` 中是约束的。

{::comment}
We formalise existential quantification by declaring a suitable
inductive type:
{:/}

我们定义一个合适的归纳数据类型来形式化存在量化：

{% raw %}<pre class="Agda"><a id="6495" class="Keyword">data</a> <a id="Σ"></a><a id="6500" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6500" class="Datatype">Σ</a> <a id="6502" class="Symbol">(</a><a id="6503" href="plfa.Quantifiers.html#6503" class="Bound">A</a> <a id="6505" class="Symbol">:</a> <a id="6507" class="PrimitiveType">Set</a><a id="6510" class="Symbol">)</a> <a id="6512" class="Symbol">(</a><a id="6513" href="plfa.Quantifiers.html#6513" class="Bound">B</a> <a id="6515" class="Symbol">:</a> <a id="6517" href="plfa.Quantifiers.html#6503" class="Bound">A</a> <a id="6519" class="Symbol">→</a> <a id="6521" class="PrimitiveType">Set</a><a id="6524" class="Symbol">)</a> <a id="6526" class="Symbol">:</a> <a id="6528" class="PrimitiveType">Set</a> <a id="6532" class="Keyword">where</a>
  <a id="Σ.⟨_,_⟩"></a><a id="6540" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6540" class="InductiveConstructor Operator">⟨_,_⟩</a> <a id="6546" class="Symbol">:</a> <a id="6548" class="Symbol">(</a><a id="6549" href="plfa.Quantifiers.html#6549" class="Bound">x</a> <a id="6551" class="Symbol">:</a> <a id="6553" href="plfa.Quantifiers.html#6503" class="Bound">A</a><a id="6554" class="Symbol">)</a> <a id="6556" class="Symbol">→</a> <a id="6558" href="plfa.Quantifiers.html#6513" class="Bound">B</a> <a id="6560" href="plfa.Quantifiers.html#6549" class="Bound">x</a> <a id="6562" class="Symbol">→</a> <a id="6564" href="plfa.Quantifiers.html#6500" class="Datatype">Σ</a> <a id="6566" href="plfa.Quantifiers.html#6503" class="Bound">A</a> <a id="6568" href="plfa.Quantifiers.html#6513" class="Bound">B</a>
</pre>{% endraw %}
{::comment}
We define a convenient syntax for existentials as follows:
{:/}

我们为存在量词定义一个方便的语法：

{% raw %}<pre class="Agda"><a id="Σ-syntax"></a><a id="6675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6675" class="Function">Σ-syntax</a> <a id="6684" class="Symbol">=</a> <a id="6686" href="plfa.Quantifiers.html#6500" class="Datatype">Σ</a>
<a id="6688" class="Keyword">infix</a> <a id="6694" class="Number">2</a> <a id="6696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6675" class="Function">Σ-syntax</a>
<a id="6705" class="Keyword">syntax</a> <a id="6712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6675" class="Function">Σ-syntax</a> <a id="6721" class="Bound">A</a> <a id="6723" class="Symbol">(λ</a> <a id="6726" class="Bound">x</a> <a id="6728" class="Symbol">→</a> <a id="6730" class="Bound">B</a><a id="6731" class="Symbol">)</a> <a id="6733" class="Symbol">=</a> <a id="6735" class="Function">Σ[</a> <a id="6738" class="Bound">x</a> <a id="6740" class="Function">∈</a> <a id="6742" class="Bound">A</a> <a id="6744" class="Function">]</a> <a id="6746" class="Bound">B</a>
</pre>{% endraw %}
{::comment}
This is our first use of a syntax declaration, which specifies that
the term on the left may be written with the syntax on the right.
The special syntax is available only when the identifier
`Σ-syntax` is imported.
{:/}

这是我们第一次使用语法声明，其表示左手边的项可以以右手边的语法来书写。
这种特殊语法只有在标识符 `Σ-syntax` 被导入时可用。

{::comment}
Evidence that `Σ[ x ∈ A ] B x` holds is of the form
`⟨ M , N ⟩` where `M` is a term of type `A`, and `N` is evidence
that `B M` holds.
{:/}

`Σ[ x ∈ A ] B x` 成立的证明由 `⟨ M , N ⟩` 组成，其中 `M` 是类型为 `A` 的项，
`N` 是 `B M` 成立的证明。


{::comment}
Equivalently, we could also declare existentials as a record type:
{:/}

我们也可以用记录类型来等价地定义存在量化。

{% raw %}<pre class="Agda"><a id="7400" class="Keyword">record</a> <a id="Σ′"></a><a id="7407" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7407" class="Record">Σ′</a> <a id="7410" class="Symbol">(</a><a id="7411" href="plfa.Quantifiers.html#7411" class="Bound">A</a> <a id="7413" class="Symbol">:</a> <a id="7415" class="PrimitiveType">Set</a><a id="7418" class="Symbol">)</a> <a id="7420" class="Symbol">(</a><a id="7421" href="plfa.Quantifiers.html#7421" class="Bound">B</a> <a id="7423" class="Symbol">:</a> <a id="7425" href="plfa.Quantifiers.html#7411" class="Bound">A</a> <a id="7427" class="Symbol">→</a> <a id="7429" class="PrimitiveType">Set</a><a id="7432" class="Symbol">)</a> <a id="7434" class="Symbol">:</a> <a id="7436" class="PrimitiveType">Set</a> <a id="7440" class="Keyword">where</a>
  <a id="7448" class="Keyword">field</a>
    <a id="Σ′.proj₁′"></a><a id="7458" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7458" class="Field">proj₁′</a> <a id="7465" class="Symbol">:</a> <a id="7467" href="plfa.Quantifiers.html#7411" class="Bound">A</a>
    <a id="Σ′.proj₂′"></a><a id="7473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#7473" class="Field">proj₂′</a> <a id="7480" class="Symbol">:</a> <a id="7482" href="plfa.Quantifiers.html#7421" class="Bound">B</a> <a id="7484" href="plfa.Quantifiers.html#7458" class="Field">proj₁′</a>
</pre>{% endraw %}
{::comment}
Here record construction
{:/}

这里的记录构造

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

{::comment}
corresponds to the term
{:/}

对应了项

    ⟨ M , N ⟩

{::comment}
where `M` is a term of type `A` and `N` is a term of type `B M`.
{:/}

其中 `M` 是类型为 `A` 的项，`N` 是类型为 `B M` 的项。

{::comment}
Products arise as a special case of existentials, where the second
component does not depend on a variable drawn from the first
component.  When a product is viewed as evidence of a conjunction,
both of its components are viewed as evidence, whereas when it is
viewed as evidence of an existential, the first component is viewed as
an element of a datatype and the second component is viewed as
evidence of a proposition that depends on the first component.  This
difference is largely a matter of interpretation, since in Agda a value
of a type and evidence of a proposition are indistinguishable.
{:/}

积是依赖积的一种特殊形式，其第二分量不取决于第一分量中的变量。当一个积被视为
合取的证明时，它的两个分量都是证明，而当一个依赖积被视为存在量词的证明时，
它的第一分量被视为数据类型中的一个元素，而第二分量是一个依赖于第一分量的命题的证明。因为在
Agda 中，一个数据类型中的一个值一个命题的证明是无法区别的，这样的区别很大程度上
取决于如何来诠释。

{::comment}
Existentials are sometimes referred to as dependent sums,
because if `A` is a finite type with values `x₁ , ⋯ , xₙ`, and if
each of the types `B x₁ , ⋯ B xₙ` has `m₁ , ⋯ , mₙ` distinct members,
then `Σ[ x ∈ A ] B x` has `m₁ + ⋯ + mₙ` members, which explains the
choice of notation for existentials, since `Σ` stands for sum.
{:/}

存在量化也被叫做依赖和（Dependent Sum），因为如果 `A` 是一个有限的数据类型，
有值 `x₁ , ⋯ , xₙ`，如果每个类型 `B x₁ , ⋯ , B xₙ` 有 `m₁ , ⋯ , mₙ` 个不同的成员，
那么 `Σ[ x ∈ A ] B x` 有 `m₁ + ⋯ + mₙ` 个成员，这也解释了选择使用这个记法的原因——
`Σ` 代表和。

{::comment}
Existentials are sometimes referred to as dependent products, since
products arise as a special case.  However, that choice of names is
doubly confusing, since universals also have a claim to the name dependent
product and since existentials also have a claim to the name dependent sum.
{:/}

存在量化有时也被叫做依赖积（Dependent Product），因为积是其中的一种特殊形式。但是，
这样的叫法非常让人困扰，因为全程量化也被叫做依赖积，而存在量化已经有依赖和的叫法。

{::comment}
A common notation for existentials is `∃` (analogous to `∀` for universals).
We follow the convention of the Agda standard library, and reserve this
notation for the case where the domain of the bound variable is left implicit:
{:/}

存在量词的普通记法是 `∃` （与全程量词的 `∀` 记法相类似）。我们使用 Agda 标准库中的惯例，
使用一种隐式申明约束变量定义域的记法。

{% raw %}<pre class="Agda"><a id="∃"></a><a id="9834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9834" class="Function">∃</a> <a id="9836" class="Symbol">:</a> <a id="9838" class="Symbol">∀</a> <a id="9840" class="Symbol">{</a><a id="9841" href="plfa.Quantifiers.html#9841" class="Bound">A</a> <a id="9843" class="Symbol">:</a> <a id="9845" class="PrimitiveType">Set</a><a id="9848" class="Symbol">}</a> <a id="9850" class="Symbol">(</a><a id="9851" href="plfa.Quantifiers.html#9851" class="Bound">B</a> <a id="9853" class="Symbol">:</a> <a id="9855" href="plfa.Quantifiers.html#9841" class="Bound">A</a> <a id="9857" class="Symbol">→</a> <a id="9859" class="PrimitiveType">Set</a><a id="9862" class="Symbol">)</a> <a id="9864" class="Symbol">→</a> <a id="9866" class="PrimitiveType">Set</a>
<a id="9870" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9834" class="Function">∃</a> <a id="9872" class="Symbol">{</a><a id="9873" href="plfa.Quantifiers.html#9873" class="Bound">A</a><a id="9874" class="Symbol">}</a> <a id="9876" href="plfa.Quantifiers.html#9876" class="Bound">B</a> <a id="9878" class="Symbol">=</a> <a id="9880" href="plfa.Quantifiers.html#6500" class="Datatype">Σ</a> <a id="9882" href="plfa.Quantifiers.html#9873" class="Bound">A</a> <a id="9884" href="plfa.Quantifiers.html#9876" class="Bound">B</a>

<a id="∃-syntax"></a><a id="9887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9887" class="Function">∃-syntax</a> <a id="9896" class="Symbol">=</a> <a id="9898" href="plfa.Quantifiers.html#9834" class="Function">∃</a>
<a id="9900" class="Keyword">syntax</a> <a id="9907" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9887" class="Function">∃-syntax</a> <a id="9916" class="Symbol">(λ</a> <a id="9919" class="Bound">x</a> <a id="9921" class="Symbol">→</a> <a id="9923" class="Bound">B</a><a id="9924" class="Symbol">)</a> <a id="9926" class="Symbol">=</a> <a id="9928" class="Function">∃[</a> <a id="9931" class="Bound">x</a> <a id="9933" class="Function">]</a> <a id="9935" class="Bound">B</a>
</pre>{% endraw %}
{::comment}
The special syntax is available only when the identifier `∃-syntax` is imported.
We will tend to use this syntax, since it is shorter and more familiar.
{:/}

这种特殊的语法只有在 `∃-syntax` 标识符被导入时可用。我们将倾向于使用这种语法，因为它更短，
而且看上去更熟悉。

{::comment}
Given evidence that `∀ x → B x → C` holds, where `C` does not contain
`x` as a free variable, and given evidence that `∃[ x ] B x` holds, we
may conclude that `C` holds:
{:/}

给定 `∀ x → B x → C` 成立的证明，其中 `C` 不包括自由变量 `x`，给定 `∃[ x ] B x` 成立的
证明，我们可以推导出 `C` 成立。

{% raw %}<pre class="Agda"><a id="∃-elim"></a><a id="10452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10452" class="Function">∃-elim</a> <a id="10459" class="Symbol">:</a> <a id="10461" class="Symbol">∀</a> <a id="10463" class="Symbol">{</a><a id="10464" href="plfa.Quantifiers.html#10464" class="Bound">A</a> <a id="10466" class="Symbol">:</a> <a id="10468" class="PrimitiveType">Set</a><a id="10471" class="Symbol">}</a> <a id="10473" class="Symbol">{</a><a id="10474" href="plfa.Quantifiers.html#10474" class="Bound">B</a> <a id="10476" class="Symbol">:</a> <a id="10478" href="plfa.Quantifiers.html#10464" class="Bound">A</a> <a id="10480" class="Symbol">→</a> <a id="10482" class="PrimitiveType">Set</a><a id="10485" class="Symbol">}</a> <a id="10487" class="Symbol">{</a><a id="10488" href="plfa.Quantifiers.html#10488" class="Bound">C</a> <a id="10490" class="Symbol">:</a> <a id="10492" class="PrimitiveType">Set</a><a id="10495" class="Symbol">}</a>
  <a id="10499" class="Symbol">→</a> <a id="10501" class="Symbol">(∀</a> <a id="10504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10504" class="Bound">x</a> <a id="10506" class="Symbol">→</a> <a id="10508" href="plfa.Quantifiers.html#10474" class="Bound">B</a> <a id="10510" href="plfa.Quantifiers.html#10504" class="Bound">x</a> <a id="10512" class="Symbol">→</a> <a id="10514" href="plfa.Quantifiers.html#10488" class="Bound">C</a><a id="10515" class="Symbol">)</a>
  <a id="10519" class="Symbol">→</a> <a id="10521" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9887" class="Function">∃[</a> <a id="10524" href="plfa.Quantifiers.html#10524" class="Bound">x</a> <a id="10526" href="plfa.Quantifiers.html#9887" class="Function">]</a> <a id="10528" href="plfa.Quantifiers.html#10474" class="Bound">B</a> <a id="10530" href="plfa.Quantifiers.html#10524" class="Bound">x</a>
    <a id="10536" class="Comment">---------------</a>
  <a id="10554" class="Symbol">→</a> <a id="10556" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10488" class="Bound">C</a>
<a id="10558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#10452" class="Function">∃-elim</a> <a id="10565" href="plfa.Quantifiers.html#10565" class="Bound">f</a> <a id="10567" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟨</a> <a id="10569" href="plfa.Quantifiers.html#10569" class="Bound">x</a> <a id="10571" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">,</a> <a id="10573" href="plfa.Quantifiers.html#10573" class="Bound">y</a> <a id="10575" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟩</a> <a id="10577" class="Symbol">=</a> <a id="10579" href="plfa.Quantifiers.html#10565" class="Bound">f</a> <a id="10581" href="plfa.Quantifiers.html#10569" class="Bound">x</a> <a id="10583" href="plfa.Quantifiers.html#10573" class="Bound">y</a>
</pre>{% endraw %}
{::comment}
In other words, if we know for every `x` of type `A` that `B x`
implies `C`, and we know for some `x` of type `A` that `B x` holds,
then we may conclude that `C` holds.  This is because we may
instantiate that proof that `∀ x → B x → C` to any value `x` of type
`A` and any `y` of type `B x`, and exactly such values are provided by
the evidence for `∃[ x ] B x`.
{:/}

换句话说，如果我们知道对于任何 `A` 类型的 `x`，`B x` 蕴涵了 `C`，还知道对于某个类型
`A` 的 `x`，`B x` 成立，那么我们可以推导出 `C` 成立。这是因为我们可以先将 `∀ x → B x → C`
的证明对于 `A` 类型的 `x` 和 `B x` 类型的 `y` 实例化，而这样的值恰好可以由 `∃[ x ] B x`
的证明来提供。

{::comment}
Indeed, the converse also holds, and the two together form an isomorphism:
{:/}

的确，逆命题也成立，两者合起来构成一个同构：

{% raw %}<pre class="Agda"><a id="∀∃-currying"></a><a id="11279" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11279" class="Function">∀∃-currying</a> <a id="11291" class="Symbol">:</a> <a id="11293" class="Symbol">∀</a> <a id="11295" class="Symbol">{</a><a id="11296" href="plfa.Quantifiers.html#11296" class="Bound">A</a> <a id="11298" class="Symbol">:</a> <a id="11300" class="PrimitiveType">Set</a><a id="11303" class="Symbol">}</a> <a id="11305" class="Symbol">{</a><a id="11306" href="plfa.Quantifiers.html#11306" class="Bound">B</a> <a id="11308" class="Symbol">:</a> <a id="11310" href="plfa.Quantifiers.html#11296" class="Bound">A</a> <a id="11312" class="Symbol">→</a> <a id="11314" class="PrimitiveType">Set</a><a id="11317" class="Symbol">}</a> <a id="11319" class="Symbol">{</a><a id="11320" href="plfa.Quantifiers.html#11320" class="Bound">C</a> <a id="11322" class="Symbol">:</a> <a id="11324" class="PrimitiveType">Set</a><a id="11327" class="Symbol">}</a>
  <a id="11331" class="Symbol">→</a> <a id="11333" class="Symbol">(∀</a> <a id="11336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11336" class="Bound">x</a> <a id="11338" class="Symbol">→</a> <a id="11340" href="plfa.Quantifiers.html#11306" class="Bound">B</a> <a id="11342" href="plfa.Quantifiers.html#11336" class="Bound">x</a> <a id="11344" class="Symbol">→</a> <a id="11346" href="plfa.Quantifiers.html#11320" class="Bound">C</a><a id="11347" class="Symbol">)</a> <a id="11349" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5424" class="Record Operator">≃</a> <a id="11351" class="Symbol">(</a><a id="11352" href="plfa.Quantifiers.html#9887" class="Function">∃[</a> <a id="11355" href="plfa.Quantifiers.html#11355" class="Bound">x</a> <a id="11357" href="plfa.Quantifiers.html#9887" class="Function">]</a> <a id="11359" href="plfa.Quantifiers.html#11306" class="Bound">B</a> <a id="11361" href="plfa.Quantifiers.html#11355" class="Bound">x</a> <a id="11363" class="Symbol">→</a> <a id="11365" href="plfa.Quantifiers.html#11320" class="Bound">C</a><a id="11366" class="Symbol">)</a>
<a id="11368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11279" class="Function">∀∃-currying</a> <a id="11380" class="Symbol">=</a>
  <a id="11384" class="Keyword">record</a>
    <a id="11395" class="Symbol">{</a> <a id="11397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5464" class="Field">to</a>      <a id="11405" class="Symbol">=</a>  <a id="11408" class="Symbol">λ{</a> <a id="11411" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11411" class="Bound">f</a> <a id="11413" class="Symbol">→</a> <a id="11415" class="Symbol">λ{</a> <a id="11418" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟨</a> <a id="11420" href="plfa.Quantifiers.html#11420" class="Bound">x</a> <a id="11422" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">,</a> <a id="11424" href="plfa.Quantifiers.html#11424" class="Bound">y</a> <a id="11426" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟩</a> <a id="11428" class="Symbol">→</a> <a id="11430" href="plfa.Quantifiers.html#11411" class="Bound">f</a> <a id="11432" href="plfa.Quantifiers.html#11420" class="Bound">x</a> <a id="11434" href="plfa.Quantifiers.html#11424" class="Bound">y</a> <a id="11436" class="Symbol">}}</a>
    <a id="11443" class="Symbol">;</a> <a id="11445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5481" class="Field">from</a>    <a id="11453" class="Symbol">=</a>  <a id="11456" class="Symbol">λ{</a> <a id="11459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11459" class="Bound">g</a> <a id="11461" class="Symbol">→</a> <a id="11463" class="Symbol">λ{</a> <a id="11466" href="plfa.Quantifiers.html#11466" class="Bound">x</a> <a id="11468" class="Symbol">→</a> <a id="11470" class="Symbol">λ{</a> <a id="11473" href="plfa.Quantifiers.html#11473" class="Bound">y</a> <a id="11475" class="Symbol">→</a> <a id="11477" href="plfa.Quantifiers.html#11459" class="Bound">g</a> <a id="11479" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟨</a> <a id="11481" href="plfa.Quantifiers.html#11466" class="Bound">x</a> <a id="11483" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">,</a> <a id="11485" href="plfa.Quantifiers.html#11473" class="Bound">y</a> <a id="11487" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟩</a> <a id="11489" class="Symbol">}}}</a>
    <a id="11497" class="Symbol">;</a> <a id="11499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5498" class="Field">from∘to</a> <a id="11507" class="Symbol">=</a>  <a id="11510" class="Symbol">λ{</a> <a id="11513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11513" class="Bound">f</a> <a id="11515" class="Symbol">→</a> <a id="11517" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11522" class="Symbol">}</a>
    <a id="11528" class="Symbol">;</a> <a id="11530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5540" class="Field">to∘from</a> <a id="11538" class="Symbol">=</a>  <a id="11541" class="Symbol">λ{</a> <a id="11544" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#11544" class="Bound">g</a> <a id="11546" class="Symbol">→</a> <a id="11548" href="plfa.Isomorphism.html#3728" class="Postulate">extensionality</a> <a id="11563" class="Symbol">λ{</a> <a id="11566" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟨</a> <a id="11568" href="plfa.Quantifiers.html#11568" class="Bound">x</a> <a id="11570" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">,</a> <a id="11572" href="plfa.Quantifiers.html#11572" class="Bound">y</a> <a id="11574" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟩</a> <a id="11576" class="Symbol">→</a> <a id="11578" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="11583" class="Symbol">}}</a>
    <a id="11590" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
The result can be viewed as a generalisation of currying.  Indeed, the code to
establish the isomorphism is identical to what we wrote when discussing
[implication][plfa.Connectives#implication].
{:/}

这可以被看做是将柯里化推广的结果。的确，建立这两者同构的证明与之前我们讨论
[蕴涵][plfa.Connectives#implication]时给出的证明是一样的。

{::comment}
#### Exercise `∃-distrib-⊎` (recommended)
{:/}

#### 练习 `∃-distrib-⊎` （推荐）

{::comment}
Show that existentials distribute over disjunction:
{:/}

证明存在量词对于析取满足分配律：

{% raw %}<pre class="Agda"><a id="12076" class="Keyword">postulate</a>
  <a id="∃-distrib-⊎"></a><a id="12088" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12088" class="Postulate">∃-distrib-⊎</a> <a id="12100" class="Symbol">:</a> <a id="12102" class="Symbol">∀</a> <a id="12104" class="Symbol">{</a><a id="12105" href="plfa.Quantifiers.html#12105" class="Bound">A</a> <a id="12107" class="Symbol">:</a> <a id="12109" class="PrimitiveType">Set</a><a id="12112" class="Symbol">}</a> <a id="12114" class="Symbol">{</a><a id="12115" href="plfa.Quantifiers.html#12115" class="Bound">B</a> <a id="12117" href="plfa.Quantifiers.html#12117" class="Bound">C</a> <a id="12119" class="Symbol">:</a> <a id="12121" href="plfa.Quantifiers.html#12105" class="Bound">A</a> <a id="12123" class="Symbol">→</a> <a id="12125" class="PrimitiveType">Set</a><a id="12128" class="Symbol">}</a> <a id="12130" class="Symbol">→</a>
    <a id="12136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9887" class="Function">∃[</a> <a id="12139" href="plfa.Quantifiers.html#12139" class="Bound">x</a> <a id="12141" href="plfa.Quantifiers.html#9887" class="Function">]</a> <a id="12143" class="Symbol">(</a><a id="12144" href="plfa.Quantifiers.html#12115" class="Bound">B</a> <a id="12146" href="plfa.Quantifiers.html#12139" class="Bound">x</a> <a id="12148" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="12150" href="plfa.Quantifiers.html#12117" class="Bound">C</a> <a id="12152" href="plfa.Quantifiers.html#12139" class="Bound">x</a><a id="12153" class="Symbol">)</a> <a id="12155" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5424" class="Record Operator">≃</a> <a id="12157" class="Symbol">(</a><a id="12158" href="plfa.Quantifiers.html#9887" class="Function">∃[</a> <a id="12161" href="plfa.Quantifiers.html#12161" class="Bound">x</a> <a id="12163" href="plfa.Quantifiers.html#9887" class="Function">]</a> <a id="12165" href="plfa.Quantifiers.html#12115" class="Bound">B</a> <a id="12167" href="plfa.Quantifiers.html#12161" class="Bound">x</a><a id="12168" class="Symbol">)</a> <a id="12170" href="https://agda.github.io/agda-stdlib/v1.1/Data.Sum.Base.html#612" class="Datatype Operator">⊎</a> <a id="12172" class="Symbol">(</a><a id="12173" href="plfa.Quantifiers.html#9887" class="Function">∃[</a> <a id="12176" href="plfa.Quantifiers.html#12176" class="Bound">x</a> <a id="12178" href="plfa.Quantifiers.html#9887" class="Function">]</a> <a id="12180" href="plfa.Quantifiers.html#12117" class="Bound">C</a> <a id="12182" href="plfa.Quantifiers.html#12176" class="Bound">x</a><a id="12183" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
#### Exercise `∃×-implies-×∃`
{:/}

#### 练习 `∃×-implies-×∃`

{::comment}
Show that an existential of conjunctions implies a conjunction of existentials:
{:/}

证明合取的存在命题蕴涵了存在命题的合取：

{% raw %}<pre class="Agda"><a id="12387" class="Keyword">postulate</a>
  <a id="∃×-implies-×∃"></a><a id="12399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#12399" class="Postulate">∃×-implies-×∃</a> <a id="12413" class="Symbol">:</a> <a id="12415" class="Symbol">∀</a> <a id="12417" class="Symbol">{</a><a id="12418" href="plfa.Quantifiers.html#12418" class="Bound">A</a> <a id="12420" class="Symbol">:</a> <a id="12422" class="PrimitiveType">Set</a><a id="12425" class="Symbol">}</a> <a id="12427" class="Symbol">{</a><a id="12428" href="plfa.Quantifiers.html#12428" class="Bound">B</a> <a id="12430" href="plfa.Quantifiers.html#12430" class="Bound">C</a> <a id="12432" class="Symbol">:</a> <a id="12434" href="plfa.Quantifiers.html#12418" class="Bound">A</a> <a id="12436" class="Symbol">→</a> <a id="12438" class="PrimitiveType">Set</a><a id="12441" class="Symbol">}</a> <a id="12443" class="Symbol">→</a>
    <a id="12449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9887" class="Function">∃[</a> <a id="12452" href="plfa.Quantifiers.html#12452" class="Bound">x</a> <a id="12454" href="plfa.Quantifiers.html#9887" class="Function">]</a> <a id="12456" class="Symbol">(</a><a id="12457" href="plfa.Quantifiers.html#12428" class="Bound">B</a> <a id="12459" href="plfa.Quantifiers.html#12452" class="Bound">x</a> <a id="12461" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="12463" href="plfa.Quantifiers.html#12430" class="Bound">C</a> <a id="12465" href="plfa.Quantifiers.html#12452" class="Bound">x</a><a id="12466" class="Symbol">)</a> <a id="12468" class="Symbol">→</a> <a id="12470" class="Symbol">(</a><a id="12471" href="plfa.Quantifiers.html#9887" class="Function">∃[</a> <a id="12474" href="plfa.Quantifiers.html#12474" class="Bound">x</a> <a id="12476" href="plfa.Quantifiers.html#9887" class="Function">]</a> <a id="12478" href="plfa.Quantifiers.html#12428" class="Bound">B</a> <a id="12480" href="plfa.Quantifiers.html#12474" class="Bound">x</a><a id="12481" class="Symbol">)</a> <a id="12483" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1162" class="Function Operator">×</a> <a id="12485" class="Symbol">(</a><a id="12486" href="plfa.Quantifiers.html#9887" class="Function">∃[</a> <a id="12489" href="plfa.Quantifiers.html#12489" class="Bound">x</a> <a id="12491" href="plfa.Quantifiers.html#9887" class="Function">]</a> <a id="12493" href="plfa.Quantifiers.html#12430" class="Bound">C</a> <a id="12495" href="plfa.Quantifiers.html#12489" class="Bound">x</a><a id="12496" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Does the converse hold? If so, prove; if not, explain why.
{:/}

逆命题成立么？如果成立，给出证明。如果不成立，解释为什么。

{::comment}
#### Exercise `∃-⊎`
{:/}

#### 练习 `∃-⊎`

{::comment}
Let `Tri` and `B` be as in Exercise `∀-×`.
Show that `∃[ x ] B x` is isomorphic to `B aa ⊎ B bb ⊎ B cc`.
{:/}

沿用练习 `∀-×` 中的 `Tri` 和 `B` 。
证明 `∃[ x ] B x` 与 `B aa ⊎ B bb ⊎ B cc` 是同构的。

{::comment}
## An existential example
{:/}

## 一个存在量化的例子

{::comment}
Recall the definitions of `even` and `odd` from
Chapter [Relations][plfa.Relations]:
{:/}

回忆我们在 [Relations][plfa.Relations] 章节中定义的 `even` 和 `odd`：

{% raw %}<pre class="Agda"><a id="13084" class="Keyword">data</a> <a id="even"></a><a id="13089" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13089" class="Datatype">even</a> <a id="13094" class="Symbol">:</a> <a id="13096" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="13098" class="Symbol">→</a> <a id="13100" class="PrimitiveType">Set</a>
<a id="13104" class="Keyword">data</a> <a id="odd"></a><a id="13109" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13109" class="Datatype">odd</a>  <a id="13114" class="Symbol">:</a> <a id="13116" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="13118" class="Symbol">→</a> <a id="13120" class="PrimitiveType">Set</a>

<a id="13125" class="Keyword">data</a> <a id="13130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13089" class="Datatype">even</a> <a id="13135" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="13144" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13144" class="InductiveConstructor">even-zero</a> <a id="13154" class="Symbol">:</a> <a id="13156" href="plfa.Quantifiers.html#13089" class="Datatype">even</a> <a id="13161" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="13169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13169" class="InductiveConstructor">even-suc</a> <a id="13178" class="Symbol">:</a> <a id="13180" class="Symbol">∀</a> <a id="13182" class="Symbol">{</a><a id="13183" href="plfa.Quantifiers.html#13183" class="Bound">n</a> <a id="13185" class="Symbol">:</a> <a id="13187" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="13188" class="Symbol">}</a>
    <a id="13194" class="Symbol">→</a> <a id="13196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13109" class="Datatype">odd</a> <a id="13200" href="plfa.Quantifiers.html#13183" class="Bound">n</a>
      <a id="13208" class="Comment">------------</a>
    <a id="13225" class="Symbol">→</a> <a id="13227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13089" class="Datatype">even</a> <a id="13232" class="Symbol">(</a><a id="13233" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13237" href="plfa.Quantifiers.html#13183" class="Bound">n</a><a id="13238" class="Symbol">)</a>

<a id="13241" class="Keyword">data</a> <a id="13246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13109" class="Datatype">odd</a> <a id="13250" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="13258" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13258" class="InductiveConstructor">odd-suc</a> <a id="13266" class="Symbol">:</a> <a id="13268" class="Symbol">∀</a> <a id="13270" class="Symbol">{</a><a id="13271" href="plfa.Quantifiers.html#13271" class="Bound">n</a> <a id="13273" class="Symbol">:</a> <a id="13275" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="13276" class="Symbol">}</a>
    <a id="13282" class="Symbol">→</a> <a id="13284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13089" class="Datatype">even</a> <a id="13289" href="plfa.Quantifiers.html#13271" class="Bound">n</a>
      <a id="13297" class="Comment">-----------</a>
    <a id="13313" class="Symbol">→</a> <a id="13315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#13109" class="Datatype">odd</a> <a id="13319" class="Symbol">(</a><a id="13320" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13324" href="plfa.Quantifiers.html#13271" class="Bound">n</a><a id="13325" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
A number is even if it is zero or the successor of an odd number, and
odd if it is the successor of an even number.
{:/}

如果一个数是 0 或者它是奇数的后继，那么这个数是偶数。如果一个数是偶数的后继，那么这个数是奇数。

{::comment}
We will show that a number is even if and only if it is twice some
other number, and odd if and only if it is one more than twice
some other number.  In other words, we will show:
{:/}

我们接下来要证明，一个数是偶数当且仅当这个数是一个数的两倍，一个数是奇数当且仅当这个数
是一个数的两倍多一。换句话说，我们要证明的是：

{::comment}
`even n`   iff   `∃[ m ] (    m * 2 ≡ n)`

`odd  n`   iff   `∃[ m ] (1 + m * 2 ≡ n)`
{:/}

`even n`   当且仅当   `∃[ m ] (    m * 2 ≡ n)`

`odd  n`   当且仅当   `∃[ m ] (1 + m * 2 ≡ n)`

{::comment}
By convention, one tends to write constant factors first and to put
the constant term in a sum last. Here we've reversed each of those
conventions, because doing so eases the proof.
{:/}

惯例来说，我们往往将常数因子写在前面、将和里的常数项写在后面。但是这里我们没有按照惯例，
而是反了过来，因为这样可以让证明更简单：

{::comment}
Here is the proof in the forward direction:
{:/}

这是向前方向的证明：

{% raw %}<pre class="Agda"><a id="even-∃"></a><a id="14320" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14320" class="Function">even-∃</a> <a id="14327" class="Symbol">:</a> <a id="14329" class="Symbol">∀</a> <a id="14331" class="Symbol">{</a><a id="14332" href="plfa.Quantifiers.html#14332" class="Bound">n</a> <a id="14334" class="Symbol">:</a> <a id="14336" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="14337" class="Symbol">}</a> <a id="14339" class="Symbol">→</a> <a id="14341" href="plfa.Quantifiers.html#13089" class="Datatype">even</a> <a id="14346" href="plfa.Quantifiers.html#14332" class="Bound">n</a> <a id="14348" class="Symbol">→</a> <a id="14350" href="plfa.Quantifiers.html#9887" class="Function">∃[</a> <a id="14353" href="plfa.Quantifiers.html#14353" class="Bound">m</a> <a id="14355" href="plfa.Quantifiers.html#9887" class="Function">]</a> <a id="14357" class="Symbol">(</a>    <a id="14362" href="plfa.Quantifiers.html#14353" class="Bound">m</a> <a id="14364" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="14366" class="Number">2</a> <a id="14368" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="14370" href="plfa.Quantifiers.html#14332" class="Bound">n</a><a id="14371" class="Symbol">)</a>
<a id="odd-∃"></a><a id="14373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14373" class="Function">odd-∃</a>  <a id="14380" class="Symbol">:</a> <a id="14382" class="Symbol">∀</a> <a id="14384" class="Symbol">{</a><a id="14385" href="plfa.Quantifiers.html#14385" class="Bound">n</a> <a id="14387" class="Symbol">:</a> <a id="14389" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="14390" class="Symbol">}</a> <a id="14392" class="Symbol">→</a>  <a id="14395" href="plfa.Quantifiers.html#13109" class="Datatype">odd</a> <a id="14399" href="plfa.Quantifiers.html#14385" class="Bound">n</a> <a id="14401" class="Symbol">→</a> <a id="14403" href="plfa.Quantifiers.html#9887" class="Function">∃[</a> <a id="14406" href="plfa.Quantifiers.html#14406" class="Bound">m</a> <a id="14408" href="plfa.Quantifiers.html#9887" class="Function">]</a> <a id="14410" class="Symbol">(</a><a id="14411" class="Number">1</a> <a id="14413" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14415" href="plfa.Quantifiers.html#14406" class="Bound">m</a> <a id="14417" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="14419" class="Number">2</a> <a id="14421" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="14423" href="plfa.Quantifiers.html#14385" class="Bound">n</a><a id="14424" class="Symbol">)</a>

<a id="14427" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14320" class="Function">even-∃</a> <a id="14434" href="plfa.Quantifiers.html#13144" class="InductiveConstructor">even-zero</a>                       <a id="14466" class="Symbol">=</a>  <a id="14469" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟨</a> <a id="14471" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="14476" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">,</a> <a id="14478" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="14483" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟩</a>
<a id="14485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14320" class="Function">even-∃</a> <a id="14492" class="Symbol">(</a><a id="14493" href="plfa.Quantifiers.html#13169" class="InductiveConstructor">even-suc</a> <a id="14502" href="plfa.Quantifiers.html#14502" class="Bound">o</a><a id="14503" class="Symbol">)</a> <a id="14505" class="Keyword">with</a> <a id="14510" href="plfa.Quantifiers.html#14373" class="Function">odd-∃</a> <a id="14516" href="plfa.Quantifiers.html#14502" class="Bound">o</a>
<a id="14518" class="Symbol">...</a>                    <a id="14541" class="Symbol">|</a> <a id="14543" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6540" class="InductiveConstructor Operator">⟨</a> <a id="14545" href="plfa.Quantifiers.html#14545" class="Bound">m</a> <a id="14547" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">,</a> <a id="14549" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="14554" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟩</a>  <a id="14557" class="Symbol">=</a>  <a id="14560" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟨</a> <a id="14562" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14566" href="plfa.Quantifiers.html#14545" class="Bound">m</a> <a id="14568" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">,</a> <a id="14570" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="14575" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟩</a>

<a id="14578" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#14373" class="Function">odd-∃</a>  <a id="14585" class="Symbol">(</a><a id="14586" href="plfa.Quantifiers.html#13258" class="InductiveConstructor">odd-suc</a> <a id="14594" href="plfa.Quantifiers.html#14594" class="Bound">e</a><a id="14595" class="Symbol">)</a>  <a id="14598" class="Keyword">with</a> <a id="14603" href="plfa.Quantifiers.html#14320" class="Function">even-∃</a> <a id="14610" href="plfa.Quantifiers.html#14594" class="Bound">e</a>
<a id="14612" class="Symbol">...</a>                    <a id="14635" class="Symbol">|</a> <a id="14637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#6540" class="InductiveConstructor Operator">⟨</a> <a id="14639" href="plfa.Quantifiers.html#14639" class="Bound">m</a> <a id="14641" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">,</a> <a id="14643" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="14648" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟩</a>  <a id="14651" class="Symbol">=</a>  <a id="14654" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟨</a> <a id="14656" href="plfa.Quantifiers.html#14639" class="Bound">m</a> <a id="14658" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">,</a> <a id="14660" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="14665" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟩</a>
</pre>{% endraw %}
{::comment}
We define two mutually recursive functions. Given
evidence that `n` is even or odd, we return a
number `m` and evidence that `m * 2 ≡ n` or `1 + m * 2 ≡ n`.
We induct over the evidence that `n` is even or odd:
{:/}

我们定义两个相互递归的函数。给定 `n` 是奇数或者是偶数的证明，我们返回一个数
`m`，以及 `m * 2 ≡ n` 或者 `1 + m * 2 ≡ n` 的证明。我们根据 `n` 是奇数
或者是偶数的证明进行归纳：

{::comment}
* If the number is even because it is zero, then we return a pair
consisting of zero and the evidence that twice zero is zero.

* If the number is even because it is one more than an odd number,
then we apply the induction hypothesis to give a number `m` and
evidence that `1 + m * 2 ≡ n`. We return a pair consisting of `suc m`
and evidence that `suc m * 2 ≡ suc n`, which is immediate after
substituting for `n`.

* If the number is odd because it is the successor of an even number,
then we apply the induction hypothesis to give a number `m` and
evidence that `m * 2 ≡ n`. We return a pair consisting of `suc m` and
evidence that `1 + m * 2 ≡ suc n`, which is immediate after
substituting for `n`.
{:/}

* 如果这个数是偶数，因为它是 0，那么我们返回数据对 0 ，以及 0 的两倍是 0 的证明。

* 如果这个数是偶数，因为它是比一个奇数多 1，那么我们可以使用归纳假设，来获得一个数 `m` 和
`1 + m * 2 ≡ n` 的证明。我们返回数据对 `suc m` 以及 `suc m * 2 ≡ suc n` 的证明——
我们可以直接通过替换 `n` 来得到证明。

* 如果这个数是奇数，因为它是一个偶数的后继，那么我们可以使用归纳假设，来获得一个数 `m` 和
`m * 2 ≡ n` 的证明。我们返回数据对 `suc m` 以及 `1 + m * 2 ≡ suc n` 的证明——
我们可以直接通过替换 `n` 来得到证明。

{::comment}
This completes the proof in the forward direction.
{:/}

这样，我们就完成了正方向的证明。

{::comment}
Here is the proof in the reverse direction:
{:/}

接下来是反方向的证明：

{% raw %}<pre class="Agda"><a id="∃-even"></a><a id="16217" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16217" class="Function">∃-even</a> <a id="16224" class="Symbol">:</a> <a id="16226" class="Symbol">∀</a> <a id="16228" class="Symbol">{</a><a id="16229" href="plfa.Quantifiers.html#16229" class="Bound">n</a> <a id="16231" class="Symbol">:</a> <a id="16233" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16234" class="Symbol">}</a> <a id="16236" class="Symbol">→</a> <a id="16238" href="plfa.Quantifiers.html#9887" class="Function">∃[</a> <a id="16241" href="plfa.Quantifiers.html#16241" class="Bound">m</a> <a id="16243" href="plfa.Quantifiers.html#9887" class="Function">]</a> <a id="16245" class="Symbol">(</a>    <a id="16250" href="plfa.Quantifiers.html#16241" class="Bound">m</a> <a id="16252" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="16254" class="Number">2</a> <a id="16256" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16258" href="plfa.Quantifiers.html#16229" class="Bound">n</a><a id="16259" class="Symbol">)</a> <a id="16261" class="Symbol">→</a> <a id="16263" href="plfa.Quantifiers.html#13089" class="Datatype">even</a> <a id="16268" href="plfa.Quantifiers.html#16229" class="Bound">n</a>
<a id="∃-odd"></a><a id="16270" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16270" class="Function">∃-odd</a>  <a id="16277" class="Symbol">:</a> <a id="16279" class="Symbol">∀</a> <a id="16281" class="Symbol">{</a><a id="16282" href="plfa.Quantifiers.html#16282" class="Bound">n</a> <a id="16284" class="Symbol">:</a> <a id="16286" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16287" class="Symbol">}</a> <a id="16289" class="Symbol">→</a> <a id="16291" href="plfa.Quantifiers.html#9887" class="Function">∃[</a> <a id="16294" href="plfa.Quantifiers.html#16294" class="Bound">m</a> <a id="16296" href="plfa.Quantifiers.html#9887" class="Function">]</a> <a id="16298" class="Symbol">(</a><a id="16299" class="Number">1</a> <a id="16301" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16303" href="plfa.Quantifiers.html#16294" class="Bound">m</a> <a id="16305" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">*</a> <a id="16307" class="Number">2</a> <a id="16309" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16311" href="plfa.Quantifiers.html#16282" class="Bound">n</a><a id="16312" class="Symbol">)</a> <a id="16314" class="Symbol">→</a>  <a id="16317" href="plfa.Quantifiers.html#13109" class="Datatype">odd</a> <a id="16321" href="plfa.Quantifiers.html#16282" class="Bound">n</a>

<a id="16324" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16217" class="Function">∃-even</a> <a id="16331" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟨</a>  <a id="16334" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="16339" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">,</a> <a id="16341" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="16346" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟩</a>  <a id="16349" class="Symbol">=</a>  <a id="16352" href="plfa.Quantifiers.html#13144" class="InductiveConstructor">even-zero</a>
<a id="16362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16217" class="Function">∃-even</a> <a id="16369" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟨</a> <a id="16371" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16375" href="plfa.Quantifiers.html#16375" class="Bound">m</a> <a id="16377" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">,</a> <a id="16379" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="16384" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟩</a>  <a id="16387" class="Symbol">=</a>  <a id="16390" href="plfa.Quantifiers.html#13169" class="InductiveConstructor">even-suc</a> <a id="16399" class="Symbol">(</a><a id="16400" href="plfa.Quantifiers.html#16270" class="Function">∃-odd</a> <a id="16406" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟨</a> <a id="16408" href="plfa.Quantifiers.html#16375" class="Bound">m</a> <a id="16410" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">,</a> <a id="16412" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="16417" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟩</a><a id="16418" class="Symbol">)</a>

<a id="16421" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#16270" class="Function">∃-odd</a>  <a id="16428" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟨</a>     <a id="16434" href="plfa.Quantifiers.html#16434" class="Bound">m</a> <a id="16436" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">,</a> <a id="16438" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="16443" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟩</a>  <a id="16446" class="Symbol">=</a>  <a id="16449" href="plfa.Quantifiers.html#13258" class="InductiveConstructor">odd-suc</a> <a id="16457" class="Symbol">(</a><a id="16458" href="plfa.Quantifiers.html#16217" class="Function">∃-even</a> <a id="16465" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟨</a> <a id="16467" href="plfa.Quantifiers.html#16434" class="Bound">m</a> <a id="16469" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">,</a> <a id="16471" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="16476" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟩</a><a id="16477" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Given a number that is twice some other number we must show it is
even, and a number that is one more than twice some other number we
must show it is odd.  We induct over the evidence of the existential,
and in the even case consider the two possibilities for the number
that is doubled:
{:/}

给定一个是另一个数两倍的数，我们需要证明这个数是偶数。给定一个是另一个数两倍多一的数，
我们需要证明这个数是奇数。我们对于存在量化的证明进行归纳。在偶数的情况，我们也需要考虑两种
一个数是另一个数两倍的情况。

{::comment}
- In the even case for `zero`, we must show `zero * 2` is even, which
follows by `even-zero`.

- In the even case for `suc n`, we must show `suc m * 2` is even.  The
inductive hypothesis tells us that `1 + m * 2` is odd, from which the
desired result follows by `even-suc`.

- In the odd case, we must show `1 + m * 2` is odd.  The inductive
hypothesis tell us that `m * 2` is even, from which the desired result
follows by `odd-suc`.
{:/}

- 在偶数是 `zero` 的情况中，我们需要证明 `zero * 2` 是偶数，由 `even-zero` 可得。

- 在偶数是 `suc n` 的情况中，我们需要证明 `suc m * 2` 是偶数。归纳假设告诉我们，
`1 + m * 2` 是奇数，那么所求证的结果由 `even-suc` 可得。

- 在偶数的情况中，我们需要证明 `1 + m * 2` 是奇数。归纳假设告诉我们，`m * 2` 是偶数，
那么所求证的结果由 `odd-suc` 可得。

{::comment}
This completes the proof in the backward direction.
{:/}

这样，我们就完成了向后方向的证明。

{::comment}
#### Exercise `∃-even-odd`
{:/}

#### 练习 `∃-even-odd`

{::comment}
How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.
{:/}

如果我们用 `m * 2` 代替 `2 * m`，`1 + m * 2` 代替 `2 * m + 1`，上述证明会变得复杂多少呢？
用这种方法来重写 `∃-even` 和 `∃-odd`。

{::comment}
{% raw %}<pre class="Agda"><a id="18047" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="18084" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `∃-+-≤`
{:/}

#### 练习 `∃-+-≤`

{::comment}
Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.
{:/}

证明 `y ≤ z` 当且仅当存在一个 `x` 使得 `x + y ≡ z` 成立时成立。

{::comment}
{% raw %}<pre class="Agda"><a id="18321" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="18358" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## Existentials, Universals, and Negation
{:/}

## 存在量化、全称量化和否定

{::comment}
Negation of an existential is isomorphic to the universal
of a negation.  Considering that existentials are generalised
disjunction and universals are generalised conjunction, this
result is analogous to the one which tells us that negation
of a disjunction is isomorphic to a conjunction of negations:
{:/}

存在量化的否定与否定的全称量化是同构的。考虑到存在量化是析构的推广，全称量化是合构的推广，
这样的结果与析构的否定与否定的合构是同构的结果相似。

{% raw %}<pre class="Agda"><a id="¬∃≃∀¬"></a><a id="18852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#18852" class="Function">¬∃≃∀¬</a> <a id="18858" class="Symbol">:</a> <a id="18860" class="Symbol">∀</a> <a id="18862" class="Symbol">{</a><a id="18863" href="plfa.Quantifiers.html#18863" class="Bound">A</a> <a id="18865" class="Symbol">:</a> <a id="18867" class="PrimitiveType">Set</a><a id="18870" class="Symbol">}</a> <a id="18872" class="Symbol">{</a><a id="18873" href="plfa.Quantifiers.html#18873" class="Bound">B</a> <a id="18875" class="Symbol">:</a> <a id="18877" href="plfa.Quantifiers.html#18863" class="Bound">A</a> <a id="18879" class="Symbol">→</a> <a id="18881" class="PrimitiveType">Set</a><a id="18884" class="Symbol">}</a>
  <a id="18888" class="Symbol">→</a> <a id="18890" class="Symbol">(</a><a id="18891" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="18893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9887" class="Function">∃[</a> <a id="18896" href="plfa.Quantifiers.html#18896" class="Bound">x</a> <a id="18898" href="plfa.Quantifiers.html#9887" class="Function">]</a> <a id="18900" href="plfa.Quantifiers.html#18873" class="Bound">B</a> <a id="18902" href="plfa.Quantifiers.html#18896" class="Bound">x</a><a id="18903" class="Symbol">)</a> <a id="18905" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5424" class="Record Operator">≃</a> <a id="18907" class="Symbol">∀</a> <a id="18909" href="plfa.Quantifiers.html#18909" class="Bound">x</a> <a id="18911" class="Symbol">→</a> <a id="18913" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="18915" href="plfa.Quantifiers.html#18873" class="Bound">B</a> <a id="18917" href="plfa.Quantifiers.html#18909" class="Bound">x</a>
<a id="18919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#18852" class="Function">¬∃≃∀¬</a> <a id="18925" class="Symbol">=</a>
  <a id="18929" class="Keyword">record</a>
    <a id="18940" class="Symbol">{</a> <a id="18942" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5464" class="Field">to</a>      <a id="18950" class="Symbol">=</a>  <a id="18953" class="Symbol">λ{</a> <a id="18956" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#18956" class="Bound">¬∃xy</a> <a id="18961" href="plfa.Quantifiers.html#18961" class="Bound">x</a> <a id="18963" href="plfa.Quantifiers.html#18963" class="Bound">y</a> <a id="18965" class="Symbol">→</a> <a id="18967" href="plfa.Quantifiers.html#18956" class="Bound">¬∃xy</a> <a id="18972" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟨</a> <a id="18974" href="plfa.Quantifiers.html#18961" class="Bound">x</a> <a id="18976" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">,</a> <a id="18978" href="plfa.Quantifiers.html#18963" class="Bound">y</a> <a id="18980" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟩</a> <a id="18982" class="Symbol">}</a>
    <a id="18988" class="Symbol">;</a> <a id="18990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5481" class="Field">from</a>    <a id="18998" class="Symbol">=</a>  <a id="19001" class="Symbol">λ{</a> <a id="19004" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19004" class="Bound">∀¬xy</a> <a id="19009" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟨</a> <a id="19011" href="plfa.Quantifiers.html#19011" class="Bound">x</a> <a id="19013" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">,</a> <a id="19015" href="plfa.Quantifiers.html#19015" class="Bound">y</a> <a id="19017" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟩</a> <a id="19019" class="Symbol">→</a> <a id="19021" href="plfa.Quantifiers.html#19004" class="Bound">∀¬xy</a> <a id="19026" href="plfa.Quantifiers.html#19011" class="Bound">x</a> <a id="19028" href="plfa.Quantifiers.html#19015" class="Bound">y</a> <a id="19030" class="Symbol">}</a>
    <a id="19036" class="Symbol">;</a> <a id="19038" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5498" class="Field">from∘to</a> <a id="19046" class="Symbol">=</a>  <a id="19049" class="Symbol">λ{</a> <a id="19052" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19052" class="Bound">¬∃xy</a> <a id="19057" class="Symbol">→</a> <a id="19059" href="plfa.Isomorphism.html#3728" class="Postulate">extensionality</a> <a id="19074" class="Symbol">λ{</a> <a id="19077" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟨</a> <a id="19079" href="plfa.Quantifiers.html#19079" class="Bound">x</a> <a id="19081" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">,</a> <a id="19083" href="plfa.Quantifiers.html#19083" class="Bound">y</a> <a id="19085" href="plfa.Quantifiers.html#6540" class="InductiveConstructor Operator">⟩</a> <a id="19087" class="Symbol">→</a> <a id="19089" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="19094" class="Symbol">}</a> <a id="19096" class="Symbol">}</a>
    <a id="19102" class="Symbol">;</a> <a id="19104" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5540" class="Field">to∘from</a> <a id="19112" class="Symbol">=</a>  <a id="19115" class="Symbol">λ{</a> <a id="19118" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#19118" class="Bound">∀¬xy</a> <a id="19123" class="Symbol">→</a> <a id="19125" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a> <a id="19130" class="Symbol">}</a>
    <a id="19136" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
In the `to` direction, we are given a value `¬∃xy` of type
`¬ ∃[ x ] B x`, and need to show that given a value
`x` that `¬ B x` follows, in other words, from
a value `y` of type `B x` we can derive false.  Combining
`x` and `y` gives us a value `⟨ x , y ⟩` of type `∃[ x ] B x`,
and applying `¬∃xy` to that yields a contradiction.
{:/}

在 `to` 的方向，给定了一个 `¬ ∃[ x ] B x` 类型的值 `¬∃xy`，需要证明给定一个 `x` 的值，
可以推导出 `¬ B x`。换句话说，给定一个 `B x` 类型的值 `y`，我们可以推导出假。将 `x` 和 `y`
合并起来我们就得到了 `∃[ x ] B x` 类型的值 `⟨ x , y ⟩`，对其使用 `¬∃xy` 即可获得矛盾。

{::comment}
In the `from` direction, we are given a value `∀¬xy` of type
`∀ x → ¬ B x`, and need to show that from a value `⟨ x , y ⟩`
of type `∃[ x ] B x` we can derive false.  Applying `∀¬xy`
to `x` gives a value of type `¬ B x`, and applying that to `y` yields
a contradiction.
{:/}

在 `from` 的方向，给定了一个 `∀ x → ¬ B x` 类型的值 `∀¬xy`，需要证明从一个类型为
`∃[ x ] B x` 类型的值 `⟨ x , y ⟩` ，我们可以推导出假。将 `∀¬xy` 使用于 `x` 之上，
可以得到类型为 `¬ B x` 的值，对其使用 `y` 即可获得矛盾。

{::comment}
The two inverse proofs are straightforward, where one direction
requires extensionality.
{:/}

两个逆的证明很直接，其中有一个方向需要外延性。

{::comment}
#### Exercise `∃¬-implies-¬∀` (recommended)
{:/}

#### 练习 `∃¬-implies-¬∀` （推荐）

{::comment}
Show that existential of a negation implies negation of a universal:
{:/}

证明否定的存在量化蕴涵了全称量化的否定：

{% raw %}<pre class="Agda"><a id="20453" class="Keyword">postulate</a>
  <a id="∃¬-implies-¬∀"></a><a id="20465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#20465" class="Postulate">∃¬-implies-¬∀</a> <a id="20479" class="Symbol">:</a> <a id="20481" class="Symbol">∀</a> <a id="20483" class="Symbol">{</a><a id="20484" href="plfa.Quantifiers.html#20484" class="Bound">A</a> <a id="20486" class="Symbol">:</a> <a id="20488" class="PrimitiveType">Set</a><a id="20491" class="Symbol">}</a> <a id="20493" class="Symbol">{</a><a id="20494" href="plfa.Quantifiers.html#20494" class="Bound">B</a> <a id="20496" class="Symbol">:</a> <a id="20498" href="plfa.Quantifiers.html#20484" class="Bound">A</a> <a id="20500" class="Symbol">→</a> <a id="20502" class="PrimitiveType">Set</a><a id="20505" class="Symbol">}</a>
    <a id="20511" class="Symbol">→</a> <a id="20513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#9887" class="Function">∃[</a> <a id="20516" href="plfa.Quantifiers.html#20516" class="Bound">x</a> <a id="20518" href="plfa.Quantifiers.html#9887" class="Function">]</a> <a id="20520" class="Symbol">(</a><a id="20521" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="20523" href="plfa.Quantifiers.html#20494" class="Bound">B</a> <a id="20525" href="plfa.Quantifiers.html#20516" class="Bound">x</a><a id="20526" class="Symbol">)</a>
      <a id="20534" class="Comment">--------------</a>
    <a id="20553" class="Symbol">→</a> <a id="20555" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="20557" class="Symbol">(∀</a> <a id="20560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#20560" class="Bound">x</a> <a id="20562" class="Symbol">→</a> <a id="20564" href="plfa.Quantifiers.html#20494" class="Bound">B</a> <a id="20566" href="plfa.Quantifiers.html#20560" class="Bound">x</a><a id="20567" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Does the converse hold? If so, prove; if not, explain why.
{:/}

逆命题成立么？如果成立，给出证明。如果不成立，解释为什么。

{::comment}
#### Exercise `Bin-isomorphism` (stretch) {#Bin-isomorphism}
{:/}

#### 练习 `Bin-isomorphism` （延伸） {#Bin-isomorphism}

{::comment}
Recall that Exercises
[Bin][plfa.Naturals#Bin],
[Bin-laws][plfa.Induction#Bin-laws], and
[Bin-predicates][plfa.Relations#Bin-predicates]
define a datatype of bitstrings representing natural numbers:
{:/}

回忆在练习 [Bin][plfa.Naturals#Bin]、
[Bin-laws][plfa.Induction#Bin-laws] 和
[Bin-predicates][plfa.Relations#Bin-predicates] 中，
我们定义了比特串的数据类型来表示自然数：

{% raw %}<pre class="Agda"><a id="21176" class="Keyword">data</a> <a id="Bin"></a><a id="21181" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#21181" class="Datatype">Bin</a> <a id="21185" class="Symbol">:</a> <a id="21187" class="PrimitiveType">Set</a> <a id="21191" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="21199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#21199" class="InductiveConstructor">nil</a> <a id="21203" class="Symbol">:</a> <a id="21205" href="plfa.Quantifiers.html#21181" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="21211" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#21211" class="InductiveConstructor Operator">x0_</a> <a id="21215" class="Symbol">:</a> <a id="21217" href="plfa.Quantifiers.html#21181" class="Datatype">Bin</a> <a id="21221" class="Symbol">→</a> <a id="21223" href="plfa.Quantifiers.html#21181" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="21229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Quantifiers.md %}{% raw %}#21229" class="InductiveConstructor Operator">x1_</a> <a id="21233" class="Symbol">:</a> <a id="21235" href="plfa.Quantifiers.html#21181" class="Datatype">Bin</a> <a id="21239" class="Symbol">→</a> <a id="21241" href="plfa.Quantifiers.html#21181" class="Datatype">Bin</a>
</pre>{% endraw %}
{::comment}
And ask you to define the following functions and predicates:
{:/}

并要求你来定义下列函数和谓词：

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

{::comment}
And to establish the following properties:
{:/}

以及证明下列性质：

    from (to n) ≡ n

    ----------
    Can (to n)

    Can x
    ---------------
    to (from x) ≡ x

{::comment}
Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ x ](Can x)`.
{:/}

使用上述，证明 `ℕ` 与 `∃[ x ](Can x)` 之间存在同构。

{::comment}
{% raw %}<pre class="Agda"><a id="21744" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="21781" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

标准库中可以找到与本章节中相似的定义：

{% raw %}<pre class="Agda"><a id="21971" class="Keyword">import</a> <a id="21978" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html" class="Module">Data.Product</a> <a id="21991" class="Keyword">using</a> <a id="21997" class="Symbol">(</a><a id="21998" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Sigma.html#139" class="Record">Σ</a><a id="21999" class="Symbol">;</a> <a id="22001" href="Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a><a id="22004" class="Symbol">;</a> <a id="22006" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1364" class="Function">∃</a><a id="22007" class="Symbol">;</a> <a id="22009" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#911" class="Function">Σ-syntax</a><a id="22017" class="Symbol">;</a> <a id="22019" href="https://agda.github.io/agda-stdlib/v1.1/Data.Product.html#1783" class="Function">∃-syntax</a><a id="22027" class="Symbol">)</a>
</pre>{% endraw %}

## Unicode

{::comment}
This chapter uses the following unicode:

    Π  U+03A0  GREEK CAPITAL LETTER PI (\Pi)
    Σ  U+03A3  GREEK CAPITAL LETTER SIGMA (\Sigma)
    ∃  U+2203  THERE EXISTS (\ex, \exists)

{:/}

本章节使用下列 Unicode：

    Π  U+03A0  希腊大写字母 PI (\Pi)
    Σ  U+03A3  希腊大写字母 SIGMA (\Sigma)
    ∃  U+2203  存在 (\ex, \exists)
