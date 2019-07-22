---
src: ./src/plfa/Isomorphism.lagda.md
title     : "Isomorphism: 同构与嵌入"
layout    : page
prev      : /Equality/
permalink : /Isomorphism/
next      : /Connectives/
translators : ["Fangyi Zhou"]
progress  : 100
---

{% raw %}<pre class="Agda"><a id="185" class="Keyword">module</a> <a id="192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}" class="Module">plfa.Isomorphism</a> <a id="209" class="Keyword">where</a>
</pre>{% endraw %}
{::comment}
This section introduces isomorphism as a way of asserting that two
types are equal, and embedding as a way of asserting that one type is
smaller than another.  We apply isomorphisms in the next chapter
to demonstrate that operations on types such as product and sum
satisfy properties akin to associativity, commutativity, and
distributivity.
{:/}

本部分介绍同构（Isomorphism）与嵌入（Embedding）。
同构可以断言两个类型是相等的，嵌入可以断言一个类型比另一个类型小。
我们会在下一章中使用同构来展示类型上的运算，例如积或者和，满足类似于交换律、结合律和分配律的性质。


{::comment}
## Imports
{:/}

## 导入

{% raw %}<pre class="Agda"><a id="743" class="Keyword">import</a> <a id="750" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="788" class="Symbol">as</a> <a id="791" class="Module">Eq</a>
<a id="794" class="Keyword">open</a> <a id="799" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="802" class="Keyword">using</a> <a id="808" class="Symbol">(</a><a id="809" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="812" class="Symbol">;</a> <a id="814" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="818" class="Symbol">;</a> <a id="820" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="824" class="Symbol">;</a> <a id="826" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html#1308" class="Function">cong-app</a><a id="834" class="Symbol">)</a>
<a id="836" class="Keyword">open</a> <a id="841" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a>
<a id="856" class="Keyword">open</a> <a id="861" class="Keyword">import</a> <a id="868" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="877" class="Keyword">using</a> <a id="883" class="Symbol">(</a><a id="884" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="885" class="Symbol">;</a> <a id="887" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="891" class="Symbol">;</a> <a id="893" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="896" class="Symbol">;</a> <a id="898" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="901" class="Symbol">)</a>
<a id="903" class="Keyword">open</a> <a id="908" class="Keyword">import</a> <a id="915" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="935" class="Keyword">using</a> <a id="941" class="Symbol">(</a><a id="942" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="948" class="Symbol">)</a>
</pre>{% endraw %}

{::comment}
## Lambda expressions
{:/}

## Lambda 表达式

{::comment}
The chapter begins with a few preliminaries that will be useful
here and elsewhere: lambda expressions, function composition, and
extensionality.
{:/}

本章节开头将补充一些有用的基础知识：lambda 表达式，函数组合，以及外延性。

{::comment}
_Lambda expressions_ provide a compact way to define functions without
naming them.  A term of the form
{:/}

*Lambda 表达式*提供了一种简洁的定义函数的方法，且不需要提供函数名。一个如同这样的项：

    λ{ P₁ → N₁; ⋯ ; Pₙ → Nₙ }

{::comment}
is equivalent to a function `f` defined by the equations
{:/}

等同于定义一个函数 `f`，使用下列等式：

    f P₁ = N₁
    ⋯
    f Pₙ = Nₙ

{::comment}
where the `Pₙ` are patterns (left-hand sides of an equation) and the
`Nₙ` are expressions (right-hand side of an equation).
{:/}

其中 `Pₙ` 是模式（即等式的左手边），`Nₙ` 是表达式（即等式的右手边）。

{::comment}
In the case that there is one equation and the pattern is a variable,
we may also use the syntax
{:/}

如果只有一个等式，且模式是一个变量，我们亦可使用下面的语法：

    λ x → N

{::comment}
or
{:/}

或者

    λ (x : A) → N

{::comment}
both of which are equivalent to `λ{x → N}`. The latter allows one to
specify the domain of the function.
{:/}

两个都与 `λ{x → N}` 等价。后者可以指定函数的作用域。

{::comment}
Often using an anonymous lambda expression is more convenient than
using a named function: it avoids a lengthy type declaration; and the
definition appears exactly where the function is used, so there is no
need for the writer to remember to declare it in advance, or for the
reader to search for the definition in the code.
{:/}

往往使用匿名的 lambda 表达式比使用带名字的函数要方便：它避免了冗长的类型声明；
其定义出现在其使用的地方，所以在书写时不需要记得提前声明，在阅读时不需要上下搜索函数定义。


{::comment}
## Function composition
{:/}

## 函数组合 （Function Composition）

{::comment}
In what follows, we will make use of function composition:
{:/}

接下来，我们将使用函数组合：

{% raw %}<pre class="Agda"><a id="_∘_"></a><a id="2703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2703" class="Function Operator">_∘_</a> <a id="2707" class="Symbol">:</a> <a id="2709" class="Symbol">∀</a> <a id="2711" class="Symbol">{</a><a id="2712" href="plfa.Isomorphism.html#2712" class="Bound">A</a> <a id="2714" href="plfa.Isomorphism.html#2714" class="Bound">B</a> <a id="2716" href="plfa.Isomorphism.html#2716" class="Bound">C</a> <a id="2718" class="Symbol">:</a> <a id="2720" class="PrimitiveType">Set</a><a id="2723" class="Symbol">}</a> <a id="2725" class="Symbol">→</a> <a id="2727" class="Symbol">(</a><a id="2728" href="plfa.Isomorphism.html#2714" class="Bound">B</a> <a id="2730" class="Symbol">→</a> <a id="2732" href="plfa.Isomorphism.html#2716" class="Bound">C</a><a id="2733" class="Symbol">)</a> <a id="2735" class="Symbol">→</a> <a id="2737" class="Symbol">(</a><a id="2738" href="plfa.Isomorphism.html#2712" class="Bound">A</a> <a id="2740" class="Symbol">→</a> <a id="2742" href="plfa.Isomorphism.html#2714" class="Bound">B</a><a id="2743" class="Symbol">)</a> <a id="2745" class="Symbol">→</a> <a id="2747" class="Symbol">(</a><a id="2748" href="plfa.Isomorphism.html#2712" class="Bound">A</a> <a id="2750" class="Symbol">→</a> <a id="2752" href="plfa.Isomorphism.html#2716" class="Bound">C</a><a id="2753" class="Symbol">)</a>
<a id="2755" class="Symbol">(</a><a id="2756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2756" class="Bound">g</a> <a id="2758" href="plfa.Isomorphism.html#2703" class="Function Operator">∘</a> <a id="2760" href="plfa.Isomorphism.html#2760" class="Bound">f</a><a id="2761" class="Symbol">)</a> <a id="2763" href="plfa.Isomorphism.html#2763" class="Bound">x</a>  <a id="2766" class="Symbol">=</a> <a id="2768" href="plfa.Isomorphism.html#2756" class="Bound">g</a> <a id="2770" class="Symbol">(</a><a id="2771" href="plfa.Isomorphism.html#2760" class="Bound">f</a> <a id="2773" href="plfa.Isomorphism.html#2763" class="Bound">x</a><a id="2774" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Thus, `g ∘ f` is the function that first applies `f` and
then applies `g`.  An equivalent definition, exploiting lambda
expressions, is as follows:
{:/}

`g ∘ f` 是一个函数，先使用函数 `f`，再使用函数 `g`。
一个等价的定义，使用 lambda 表达式，如下：

{% raw %}<pre class="Agda"><a id="_∘′_"></a><a id="3013" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3013" class="Function Operator">_∘′_</a> <a id="3018" class="Symbol">:</a> <a id="3020" class="Symbol">∀</a> <a id="3022" class="Symbol">{</a><a id="3023" href="plfa.Isomorphism.html#3023" class="Bound">A</a> <a id="3025" href="plfa.Isomorphism.html#3025" class="Bound">B</a> <a id="3027" href="plfa.Isomorphism.html#3027" class="Bound">C</a> <a id="3029" class="Symbol">:</a> <a id="3031" class="PrimitiveType">Set</a><a id="3034" class="Symbol">}</a> <a id="3036" class="Symbol">→</a> <a id="3038" class="Symbol">(</a><a id="3039" href="plfa.Isomorphism.html#3025" class="Bound">B</a> <a id="3041" class="Symbol">→</a> <a id="3043" href="plfa.Isomorphism.html#3027" class="Bound">C</a><a id="3044" class="Symbol">)</a> <a id="3046" class="Symbol">→</a> <a id="3048" class="Symbol">(</a><a id="3049" href="plfa.Isomorphism.html#3023" class="Bound">A</a> <a id="3051" class="Symbol">→</a> <a id="3053" href="plfa.Isomorphism.html#3025" class="Bound">B</a><a id="3054" class="Symbol">)</a> <a id="3056" class="Symbol">→</a> <a id="3058" class="Symbol">(</a><a id="3059" href="plfa.Isomorphism.html#3023" class="Bound">A</a> <a id="3061" class="Symbol">→</a> <a id="3063" href="plfa.Isomorphism.html#3027" class="Bound">C</a><a id="3064" class="Symbol">)</a>
<a id="3066" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3066" class="Bound">g</a> <a id="3068" href="plfa.Isomorphism.html#3013" class="Function Operator">∘′</a> <a id="3071" href="plfa.Isomorphism.html#3071" class="Bound">f</a>  <a id="3074" class="Symbol">=</a>  <a id="3077" class="Symbol">λ</a> <a id="3079" href="plfa.Isomorphism.html#3079" class="Bound">x</a> <a id="3081" class="Symbol">→</a> <a id="3083" href="plfa.Isomorphism.html#3066" class="Bound">g</a> <a id="3085" class="Symbol">(</a><a id="3086" href="plfa.Isomorphism.html#3071" class="Bound">f</a> <a id="3088" href="plfa.Isomorphism.html#3079" class="Bound">x</a><a id="3089" class="Symbol">)</a>
</pre>{% endraw %}

{::comment}
## Extensionality {#extensionality}
{:/}

## 外延性（Extensionality） {#extensionality}

{::comment}
Extensionality asserts that the only way to distinguish functions is
by applying them; if two functions applied to the same argument always
yield the same result, then they are the same function.  It is the
converse of `cong-app`, as introduced
[earlier][plfa.Equality#cong].
{:/}

外延性断言了区分函数的唯一方法是应用它们。如果两个函数作用在相同的参数上永远返回相同的结果，
那么两个函数相同。这是 `cong-app` 的逆命题，在[之前][plfa.Equality#cong]有所介绍。

{::comment}
Agda does not presume extensionality, but we can postulate that it holds:
{:/}

Agda 并不预设外延性，但我们可以假设其成立：

{% raw %}<pre class="Agda"><a id="3716" class="Keyword">postulate</a>
  <a id="extensionality"></a><a id="3728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3728" class="Postulate">extensionality</a> <a id="3743" class="Symbol">:</a> <a id="3745" class="Symbol">∀</a> <a id="3747" class="Symbol">{</a><a id="3748" href="plfa.Isomorphism.html#3748" class="Bound">A</a> <a id="3750" href="plfa.Isomorphism.html#3750" class="Bound">B</a> <a id="3752" class="Symbol">:</a> <a id="3754" class="PrimitiveType">Set</a><a id="3757" class="Symbol">}</a> <a id="3759" class="Symbol">{</a><a id="3760" href="plfa.Isomorphism.html#3760" class="Bound">f</a> <a id="3762" href="plfa.Isomorphism.html#3762" class="Bound">g</a> <a id="3764" class="Symbol">:</a> <a id="3766" href="plfa.Isomorphism.html#3748" class="Bound">A</a> <a id="3768" class="Symbol">→</a> <a id="3770" href="plfa.Isomorphism.html#3750" class="Bound">B</a><a id="3771" class="Symbol">}</a>
    <a id="3777" class="Symbol">→</a> <a id="3779" class="Symbol">(∀</a> <a id="3782" class="Symbol">(</a><a id="3783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3783" class="Bound">x</a> <a id="3785" class="Symbol">:</a> <a id="3787" href="plfa.Isomorphism.html#3748" class="Bound">A</a><a id="3788" class="Symbol">)</a> <a id="3790" class="Symbol">→</a> <a id="3792" href="plfa.Isomorphism.html#3760" class="Bound">f</a> <a id="3794" href="plfa.Isomorphism.html#3783" class="Bound">x</a> <a id="3796" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="3798" href="plfa.Isomorphism.html#3762" class="Bound">g</a> <a id="3800" href="plfa.Isomorphism.html#3783" class="Bound">x</a><a id="3801" class="Symbol">)</a>
      <a id="3809" class="Comment">-----------------------</a>
    <a id="3837" class="Symbol">→</a> <a id="3839" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#3760" class="Bound">f</a> <a id="3841" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="3843" href="plfa.Isomorphism.html#3762" class="Bound">g</a>
</pre>{% endraw %}
{::comment}
Postulating extensionality does not lead to difficulties, as it is
known to be consistent with the theory that underlies https://agda.github.io/agda-stdlib/v1.1/Agda.
{:/}

假设外延性不会造成困顿，因为我们知道它与 Agda 使用的理论是连贯一致的。

{::comment}
As an example, consider that we need results from two libraries,
one where addition is defined, as in
Chapter [Naturals][plfa.Naturals],
and one where it is defined the other way around.
{:/}

举个例子，我们考虑两个库都定义了加法，一个按照我们在 [Naturals][plfa.Naturals]
章节中那样定义，另一个如下，反过来定义：

{% raw %}<pre class="Agda"><a id="_+′_"></a><a id="4319" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4319" class="Function Operator">_+′_</a> <a id="4324" class="Symbol">:</a> <a id="4326" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="4328" class="Symbol">→</a> <a id="4330" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="4332" class="Symbol">→</a> <a id="4334" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a>
<a id="4336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4336" class="Bound">m</a> <a id="4338" href="plfa.Isomorphism.html#4319" class="Function Operator">+′</a> <a id="4341" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>  <a id="4347" class="Symbol">=</a> <a id="4349" href="plfa.Isomorphism.html#4336" class="Bound">m</a>
<a id="4351" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4351" class="Bound">m</a> <a id="4353" href="plfa.Isomorphism.html#4319" class="Function Operator">+′</a> <a id="4356" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="4360" href="plfa.Isomorphism.html#4360" class="Bound">n</a> <a id="4362" class="Symbol">=</a> <a id="4364" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="4368" class="Symbol">(</a><a id="4369" href="plfa.Isomorphism.html#4351" class="Bound">m</a> <a id="4371" href="plfa.Isomorphism.html#4319" class="Function Operator">+′</a> <a id="4374" href="plfa.Isomorphism.html#4360" class="Bound">n</a><a id="4375" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Applying commutativity, it is easy to show that both operators always
return the same result given the same arguments:
{:/}

通过使用交换律，我们可以简单地证明两个运算符在给定相同参数的情况下，
会返回相同的值：

{% raw %}<pre class="Agda"><a id="same-app"></a><a id="4568" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4568" class="Function">same-app</a> <a id="4577" class="Symbol">:</a> <a id="4579" class="Symbol">∀</a> <a id="4581" class="Symbol">(</a><a id="4582" href="plfa.Isomorphism.html#4582" class="Bound">m</a> <a id="4584" href="plfa.Isomorphism.html#4584" class="Bound">n</a> <a id="4586" class="Symbol">:</a> <a id="4588" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="4589" class="Symbol">)</a> <a id="4591" class="Symbol">→</a> <a id="4593" href="plfa.Isomorphism.html#4582" class="Bound">m</a> <a id="4595" href="plfa.Isomorphism.html#4319" class="Function Operator">+′</a> <a id="4598" href="plfa.Isomorphism.html#4584" class="Bound">n</a> <a id="4600" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="4602" href="plfa.Isomorphism.html#4582" class="Bound">m</a> <a id="4604" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="4606" href="plfa.Isomorphism.html#4584" class="Bound">n</a>
<a id="4608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4568" class="Function">same-app</a> <a id="4617" href="plfa.Isomorphism.html#4617" class="Bound">m</a> <a id="4619" href="plfa.Isomorphism.html#4619" class="Bound">n</a> <a id="4621" class="Keyword">rewrite</a> <a id="4629" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a> <a id="4636" href="plfa.Isomorphism.html#4617" class="Bound">m</a> <a id="4638" href="plfa.Isomorphism.html#4619" class="Bound">n</a> <a id="4640" class="Symbol">=</a> <a id="4642" href="plfa.Isomorphism.html#4663" class="Function">helper</a> <a id="4649" href="plfa.Isomorphism.html#4617" class="Bound">m</a> <a id="4651" href="plfa.Isomorphism.html#4619" class="Bound">n</a>
  <a id="4655" class="Keyword">where</a>
  <a id="4663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4663" class="Function">helper</a> <a id="4670" class="Symbol">:</a> <a id="4672" class="Symbol">∀</a> <a id="4674" class="Symbol">(</a><a id="4675" href="plfa.Isomorphism.html#4675" class="Bound">m</a> <a id="4677" href="plfa.Isomorphism.html#4677" class="Bound">n</a> <a id="4679" class="Symbol">:</a> <a id="4681" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="4682" class="Symbol">)</a> <a id="4684" class="Symbol">→</a> <a id="4686" href="plfa.Isomorphism.html#4675" class="Bound">m</a> <a id="4688" href="plfa.Isomorphism.html#4319" class="Function Operator">+′</a> <a id="4691" href="plfa.Isomorphism.html#4677" class="Bound">n</a> <a id="4693" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="4695" href="plfa.Isomorphism.html#4677" class="Bound">n</a> <a id="4697" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="4699" href="plfa.Isomorphism.html#4675" class="Bound">m</a>
  <a id="4703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4663" class="Function">helper</a> <a id="4710" href="plfa.Isomorphism.html#4710" class="Bound">m</a> <a id="4712" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="4720" class="Symbol">=</a> <a id="4722" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
  <a id="4729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4663" class="Function">helper</a> <a id="4736" href="plfa.Isomorphism.html#4736" class="Bound">m</a> <a id="4738" class="Symbol">(</a><a id="4739" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="4743" href="plfa.Isomorphism.html#4743" class="Bound">n</a><a id="4744" class="Symbol">)</a> <a id="4746" class="Symbol">=</a> <a id="4748" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="4753" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="4757" class="Symbol">(</a><a id="4758" href="plfa.Isomorphism.html#4663" class="Function">helper</a> <a id="4765" href="plfa.Isomorphism.html#4736" class="Bound">m</a> <a id="4767" href="plfa.Isomorphism.html#4743" class="Bound">n</a><a id="4768" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
However, it might be convenient to assert that the two operators are
actually indistinguishable. This we can do via two applications of
extensionality:
{:/}

然而，有时断言两个运算符是无法区分的会更加方便。我们可以使用两次外延性：

{% raw %}<pre class="Agda"><a id="same"></a><a id="4987" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4987" class="Function">same</a> <a id="4992" class="Symbol">:</a> <a id="4994" href="plfa.Isomorphism.html#4319" class="Function Operator">_+′_</a> <a id="4999" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5001" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a>
<a id="5005" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4987" class="Function">same</a> <a id="5010" class="Symbol">=</a> <a id="5012" href="plfa.Isomorphism.html#3728" class="Postulate">extensionality</a> <a id="5027" class="Symbol">(λ</a> <a id="5030" href="plfa.Isomorphism.html#5030" class="Bound">m</a> <a id="5032" class="Symbol">→</a> <a id="5034" href="plfa.Isomorphism.html#3728" class="Postulate">extensionality</a> <a id="5049" class="Symbol">(λ</a> <a id="5052" href="plfa.Isomorphism.html#5052" class="Bound">n</a> <a id="5054" class="Symbol">→</a> <a id="5056" href="plfa.Isomorphism.html#4568" class="Function">same-app</a> <a id="5065" href="plfa.Isomorphism.html#5030" class="Bound">m</a> <a id="5067" href="plfa.Isomorphism.html#5052" class="Bound">n</a><a id="5068" class="Symbol">))</a>
</pre>{% endraw %}
{::comment}
We occasionally need to postulate extensionality in what follows.
{:/}

我们偶尔需要在之后的情况中假设外延性。


{::comment}
## Isomorphism
{:/}

## 同构（Isomorphism）

{::comment}
Two sets are isomorphic if they are in one-to-one correspondence.
Here is a formal definition of isomorphism:
{:/}

如果两个集合有一一对应的关系，那么它们是同构的。
下面是同构的正式定义：

{% raw %}<pre class="Agda"><a id="5405" class="Keyword">infix</a> <a id="5411" class="Number">0</a> <a id="5413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5424" class="Record Operator">_≃_</a>
<a id="5417" class="Keyword">record</a> <a id="_≃_"></a><a id="5424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5424" class="Record Operator">_≃_</a> <a id="5428" class="Symbol">(</a><a id="5429" href="plfa.Isomorphism.html#5429" class="Bound">A</a> <a id="5431" href="plfa.Isomorphism.html#5431" class="Bound">B</a> <a id="5433" class="Symbol">:</a> <a id="5435" class="PrimitiveType">Set</a><a id="5438" class="Symbol">)</a> <a id="5440" class="Symbol">:</a> <a id="5442" class="PrimitiveType">Set</a> <a id="5446" class="Keyword">where</a>
  <a id="5454" class="Keyword">field</a>
    <a id="_≃_.to"></a><a id="5464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5464" class="Field">to</a>   <a id="5469" class="Symbol">:</a> <a id="5471" href="plfa.Isomorphism.html#5429" class="Bound">A</a> <a id="5473" class="Symbol">→</a> <a id="5475" href="plfa.Isomorphism.html#5431" class="Bound">B</a>
    <a id="_≃_.from"></a><a id="5481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5481" class="Field">from</a> <a id="5486" class="Symbol">:</a> <a id="5488" href="plfa.Isomorphism.html#5431" class="Bound">B</a> <a id="5490" class="Symbol">→</a> <a id="5492" href="plfa.Isomorphism.html#5429" class="Bound">A</a>
    <a id="_≃_.from∘to"></a><a id="5498" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5498" class="Field">from∘to</a> <a id="5506" class="Symbol">:</a> <a id="5508" class="Symbol">∀</a> <a id="5510" class="Symbol">(</a><a id="5511" href="plfa.Isomorphism.html#5511" class="Bound">x</a> <a id="5513" class="Symbol">:</a> <a id="5515" href="plfa.Isomorphism.html#5429" class="Bound">A</a><a id="5516" class="Symbol">)</a> <a id="5518" class="Symbol">→</a> <a id="5520" href="plfa.Isomorphism.html#5481" class="Field">from</a> <a id="5525" class="Symbol">(</a><a id="5526" href="plfa.Isomorphism.html#5464" class="Field">to</a> <a id="5529" href="plfa.Isomorphism.html#5511" class="Bound">x</a><a id="5530" class="Symbol">)</a> <a id="5532" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5534" href="plfa.Isomorphism.html#5511" class="Bound">x</a>
    <a id="_≃_.to∘from"></a><a id="5540" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5540" class="Field">to∘from</a> <a id="5548" class="Symbol">:</a> <a id="5550" class="Symbol">∀</a> <a id="5552" class="Symbol">(</a><a id="5553" href="plfa.Isomorphism.html#5553" class="Bound">y</a> <a id="5555" class="Symbol">:</a> <a id="5557" href="plfa.Isomorphism.html#5431" class="Bound">B</a><a id="5558" class="Symbol">)</a> <a id="5560" class="Symbol">→</a> <a id="5562" href="plfa.Isomorphism.html#5464" class="Field">to</a> <a id="5565" class="Symbol">(</a><a id="5566" href="plfa.Isomorphism.html#5481" class="Field">from</a> <a id="5571" href="plfa.Isomorphism.html#5553" class="Bound">y</a><a id="5572" class="Symbol">)</a> <a id="5574" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="5576" href="plfa.Isomorphism.html#5553" class="Bound">y</a>
<a id="5578" class="Keyword">open</a> <a id="5583" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5424" class="Module Operator">_≃_</a>
</pre>{% endraw %}
{::comment}
Let's unpack the definition. An isomorphism between sets `A` and `B` consists
of four things:
+ A function `to` from `A` to `B`,
+ A function `from` from `B` back to `A`,
+ Evidence `from∘to` asserting that `from` is a *left-inverse* for `to`,
+ Evidence `to∘from` asserting that `from` is a *right-inverse* for `to`.
{:/}

我们来一一展开这个定义。一个集合 `A` 和 `B` 之间的同构有四个要素：
+ 从 `A` 到 `B` 的函数 `to`
+ 从 `B` 回到 `A` 的函数 `from`
+ `from` 是 `to` 的*左逆*（left-inverse）的证明 `from∘to`
+ `from` 是 `to` 的*右逆*（right-inverse）的证明 `to∘from`

{::comment}
In particular, the third asserts that `from ∘ to` is the identity, and
the fourth that `to ∘ from` is the identity, hence the names.
The declaration `open _≃_` makes available the names `to`, `from`,
`from∘to`, and `to∘from`, otherwise we would need to write `_≃_.to` and so on.
{:/}

具体来说，第三条断言了 `from ∘ to` 是恒等函数，第四条断言了 `to ∘ from` 是恒等函数，
它们的名称由此得来。声明 `open _≃_` 使得 `to`、`from`、`from∘to` 和 `to∘from`
在当前作用域内可用，否则我们需要使用类似 `_≃_.to` 的写法。

{::comment}
The above is our first use of records. A record declaration is equivalent
to a corresponding inductive data declaration:
{:/}

这是我们第一次使用记录（Record）。记录声明等同于下面的归纳数据声明：

{% raw %}<pre class="Agda"><a id="6748" class="Keyword">data</a> <a id="_≃′_"></a><a id="6753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6753" class="Datatype Operator">_≃′_</a> <a id="6758" class="Symbol">(</a><a id="6759" href="plfa.Isomorphism.html#6759" class="Bound">A</a> <a id="6761" href="plfa.Isomorphism.html#6761" class="Bound">B</a> <a id="6763" class="Symbol">:</a> <a id="6765" class="PrimitiveType">Set</a><a id="6768" class="Symbol">):</a> <a id="6771" class="PrimitiveType">Set</a> <a id="6775" class="Keyword">where</a>
  <a id="_≃′_.mk-≃′"></a><a id="6783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6783" class="InductiveConstructor">mk-≃′</a> <a id="6789" class="Symbol">:</a> <a id="6791" class="Symbol">∀</a> <a id="6793" class="Symbol">(</a><a id="6794" href="plfa.Isomorphism.html#6794" class="Bound">to</a> <a id="6797" class="Symbol">:</a> <a id="6799" href="plfa.Isomorphism.html#6759" class="Bound">A</a> <a id="6801" class="Symbol">→</a> <a id="6803" href="plfa.Isomorphism.html#6761" class="Bound">B</a><a id="6804" class="Symbol">)</a> <a id="6806" class="Symbol">→</a>
          <a id="6818" class="Symbol">∀</a> <a id="6820" class="Symbol">(</a><a id="6821" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6821" class="Bound">from</a> <a id="6826" class="Symbol">:</a> <a id="6828" href="plfa.Isomorphism.html#6761" class="Bound">B</a> <a id="6830" class="Symbol">→</a> <a id="6832" href="plfa.Isomorphism.html#6759" class="Bound">A</a><a id="6833" class="Symbol">)</a> <a id="6835" class="Symbol">→</a>
          <a id="6847" class="Symbol">∀</a> <a id="6849" class="Symbol">(</a><a id="6850" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6850" class="Bound">from∘to</a> <a id="6858" class="Symbol">:</a> <a id="6860" class="Symbol">(∀</a> <a id="6863" class="Symbol">(</a><a id="6864" href="plfa.Isomorphism.html#6864" class="Bound">x</a> <a id="6866" class="Symbol">:</a> <a id="6868" href="plfa.Isomorphism.html#6759" class="Bound">A</a><a id="6869" class="Symbol">)</a> <a id="6871" class="Symbol">→</a> <a id="6873" href="plfa.Isomorphism.html#6821" class="Bound">from</a> <a id="6878" class="Symbol">(</a><a id="6879" href="plfa.Isomorphism.html#6794" class="Bound">to</a> <a id="6882" href="plfa.Isomorphism.html#6864" class="Bound">x</a><a id="6883" class="Symbol">)</a> <a id="6885" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="6887" href="plfa.Isomorphism.html#6864" class="Bound">x</a><a id="6888" class="Symbol">))</a> <a id="6891" class="Symbol">→</a>
          <a id="6903" class="Symbol">∀</a> <a id="6905" class="Symbol">(</a><a id="6906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6906" class="Bound">to∘from</a> <a id="6914" class="Symbol">:</a> <a id="6916" class="Symbol">(∀</a> <a id="6919" class="Symbol">(</a><a id="6920" href="plfa.Isomorphism.html#6920" class="Bound">y</a> <a id="6922" class="Symbol">:</a> <a id="6924" href="plfa.Isomorphism.html#6761" class="Bound">B</a><a id="6925" class="Symbol">)</a> <a id="6927" class="Symbol">→</a> <a id="6929" href="plfa.Isomorphism.html#6794" class="Bound">to</a> <a id="6932" class="Symbol">(</a><a id="6933" href="plfa.Isomorphism.html#6821" class="Bound">from</a> <a id="6938" href="plfa.Isomorphism.html#6920" class="Bound">y</a><a id="6939" class="Symbol">)</a> <a id="6941" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="6943" href="plfa.Isomorphism.html#6920" class="Bound">y</a><a id="6944" class="Symbol">))</a> <a id="6947" class="Symbol">→</a>
          <a id="6959" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6759" class="Bound">A</a> <a id="6961" href="plfa.Isomorphism.html#6753" class="Datatype Operator">≃′</a> <a id="6964" href="plfa.Isomorphism.html#6761" class="Bound">B</a>

<a id="to′"></a><a id="6967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6967" class="Function">to′</a> <a id="6971" class="Symbol">:</a> <a id="6973" class="Symbol">∀</a> <a id="6975" class="Symbol">{</a><a id="6976" href="plfa.Isomorphism.html#6976" class="Bound">A</a> <a id="6978" href="plfa.Isomorphism.html#6978" class="Bound">B</a> <a id="6980" class="Symbol">:</a> <a id="6982" class="PrimitiveType">Set</a><a id="6985" class="Symbol">}</a> <a id="6987" class="Symbol">→</a> <a id="6989" class="Symbol">(</a><a id="6990" href="plfa.Isomorphism.html#6976" class="Bound">A</a> <a id="6992" href="plfa.Isomorphism.html#6753" class="Datatype Operator">≃′</a> <a id="6995" href="plfa.Isomorphism.html#6978" class="Bound">B</a><a id="6996" class="Symbol">)</a> <a id="6998" class="Symbol">→</a> <a id="7000" class="Symbol">(</a><a id="7001" href="plfa.Isomorphism.html#6976" class="Bound">A</a> <a id="7003" class="Symbol">→</a> <a id="7005" href="plfa.Isomorphism.html#6978" class="Bound">B</a><a id="7006" class="Symbol">)</a>
<a id="7008" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6967" class="Function">to′</a> <a id="7012" class="Symbol">(</a><a id="7013" href="plfa.Isomorphism.html#6783" class="InductiveConstructor">mk-≃′</a> <a id="7019" href="plfa.Isomorphism.html#7019" class="Bound">f</a> <a id="7021" href="plfa.Isomorphism.html#7021" class="Bound">g</a> <a id="7023" href="plfa.Isomorphism.html#7023" class="Bound">g∘f</a> <a id="7027" href="plfa.Isomorphism.html#7027" class="Bound">f∘g</a><a id="7030" class="Symbol">)</a> <a id="7032" class="Symbol">=</a> <a id="7034" href="plfa.Isomorphism.html#7019" class="Bound">f</a>

<a id="from′"></a><a id="7037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7037" class="Function">from′</a> <a id="7043" class="Symbol">:</a> <a id="7045" class="Symbol">∀</a> <a id="7047" class="Symbol">{</a><a id="7048" href="plfa.Isomorphism.html#7048" class="Bound">A</a> <a id="7050" href="plfa.Isomorphism.html#7050" class="Bound">B</a> <a id="7052" class="Symbol">:</a> <a id="7054" class="PrimitiveType">Set</a><a id="7057" class="Symbol">}</a> <a id="7059" class="Symbol">→</a> <a id="7061" class="Symbol">(</a><a id="7062" href="plfa.Isomorphism.html#7048" class="Bound">A</a> <a id="7064" href="plfa.Isomorphism.html#6753" class="Datatype Operator">≃′</a> <a id="7067" href="plfa.Isomorphism.html#7050" class="Bound">B</a><a id="7068" class="Symbol">)</a> <a id="7070" class="Symbol">→</a> <a id="7072" class="Symbol">(</a><a id="7073" href="plfa.Isomorphism.html#7050" class="Bound">B</a> <a id="7075" class="Symbol">→</a> <a id="7077" href="plfa.Isomorphism.html#7048" class="Bound">A</a><a id="7078" class="Symbol">)</a>
<a id="7080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7037" class="Function">from′</a> <a id="7086" class="Symbol">(</a><a id="7087" href="plfa.Isomorphism.html#6783" class="InductiveConstructor">mk-≃′</a> <a id="7093" href="plfa.Isomorphism.html#7093" class="Bound">f</a> <a id="7095" href="plfa.Isomorphism.html#7095" class="Bound">g</a> <a id="7097" href="plfa.Isomorphism.html#7097" class="Bound">g∘f</a> <a id="7101" href="plfa.Isomorphism.html#7101" class="Bound">f∘g</a><a id="7104" class="Symbol">)</a> <a id="7106" class="Symbol">=</a> <a id="7108" href="plfa.Isomorphism.html#7095" class="Bound">g</a>

<a id="from∘to′"></a><a id="7111" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7111" class="Function">from∘to′</a> <a id="7120" class="Symbol">:</a> <a id="7122" class="Symbol">∀</a> <a id="7124" class="Symbol">{</a><a id="7125" href="plfa.Isomorphism.html#7125" class="Bound">A</a> <a id="7127" href="plfa.Isomorphism.html#7127" class="Bound">B</a> <a id="7129" class="Symbol">:</a> <a id="7131" class="PrimitiveType">Set</a><a id="7134" class="Symbol">}</a> <a id="7136" class="Symbol">→</a> <a id="7138" class="Symbol">(</a><a id="7139" href="plfa.Isomorphism.html#7139" class="Bound">A≃B</a> <a id="7143" class="Symbol">:</a> <a id="7145" href="plfa.Isomorphism.html#7125" class="Bound">A</a> <a id="7147" href="plfa.Isomorphism.html#6753" class="Datatype Operator">≃′</a> <a id="7150" href="plfa.Isomorphism.html#7127" class="Bound">B</a><a id="7151" class="Symbol">)</a> <a id="7153" class="Symbol">→</a> <a id="7155" class="Symbol">(∀</a> <a id="7158" class="Symbol">(</a><a id="7159" href="plfa.Isomorphism.html#7159" class="Bound">x</a> <a id="7161" class="Symbol">:</a> <a id="7163" href="plfa.Isomorphism.html#7125" class="Bound">A</a><a id="7164" class="Symbol">)</a> <a id="7166" class="Symbol">→</a> <a id="7168" href="plfa.Isomorphism.html#7037" class="Function">from′</a> <a id="7174" href="plfa.Isomorphism.html#7139" class="Bound">A≃B</a> <a id="7178" class="Symbol">(</a><a id="7179" href="plfa.Isomorphism.html#6967" class="Function">to′</a> <a id="7183" href="plfa.Isomorphism.html#7139" class="Bound">A≃B</a> <a id="7187" href="plfa.Isomorphism.html#7159" class="Bound">x</a><a id="7188" class="Symbol">)</a> <a id="7190" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="7192" href="plfa.Isomorphism.html#7159" class="Bound">x</a><a id="7193" class="Symbol">)</a>
<a id="7195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7111" class="Function">from∘to′</a> <a id="7204" class="Symbol">(</a><a id="7205" href="plfa.Isomorphism.html#6783" class="InductiveConstructor">mk-≃′</a> <a id="7211" href="plfa.Isomorphism.html#7211" class="Bound">f</a> <a id="7213" href="plfa.Isomorphism.html#7213" class="Bound">g</a> <a id="7215" href="plfa.Isomorphism.html#7215" class="Bound">g∘f</a> <a id="7219" href="plfa.Isomorphism.html#7219" class="Bound">f∘g</a><a id="7222" class="Symbol">)</a> <a id="7224" class="Symbol">=</a> <a id="7226" href="plfa.Isomorphism.html#7215" class="Bound">g∘f</a>

<a id="to∘from′"></a><a id="7231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7231" class="Function">to∘from′</a> <a id="7240" class="Symbol">:</a> <a id="7242" class="Symbol">∀</a> <a id="7244" class="Symbol">{</a><a id="7245" href="plfa.Isomorphism.html#7245" class="Bound">A</a> <a id="7247" href="plfa.Isomorphism.html#7247" class="Bound">B</a> <a id="7249" class="Symbol">:</a> <a id="7251" class="PrimitiveType">Set</a><a id="7254" class="Symbol">}</a> <a id="7256" class="Symbol">→</a> <a id="7258" class="Symbol">(</a><a id="7259" href="plfa.Isomorphism.html#7259" class="Bound">A≃B</a> <a id="7263" class="Symbol">:</a> <a id="7265" href="plfa.Isomorphism.html#7245" class="Bound">A</a> <a id="7267" href="plfa.Isomorphism.html#6753" class="Datatype Operator">≃′</a> <a id="7270" href="plfa.Isomorphism.html#7247" class="Bound">B</a><a id="7271" class="Symbol">)</a> <a id="7273" class="Symbol">→</a> <a id="7275" class="Symbol">(∀</a> <a id="7278" class="Symbol">(</a><a id="7279" href="plfa.Isomorphism.html#7279" class="Bound">y</a> <a id="7281" class="Symbol">:</a> <a id="7283" href="plfa.Isomorphism.html#7247" class="Bound">B</a><a id="7284" class="Symbol">)</a> <a id="7286" class="Symbol">→</a> <a id="7288" href="plfa.Isomorphism.html#6967" class="Function">to′</a> <a id="7292" href="plfa.Isomorphism.html#7259" class="Bound">A≃B</a> <a id="7296" class="Symbol">(</a><a id="7297" href="plfa.Isomorphism.html#7037" class="Function">from′</a> <a id="7303" href="plfa.Isomorphism.html#7259" class="Bound">A≃B</a> <a id="7307" href="plfa.Isomorphism.html#7279" class="Bound">y</a><a id="7308" class="Symbol">)</a> <a id="7310" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="7312" href="plfa.Isomorphism.html#7279" class="Bound">y</a><a id="7313" class="Symbol">)</a>
<a id="7315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7231" class="Function">to∘from′</a> <a id="7324" class="Symbol">(</a><a id="7325" href="plfa.Isomorphism.html#6783" class="InductiveConstructor">mk-≃′</a> <a id="7331" href="plfa.Isomorphism.html#7331" class="Bound">f</a> <a id="7333" href="plfa.Isomorphism.html#7333" class="Bound">g</a> <a id="7335" href="plfa.Isomorphism.html#7335" class="Bound">g∘f</a> <a id="7339" href="plfa.Isomorphism.html#7339" class="Bound">f∘g</a><a id="7342" class="Symbol">)</a> <a id="7344" class="Symbol">=</a> <a id="7346" href="plfa.Isomorphism.html#7339" class="Bound">f∘g</a>
</pre>{% endraw %}
{::comment}
We construct values of the record type with the syntax
{:/}

我们用下面的语法来构造一个记录类型的值：

    record
      { to    = f
      ; from  = g
      ; from∘to = g∘f
      ; to∘from = f∘g
      }

{::comment}
which corresponds to using the constructor of the corresponding
inductive type
{:/}

这与使用相应的归纳类型的构造器对应：

    mk-≃′ f g g∘f f∘g

{::comment}
where `f`, `g`, `g∘f`, and `f∘g` are values of suitable types.
{:/}

其中 `f`、`g`、`g∘f` 和 `f∘g` 是相应类型的值。


{::comment}
## Isomorphism is an equivalence
{:/}

## 同构是一个等价关系

{::comment}
Isomorphism is an equivalence, meaning that it is reflexive, symmetric,
and transitive.  To show isomorphism is reflexive, we take both `to`
and `from` to be the identity function:
{:/}

同构是一个等价关系。这意味着它自反、对称、传递。要证明同构是自反的，我们用恒等函数
作为 `to` 和 `from`：

{% raw %}<pre class="Agda"><a id="≃-refl"></a><a id="8136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8136" class="Function">≃-refl</a> <a id="8143" class="Symbol">:</a> <a id="8145" class="Symbol">∀</a> <a id="8147" class="Symbol">{</a><a id="8148" href="plfa.Isomorphism.html#8148" class="Bound">A</a> <a id="8150" class="Symbol">:</a> <a id="8152" class="PrimitiveType">Set</a><a id="8155" class="Symbol">}</a>
    <a id="8161" class="Comment">-----</a>
  <a id="8169" class="Symbol">→</a> <a id="8171" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8148" class="Bound">A</a> <a id="8173" href="plfa.Isomorphism.html#5424" class="Record Operator">≃</a> <a id="8175" href="plfa.Isomorphism.html#8148" class="Bound">A</a>
<a id="8177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8136" class="Function">≃-refl</a> <a id="8184" class="Symbol">=</a>
  <a id="8188" class="Keyword">record</a>
    <a id="8199" class="Symbol">{</a> <a id="8201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5464" class="Field">to</a>      <a id="8209" class="Symbol">=</a> <a id="8211" class="Symbol">λ{</a><a id="8213" href="plfa.Isomorphism.html#8213" class="Bound">x</a> <a id="8215" class="Symbol">→</a> <a id="8217" href="plfa.Isomorphism.html#8213" class="Bound">x</a><a id="8218" class="Symbol">}</a>
    <a id="8224" class="Symbol">;</a> <a id="8226" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5481" class="Field">from</a>    <a id="8234" class="Symbol">=</a> <a id="8236" class="Symbol">λ{</a><a id="8238" href="plfa.Isomorphism.html#8238" class="Bound">y</a> <a id="8240" class="Symbol">→</a> <a id="8242" href="plfa.Isomorphism.html#8238" class="Bound">y</a><a id="8243" class="Symbol">}</a>
    <a id="8249" class="Symbol">;</a> <a id="8251" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5498" class="Field">from∘to</a> <a id="8259" class="Symbol">=</a> <a id="8261" class="Symbol">λ{</a><a id="8263" href="plfa.Isomorphism.html#8263" class="Bound">x</a> <a id="8265" class="Symbol">→</a> <a id="8267" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="8271" class="Symbol">}</a>
    <a id="8277" class="Symbol">;</a> <a id="8279" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5540" class="Field">to∘from</a> <a id="8287" class="Symbol">=</a> <a id="8289" class="Symbol">λ{</a><a id="8291" href="plfa.Isomorphism.html#8291" class="Bound">y</a> <a id="8293" class="Symbol">→</a> <a id="8295" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="8299" class="Symbol">}</a>
    <a id="8305" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
In the above, `to` and `from` are both bound to identity functions,
and `from∘to` and `to∘from` are both bound to functions that discard
their argument and return `refl`.  In this case, `refl` alone is an
adequate proof since for the left inverse, `from (to x)`
simplifies to `x`, and similarly for the right inverse.
{:/}

如上，`to` 和 `from` 都是恒等函数，`from∘to` 和 `to∘from` 都是丢弃参数、返回
`refl` 的函数。在这样的情况下，`refl` 足够可以证明左逆，因为 `from (to x)`
化简为 `x`。右逆的证明同理。

{::comment}
To show isomorphism is symmetric, we simply swap the roles of `to`
and `from`, and `from∘to` and `to∘from`:
{:/}

要证明同构是对称的，我们把 `to` 和 `from`、`from∘to` 和 `to∘from` 互换：

{% raw %}<pre class="Agda"><a id="≃-sym"></a><a id="8959" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8959" class="Function">≃-sym</a> <a id="8965" class="Symbol">:</a> <a id="8967" class="Symbol">∀</a> <a id="8969" class="Symbol">{</a><a id="8970" href="plfa.Isomorphism.html#8970" class="Bound">A</a> <a id="8972" href="plfa.Isomorphism.html#8972" class="Bound">B</a> <a id="8974" class="Symbol">:</a> <a id="8976" class="PrimitiveType">Set</a><a id="8979" class="Symbol">}</a>
  <a id="8983" class="Symbol">→</a> <a id="8985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8970" class="Bound">A</a> <a id="8987" href="plfa.Isomorphism.html#5424" class="Record Operator">≃</a> <a id="8989" href="plfa.Isomorphism.html#8972" class="Bound">B</a>
    <a id="8995" class="Comment">-----</a>
  <a id="9003" class="Symbol">→</a> <a id="9005" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8972" class="Bound">B</a> <a id="9007" href="plfa.Isomorphism.html#5424" class="Record Operator">≃</a> <a id="9009" href="plfa.Isomorphism.html#8970" class="Bound">A</a>
<a id="9011" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8959" class="Function">≃-sym</a> <a id="9017" href="plfa.Isomorphism.html#9017" class="Bound">A≃B</a> <a id="9021" class="Symbol">=</a>
  <a id="9025" class="Keyword">record</a>
    <a id="9036" class="Symbol">{</a> <a id="9038" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5464" class="Field">to</a>      <a id="9046" class="Symbol">=</a> <a id="9048" href="plfa.Isomorphism.html#5481" class="Field">from</a> <a id="9053" href="plfa.Isomorphism.html#9017" class="Bound">A≃B</a>
    <a id="9061" class="Symbol">;</a> <a id="9063" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5481" class="Field">from</a>    <a id="9071" class="Symbol">=</a> <a id="9073" href="plfa.Isomorphism.html#5464" class="Field">to</a>   <a id="9078" href="plfa.Isomorphism.html#9017" class="Bound">A≃B</a>
    <a id="9086" class="Symbol">;</a> <a id="9088" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5498" class="Field">from∘to</a> <a id="9096" class="Symbol">=</a> <a id="9098" href="plfa.Isomorphism.html#5540" class="Field">to∘from</a> <a id="9106" href="plfa.Isomorphism.html#9017" class="Bound">A≃B</a>
    <a id="9114" class="Symbol">;</a> <a id="9116" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5540" class="Field">to∘from</a> <a id="9124" class="Symbol">=</a> <a id="9126" href="plfa.Isomorphism.html#5498" class="Field">from∘to</a> <a id="9134" href="plfa.Isomorphism.html#9017" class="Bound">A≃B</a>
    <a id="9142" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
To show isomorphism is transitive, we compose the `to` and `from`
functions, and use equational reasoning to combine the inverses:
{:/}

要证明同构是传递的，我们将 `to` 和 `from` 函数进行组合，并使用相等性论证来结合左逆和右逆：

{% raw %}<pre class="Agda"><a id="≃-trans"></a><a id="9356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9356" class="Function">≃-trans</a> <a id="9364" class="Symbol">:</a> <a id="9366" class="Symbol">∀</a> <a id="9368" class="Symbol">{</a><a id="9369" href="plfa.Isomorphism.html#9369" class="Bound">A</a> <a id="9371" href="plfa.Isomorphism.html#9371" class="Bound">B</a> <a id="9373" href="plfa.Isomorphism.html#9373" class="Bound">C</a> <a id="9375" class="Symbol">:</a> <a id="9377" class="PrimitiveType">Set</a><a id="9380" class="Symbol">}</a>
  <a id="9384" class="Symbol">→</a> <a id="9386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9369" class="Bound">A</a> <a id="9388" href="plfa.Isomorphism.html#5424" class="Record Operator">≃</a> <a id="9390" href="plfa.Isomorphism.html#9371" class="Bound">B</a>
  <a id="9394" class="Symbol">→</a> <a id="9396" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9371" class="Bound">B</a> <a id="9398" href="plfa.Isomorphism.html#5424" class="Record Operator">≃</a> <a id="9400" href="plfa.Isomorphism.html#9373" class="Bound">C</a>
    <a id="9406" class="Comment">-----</a>
  <a id="9414" class="Symbol">→</a> <a id="9416" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9369" class="Bound">A</a> <a id="9418" href="plfa.Isomorphism.html#5424" class="Record Operator">≃</a> <a id="9420" href="plfa.Isomorphism.html#9373" class="Bound">C</a>
<a id="9422" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9356" class="Function">≃-trans</a> <a id="9430" href="plfa.Isomorphism.html#9430" class="Bound">A≃B</a> <a id="9434" href="plfa.Isomorphism.html#9434" class="Bound">B≃C</a> <a id="9438" class="Symbol">=</a>
  <a id="9442" class="Keyword">record</a>
    <a id="9453" class="Symbol">{</a> <a id="9455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5464" class="Field">to</a>       <a id="9464" class="Symbol">=</a> <a id="9466" href="plfa.Isomorphism.html#5464" class="Field">to</a>   <a id="9471" href="plfa.Isomorphism.html#9434" class="Bound">B≃C</a> <a id="9475" href="plfa.Isomorphism.html#2703" class="Function Operator">∘</a> <a id="9477" href="plfa.Isomorphism.html#5464" class="Field">to</a>   <a id="9482" href="plfa.Isomorphism.html#9430" class="Bound">A≃B</a>
    <a id="9490" class="Symbol">;</a> <a id="9492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5481" class="Field">from</a>     <a id="9501" class="Symbol">=</a> <a id="9503" href="plfa.Isomorphism.html#5481" class="Field">from</a> <a id="9508" href="plfa.Isomorphism.html#9430" class="Bound">A≃B</a> <a id="9512" href="plfa.Isomorphism.html#2703" class="Function Operator">∘</a> <a id="9514" href="plfa.Isomorphism.html#5481" class="Field">from</a> <a id="9519" href="plfa.Isomorphism.html#9434" class="Bound">B≃C</a>
    <a id="9527" class="Symbol">;</a> <a id="9529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5498" class="Field">from∘to</a>  <a id="9538" class="Symbol">=</a> <a id="9540" class="Symbol">λ{</a><a id="9542" href="plfa.Isomorphism.html#9542" class="Bound">x</a> <a id="9544" class="Symbol">→</a>
        <a id="9554" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
          <a id="9570" class="Symbol">(</a><a id="9571" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5481" class="Field">from</a> <a id="9576" href="plfa.Isomorphism.html#9430" class="Bound">A≃B</a> <a id="9580" href="plfa.Isomorphism.html#2703" class="Function Operator">∘</a> <a id="9582" href="plfa.Isomorphism.html#5481" class="Field">from</a> <a id="9587" href="plfa.Isomorphism.html#9434" class="Bound">B≃C</a><a id="9590" class="Symbol">)</a> <a id="9592" class="Symbol">((</a><a id="9594" href="plfa.Isomorphism.html#5464" class="Field">to</a> <a id="9597" href="plfa.Isomorphism.html#9434" class="Bound">B≃C</a> <a id="9601" href="plfa.Isomorphism.html#2703" class="Function Operator">∘</a> <a id="9603" href="plfa.Isomorphism.html#5464" class="Field">to</a> <a id="9606" href="plfa.Isomorphism.html#9430" class="Bound">A≃B</a><a id="9609" class="Symbol">)</a> <a id="9611" href="plfa.Isomorphism.html#9542" class="Bound">x</a><a id="9612" class="Symbol">)</a>
        <a id="9622" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
          <a id="9636" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5481" class="Field">from</a> <a id="9641" href="plfa.Isomorphism.html#9430" class="Bound">A≃B</a> <a id="9645" class="Symbol">(</a><a id="9646" href="plfa.Isomorphism.html#5481" class="Field">from</a> <a id="9651" href="plfa.Isomorphism.html#9434" class="Bound">B≃C</a> <a id="9655" class="Symbol">(</a><a id="9656" href="plfa.Isomorphism.html#5464" class="Field">to</a> <a id="9659" href="plfa.Isomorphism.html#9434" class="Bound">B≃C</a> <a id="9663" class="Symbol">(</a><a id="9664" href="plfa.Isomorphism.html#5464" class="Field">to</a> <a id="9667" href="plfa.Isomorphism.html#9430" class="Bound">A≃B</a> <a id="9671" href="plfa.Isomorphism.html#9542" class="Bound">x</a><a id="9672" class="Symbol">)))</a>
        <a id="9684" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="9687" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="9692" class="Symbol">(</a><a id="9693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5481" class="Field">from</a> <a id="9698" href="plfa.Isomorphism.html#9430" class="Bound">A≃B</a><a id="9701" class="Symbol">)</a> <a id="9703" class="Symbol">(</a><a id="9704" href="plfa.Isomorphism.html#5498" class="Field">from∘to</a> <a id="9712" href="plfa.Isomorphism.html#9434" class="Bound">B≃C</a> <a id="9716" class="Symbol">(</a><a id="9717" href="plfa.Isomorphism.html#5464" class="Field">to</a> <a id="9720" href="plfa.Isomorphism.html#9430" class="Bound">A≃B</a> <a id="9724" href="plfa.Isomorphism.html#9542" class="Bound">x</a><a id="9725" class="Symbol">))</a> <a id="9728" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="9740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5481" class="Field">from</a> <a id="9745" href="plfa.Isomorphism.html#9430" class="Bound">A≃B</a> <a id="9749" class="Symbol">(</a><a id="9750" href="plfa.Isomorphism.html#5464" class="Field">to</a> <a id="9753" href="plfa.Isomorphism.html#9430" class="Bound">A≃B</a> <a id="9757" href="plfa.Isomorphism.html#9542" class="Bound">x</a><a id="9758" class="Symbol">)</a>
        <a id="9768" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="9771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5498" class="Field">from∘to</a> <a id="9779" href="plfa.Isomorphism.html#9430" class="Bound">A≃B</a> <a id="9783" href="plfa.Isomorphism.html#9542" class="Bound">x</a> <a id="9785" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="9797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9542" class="Bound">x</a>
        <a id="9807" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a><a id="9808" class="Symbol">}</a>
    <a id="9814" class="Symbol">;</a> <a id="9816" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5540" class="Field">to∘from</a> <a id="9824" class="Symbol">=</a> <a id="9826" class="Symbol">λ{</a><a id="9828" href="plfa.Isomorphism.html#9828" class="Bound">y</a> <a id="9830" class="Symbol">→</a>
        <a id="9840" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
          <a id="9856" class="Symbol">(</a><a id="9857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5464" class="Field">to</a> <a id="9860" href="plfa.Isomorphism.html#9434" class="Bound">B≃C</a> <a id="9864" href="plfa.Isomorphism.html#2703" class="Function Operator">∘</a> <a id="9866" href="plfa.Isomorphism.html#5464" class="Field">to</a> <a id="9869" href="plfa.Isomorphism.html#9430" class="Bound">A≃B</a><a id="9872" class="Symbol">)</a> <a id="9874" class="Symbol">((</a><a id="9876" href="plfa.Isomorphism.html#5481" class="Field">from</a> <a id="9881" href="plfa.Isomorphism.html#9430" class="Bound">A≃B</a> <a id="9885" href="plfa.Isomorphism.html#2703" class="Function Operator">∘</a> <a id="9887" href="plfa.Isomorphism.html#5481" class="Field">from</a> <a id="9892" href="plfa.Isomorphism.html#9434" class="Bound">B≃C</a><a id="9895" class="Symbol">)</a> <a id="9897" href="plfa.Isomorphism.html#9828" class="Bound">y</a><a id="9898" class="Symbol">)</a>
        <a id="9908" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
          <a id="9922" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5464" class="Field">to</a> <a id="9925" href="plfa.Isomorphism.html#9434" class="Bound">B≃C</a> <a id="9929" class="Symbol">(</a><a id="9930" href="plfa.Isomorphism.html#5464" class="Field">to</a> <a id="9933" href="plfa.Isomorphism.html#9430" class="Bound">A≃B</a> <a id="9937" class="Symbol">(</a><a id="9938" href="plfa.Isomorphism.html#5481" class="Field">from</a> <a id="9943" href="plfa.Isomorphism.html#9430" class="Bound">A≃B</a> <a id="9947" class="Symbol">(</a><a id="9948" href="plfa.Isomorphism.html#5481" class="Field">from</a> <a id="9953" href="plfa.Isomorphism.html#9434" class="Bound">B≃C</a> <a id="9957" href="plfa.Isomorphism.html#9828" class="Bound">y</a><a id="9958" class="Symbol">)))</a>
        <a id="9970" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="9973" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="9978" class="Symbol">(</a><a id="9979" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5464" class="Field">to</a> <a id="9982" href="plfa.Isomorphism.html#9434" class="Bound">B≃C</a><a id="9985" class="Symbol">)</a> <a id="9987" class="Symbol">(</a><a id="9988" href="plfa.Isomorphism.html#5540" class="Field">to∘from</a> <a id="9996" href="plfa.Isomorphism.html#9430" class="Bound">A≃B</a> <a id="10000" class="Symbol">(</a><a id="10001" href="plfa.Isomorphism.html#5481" class="Field">from</a> <a id="10006" href="plfa.Isomorphism.html#9434" class="Bound">B≃C</a> <a id="10010" href="plfa.Isomorphism.html#9828" class="Bound">y</a><a id="10011" class="Symbol">))</a> <a id="10014" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="10026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5464" class="Field">to</a> <a id="10029" href="plfa.Isomorphism.html#9434" class="Bound">B≃C</a> <a id="10033" class="Symbol">(</a><a id="10034" href="plfa.Isomorphism.html#5481" class="Field">from</a> <a id="10039" href="plfa.Isomorphism.html#9434" class="Bound">B≃C</a> <a id="10043" href="plfa.Isomorphism.html#9828" class="Bound">y</a><a id="10044" class="Symbol">)</a>
        <a id="10054" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="10057" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5540" class="Field">to∘from</a> <a id="10065" href="plfa.Isomorphism.html#9434" class="Bound">B≃C</a> <a id="10069" href="plfa.Isomorphism.html#9828" class="Bound">y</a> <a id="10071" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="10083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9828" class="Bound">y</a>
        <a id="10093" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a><a id="10094" class="Symbol">}</a>
     <a id="10101" class="Symbol">}</a>
</pre>{% endraw %}

{::comment}
## Equational reasoning for isomorphism
{:/}

## 同构的相等性论证

{::comment}
It is straightforward to support a variant of equational reasoning for
isomorphism.  We essentially copy the previous definition
of equality for isomorphism.  We omit the form that corresponds to `_≡⟨⟩_`, since
trivial isomorphisms arise far less often than trivial equalities:
{:/}

我们可以直接的构造一种同构的相等性论证方法。我们对之前的相等性论证定义进行修改。
我们省略 `_≡⟨⟩_` 的定义，因为简单的同构比简单的相等性出现的少很多：

{% raw %}<pre class="Agda"><a id="10561" class="Keyword">module</a> <a id="≃-Reasoning"></a><a id="10568" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10568" class="Module">≃-Reasoning</a> <a id="10580" class="Keyword">where</a>

  <a id="10589" class="Keyword">infix</a>  <a id="10596" class="Number">1</a> <a id="10598" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10644" class="Function Operator">≃-begin_</a>
  <a id="10609" class="Keyword">infixr</a> <a id="10616" class="Number">2</a> <a id="10618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10728" class="Function Operator">_≃⟨_⟩_</a>
  <a id="10627" class="Keyword">infix</a>  <a id="10634" class="Number">3</a> <a id="10636" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10847" class="Function Operator">_≃-∎</a>

  <a id="≃-Reasoning.≃-begin_"></a><a id="10644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10644" class="Function Operator">≃-begin_</a> <a id="10653" class="Symbol">:</a> <a id="10655" class="Symbol">∀</a> <a id="10657" class="Symbol">{</a><a id="10658" href="plfa.Isomorphism.html#10658" class="Bound">A</a> <a id="10660" href="plfa.Isomorphism.html#10660" class="Bound">B</a> <a id="10662" class="Symbol">:</a> <a id="10664" class="PrimitiveType">Set</a><a id="10667" class="Symbol">}</a>
    <a id="10673" class="Symbol">→</a> <a id="10675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10658" class="Bound">A</a> <a id="10677" href="plfa.Isomorphism.html#5424" class="Record Operator">≃</a> <a id="10679" href="plfa.Isomorphism.html#10660" class="Bound">B</a>
      <a id="10687" class="Comment">-----</a>
    <a id="10697" class="Symbol">→</a> <a id="10699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10658" class="Bound">A</a> <a id="10701" href="plfa.Isomorphism.html#5424" class="Record Operator">≃</a> <a id="10703" href="plfa.Isomorphism.html#10660" class="Bound">B</a>
  <a id="10707" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10644" class="Function Operator">≃-begin</a> <a id="10715" href="plfa.Isomorphism.html#10715" class="Bound">A≃B</a> <a id="10719" class="Symbol">=</a> <a id="10721" href="plfa.Isomorphism.html#10715" class="Bound">A≃B</a>

  <a id="≃-Reasoning._≃⟨_⟩_"></a><a id="10728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10728" class="Function Operator">_≃⟨_⟩_</a> <a id="10735" class="Symbol">:</a> <a id="10737" class="Symbol">∀</a> <a id="10739" class="Symbol">(</a><a id="10740" href="plfa.Isomorphism.html#10740" class="Bound">A</a> <a id="10742" class="Symbol">:</a> <a id="10744" class="PrimitiveType">Set</a><a id="10747" class="Symbol">)</a> <a id="10749" class="Symbol">{</a><a id="10750" href="plfa.Isomorphism.html#10750" class="Bound">B</a> <a id="10752" href="plfa.Isomorphism.html#10752" class="Bound">C</a> <a id="10754" class="Symbol">:</a> <a id="10756" class="PrimitiveType">Set</a><a id="10759" class="Symbol">}</a>
    <a id="10765" class="Symbol">→</a> <a id="10767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10740" class="Bound">A</a> <a id="10769" href="plfa.Isomorphism.html#5424" class="Record Operator">≃</a> <a id="10771" href="plfa.Isomorphism.html#10750" class="Bound">B</a>
    <a id="10777" class="Symbol">→</a> <a id="10779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10750" class="Bound">B</a> <a id="10781" href="plfa.Isomorphism.html#5424" class="Record Operator">≃</a> <a id="10783" href="plfa.Isomorphism.html#10752" class="Bound">C</a>
      <a id="10791" class="Comment">-----</a>
    <a id="10801" class="Symbol">→</a> <a id="10803" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10740" class="Bound">A</a> <a id="10805" href="plfa.Isomorphism.html#5424" class="Record Operator">≃</a> <a id="10807" href="plfa.Isomorphism.html#10752" class="Bound">C</a>
  <a id="10811" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10811" class="Bound">A</a> <a id="10813" href="plfa.Isomorphism.html#10728" class="Function Operator">≃⟨</a> <a id="10816" href="plfa.Isomorphism.html#10816" class="Bound">A≃B</a> <a id="10820" href="plfa.Isomorphism.html#10728" class="Function Operator">⟩</a> <a id="10822" href="plfa.Isomorphism.html#10822" class="Bound">B≃C</a> <a id="10826" class="Symbol">=</a> <a id="10828" href="plfa.Isomorphism.html#9356" class="Function">≃-trans</a> <a id="10836" href="plfa.Isomorphism.html#10816" class="Bound">A≃B</a> <a id="10840" href="plfa.Isomorphism.html#10822" class="Bound">B≃C</a>

  <a id="≃-Reasoning._≃-∎"></a><a id="10847" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10847" class="Function Operator">_≃-∎</a> <a id="10852" class="Symbol">:</a> <a id="10854" class="Symbol">∀</a> <a id="10856" class="Symbol">(</a><a id="10857" href="plfa.Isomorphism.html#10857" class="Bound">A</a> <a id="10859" class="Symbol">:</a> <a id="10861" class="PrimitiveType">Set</a><a id="10864" class="Symbol">)</a>
      <a id="10872" class="Comment">-----</a>
    <a id="10882" class="Symbol">→</a> <a id="10884" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10857" class="Bound">A</a> <a id="10886" href="plfa.Isomorphism.html#5424" class="Record Operator">≃</a> <a id="10888" href="plfa.Isomorphism.html#10857" class="Bound">A</a>
  <a id="10892" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10892" class="Bound">A</a> <a id="10894" href="plfa.Isomorphism.html#10847" class="Function Operator">≃-∎</a> <a id="10898" class="Symbol">=</a> <a id="10900" href="plfa.Isomorphism.html#8136" class="Function">≃-refl</a>

<a id="10908" class="Keyword">open</a> <a id="10913" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#10568" class="Module">≃-Reasoning</a>
</pre>{% endraw %}

{::comment}
## Embedding
{:/}

## 嵌入（Embedding）

{::comment}
We also need the notion of _embedding_, which is a weakening of
isomorphism.  While an isomorphism shows that two types are in
one-to-one correspondence, an embedding shows that the first type is
included in the second; or, equivalently, that there is a many-to-one
correspondence between the second type and the first.
{:/}

我们同时也需要*嵌入*的概念，它是同构的弱化概念。同构要求证明两个类型之间的一一对应，
而嵌入只需要第一种类型涵盖在第二种类型内，所以两个类型之间有一对多的对应关系。

{::comment}
Here is the formal definition of embedding:
{:/}

嵌入的正式定义如下：

{% raw %}<pre class="Agda"><a id="11481" class="Keyword">infix</a> <a id="11487" class="Number">0</a> <a id="11489" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11500" class="Record Operator">_≲_</a>
<a id="11493" class="Keyword">record</a> <a id="_≲_"></a><a id="11500" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11500" class="Record Operator">_≲_</a> <a id="11504" class="Symbol">(</a><a id="11505" href="plfa.Isomorphism.html#11505" class="Bound">A</a> <a id="11507" href="plfa.Isomorphism.html#11507" class="Bound">B</a> <a id="11509" class="Symbol">:</a> <a id="11511" class="PrimitiveType">Set</a><a id="11514" class="Symbol">)</a> <a id="11516" class="Symbol">:</a> <a id="11518" class="PrimitiveType">Set</a> <a id="11522" class="Keyword">where</a>
  <a id="11530" class="Keyword">field</a>
    <a id="_≲_.to"></a><a id="11540" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11540" class="Field">to</a>      <a id="11548" class="Symbol">:</a> <a id="11550" href="plfa.Isomorphism.html#11505" class="Bound">A</a> <a id="11552" class="Symbol">→</a> <a id="11554" href="plfa.Isomorphism.html#11507" class="Bound">B</a>
    <a id="_≲_.from"></a><a id="11560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11560" class="Field">from</a>    <a id="11568" class="Symbol">:</a> <a id="11570" href="plfa.Isomorphism.html#11507" class="Bound">B</a> <a id="11572" class="Symbol">→</a> <a id="11574" href="plfa.Isomorphism.html#11505" class="Bound">A</a>
    <a id="_≲_.from∘to"></a><a id="11580" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11580" class="Field">from∘to</a> <a id="11588" class="Symbol">:</a> <a id="11590" class="Symbol">∀</a> <a id="11592" class="Symbol">(</a><a id="11593" href="plfa.Isomorphism.html#11593" class="Bound">x</a> <a id="11595" class="Symbol">:</a> <a id="11597" href="plfa.Isomorphism.html#11505" class="Bound">A</a><a id="11598" class="Symbol">)</a> <a id="11600" class="Symbol">→</a> <a id="11602" class="Field">from</a> <a id="11607" class="Symbol">(</a><a id="11608" class="Field">to</a> <a id="11611" href="plfa.Isomorphism.html#11593" class="Bound">x</a><a id="11612" class="Symbol">)</a> <a id="11614" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11616" href="plfa.Isomorphism.html#11593" class="Bound">x</a>
<a id="11618" class="Keyword">open</a> <a id="11623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11500" class="Module Operator">_≲_</a>
</pre>{% endraw %}
{::comment}
It is the same as an isomorphism, save that it lacks the `to∘from` field.
Hence, we know that `from` is left-inverse to `to`, but not that `from`
is right-inverse to `to`.
{:/}

除了它缺少了 `to∘from` 字段以外，嵌入的定义和同构是一样的。因此，我们可以得知 `from` 是 `to`
的左逆，但是 `from` 不是 `to` 的右逆。

{::comment}
Embedding is reflexive and transitive, but not symmetric.  The proofs
are cut down versions of the similar proofs for isomorphism:
{:/}

嵌入是自反和传递的，但不是对称的。证明与同构类似，不过去除了不需要的部分：

{% raw %}<pre class="Agda"><a id="≲-refl"></a><a id="12101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12101" class="Function">≲-refl</a> <a id="12108" class="Symbol">:</a> <a id="12110" class="Symbol">∀</a> <a id="12112" class="Symbol">{</a><a id="12113" href="plfa.Isomorphism.html#12113" class="Bound">A</a> <a id="12115" class="Symbol">:</a> <a id="12117" class="PrimitiveType">Set</a><a id="12120" class="Symbol">}</a> <a id="12122" class="Symbol">→</a> <a id="12124" href="plfa.Isomorphism.html#12113" class="Bound">A</a> <a id="12126" href="plfa.Isomorphism.html#11500" class="Record Operator">≲</a> <a id="12128" href="plfa.Isomorphism.html#12113" class="Bound">A</a>
<a id="12130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12101" class="Function">≲-refl</a> <a id="12137" class="Symbol">=</a>
  <a id="12141" class="Keyword">record</a>
    <a id="12152" class="Symbol">{</a> <a id="12154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11540" class="Field">to</a>      <a id="12162" class="Symbol">=</a> <a id="12164" class="Symbol">λ{</a><a id="12166" href="plfa.Isomorphism.html#12166" class="Bound">x</a> <a id="12168" class="Symbol">→</a> <a id="12170" href="plfa.Isomorphism.html#12166" class="Bound">x</a><a id="12171" class="Symbol">}</a>
    <a id="12177" class="Symbol">;</a> <a id="12179" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11560" class="Field">from</a>    <a id="12187" class="Symbol">=</a> <a id="12189" class="Symbol">λ{</a><a id="12191" href="plfa.Isomorphism.html#12191" class="Bound">y</a> <a id="12193" class="Symbol">→</a> <a id="12195" href="plfa.Isomorphism.html#12191" class="Bound">y</a><a id="12196" class="Symbol">}</a>
    <a id="12202" class="Symbol">;</a> <a id="12204" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11580" class="Field">from∘to</a> <a id="12212" class="Symbol">=</a> <a id="12214" class="Symbol">λ{</a><a id="12216" href="plfa.Isomorphism.html#12216" class="Bound">x</a> <a id="12218" class="Symbol">→</a> <a id="12220" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="12224" class="Symbol">}</a>
    <a id="12230" class="Symbol">}</a>

<a id="≲-trans"></a><a id="12233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12233" class="Function">≲-trans</a> <a id="12241" class="Symbol">:</a> <a id="12243" class="Symbol">∀</a> <a id="12245" class="Symbol">{</a><a id="12246" href="plfa.Isomorphism.html#12246" class="Bound">A</a> <a id="12248" href="plfa.Isomorphism.html#12248" class="Bound">B</a> <a id="12250" href="plfa.Isomorphism.html#12250" class="Bound">C</a> <a id="12252" class="Symbol">:</a> <a id="12254" class="PrimitiveType">Set</a><a id="12257" class="Symbol">}</a> <a id="12259" class="Symbol">→</a> <a id="12261" href="plfa.Isomorphism.html#12246" class="Bound">A</a> <a id="12263" href="plfa.Isomorphism.html#11500" class="Record Operator">≲</a> <a id="12265" href="plfa.Isomorphism.html#12248" class="Bound">B</a> <a id="12267" class="Symbol">→</a> <a id="12269" href="plfa.Isomorphism.html#12248" class="Bound">B</a> <a id="12271" href="plfa.Isomorphism.html#11500" class="Record Operator">≲</a> <a id="12273" href="plfa.Isomorphism.html#12250" class="Bound">C</a> <a id="12275" class="Symbol">→</a> <a id="12277" href="plfa.Isomorphism.html#12246" class="Bound">A</a> <a id="12279" href="plfa.Isomorphism.html#11500" class="Record Operator">≲</a> <a id="12281" href="plfa.Isomorphism.html#12250" class="Bound">C</a>
<a id="12283" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12233" class="Function">≲-trans</a> <a id="12291" href="plfa.Isomorphism.html#12291" class="Bound">A≲B</a> <a id="12295" href="plfa.Isomorphism.html#12295" class="Bound">B≲C</a> <a id="12299" class="Symbol">=</a>
  <a id="12303" class="Keyword">record</a>
    <a id="12314" class="Symbol">{</a> <a id="12316" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11540" class="Field">to</a>      <a id="12324" class="Symbol">=</a> <a id="12326" class="Symbol">λ{</a><a id="12328" href="plfa.Isomorphism.html#12328" class="Bound">x</a> <a id="12330" class="Symbol">→</a> <a id="12332" href="plfa.Isomorphism.html#11540" class="Field">to</a>   <a id="12337" href="plfa.Isomorphism.html#12295" class="Bound">B≲C</a> <a id="12341" class="Symbol">(</a><a id="12342" href="plfa.Isomorphism.html#11540" class="Field">to</a>   <a id="12347" href="plfa.Isomorphism.html#12291" class="Bound">A≲B</a> <a id="12351" href="plfa.Isomorphism.html#12328" class="Bound">x</a><a id="12352" class="Symbol">)}</a>
    <a id="12359" class="Symbol">;</a> <a id="12361" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11560" class="Field">from</a>    <a id="12369" class="Symbol">=</a> <a id="12371" class="Symbol">λ{</a><a id="12373" href="plfa.Isomorphism.html#12373" class="Bound">y</a> <a id="12375" class="Symbol">→</a> <a id="12377" href="plfa.Isomorphism.html#11560" class="Field">from</a> <a id="12382" href="plfa.Isomorphism.html#12291" class="Bound">A≲B</a> <a id="12386" class="Symbol">(</a><a id="12387" href="plfa.Isomorphism.html#11560" class="Field">from</a> <a id="12392" href="plfa.Isomorphism.html#12295" class="Bound">B≲C</a> <a id="12396" href="plfa.Isomorphism.html#12373" class="Bound">y</a><a id="12397" class="Symbol">)}</a>
    <a id="12404" class="Symbol">;</a> <a id="12406" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11580" class="Field">from∘to</a> <a id="12414" class="Symbol">=</a> <a id="12416" class="Symbol">λ{</a><a id="12418" href="plfa.Isomorphism.html#12418" class="Bound">x</a> <a id="12420" class="Symbol">→</a>
        <a id="12430" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
          <a id="12446" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11560" class="Field">from</a> <a id="12451" href="plfa.Isomorphism.html#12291" class="Bound">A≲B</a> <a id="12455" class="Symbol">(</a><a id="12456" href="plfa.Isomorphism.html#11560" class="Field">from</a> <a id="12461" href="plfa.Isomorphism.html#12295" class="Bound">B≲C</a> <a id="12465" class="Symbol">(</a><a id="12466" href="plfa.Isomorphism.html#11540" class="Field">to</a> <a id="12469" href="plfa.Isomorphism.html#12295" class="Bound">B≲C</a> <a id="12473" class="Symbol">(</a><a id="12474" href="plfa.Isomorphism.html#11540" class="Field">to</a> <a id="12477" href="plfa.Isomorphism.html#12291" class="Bound">A≲B</a> <a id="12481" href="plfa.Isomorphism.html#12418" class="Bound">x</a><a id="12482" class="Symbol">)))</a>
        <a id="12494" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="12497" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="12502" class="Symbol">(</a><a id="12503" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11560" class="Field">from</a> <a id="12508" href="plfa.Isomorphism.html#12291" class="Bound">A≲B</a><a id="12511" class="Symbol">)</a> <a id="12513" class="Symbol">(</a><a id="12514" href="plfa.Isomorphism.html#11580" class="Field">from∘to</a> <a id="12522" href="plfa.Isomorphism.html#12295" class="Bound">B≲C</a> <a id="12526" class="Symbol">(</a><a id="12527" href="plfa.Isomorphism.html#11540" class="Field">to</a> <a id="12530" href="plfa.Isomorphism.html#12291" class="Bound">A≲B</a> <a id="12534" href="plfa.Isomorphism.html#12418" class="Bound">x</a><a id="12535" class="Symbol">))</a> <a id="12538" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="12550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11560" class="Field">from</a> <a id="12555" href="plfa.Isomorphism.html#12291" class="Bound">A≲B</a> <a id="12559" class="Symbol">(</a><a id="12560" href="plfa.Isomorphism.html#11540" class="Field">to</a> <a id="12563" href="plfa.Isomorphism.html#12291" class="Bound">A≲B</a> <a id="12567" href="plfa.Isomorphism.html#12418" class="Bound">x</a><a id="12568" class="Symbol">)</a>
        <a id="12578" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="12581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11580" class="Field">from∘to</a> <a id="12589" href="plfa.Isomorphism.html#12291" class="Bound">A≲B</a> <a id="12593" href="plfa.Isomorphism.html#12418" class="Bound">x</a> <a id="12595" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="12607" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12418" class="Bound">x</a>
        <a id="12617" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a><a id="12618" class="Symbol">}</a>
     <a id="12625" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
It is also easy to see that if two types embed in each other, and the
embedding functions correspond, then they are isomorphic.  This is a
weak form of anti-symmetry:
{:/}

显而易见的是，如果两个类型相互嵌入，且其嵌入函数相互对应，那么它们是同构的。
这个一种反对称性的弱化形式：

{% raw %}<pre class="Agda"><a id="≲-antisym"></a><a id="12876" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12876" class="Function">≲-antisym</a> <a id="12886" class="Symbol">:</a> <a id="12888" class="Symbol">∀</a> <a id="12890" class="Symbol">{</a><a id="12891" href="plfa.Isomorphism.html#12891" class="Bound">A</a> <a id="12893" href="plfa.Isomorphism.html#12893" class="Bound">B</a> <a id="12895" class="Symbol">:</a> <a id="12897" class="PrimitiveType">Set</a><a id="12900" class="Symbol">}</a>
  <a id="12904" class="Symbol">→</a> <a id="12906" class="Symbol">(</a><a id="12907" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12907" class="Bound">A≲B</a> <a id="12911" class="Symbol">:</a> <a id="12913" href="plfa.Isomorphism.html#12891" class="Bound">A</a> <a id="12915" href="plfa.Isomorphism.html#11500" class="Record Operator">≲</a> <a id="12917" href="plfa.Isomorphism.html#12893" class="Bound">B</a><a id="12918" class="Symbol">)</a>
  <a id="12922" class="Symbol">→</a> <a id="12924" class="Symbol">(</a><a id="12925" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12925" class="Bound">B≲A</a> <a id="12929" class="Symbol">:</a> <a id="12931" href="plfa.Isomorphism.html#12893" class="Bound">B</a> <a id="12933" href="plfa.Isomorphism.html#11500" class="Record Operator">≲</a> <a id="12935" href="plfa.Isomorphism.html#12891" class="Bound">A</a><a id="12936" class="Symbol">)</a>
  <a id="12940" class="Symbol">→</a> <a id="12942" class="Symbol">(</a><a id="12943" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11540" class="Field">to</a> <a id="12946" href="plfa.Isomorphism.html#12907" class="Bound">A≲B</a> <a id="12950" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="12952" href="plfa.Isomorphism.html#11560" class="Field">from</a> <a id="12957" href="plfa.Isomorphism.html#12925" class="Bound">B≲A</a><a id="12960" class="Symbol">)</a>
  <a id="12964" class="Symbol">→</a> <a id="12966" class="Symbol">(</a><a id="12967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11560" class="Field">from</a> <a id="12972" href="plfa.Isomorphism.html#12907" class="Bound">A≲B</a> <a id="12976" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="12978" href="plfa.Isomorphism.html#11540" class="Field">to</a> <a id="12981" href="plfa.Isomorphism.html#12925" class="Bound">B≲A</a><a id="12984" class="Symbol">)</a>
    <a id="12990" class="Comment">-------------------</a>
  <a id="13012" class="Symbol">→</a> <a id="13014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12891" class="Bound">A</a> <a id="13016" href="plfa.Isomorphism.html#5424" class="Record Operator">≃</a> <a id="13018" href="plfa.Isomorphism.html#12893" class="Bound">B</a>
<a id="13020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#12876" class="Function">≲-antisym</a> <a id="13030" href="plfa.Isomorphism.html#13030" class="Bound">A≲B</a> <a id="13034" href="plfa.Isomorphism.html#13034" class="Bound">B≲A</a> <a id="13038" href="plfa.Isomorphism.html#13038" class="Bound">to≡from</a> <a id="13046" href="plfa.Isomorphism.html#13046" class="Bound">from≡to</a> <a id="13054" class="Symbol">=</a>
  <a id="13058" class="Keyword">record</a>
    <a id="13069" class="Symbol">{</a> <a id="13071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5464" class="Field">to</a>      <a id="13079" class="Symbol">=</a> <a id="13081" href="plfa.Isomorphism.html#11540" class="Field">to</a> <a id="13084" href="plfa.Isomorphism.html#13030" class="Bound">A≲B</a>
    <a id="13092" class="Symbol">;</a> <a id="13094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5481" class="Field">from</a>    <a id="13102" class="Symbol">=</a> <a id="13104" href="plfa.Isomorphism.html#11560" class="Field">from</a> <a id="13109" href="plfa.Isomorphism.html#13030" class="Bound">A≲B</a>
    <a id="13117" class="Symbol">;</a> <a id="13119" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5498" class="Field">from∘to</a> <a id="13127" class="Symbol">=</a> <a id="13129" href="plfa.Isomorphism.html#11580" class="Field">from∘to</a> <a id="13137" href="plfa.Isomorphism.html#13030" class="Bound">A≲B</a>
    <a id="13145" class="Symbol">;</a> <a id="13147" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#5540" class="Field">to∘from</a> <a id="13155" class="Symbol">=</a> <a id="13157" class="Symbol">λ{</a><a id="13159" href="plfa.Isomorphism.html#13159" class="Bound">y</a> <a id="13161" class="Symbol">→</a>
        <a id="13171" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
          <a id="13187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11540" class="Field">to</a> <a id="13190" href="plfa.Isomorphism.html#13030" class="Bound">A≲B</a> <a id="13194" class="Symbol">(</a><a id="13195" href="plfa.Isomorphism.html#11560" class="Field">from</a> <a id="13200" href="plfa.Isomorphism.html#13030" class="Bound">A≲B</a> <a id="13204" href="plfa.Isomorphism.html#13159" class="Bound">y</a><a id="13205" class="Symbol">)</a>
        <a id="13215" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="13218" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="13223" class="Symbol">(</a><a id="13224" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11540" class="Field">to</a> <a id="13227" href="plfa.Isomorphism.html#13030" class="Bound">A≲B</a><a id="13230" class="Symbol">)</a> <a id="13232" class="Symbol">(</a><a id="13233" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html#1308" class="Function">cong-app</a> <a id="13242" href="plfa.Isomorphism.html#13046" class="Bound">from≡to</a> <a id="13250" href="plfa.Isomorphism.html#13159" class="Bound">y</a><a id="13251" class="Symbol">)</a> <a id="13253" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="13265" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11540" class="Field">to</a> <a id="13268" href="plfa.Isomorphism.html#13030" class="Bound">A≲B</a> <a id="13272" class="Symbol">(</a><a id="13273" href="plfa.Isomorphism.html#11540" class="Field">to</a> <a id="13276" href="plfa.Isomorphism.html#13034" class="Bound">B≲A</a> <a id="13280" href="plfa.Isomorphism.html#13159" class="Bound">y</a><a id="13281" class="Symbol">)</a>
        <a id="13291" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="13294" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html#1308" class="Function">cong-app</a> <a id="13303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13038" class="Bound">to≡from</a> <a id="13311" class="Symbol">(</a><a id="13312" href="plfa.Isomorphism.html#11540" class="Field">to</a> <a id="13315" href="plfa.Isomorphism.html#13034" class="Bound">B≲A</a> <a id="13319" href="plfa.Isomorphism.html#13159" class="Bound">y</a><a id="13320" class="Symbol">)</a> <a id="13322" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="13334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11560" class="Field">from</a> <a id="13339" href="plfa.Isomorphism.html#13034" class="Bound">B≲A</a> <a id="13343" class="Symbol">(</a><a id="13344" href="plfa.Isomorphism.html#11540" class="Field">to</a> <a id="13347" href="plfa.Isomorphism.html#13034" class="Bound">B≲A</a> <a id="13351" href="plfa.Isomorphism.html#13159" class="Bound">y</a><a id="13352" class="Symbol">)</a>
        <a id="13362" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="13365" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#11580" class="Field">from∘to</a> <a id="13373" href="plfa.Isomorphism.html#13034" class="Bound">B≲A</a> <a id="13377" href="plfa.Isomorphism.html#13159" class="Bound">y</a> <a id="13379" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
          <a id="13391" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13159" class="Bound">y</a>
        <a id="13401" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a><a id="13402" class="Symbol">}</a>
    <a id="13408" class="Symbol">}</a>
</pre>{% endraw %}
{::comment}
The first three components are copied from the embedding, while the
last combines the left inverse of `B ≲ A` with the equivalences of
the `to` and `from` components from the two embeddings to obtain
the right inverse of the isomorphism.
{:/}

前三部分可以直接从嵌入中得来，最后一部分我们可以把 `B ≲ A` 中的左逆和
两个嵌入中的 `to` 与 `from` 部分的相等性来获得同构中的右逆。


{::comment}
## Equational reasoning for embedding
{:/}

## 嵌入的相等性论证

{::comment}
We can also support tabular reasoning for embedding,
analogous to that used for isomorphism:
{:/}

和同构类似，我们亦支持嵌入的相等性论证：

{% raw %}<pre class="Agda"><a id="13957" class="Keyword">module</a> <a id="≲-Reasoning"></a><a id="13964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13964" class="Module">≲-Reasoning</a> <a id="13976" class="Keyword">where</a>

  <a id="13985" class="Keyword">infix</a>  <a id="13992" class="Number">1</a> <a id="13994" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14040" class="Function Operator">≲-begin_</a>
  <a id="14005" class="Keyword">infixr</a> <a id="14012" class="Number">2</a> <a id="14014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14124" class="Function Operator">_≲⟨_⟩_</a>
  <a id="14023" class="Keyword">infix</a>  <a id="14030" class="Number">3</a> <a id="14032" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14243" class="Function Operator">_≲-∎</a>

  <a id="≲-Reasoning.≲-begin_"></a><a id="14040" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14040" class="Function Operator">≲-begin_</a> <a id="14049" class="Symbol">:</a> <a id="14051" class="Symbol">∀</a> <a id="14053" class="Symbol">{</a><a id="14054" href="plfa.Isomorphism.html#14054" class="Bound">A</a> <a id="14056" href="plfa.Isomorphism.html#14056" class="Bound">B</a> <a id="14058" class="Symbol">:</a> <a id="14060" class="PrimitiveType">Set</a><a id="14063" class="Symbol">}</a>
    <a id="14069" class="Symbol">→</a> <a id="14071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14054" class="Bound">A</a> <a id="14073" href="plfa.Isomorphism.html#11500" class="Record Operator">≲</a> <a id="14075" href="plfa.Isomorphism.html#14056" class="Bound">B</a>
      <a id="14083" class="Comment">-----</a>
    <a id="14093" class="Symbol">→</a> <a id="14095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14054" class="Bound">A</a> <a id="14097" href="plfa.Isomorphism.html#11500" class="Record Operator">≲</a> <a id="14099" href="plfa.Isomorphism.html#14056" class="Bound">B</a>
  <a id="14103" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14040" class="Function Operator">≲-begin</a> <a id="14111" href="plfa.Isomorphism.html#14111" class="Bound">A≲B</a> <a id="14115" class="Symbol">=</a> <a id="14117" href="plfa.Isomorphism.html#14111" class="Bound">A≲B</a>

  <a id="≲-Reasoning._≲⟨_⟩_"></a><a id="14124" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14124" class="Function Operator">_≲⟨_⟩_</a> <a id="14131" class="Symbol">:</a> <a id="14133" class="Symbol">∀</a> <a id="14135" class="Symbol">(</a><a id="14136" href="plfa.Isomorphism.html#14136" class="Bound">A</a> <a id="14138" class="Symbol">:</a> <a id="14140" class="PrimitiveType">Set</a><a id="14143" class="Symbol">)</a> <a id="14145" class="Symbol">{</a><a id="14146" href="plfa.Isomorphism.html#14146" class="Bound">B</a> <a id="14148" href="plfa.Isomorphism.html#14148" class="Bound">C</a> <a id="14150" class="Symbol">:</a> <a id="14152" class="PrimitiveType">Set</a><a id="14155" class="Symbol">}</a>
    <a id="14161" class="Symbol">→</a> <a id="14163" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14136" class="Bound">A</a> <a id="14165" href="plfa.Isomorphism.html#11500" class="Record Operator">≲</a> <a id="14167" href="plfa.Isomorphism.html#14146" class="Bound">B</a>
    <a id="14173" class="Symbol">→</a> <a id="14175" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14146" class="Bound">B</a> <a id="14177" href="plfa.Isomorphism.html#11500" class="Record Operator">≲</a> <a id="14179" href="plfa.Isomorphism.html#14148" class="Bound">C</a>
      <a id="14187" class="Comment">-----</a>
    <a id="14197" class="Symbol">→</a> <a id="14199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14136" class="Bound">A</a> <a id="14201" href="plfa.Isomorphism.html#11500" class="Record Operator">≲</a> <a id="14203" href="plfa.Isomorphism.html#14148" class="Bound">C</a>
  <a id="14207" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14207" class="Bound">A</a> <a id="14209" href="plfa.Isomorphism.html#14124" class="Function Operator">≲⟨</a> <a id="14212" href="plfa.Isomorphism.html#14212" class="Bound">A≲B</a> <a id="14216" href="plfa.Isomorphism.html#14124" class="Function Operator">⟩</a> <a id="14218" href="plfa.Isomorphism.html#14218" class="Bound">B≲C</a> <a id="14222" class="Symbol">=</a> <a id="14224" href="plfa.Isomorphism.html#12233" class="Function">≲-trans</a> <a id="14232" href="plfa.Isomorphism.html#14212" class="Bound">A≲B</a> <a id="14236" href="plfa.Isomorphism.html#14218" class="Bound">B≲C</a>

  <a id="≲-Reasoning._≲-∎"></a><a id="14243" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14243" class="Function Operator">_≲-∎</a> <a id="14248" class="Symbol">:</a> <a id="14250" class="Symbol">∀</a> <a id="14252" class="Symbol">(</a><a id="14253" href="plfa.Isomorphism.html#14253" class="Bound">A</a> <a id="14255" class="Symbol">:</a> <a id="14257" class="PrimitiveType">Set</a><a id="14260" class="Symbol">)</a>
      <a id="14268" class="Comment">-----</a>
    <a id="14278" class="Symbol">→</a> <a id="14280" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14253" class="Bound">A</a> <a id="14282" href="plfa.Isomorphism.html#11500" class="Record Operator">≲</a> <a id="14284" href="plfa.Isomorphism.html#14253" class="Bound">A</a>
  <a id="14288" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14288" class="Bound">A</a> <a id="14290" href="plfa.Isomorphism.html#14243" class="Function Operator">≲-∎</a> <a id="14294" class="Symbol">=</a> <a id="14296" href="plfa.Isomorphism.html#12101" class="Function">≲-refl</a>

<a id="14304" class="Keyword">open</a> <a id="14309" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#13964" class="Module">≲-Reasoning</a>
</pre>{% endraw %}
{::comment}
#### Exercise `≃-implies-≲`
{:/}

#### 练习 `≃-implies-≲`

{::comment}
Show that every isomorphism implies an embedding.
{:/}

证明每个同构蕴涵了一个嵌入。

{% raw %}<pre class="Agda"><a id="14483" class="Keyword">postulate</a>
  <a id="≃-implies-≲"></a><a id="14495" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14495" class="Postulate">≃-implies-≲</a> <a id="14507" class="Symbol">:</a> <a id="14509" class="Symbol">∀</a> <a id="14511" class="Symbol">{</a><a id="14512" href="plfa.Isomorphism.html#14512" class="Bound">A</a> <a id="14514" href="plfa.Isomorphism.html#14514" class="Bound">B</a> <a id="14516" class="Symbol">:</a> <a id="14518" class="PrimitiveType">Set</a><a id="14521" class="Symbol">}</a>
    <a id="14527" class="Symbol">→</a> <a id="14529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14512" class="Bound">A</a> <a id="14531" href="plfa.Isomorphism.html#5424" class="Record Operator">≃</a> <a id="14533" href="plfa.Isomorphism.html#14514" class="Bound">B</a>
      <a id="14541" class="Comment">-----</a>
    <a id="14551" class="Symbol">→</a> <a id="14553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14512" class="Bound">A</a> <a id="14555" href="plfa.Isomorphism.html#11500" class="Record Operator">≲</a> <a id="14557" href="plfa.Isomorphism.html#14514" class="Bound">B</a>
</pre>{% endraw %}
{::comment}
{% raw %}<pre class="Agda"><a id="14580" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="14617" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `_⇔_` {#iff}
{:/}

#### 练习 `_⇔_` {#iff}

{::comment}
Define equivalence of propositions (also known as "if and only if") as follows:
{:/}

按下列形式定义命题的等价性（又名“当且仅当“）：

{% raw %}<pre class="Agda"><a id="14830" class="Keyword">record</a> <a id="_⇔_"></a><a id="14837" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14837" class="Record Operator">_⇔_</a> <a id="14841" class="Symbol">(</a><a id="14842" href="plfa.Isomorphism.html#14842" class="Bound">A</a> <a id="14844" href="plfa.Isomorphism.html#14844" class="Bound">B</a> <a id="14846" class="Symbol">:</a> <a id="14848" class="PrimitiveType">Set</a><a id="14851" class="Symbol">)</a> <a id="14853" class="Symbol">:</a> <a id="14855" class="PrimitiveType">Set</a> <a id="14859" class="Keyword">where</a>
  <a id="14867" class="Keyword">field</a>
    <a id="_⇔_.to"></a><a id="14877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14877" class="Field">to</a>   <a id="14882" class="Symbol">:</a> <a id="14884" href="plfa.Isomorphism.html#14842" class="Bound">A</a> <a id="14886" class="Symbol">→</a> <a id="14888" href="plfa.Isomorphism.html#14844" class="Bound">B</a>
    <a id="_⇔_.from"></a><a id="14894" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#14894" class="Field">from</a> <a id="14899" class="Symbol">:</a> <a id="14901" href="plfa.Isomorphism.html#14844" class="Bound">B</a> <a id="14903" class="Symbol">→</a> <a id="14905" href="plfa.Isomorphism.html#14842" class="Bound">A</a>
</pre>{% endraw %}
{::comment}
Show that equivalence is reflexive, symmetric, and transitive.
{:/}

证明等价性是自反、对称和传递的。

{::comment}
{% raw %}<pre class="Agda"><a id="15027" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="15064" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
#### Exercise `Bin-embedding` (stretch) {#Bin-embedding}
{:/}

#### 练习 `Bin-embedding` （延伸） {#Bin-embedding}

{::comment}
Recall that Exercises
[Bin][plfa.Naturals#Bin] and
[Bin-laws][plfa.Induction#Bin-laws]
define a datatype of bitstrings representing natural numbers:
{:/}

回忆练习 [Bin][plfa.Naturals#Bin] 和
[Bin-laws][plfa.Induction#Bin-laws] 中，
我们定义了一个数据类型来表示二进制比特串来表示自然数：

{% raw %}<pre class="Agda"><a id="15475" class="Keyword">data</a> <a id="Bin"></a><a id="15480" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15480" class="Datatype">Bin</a> <a id="15484" class="Symbol">:</a> <a id="15486" class="PrimitiveType">Set</a> <a id="15490" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="15498" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15498" class="InductiveConstructor">nil</a> <a id="15502" class="Symbol">:</a> <a id="15504" href="plfa.Isomorphism.html#15480" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="15510" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15510" class="InductiveConstructor Operator">x0_</a> <a id="15514" class="Symbol">:</a> <a id="15516" href="plfa.Isomorphism.html#15480" class="Datatype">Bin</a> <a id="15520" class="Symbol">→</a> <a id="15522" href="plfa.Isomorphism.html#15480" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="15528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#15528" class="InductiveConstructor Operator">x1_</a> <a id="15532" class="Symbol">:</a> <a id="15534" href="plfa.Isomorphism.html#15480" class="Datatype">Bin</a> <a id="15538" class="Symbol">→</a> <a id="15540" href="plfa.Isomorphism.html#15480" class="Datatype">Bin</a>
</pre>{% endraw %}
{::comment}
And ask you to define the following functions
{:/}

我们要求你来定义下列函数：

    to : ℕ → Bin
    from : Bin → ℕ

{::comment}
which satisfy the following property:
{:/}

其满足如下性质：

    from (to n) ≡ n

{::comment}
Using the above, establish that there is an embedding of `ℕ` into `Bin`.
{:/}

使用上述条件，证明存在一个从 `ℕ` 到 `Bin` 的嵌入。

{::comment}
{% raw %}<pre class="Agda"><a id="15892" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="15929" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
Why do `to` and `from` not form an isomorphism?
{:/}

为什么 `to` 和 `from` 不能构造一个同构？


{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

标准库中可以找到与本章节中相似的定义：

{% raw %}<pre class="Agda"><a id="16215" class="Keyword">import</a> <a id="16222" href="https://agda.github.io/agda-stdlib/v1.1/Function.html" class="Module">Function</a> <a id="16231" class="Keyword">using</a> <a id="16237" class="Symbol">(</a><a id="16238" href="https://agda.github.io/agda-stdlib/v1.1/Function.html#1099" class="Function Operator">_∘_</a><a id="16241" class="Symbol">)</a>
<a id="16243" class="Keyword">import</a> <a id="16250" href="https://agda.github.io/agda-stdlib/v1.1/Function.Inverse.html" class="Module">Function.Inverse</a> <a id="16267" class="Keyword">using</a> <a id="16273" class="Symbol">(</a><a id="16274" href="https://agda.github.io/agda-stdlib/v1.1/Function.Inverse.html#2229" class="Function Operator">_↔_</a><a id="16277" class="Symbol">)</a>
<a id="16279" class="Keyword">import</a> <a id="16286" href="https://agda.github.io/agda-stdlib/v1.1/Function.LeftInverse.html" class="Module">Function.LeftInverse</a> <a id="16307" class="Keyword">using</a> <a id="16313" class="Symbol">(</a><a id="16314" href="https://agda.github.io/agda-stdlib/v1.1/Function.LeftInverse.html#2682" class="Function Operator">_↞_</a><a id="16317" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
The standard library `_↔_` and `_↞_` correspond to our `_≃_` and
`_≲_`, respectively, but those in the standard library are less
convenient, since they depend on a nested record structure and are
parameterised with regard to an arbitrary notion of equivalence.
{:/}

标准库中的 `_↔_` 和 `_↞_` 分别对应了我们定义的 `_≃_` 和 `_≲_`，
但是标准库中的定义使用起来不如我们的定义方便，因为标准库中的定义依赖于一个嵌套的记录结构，
并可以由任何相等性的记法来参数化。


## Unicode

{::comment}
This chapter uses the following unicode:

    ∘  U+2218  RING OPERATOR (\o, \circ, \comp)
    λ  U+03BB  GREEK SMALL LETTER LAMBDA (\lambda, \Gl)
    ≃  U+2243  ASYMPTOTICALLY EQUAL TO (\~-)
    ≲  U+2272  LESS-THAN OR EQUIVALENT TO (\<~)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)
{:/}

本章节使用了如下 Unicode：

    ∘  U+2218  环运算符 (\o, \circ, \comp)
    λ  U+03BB  小写希腊字母 LAMBDA (\lambda, \Gl)
    ≃  U+2243  渐进相等 (\~-)
    ≲  U+2272  小于或等价于 (\<~)
    ⇔  U+21D4  左右双箭头 (\<=>)
