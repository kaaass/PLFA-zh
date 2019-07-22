---
src: ./src/plfa/Equality.lagda.md
title     : "Equality: 相等性与等式推理"
layout    : page
prev      : /Relations/
permalink : /Equality/
next      : /Isomorphism/
translators : ["Fangyi Zhou"]
progress  : 100
---

{% raw %}<pre class="Agda"><a id="183" class="Keyword">module</a> <a id="190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}" class="Module">plfa.Equality</a> <a id="204" class="Keyword">where</a>
</pre>{% endraw %}
{::comment}
Much of our reasoning has involved equality.  Given two terms `M`
and `N`, both of type `A`, we write `M ≡ N` to assert that `M` and `N`
are interchangeable.  So far we have treated equality as a primitive,
here we show how to define it as an inductive datatype.
{:/}

我们在论证的过程中经常会使用相等性。给定两个都为 `A` 类型的项 `M` 和 `N`，
我们用 `M ≡ N` 来表示 `M` 和 `N` 可以相互替换。在此之前，
我们将相等性作为一个基础运算，而现在我们来说明如果将其定义为一个归纳的数据类型。


{::comment}
## Imports
{:/}

## 导入

{::comment}
This chapter has no imports.  Every chapter in this book, and nearly
every module in the Agda standard library, imports equality.
Since we define equality here, any import would create a conflict.
{:/}

本章节没有导入的内容。本书的每一章节，以及 Agda 标准库的每个模块都导入了相等性。
我们在此定义相等性，导入其他内容将会产生冲突。


{::comment}
## Equality
{:/}

## 相等性

{::comment}
We declare equality as follows:
{:/}

我们如下定义相等性：

{% raw %}<pre class="Agda"><a id="1048" class="Keyword">data</a> <a id="_≡_"></a><a id="1053" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1053" class="Datatype Operator">_≡_</a> <a id="1057" class="Symbol">{</a><a id="1058" href="plfa.Equality.html#1058" class="Bound">A</a> <a id="1060" class="Symbol">:</a> <a id="1062" class="PrimitiveType">Set</a><a id="1065" class="Symbol">}</a> <a id="1067" class="Symbol">(</a><a id="1068" href="plfa.Equality.html#1068" class="Bound">x</a> <a id="1070" class="Symbol">:</a> <a id="1072" href="plfa.Equality.html#1058" class="Bound">A</a><a id="1073" class="Symbol">)</a> <a id="1075" class="Symbol">:</a> <a id="1077" href="plfa.Equality.html#1058" class="Bound">A</a> <a id="1079" class="Symbol">→</a> <a id="1081" class="PrimitiveType">Set</a> <a id="1085" class="Keyword">where</a>
  <a id="_≡_.refl"></a><a id="1093" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1093" class="InductiveConstructor">refl</a> <a id="1098" class="Symbol">:</a> <a id="1100" href="plfa.Equality.html#1068" class="Bound">x</a> <a id="1102" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="1104" href="plfa.Equality.html#1068" class="Bound">x</a>
</pre>{% endraw %}
{::comment}
In other words, for any type `A` and for any `x` of type `A`, the
constructor `refl` provides evidence that `x ≡ x`. Hence, every value
is equal to itself, and we have no other way of showing values
equal.  The definition features an asymmetry, in that the
first argument to `_≡_` is given by the parameter `x : A`, while the
second is given by an index in `A → Set`.  This follows our policy
of using parameters wherever possible.  The first argument to `_≡_`
can be a parameter because it doesn't vary, while the second must be
an index, so it can be required to be equal to the first.
{:/}

用其他的话来说，对于任意类型 `A` 和任意 `A` 类型的 `x`，构造器 `refl` 提供了
`x ≡ x` 的证明。所以，每个值等同于它本身，我们并没有其他办法来证明值的相等性。
这个定义里有不对称的地方，`_≡_` 的第一个参数（Argument）由 `x : A` 给出，
而第二个参数（Argument）则是由 `A → Set` 的索引给出。
这和我们尽可能多的使用参数（Parameter）的理念相符。`_≡_` 的第一个参数（Argument）
可以作为一个参数（Parameter），因为它不会变，而第二个参数（Argument）则必须是一个索引，
这样它才可以等用于第一个。

{::comment}
We declare the precedence of equality as follows:
{:/}

我们如下定义相等性的优先级：

{% raw %}<pre class="Agda"><a id="2106" class="Keyword">infix</a> <a id="2112" class="Number">4</a> <a id="2114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1053" class="Datatype Operator">_≡_</a>
</pre>{% endraw %}
{::comment}
We set the precedence of `_≡_` at level 4, the same as `_≤_`,
which means it binds less tightly than any arithmetic operator.
It associates neither to left nor right; writing `x ≡ y ≡ z`
is illegal.
{:/}

我们将 `_≡_` 的优先级设置为 4，与 `_≤_` 相同，所以其它算术运算符的结合都比它紧密。
由于它既不是左结合，也不是右结合的，因此 `x ≡ y ≡ z` 是不合法的。


{::comment}
## Equality is an equivalence relation
{:/}

## 相等性是一个等价关系（Equivalence Relation）

{::comment}
An equivalence relation is one which is reflexive, symmetric, and transitive.
Reflexivity is built-in to the definition of equality, via the
constructor `refl`.  It is straightforward to show symmetry:
{:/}

一个等价关系是自反、对称和传递的。其中自反性可以通过构造器 `refl` 直接从相等性的定义中得来。
我们可以直接地证明其对称性：

{% raw %}<pre class="Agda"><a id="sym"></a><a id="2817" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2817" class="Function">sym</a> <a id="2821" class="Symbol">:</a> <a id="2823" class="Symbol">∀</a> <a id="2825" class="Symbol">{</a><a id="2826" href="plfa.Equality.html#2826" class="Bound">A</a> <a id="2828" class="Symbol">:</a> <a id="2830" class="PrimitiveType">Set</a><a id="2833" class="Symbol">}</a> <a id="2835" class="Symbol">{</a><a id="2836" href="plfa.Equality.html#2836" class="Bound">x</a> <a id="2838" href="plfa.Equality.html#2838" class="Bound">y</a> <a id="2840" class="Symbol">:</a> <a id="2842" href="plfa.Equality.html#2826" class="Bound">A</a><a id="2843" class="Symbol">}</a>
  <a id="2847" class="Symbol">→</a> <a id="2849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2836" class="Bound">x</a> <a id="2851" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="2853" href="plfa.Equality.html#2838" class="Bound">y</a>
    <a id="2859" class="Comment">-----</a>
  <a id="2867" class="Symbol">→</a> <a id="2869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2838" class="Bound">y</a> <a id="2871" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="2873" href="plfa.Equality.html#2836" class="Bound">x</a>
<a id="2875" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2817" class="Function">sym</a> <a id="2879" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a> <a id="2884" class="Symbol">=</a> <a id="2886" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
How does this proof work? The argument to `sym` has type `x ≡ y`, but
on the left-hand side of the equation the argument has been
instantiated to the pattern `refl`, which requires that `x` and `y`
are the same.  Hence, for the right-hand side of the equation we need
a term of type `x ≡ x`, and `refl` will do.
{:/}

这个证明是怎么运作的呢？`sym` 参数的类型是 `x ≡ y`，但是等式的左手边被 `refl` 模式实例化了，
这要求 `x` 和 `y` 相等。因此，等式的右手边需要一个类型为 `x ≡ x` 的项，用 `refl` 即可。

{::comment}
It is instructive to develop `sym` interactively.  To start, we supply
a variable for the argument on the left, and a hole for the body on
the right:
{:/}

交互式地证明 `sym` 很有教育意义。首先，我们在左手边使用一个变量来表示参数，在右手边使用一个洞：

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym e = {! !}

{::comment}
If we go into the hole and type `C-c C-,` then Agda reports:
{:/}

如果我们进入这个洞，使用 `C-c C-,`，Agda 会告诉我们：

    Goal: .y ≡ .x
    ————————————————————————————————————————————————————————————
    e  : .x ≡ .y
    .y : .A
    .x : .A
    .A : Set

{::comment}
If in the hole we type `C-c C-c e` then Agda will instantiate `e` to
all possible constructors, with one equation for each. There is only
one possible constructor:
{:/}

在这个洞里，我们使用 `C-c C-c e`，Agda 会将 `e` 逐一展开为其所有可能的构造器。
此处只有一个构造器：

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = {! !}

{::comment}
If we go into the hole again and type `C-c C-,` then Agda now reports:
{:/}

如果我们再次进入这个洞，重新使用 `C-c C-,`，然后 Agda 现在会告诉我们：

     Goal: .x ≡ .x
     ————————————————————————————————————————————————————————————
     .x : .A
     .A : Set

{::comment}
This is the key step---Agda has worked out that `x` and `y` must be
the same to match the pattern `refl`!
{:/}

这是一个重要的步骤—— Agda 发现了 `x` 和 `y` 必须相等，才能与模式 `refl` 相匹配。

{::comment}
Finally, if we go back into the hole and type `C-c C-r` it will
instantiate the hole with the one constructor that yields a value of
the expected type:
{:/}

最后，我们回到洞里，使用 `C-c C-r`，Agda 将会把洞变成一个可以满足给定类型的构造器实例。

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = refl

{::comment}
This completes the definition as given above.
{:/}

我们至此完成了与之前给出证明相同的证明。

{::comment}
Transitivity is equally straightforward:
{:/}

传递性亦是很直接：

{% raw %}<pre class="Agda"><a id="trans"></a><a id="5155" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5155" class="Function">trans</a> <a id="5161" class="Symbol">:</a> <a id="5163" class="Symbol">∀</a> <a id="5165" class="Symbol">{</a><a id="5166" href="plfa.Equality.html#5166" class="Bound">A</a> <a id="5168" class="Symbol">:</a> <a id="5170" class="PrimitiveType">Set</a><a id="5173" class="Symbol">}</a> <a id="5175" class="Symbol">{</a><a id="5176" href="plfa.Equality.html#5176" class="Bound">x</a> <a id="5178" href="plfa.Equality.html#5178" class="Bound">y</a> <a id="5180" href="plfa.Equality.html#5180" class="Bound">z</a> <a id="5182" class="Symbol">:</a> <a id="5184" href="plfa.Equality.html#5166" class="Bound">A</a><a id="5185" class="Symbol">}</a>
  <a id="5189" class="Symbol">→</a> <a id="5191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5176" class="Bound">x</a> <a id="5193" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="5195" href="plfa.Equality.html#5178" class="Bound">y</a>
  <a id="5199" class="Symbol">→</a> <a id="5201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5178" class="Bound">y</a> <a id="5203" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="5205" href="plfa.Equality.html#5180" class="Bound">z</a>
    <a id="5211" class="Comment">-----</a>
  <a id="5219" class="Symbol">→</a> <a id="5221" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5176" class="Bound">x</a> <a id="5223" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="5225" href="plfa.Equality.html#5180" class="Bound">z</a>
<a id="5227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5155" class="Function">trans</a> <a id="5233" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a> <a id="5238" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>  <a id="5244" class="Symbol">=</a>  <a id="5247" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
Again, a useful exercise is to carry out an interactive development,
checking how Agda's knowledge changes as each of the two arguments is
instantiated.
{:/}

同样，交互式地证明这个特性是一个很好的练习，尤其是观察 Agda 的已知内容根据参数的实例而变化的过程。


{::comment}
## Congruence and substitution {#cong}
{:/}

## 合同性和替换性 {#cong}

{::comment}
Equality satisfies _congruence_.  If two terms are equal,
they remain so after the same function is applied to both:
{:/}

相等性满足 *合同性*（Congurence）。如果两个项相等，那么对它们使用相同的函数，
其结果仍然相等：

{% raw %}<pre class="Agda"><a id="cong"></a><a id="5755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5755" class="Function">cong</a> <a id="5760" class="Symbol">:</a> <a id="5762" class="Symbol">∀</a> <a id="5764" class="Symbol">{</a><a id="5765" href="plfa.Equality.html#5765" class="Bound">A</a> <a id="5767" href="plfa.Equality.html#5767" class="Bound">B</a> <a id="5769" class="Symbol">:</a> <a id="5771" class="PrimitiveType">Set</a><a id="5774" class="Symbol">}</a> <a id="5776" class="Symbol">(</a><a id="5777" href="plfa.Equality.html#5777" class="Bound">f</a> <a id="5779" class="Symbol">:</a> <a id="5781" href="plfa.Equality.html#5765" class="Bound">A</a> <a id="5783" class="Symbol">→</a> <a id="5785" href="plfa.Equality.html#5767" class="Bound">B</a><a id="5786" class="Symbol">)</a> <a id="5788" class="Symbol">{</a><a id="5789" href="plfa.Equality.html#5789" class="Bound">x</a> <a id="5791" href="plfa.Equality.html#5791" class="Bound">y</a> <a id="5793" class="Symbol">:</a> <a id="5795" href="plfa.Equality.html#5765" class="Bound">A</a><a id="5796" class="Symbol">}</a>
  <a id="5800" class="Symbol">→</a> <a id="5802" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5789" class="Bound">x</a> <a id="5804" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="5806" href="plfa.Equality.html#5791" class="Bound">y</a>
    <a id="5812" class="Comment">---------</a>
  <a id="5824" class="Symbol">→</a> <a id="5826" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5777" class="Bound">f</a> <a id="5828" href="plfa.Equality.html#5789" class="Bound">x</a> <a id="5830" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="5832" href="plfa.Equality.html#5777" class="Bound">f</a> <a id="5834" href="plfa.Equality.html#5791" class="Bound">y</a>
<a id="5836" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5755" class="Function">cong</a> <a id="5841" href="plfa.Equality.html#5841" class="Bound">f</a> <a id="5843" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>  <a id="5849" class="Symbol">=</a>  <a id="5852" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
Congruence of functions with two arguments is similar:
{:/}

两个参数的函数也满足合同性：

{% raw %}<pre class="Agda"><a id="cong₂"></a><a id="5955" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5955" class="Function">cong₂</a> <a id="5961" class="Symbol">:</a> <a id="5963" class="Symbol">∀</a> <a id="5965" class="Symbol">{</a><a id="5966" href="plfa.Equality.html#5966" class="Bound">A</a> <a id="5968" href="plfa.Equality.html#5968" class="Bound">B</a> <a id="5970" href="plfa.Equality.html#5970" class="Bound">C</a> <a id="5972" class="Symbol">:</a> <a id="5974" class="PrimitiveType">Set</a><a id="5977" class="Symbol">}</a> <a id="5979" class="Symbol">(</a><a id="5980" href="plfa.Equality.html#5980" class="Bound">f</a> <a id="5982" class="Symbol">:</a> <a id="5984" href="plfa.Equality.html#5966" class="Bound">A</a> <a id="5986" class="Symbol">→</a> <a id="5988" href="plfa.Equality.html#5968" class="Bound">B</a> <a id="5990" class="Symbol">→</a> <a id="5992" href="plfa.Equality.html#5970" class="Bound">C</a><a id="5993" class="Symbol">)</a> <a id="5995" class="Symbol">{</a><a id="5996" href="plfa.Equality.html#5996" class="Bound">u</a> <a id="5998" href="plfa.Equality.html#5998" class="Bound">x</a> <a id="6000" class="Symbol">:</a> <a id="6002" href="plfa.Equality.html#5966" class="Bound">A</a><a id="6003" class="Symbol">}</a> <a id="6005" class="Symbol">{</a><a id="6006" href="plfa.Equality.html#6006" class="Bound">v</a> <a id="6008" href="plfa.Equality.html#6008" class="Bound">y</a> <a id="6010" class="Symbol">:</a> <a id="6012" href="plfa.Equality.html#5968" class="Bound">B</a><a id="6013" class="Symbol">}</a>
  <a id="6017" class="Symbol">→</a> <a id="6019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5996" class="Bound">u</a> <a id="6021" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="6023" href="plfa.Equality.html#5998" class="Bound">x</a>
  <a id="6027" class="Symbol">→</a> <a id="6029" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6006" class="Bound">v</a> <a id="6031" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="6033" href="plfa.Equality.html#6008" class="Bound">y</a>
    <a id="6039" class="Comment">-------------</a>
  <a id="6055" class="Symbol">→</a> <a id="6057" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5980" class="Bound">f</a> <a id="6059" href="plfa.Equality.html#5996" class="Bound">u</a> <a id="6061" href="plfa.Equality.html#6006" class="Bound">v</a> <a id="6063" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="6065" href="plfa.Equality.html#5980" class="Bound">f</a> <a id="6067" href="plfa.Equality.html#5998" class="Bound">x</a> <a id="6069" href="plfa.Equality.html#6008" class="Bound">y</a>
<a id="6071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5955" class="Function">cong₂</a> <a id="6077" href="plfa.Equality.html#6077" class="Bound">f</a> <a id="6079" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a> <a id="6084" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>  <a id="6090" class="Symbol">=</a>  <a id="6093" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
Equality is also a congruence in the function position of an application.
If two functions are equal, then applying them to the same term
yields equal terms:
{:/}

在函数上的等价性也满足合同性。如果两个函数是相等的，那么它们作用在同一项上的结果是相等的：

{% raw %}<pre class="Agda"><a id="cong-app"></a><a id="6330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6330" class="Function">cong-app</a> <a id="6339" class="Symbol">:</a> <a id="6341" class="Symbol">∀</a> <a id="6343" class="Symbol">{</a><a id="6344" href="plfa.Equality.html#6344" class="Bound">A</a> <a id="6346" href="plfa.Equality.html#6346" class="Bound">B</a> <a id="6348" class="Symbol">:</a> <a id="6350" class="PrimitiveType">Set</a><a id="6353" class="Symbol">}</a> <a id="6355" class="Symbol">{</a><a id="6356" href="plfa.Equality.html#6356" class="Bound">f</a> <a id="6358" href="plfa.Equality.html#6358" class="Bound">g</a> <a id="6360" class="Symbol">:</a> <a id="6362" href="plfa.Equality.html#6344" class="Bound">A</a> <a id="6364" class="Symbol">→</a> <a id="6366" href="plfa.Equality.html#6346" class="Bound">B</a><a id="6367" class="Symbol">}</a>
  <a id="6371" class="Symbol">→</a> <a id="6373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6356" class="Bound">f</a> <a id="6375" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="6377" href="plfa.Equality.html#6358" class="Bound">g</a>
    <a id="6383" class="Comment">---------------------</a>
  <a id="6407" class="Symbol">→</a> <a id="6409" class="Symbol">∀</a> <a id="6411" class="Symbol">(</a><a id="6412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6412" class="Bound">x</a> <a id="6414" class="Symbol">:</a> <a id="6416" href="plfa.Equality.html#6344" class="Bound">A</a><a id="6417" class="Symbol">)</a> <a id="6419" class="Symbol">→</a> <a id="6421" href="plfa.Equality.html#6356" class="Bound">f</a> <a id="6423" href="plfa.Equality.html#6412" class="Bound">x</a> <a id="6425" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="6427" href="plfa.Equality.html#6358" class="Bound">g</a> <a id="6429" href="plfa.Equality.html#6412" class="Bound">x</a>
<a id="6431" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6330" class="Function">cong-app</a> <a id="6440" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a> <a id="6445" href="plfa.Equality.html#6445" class="Bound">x</a> <a id="6447" class="Symbol">=</a> <a id="6449" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
Equality also satisfies *substitution*.
If two values are equal and a predicate holds of the first then it also holds of the second:
{:/}

相等性也满足*替换性*（Substitution）。
如果两个值相等，其中一个满足某谓词，那么另一个也满足此谓词。

{% raw %}<pre class="Agda"><a id="subst"></a><a id="6673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6673" class="Function">subst</a> <a id="6679" class="Symbol">:</a> <a id="6681" class="Symbol">∀</a> <a id="6683" class="Symbol">{</a><a id="6684" href="plfa.Equality.html#6684" class="Bound">A</a> <a id="6686" class="Symbol">:</a> <a id="6688" class="PrimitiveType">Set</a><a id="6691" class="Symbol">}</a> <a id="6693" class="Symbol">{</a><a id="6694" href="plfa.Equality.html#6694" class="Bound">x</a> <a id="6696" href="plfa.Equality.html#6696" class="Bound">y</a> <a id="6698" class="Symbol">:</a> <a id="6700" href="plfa.Equality.html#6684" class="Bound">A</a><a id="6701" class="Symbol">}</a> <a id="6703" class="Symbol">(</a><a id="6704" href="plfa.Equality.html#6704" class="Bound">P</a> <a id="6706" class="Symbol">:</a> <a id="6708" href="plfa.Equality.html#6684" class="Bound">A</a> <a id="6710" class="Symbol">→</a> <a id="6712" class="PrimitiveType">Set</a><a id="6715" class="Symbol">)</a>
  <a id="6719" class="Symbol">→</a> <a id="6721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6694" class="Bound">x</a> <a id="6723" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="6725" href="plfa.Equality.html#6696" class="Bound">y</a>
    <a id="6731" class="Comment">---------</a>
  <a id="6743" class="Symbol">→</a> <a id="6745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6704" class="Bound">P</a> <a id="6747" href="plfa.Equality.html#6694" class="Bound">x</a> <a id="6749" class="Symbol">→</a> <a id="6751" href="plfa.Equality.html#6704" class="Bound">P</a> <a id="6753" href="plfa.Equality.html#6696" class="Bound">y</a>
<a id="6755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6673" class="Function">subst</a> <a id="6761" href="plfa.Equality.html#6761" class="Bound">P</a> <a id="6763" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a> <a id="6768" href="plfa.Equality.html#6768" class="Bound">px</a> <a id="6771" class="Symbol">=</a> <a id="6773" href="plfa.Equality.html#6768" class="Bound">px</a>
</pre>{% endraw %}

{::comment}
## Chains of equations
{:/}

## 等式串

{::comment}
Here we show how to support reasoning with chains of equations, as
used throughout the book.  We package the declarations into a module,
named `≡-Reasoning`, to match the format used in Agda's standard
library:
{:/}

我们在此演示如何使用等式串来论证，正如本书中使用证明形式。我们讲声明放在一个叫做
`≡-Reasoning` 的模块里，与 Agda 标准库中的格式相对应。

{% raw %}<pre class="Agda"><a id="7144" class="Keyword">module</a> <a id="≡-Reasoning"></a><a id="7151" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7151" class="Module">≡-Reasoning</a> <a id="7163" class="Symbol">{</a><a id="7164" href="plfa.Equality.html#7164" class="Bound">A</a> <a id="7166" class="Symbol">:</a> <a id="7168" class="PrimitiveType">Set</a><a id="7171" class="Symbol">}</a> <a id="7173" class="Keyword">where</a>

  <a id="7182" class="Keyword">infix</a>  <a id="7189" class="Number">1</a> <a id="7191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7239" class="Function Operator">begin_</a>
  <a id="7200" class="Keyword">infixr</a> <a id="7207" class="Number">2</a> <a id="7209" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7319" class="Function Operator">_≡⟨⟩_</a> <a id="7215" href="plfa.Equality.html#7404" class="Function Operator">_≡⟨_⟩_</a>
  <a id="7224" class="Keyword">infix</a>  <a id="7231" class="Number">3</a> <a id="7233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7519" class="Function Operator">_∎</a>

  <a id="≡-Reasoning.begin_"></a><a id="7239" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7239" class="Function Operator">begin_</a> <a id="7246" class="Symbol">:</a> <a id="7248" class="Symbol">∀</a> <a id="7250" class="Symbol">{</a><a id="7251" href="plfa.Equality.html#7251" class="Bound">x</a> <a id="7253" href="plfa.Equality.html#7253" class="Bound">y</a> <a id="7255" class="Symbol">:</a> <a id="7257" href="plfa.Equality.html#7164" class="Bound">A</a><a id="7258" class="Symbol">}</a>
    <a id="7264" class="Symbol">→</a> <a id="7266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7251" class="Bound">x</a> <a id="7268" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="7270" href="plfa.Equality.html#7253" class="Bound">y</a>
      <a id="7278" class="Comment">-----</a>
    <a id="7288" class="Symbol">→</a> <a id="7290" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7251" class="Bound">x</a> <a id="7292" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="7294" href="plfa.Equality.html#7253" class="Bound">y</a>
  <a id="7298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7239" class="Function Operator">begin</a> <a id="7304" href="plfa.Equality.html#7304" class="Bound">x≡y</a>  <a id="7309" class="Symbol">=</a>  <a id="7312" href="plfa.Equality.html#7304" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨⟩_"></a><a id="7319" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7319" class="Function Operator">_≡⟨⟩_</a> <a id="7325" class="Symbol">:</a> <a id="7327" class="Symbol">∀</a> <a id="7329" class="Symbol">(</a><a id="7330" href="plfa.Equality.html#7330" class="Bound">x</a> <a id="7332" class="Symbol">:</a> <a id="7334" href="plfa.Equality.html#7164" class="Bound">A</a><a id="7335" class="Symbol">)</a> <a id="7337" class="Symbol">{</a><a id="7338" href="plfa.Equality.html#7338" class="Bound">y</a> <a id="7340" class="Symbol">:</a> <a id="7342" href="plfa.Equality.html#7164" class="Bound">A</a><a id="7343" class="Symbol">}</a>
    <a id="7349" class="Symbol">→</a> <a id="7351" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7330" class="Bound">x</a> <a id="7353" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="7355" href="plfa.Equality.html#7338" class="Bound">y</a>
      <a id="7363" class="Comment">-----</a>
    <a id="7373" class="Symbol">→</a> <a id="7375" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7330" class="Bound">x</a> <a id="7377" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="7379" href="plfa.Equality.html#7338" class="Bound">y</a>
  <a id="7383" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7383" class="Bound">x</a> <a id="7385" href="plfa.Equality.html#7319" class="Function Operator">≡⟨⟩</a> <a id="7389" href="plfa.Equality.html#7389" class="Bound">x≡y</a>  <a id="7394" class="Symbol">=</a>  <a id="7397" href="plfa.Equality.html#7389" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨_⟩_"></a><a id="7404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7404" class="Function Operator">_≡⟨_⟩_</a> <a id="7411" class="Symbol">:</a> <a id="7413" class="Symbol">∀</a> <a id="7415" class="Symbol">(</a><a id="7416" href="plfa.Equality.html#7416" class="Bound">x</a> <a id="7418" class="Symbol">:</a> <a id="7420" href="plfa.Equality.html#7164" class="Bound">A</a><a id="7421" class="Symbol">)</a> <a id="7423" class="Symbol">{</a><a id="7424" href="plfa.Equality.html#7424" class="Bound">y</a> <a id="7426" href="plfa.Equality.html#7426" class="Bound">z</a> <a id="7428" class="Symbol">:</a> <a id="7430" href="plfa.Equality.html#7164" class="Bound">A</a><a id="7431" class="Symbol">}</a>
    <a id="7437" class="Symbol">→</a> <a id="7439" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7416" class="Bound">x</a> <a id="7441" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="7443" href="plfa.Equality.html#7424" class="Bound">y</a>
    <a id="7449" class="Symbol">→</a> <a id="7451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7424" class="Bound">y</a> <a id="7453" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="7455" href="plfa.Equality.html#7426" class="Bound">z</a>
      <a id="7463" class="Comment">-----</a>
    <a id="7473" class="Symbol">→</a> <a id="7475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7416" class="Bound">x</a> <a id="7477" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="7479" href="plfa.Equality.html#7426" class="Bound">z</a>
  <a id="7483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7483" class="Bound">x</a> <a id="7485" href="plfa.Equality.html#7404" class="Function Operator">≡⟨</a> <a id="7488" href="plfa.Equality.html#7488" class="Bound">x≡y</a> <a id="7492" href="plfa.Equality.html#7404" class="Function Operator">⟩</a> <a id="7494" href="plfa.Equality.html#7494" class="Bound">y≡z</a>  <a id="7499" class="Symbol">=</a>  <a id="7502" href="plfa.Equality.html#5155" class="Function">trans</a> <a id="7508" href="plfa.Equality.html#7488" class="Bound">x≡y</a> <a id="7512" href="plfa.Equality.html#7494" class="Bound">y≡z</a>

  <a id="≡-Reasoning._∎"></a><a id="7519" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7519" class="Function Operator">_∎</a> <a id="7522" class="Symbol">:</a> <a id="7524" class="Symbol">∀</a> <a id="7526" class="Symbol">(</a><a id="7527" href="plfa.Equality.html#7527" class="Bound">x</a> <a id="7529" class="Symbol">:</a> <a id="7531" href="plfa.Equality.html#7164" class="Bound">A</a><a id="7532" class="Symbol">)</a>
      <a id="7540" class="Comment">-----</a>
    <a id="7550" class="Symbol">→</a> <a id="7552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7527" class="Bound">x</a> <a id="7554" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="7556" href="plfa.Equality.html#7527" class="Bound">x</a>
  <a id="7560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7560" class="Bound">x</a> <a id="7562" href="plfa.Equality.html#7519" class="Function Operator">∎</a>  <a id="7565" class="Symbol">=</a>  <a id="7568" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>

<a id="7574" class="Keyword">open</a> <a id="7579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7151" class="Module">≡-Reasoning</a>
</pre>{% endraw %}
{::comment}
This is our first use of a nested module. It consists of the keyword
`module` followed by the module name and any parameters, explicit or
implicit, the keyword `where`, and the contents of the module indented.
Modules may contain any sort of declaration, including other nested modules.
Nested modules are similar to the top-level modules that constitute
each chapter of this book, save that the body of a top-level module
need not be indented.  Opening the module makes all of the definitions
available in the current environment.
{:/}

这是我们第一次使用嵌套的模块。它包括了关键字 `module` 和后续的模块名、隐式或显式参数，
关键字 `where`，和模块中的内容（在缩进内）。模块里可以包括任何形式的声明，也可以包括其他模块。
嵌套的模块和本书每章节所定义的顶层模块相似，只是顶层模块不需要缩进。
打开（Open）一个模块会把模块内的所有定义导入进当前的环境中。

{::comment}
As an example, let's look at a proof of transitivity
as a chain of equations:
{:/}

举个例子，我们来看看如何用等式串证明传递性：

{% raw %}<pre class="Agda"><a id="trans′"></a><a id="8440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8440" class="Function">trans′</a> <a id="8447" class="Symbol">:</a> <a id="8449" class="Symbol">∀</a> <a id="8451" class="Symbol">{</a><a id="8452" href="plfa.Equality.html#8452" class="Bound">A</a> <a id="8454" class="Symbol">:</a> <a id="8456" class="PrimitiveType">Set</a><a id="8459" class="Symbol">}</a> <a id="8461" class="Symbol">{</a><a id="8462" href="plfa.Equality.html#8462" class="Bound">x</a> <a id="8464" href="plfa.Equality.html#8464" class="Bound">y</a> <a id="8466" href="plfa.Equality.html#8466" class="Bound">z</a> <a id="8468" class="Symbol">:</a> <a id="8470" href="plfa.Equality.html#8452" class="Bound">A</a><a id="8471" class="Symbol">}</a>
  <a id="8475" class="Symbol">→</a> <a id="8477" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8462" class="Bound">x</a> <a id="8479" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="8481" href="plfa.Equality.html#8464" class="Bound">y</a>
  <a id="8485" class="Symbol">→</a> <a id="8487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8464" class="Bound">y</a> <a id="8489" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="8491" href="plfa.Equality.html#8466" class="Bound">z</a>
    <a id="8497" class="Comment">-----</a>
  <a id="8505" class="Symbol">→</a> <a id="8507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8462" class="Bound">x</a> <a id="8509" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="8511" href="plfa.Equality.html#8466" class="Bound">z</a>
<a id="8513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8440" class="Function">trans′</a> <a id="8520" class="Symbol">{</a><a id="8521" href="plfa.Equality.html#8521" class="Bound">A</a><a id="8522" class="Symbol">}</a> <a id="8524" class="Symbol">{</a><a id="8525" href="plfa.Equality.html#8525" class="Bound">x</a><a id="8526" class="Symbol">}</a> <a id="8528" class="Symbol">{</a><a id="8529" href="plfa.Equality.html#8529" class="Bound">y</a><a id="8530" class="Symbol">}</a> <a id="8532" class="Symbol">{</a><a id="8533" href="plfa.Equality.html#8533" class="Bound">z</a><a id="8534" class="Symbol">}</a> <a id="8536" href="plfa.Equality.html#8536" class="Bound">x≡y</a> <a id="8540" href="plfa.Equality.html#8540" class="Bound">y≡z</a> <a id="8544" class="Symbol">=</a>
  <a id="8548" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7239" class="Function Operator">begin</a>
    <a id="8558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8525" class="Bound">x</a>
  <a id="8562" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7404" class="Function Operator">≡⟨</a> <a id="8565" href="plfa.Equality.html#8536" class="Bound">x≡y</a> <a id="8569" href="plfa.Equality.html#7404" class="Function Operator">⟩</a>
    <a id="8575" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8529" class="Bound">y</a>
  <a id="8579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7404" class="Function Operator">≡⟨</a> <a id="8582" href="plfa.Equality.html#8540" class="Bound">y≡z</a> <a id="8586" href="plfa.Equality.html#7404" class="Function Operator">⟩</a>
    <a id="8592" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8533" class="Bound">z</a>
  <a id="8596" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7519" class="Function Operator">∎</a>
</pre>{% endraw %}
{::comment}
According to the fixity declarations, the body parses as follows:
{:/}

根据其定义，等式右边会被解析成如下：

    begin (x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎)))

{::comment}
The application of `begin` is purely cosmetic, as it simply returns
its argument.  That argument consists of `_≡⟨_⟩_` applied to `x`,
`x≡y`, and `y ≡⟨ y≡z ⟩ (z ∎)`.  The first argument is a term, `x`,
while the second and third arguments are both proofs of equations, in
particular proofs of `x ≡ y` and `y ≡ z` respectively, which are
combined by `trans` in the body of `_≡⟨_⟩_` to yield a proof of `x ≡
z`.  The proof of `y ≡ z` consists of `_≡⟨_⟩_` applied to `y`, `y≡z`,
and `z ∎`.  The first argument is a term, `y`, while the second and
third arguments are both proofs of equations, in particular proofs of
`y ≡ z` and `z ≡ z` respectively, which are combined by `trans` in the
body of `_≡⟨_⟩_` to yield a proof of `y ≡ z`.  Finally, the proof of
`z ≡ z` consists of `_∎` applied to the term `z`, which yields `refl`.
After simplification, the body is equivalent to the term:
{:/}

这里 `begin` 的使用纯粹是装饰性的，因为它直接返回了其参数。其参数包括了
`_≡⟨_⟩_` 作用于 `x`、`x≡y` 和 `y ≡⟨ y≡z ⟩ (z ∎)`。第一个参数是一个项 `x`，
而第二、第三个参数分别是等式 `x ≡ y`、`y ≡ z` 的证明，它们在 `_≡⟨_⟩_` 的定义中用
`trans` 连接起来，形成 `x ≡ z` 的证明。`y ≡ z` 的证明包括了 `_≡⟨_⟩_` 作用于 `y`、
`y≡z` 和 `z ∎`。第一个参数是一个项 `y`，而第二、第三个参数分别是等式 `y ≡ z`、`z ≡ z` 的证明，
它们在 `_≡⟨_⟩_` 的定义中用 `trans` 连接起来，形成 `y ≡ z` 的证明。最后，`z ≡ z`
的证明包括了 `_∎` 作用于 `z` 之上，使用了 `refl`。经过化简，上述定义等同于：

    trans x≡y (trans y≡z refl)

{::comment}
We could replace any use of a chain of equations by a chain of
applications of `trans`; the result would be more compact but harder
to read.  The trick behind `∎` means that a chain of equalities
simplifies to a chain of applications of `trans` that ends in `trans e
refl`, where `e` is a term that proves some equality, even though `e`
alone would do.
{:/}

我们可以把任意等式串转化成一系列的 `trans` 的使用。这样的证明更加精简，但是更难以阅读。
`∎` 的小窍门意味着等式串化简成为的一系列 `trans` 会以 `trans e refl` 结尾，尽管只需要 `e`
就足够了，这里的 `e` 是等式的证明。


{::comment}
## Chains of equations, another example
{:/}

## 等式串的另外一个例子

{::comment}
As a second example of chains of equations, we repeat the proof that addition
is commutative.  We first repeat the definitions of naturals and addition.
We cannot import them because (as noted at the beginning of this chapter)
it would cause a conflict:
{:/}

我们重新证明加法的交换律来作为等式串的第二个例子。我们首先重复自然数和加法的定义。
我们不能导入它们（正如本章节开头中所解释的那样），因为那样会产生一个冲突：

{% raw %}<pre class="Agda"><a id="11003" class="Keyword">data</a> <a id="ℕ"></a><a id="11008" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11008" class="Datatype">ℕ</a> <a id="11010" class="Symbol">:</a> <a id="11012" class="PrimitiveType">Set</a> <a id="11016" class="Keyword">where</a>
  <a id="ℕ.zero"></a><a id="11024" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11024" class="InductiveConstructor">zero</a> <a id="11029" class="Symbol">:</a> <a id="11031" href="plfa.Equality.html#11008" class="Datatype">ℕ</a>
  <a id="ℕ.suc"></a><a id="11035" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11035" class="InductiveConstructor">suc</a>  <a id="11040" class="Symbol">:</a> <a id="11042" href="plfa.Equality.html#11008" class="Datatype">ℕ</a> <a id="11044" class="Symbol">→</a> <a id="11046" href="plfa.Equality.html#11008" class="Datatype">ℕ</a>

<a id="_+_"></a><a id="11049" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11049" class="Function Operator">_+_</a> <a id="11053" class="Symbol">:</a> <a id="11055" href="plfa.Equality.html#11008" class="Datatype">ℕ</a> <a id="11057" class="Symbol">→</a> <a id="11059" href="plfa.Equality.html#11008" class="Datatype">ℕ</a> <a id="11061" class="Symbol">→</a> <a id="11063" href="plfa.Equality.html#11008" class="Datatype">ℕ</a>
<a id="11065" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11024" class="InductiveConstructor">zero</a>    <a id="11073" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="11075" href="plfa.Equality.html#11075" class="Bound">n</a>  <a id="11078" class="Symbol">=</a>  <a id="11081" href="plfa.Equality.html#11075" class="Bound">n</a>
<a id="11083" class="Symbol">(</a><a id="11084" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11035" class="InductiveConstructor">suc</a> <a id="11088" href="plfa.Equality.html#11088" class="Bound">m</a><a id="11089" class="Symbol">)</a> <a id="11091" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="11093" href="plfa.Equality.html#11093" class="Bound">n</a>  <a id="11096" class="Symbol">=</a>  <a id="11099" href="plfa.Equality.html#11035" class="InductiveConstructor">suc</a> <a id="11103" class="Symbol">(</a><a id="11104" href="plfa.Equality.html#11088" class="Bound">m</a> <a id="11106" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="11108" href="plfa.Equality.html#11093" class="Bound">n</a><a id="11109" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
To save space we postulate (rather than prove in full) two lemmas:
{:/}

为了节约空间，我们假设两条引理（而不是证明它们）：

{% raw %}<pre class="Agda"><a id="11232" class="Keyword">postulate</a>
  <a id="+-identity"></a><a id="11244" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11244" class="Postulate">+-identity</a> <a id="11255" class="Symbol">:</a> <a id="11257" class="Symbol">∀</a> <a id="11259" class="Symbol">(</a><a id="11260" href="plfa.Equality.html#11260" class="Bound">m</a> <a id="11262" class="Symbol">:</a> <a id="11264" href="plfa.Equality.html#11008" class="Datatype">ℕ</a><a id="11265" class="Symbol">)</a> <a id="11267" class="Symbol">→</a> <a id="11269" href="plfa.Equality.html#11260" class="Bound">m</a> <a id="11271" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="11273" href="plfa.Equality.html#11024" class="InductiveConstructor">zero</a> <a id="11278" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="11280" href="plfa.Equality.html#11260" class="Bound">m</a>
  <a id="+-suc"></a><a id="11284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11284" class="Postulate">+-suc</a> <a id="11290" class="Symbol">:</a> <a id="11292" class="Symbol">∀</a> <a id="11294" class="Symbol">(</a><a id="11295" href="plfa.Equality.html#11295" class="Bound">m</a> <a id="11297" href="plfa.Equality.html#11297" class="Bound">n</a> <a id="11299" class="Symbol">:</a> <a id="11301" href="plfa.Equality.html#11008" class="Datatype">ℕ</a><a id="11302" class="Symbol">)</a> <a id="11304" class="Symbol">→</a> <a id="11306" href="plfa.Equality.html#11295" class="Bound">m</a> <a id="11308" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="11310" href="plfa.Equality.html#11035" class="InductiveConstructor">suc</a> <a id="11314" href="plfa.Equality.html#11297" class="Bound">n</a> <a id="11316" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="11318" href="plfa.Equality.html#11035" class="InductiveConstructor">suc</a> <a id="11322" class="Symbol">(</a><a id="11323" href="plfa.Equality.html#11295" class="Bound">m</a> <a id="11325" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="11327" href="plfa.Equality.html#11297" class="Bound">n</a><a id="11328" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
This is our first use of a _postulate_.  A postulate specifies a
signature for an identifier but no definition.  Here we postulate
something proved earlier to save space.  Postulates must be used with
caution.  If we postulate something false then we could use Agda to
prove anything whatsoever.
{:/}

这是我们第一次使用*假设*（Postulate）。假设为一个标识符指定一个签名，但是不提供定义。
我们在这里假设之前证明过的东西，来节约空间。假设在使用时必须加以注意。如果假设的内容为假，
那么我们可以证明出任何东西。

{::comment}
We then repeat the proof of commutativity:
{:/}

我们接下来重复交换律的证明：

{% raw %}<pre class="Agda"><a id="+-comm"></a><a id="11841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11841" class="Function">+-comm</a> <a id="11848" class="Symbol">:</a> <a id="11850" class="Symbol">∀</a> <a id="11852" class="Symbol">(</a><a id="11853" href="plfa.Equality.html#11853" class="Bound">m</a> <a id="11855" href="plfa.Equality.html#11855" class="Bound">n</a> <a id="11857" class="Symbol">:</a> <a id="11859" href="plfa.Equality.html#11008" class="Datatype">ℕ</a><a id="11860" class="Symbol">)</a> <a id="11862" class="Symbol">→</a> <a id="11864" href="plfa.Equality.html#11853" class="Bound">m</a> <a id="11866" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="11868" href="plfa.Equality.html#11855" class="Bound">n</a> <a id="11870" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="11872" href="plfa.Equality.html#11855" class="Bound">n</a> <a id="11874" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="11876" href="plfa.Equality.html#11853" class="Bound">m</a>
<a id="11878" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11841" class="Function">+-comm</a> <a id="11885" href="plfa.Equality.html#11885" class="Bound">m</a> <a id="11887" href="plfa.Equality.html#11024" class="InductiveConstructor">zero</a> <a id="11892" class="Symbol">=</a>
  <a id="11896" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7239" class="Function Operator">begin</a>
    <a id="11906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11885" class="Bound">m</a> <a id="11908" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="11910" href="plfa.Equality.html#11024" class="InductiveConstructor">zero</a>
  <a id="11917" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7404" class="Function Operator">≡⟨</a> <a id="11920" href="plfa.Equality.html#11244" class="Postulate">+-identity</a> <a id="11931" href="plfa.Equality.html#11885" class="Bound">m</a> <a id="11933" href="plfa.Equality.html#7404" class="Function Operator">⟩</a>
    <a id="11939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11885" class="Bound">m</a>
  <a id="11943" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7319" class="Function Operator">≡⟨⟩</a>
    <a id="11951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11024" class="InductiveConstructor">zero</a> <a id="11956" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="11958" href="plfa.Equality.html#11885" class="Bound">m</a>
  <a id="11962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7519" class="Function Operator">∎</a>
<a id="11964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11841" class="Function">+-comm</a> <a id="11971" href="plfa.Equality.html#11971" class="Bound">m</a> <a id="11973" class="Symbol">(</a><a id="11974" href="plfa.Equality.html#11035" class="InductiveConstructor">suc</a> <a id="11978" href="plfa.Equality.html#11978" class="Bound">n</a><a id="11979" class="Symbol">)</a> <a id="11981" class="Symbol">=</a>
  <a id="11985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7239" class="Function Operator">begin</a>
    <a id="11995" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11971" class="Bound">m</a> <a id="11997" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="11999" href="plfa.Equality.html#11035" class="InductiveConstructor">suc</a> <a id="12003" href="plfa.Equality.html#11978" class="Bound">n</a>
  <a id="12007" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7404" class="Function Operator">≡⟨</a> <a id="12010" href="plfa.Equality.html#11284" class="Postulate">+-suc</a> <a id="12016" href="plfa.Equality.html#11971" class="Bound">m</a> <a id="12018" href="plfa.Equality.html#11978" class="Bound">n</a> <a id="12020" href="plfa.Equality.html#7404" class="Function Operator">⟩</a>
    <a id="12026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11035" class="InductiveConstructor">suc</a> <a id="12030" class="Symbol">(</a><a id="12031" href="plfa.Equality.html#11971" class="Bound">m</a> <a id="12033" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="12035" href="plfa.Equality.html#11978" class="Bound">n</a><a id="12036" class="Symbol">)</a>
  <a id="12040" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7404" class="Function Operator">≡⟨</a> <a id="12043" href="plfa.Equality.html#5755" class="Function">cong</a> <a id="12048" href="plfa.Equality.html#11035" class="InductiveConstructor">suc</a> <a id="12052" class="Symbol">(</a><a id="12053" href="plfa.Equality.html#11841" class="Function">+-comm</a> <a id="12060" href="plfa.Equality.html#11971" class="Bound">m</a> <a id="12062" href="plfa.Equality.html#11978" class="Bound">n</a><a id="12063" class="Symbol">)</a> <a id="12065" href="plfa.Equality.html#7404" class="Function Operator">⟩</a>
    <a id="12071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11035" class="InductiveConstructor">suc</a> <a id="12075" class="Symbol">(</a><a id="12076" href="plfa.Equality.html#11978" class="Bound">n</a> <a id="12078" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="12080" href="plfa.Equality.html#11971" class="Bound">m</a><a id="12081" class="Symbol">)</a>
  <a id="12085" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7319" class="Function Operator">≡⟨⟩</a>
    <a id="12093" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11035" class="InductiveConstructor">suc</a> <a id="12097" href="plfa.Equality.html#11978" class="Bound">n</a> <a id="12099" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="12101" href="plfa.Equality.html#11971" class="Bound">m</a>
  <a id="12105" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7519" class="Function Operator">∎</a>
</pre>{% endraw %}
{::comment}
The reasoning here is similar to that in the
preceding section.  We use
`_≡⟨⟩_` when no justification is required.
One can think of `_≡⟨⟩_` as equivalent to `_≡⟨ refl ⟩_`.
{:/}

论证的过程和之前的相似。我们在不需要解释的地方使用 `_≡⟨⟩_`，我们可以认为
`_≡⟨⟩_` 和 `_≡⟨ refl ⟩_` 是等价的。

{::comment}
Agda always treats a term as equivalent to its
simplified term.  The reason that one can write
{:/}

Agda 总是认为一个项与其化简的项是等价的。我们之所以可以写出

      suc (n + m)
    ≡⟨⟩
      suc n + m

{::comment}
is because Agda treats both terms as the same.
This also means that one could instead interchange
the lines and write
{:/}

是因为 Agda 认为它们是一样的。这也意味着我们可以交换两行的顺序，写出

      suc n + m
    ≡⟨⟩
      suc (n + m)

{::comment}
and Agda would not object. Agda only checks that the terms separated
by `≡⟨⟩` have the same simplified form; it's up to us to write them in
an order that will make sense to the reader.
{:/}

而 Agda 并不会反对。Agda 只会检查由 `≡⟨⟩` 隔开的项是否化简后相同。
而书写的顺序合不合理则是由我们自行决定。


{::comment}
#### Exercise `≤-Reasoning` (stretch)
{:/}

#### 练习 `≤-Reasoning` (延伸)

{::comment}
The proof of monotonicity from
Chapter [Relations][plfa.Relations]
can be written in a more readable form by using an analogue of our
notation for `≡-Reasoning`.  Define `≤-Reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite all of `+-monoˡ-≤`, `+-monoʳ-≤`, and `+-mono-≤`.
{:/}

[Relations][plfa.Relations] 章节中的单调性证明亦可以用相似于 `≡-Reasoning` 的，更易于理解的形式给出。
相似地来定义 `≤-Reasoning`，并用其重新给出加法对于不等式是单调的证明。重写 `+-monoˡ-≤`、`+-monoʳ-≤`
和 `+-mono-≤`。

{::comment}
{% raw %}<pre class="Agda"><a id="13680" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="13717" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
## Rewriting
{:/}

## 重写

{::comment}
Consider a property of natural numbers, such as being even.
We repeat the earlier definition:
{:/}

考虑一个自然数的性质，比如说一个数是偶数。我们重复之前给出的定义：

{% raw %}<pre class="Agda"><a id="13925" class="Keyword">data</a> <a id="even"></a><a id="13930" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13930" class="Datatype">even</a> <a id="13935" class="Symbol">:</a> <a id="13937" href="plfa.Equality.html#11008" class="Datatype">ℕ</a> <a id="13939" class="Symbol">→</a> <a id="13941" class="PrimitiveType">Set</a>
<a id="13945" class="Keyword">data</a> <a id="odd"></a><a id="13950" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13950" class="Datatype">odd</a>  <a id="13955" class="Symbol">:</a> <a id="13957" href="plfa.Equality.html#11008" class="Datatype">ℕ</a> <a id="13959" class="Symbol">→</a> <a id="13961" class="PrimitiveType">Set</a>

<a id="13966" class="Keyword">data</a> <a id="13971" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13930" class="Datatype">even</a> <a id="13976" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="13985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13985" class="InductiveConstructor">even-zero</a> <a id="13995" class="Symbol">:</a> <a id="13997" href="plfa.Equality.html#13930" class="Datatype">even</a> <a id="14002" href="plfa.Equality.html#11024" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="14010" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14010" class="InductiveConstructor">even-suc</a> <a id="14019" class="Symbol">:</a> <a id="14021" class="Symbol">∀</a> <a id="14023" class="Symbol">{</a><a id="14024" href="plfa.Equality.html#14024" class="Bound">n</a> <a id="14026" class="Symbol">:</a> <a id="14028" href="plfa.Equality.html#11008" class="Datatype">ℕ</a><a id="14029" class="Symbol">}</a>
    <a id="14035" class="Symbol">→</a> <a id="14037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13950" class="Datatype">odd</a> <a id="14041" href="plfa.Equality.html#14024" class="Bound">n</a>
      <a id="14049" class="Comment">------------</a>
    <a id="14066" class="Symbol">→</a> <a id="14068" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13930" class="Datatype">even</a> <a id="14073" class="Symbol">(</a><a id="14074" href="plfa.Equality.html#11035" class="InductiveConstructor">suc</a> <a id="14078" href="plfa.Equality.html#14024" class="Bound">n</a><a id="14079" class="Symbol">)</a>

<a id="14082" class="Keyword">data</a> <a id="14087" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13950" class="Datatype">odd</a> <a id="14091" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="14099" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14099" class="InductiveConstructor">odd-suc</a> <a id="14107" class="Symbol">:</a> <a id="14109" class="Symbol">∀</a> <a id="14111" class="Symbol">{</a><a id="14112" href="plfa.Equality.html#14112" class="Bound">n</a> <a id="14114" class="Symbol">:</a> <a id="14116" href="plfa.Equality.html#11008" class="Datatype">ℕ</a><a id="14117" class="Symbol">}</a>
    <a id="14123" class="Symbol">→</a> <a id="14125" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13930" class="Datatype">even</a> <a id="14130" href="plfa.Equality.html#14112" class="Bound">n</a>
      <a id="14138" class="Comment">-----------</a>
    <a id="14154" class="Symbol">→</a> <a id="14156" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13950" class="Datatype">odd</a> <a id="14160" class="Symbol">(</a><a id="14161" href="plfa.Equality.html#11035" class="InductiveConstructor">suc</a> <a id="14165" href="plfa.Equality.html#14112" class="Bound">n</a><a id="14166" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
In the previous section, we proved addition is commutative.  Given
evidence that `even (m + n)` holds, we ought also to be able to take
that as evidence that `even (n + m)` holds.
{:/}

在前面的部分中，我们证明了加法满足交换律。给定 `even (m + n)` 成立的证据，我们应当可以用它来做
`even (n + m)` 成立的证据。

{::comment}
Agda includes special notation to support just this kind of reasoning,
the `rewrite` notation we encountered earlier.
To enable this notation, we use pragmas to tell Agda which type
corresponds to equality:
{:/}

Agda 对这种论证有特殊记法的支持——我们之前提到过的 `rewrite` 记法。来启用这种记法，
我们只用编译程序指令来告诉 Agda 什么类型对应相等性：

{% raw %}<pre class="Agda"><a id="14761" class="Symbol">{-#</a> <a id="14765" class="Keyword">BUILTIN</a> <a id="14773" class="Pragma">EQUALITY</a> <a id="14782" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1053" class="Datatype Operator">_≡_</a> <a id="14786" class="Symbol">#-}</a>
</pre>{% endraw %}
{::comment}
We can then prove the desired property as follows:
{:/}

我们然后就可以如下证明求证的性质：

{% raw %}<pre class="Agda"><a id="even-comm"></a><a id="14887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14887" class="Function">even-comm</a> <a id="14897" class="Symbol">:</a> <a id="14899" class="Symbol">∀</a> <a id="14901" class="Symbol">(</a><a id="14902" href="plfa.Equality.html#14902" class="Bound">m</a> <a id="14904" href="plfa.Equality.html#14904" class="Bound">n</a> <a id="14906" class="Symbol">:</a> <a id="14908" href="plfa.Equality.html#11008" class="Datatype">ℕ</a><a id="14909" class="Symbol">)</a>
  <a id="14913" class="Symbol">→</a> <a id="14915" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13930" class="Datatype">even</a> <a id="14920" class="Symbol">(</a><a id="14921" href="plfa.Equality.html#14902" class="Bound">m</a> <a id="14923" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="14925" href="plfa.Equality.html#14904" class="Bound">n</a><a id="14926" class="Symbol">)</a>
    <a id="14932" class="Comment">------------</a>
  <a id="14947" class="Symbol">→</a> <a id="14949" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13930" class="Datatype">even</a> <a id="14954" class="Symbol">(</a><a id="14955" href="plfa.Equality.html#14904" class="Bound">n</a> <a id="14957" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="14959" href="plfa.Equality.html#14902" class="Bound">m</a><a id="14960" class="Symbol">)</a>
<a id="14962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14887" class="Function">even-comm</a> <a id="14972" href="plfa.Equality.html#14972" class="Bound">m</a> <a id="14974" href="plfa.Equality.html#14974" class="Bound">n</a> <a id="14976" href="plfa.Equality.html#14976" class="Bound">ev</a>  <a id="14980" class="Keyword">rewrite</a> <a id="14988" href="plfa.Equality.html#11841" class="Function">+-comm</a> <a id="14995" href="plfa.Equality.html#14974" class="Bound">n</a> <a id="14997" href="plfa.Equality.html#14972" class="Bound">m</a>  <a id="15000" class="Symbol">=</a>  <a id="15003" href="plfa.Equality.html#14976" class="Bound">ev</a>
</pre>{% endraw %}
{::comment}
Here `ev` ranges over evidence that `even (m + n)` holds, and we show
that it also provides evidence that `even (n + m)` holds.  In
general, the keyword `rewrite` is followed by evidence of an
equality, and that equality is used to rewrite the type of the
goal and of any variable in scope.
{:/}

在这里，`ev` 包括了所有 `even (m + n)` 成立的证据，我们证明它亦可作为 `even (n + m)`
成立的证据。一般来说，关键字 `rewrite` 之后跟着一个等式的证明，这个等式被用于重写目标和任意作用域内变量的类型。

{::comment}
It is instructive to develop `even-comm` interactively.  To start, we
supply variables for the arguments on the left, and a hole for the
body on the right:
{:/}

交互性地证明 `even-comm` 是很有帮助的。一开始，我们先给左边的参数赋予变量，给右手边放上一个洞：

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev = {! !}

{::comment}
If we go into the hole and type `C-c C-,` then Agda reports:
{:/}

如果我们进入洞里，输入 `C-c C-,`，Agda 会报告：

    Goal: even (n + m)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

{::comment}
Now we add the rewrite:
{:/}

现在我们加入重写：

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev rewrite +-comm n m = {! !}

{::comment}
If we go into the hole again and type `C-c C-,` then Agda now reports:
{:/}

如果我们再次进入洞里，并输入 `C-c C-,`，Agda 现在会报告：

    Goal: even (m + n)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

{::comment}
The arguments have been swapped in the goal.  Now it is trivial to see
that `ev` satisfies the goal, and typing `C-c C-a` in the hole causes
it to be filled with `ev`.  The command `C-c C-a` performs an
automated search, including checking whether a variable in scope has
the same type as the goal.
{:/}

目标里的参数被交换了。现在 `ev` 显然满足目标条件，输入 `C-c C-a` 会用 `ev` 来填充这个洞。
命令 `C-c C-a` 可以进行自动搜索，检查作用域内的变量是否和目标有相同的类型。


{::comment}
## Multiple rewrites
{:/}

## 多重重写

{::comment}
One may perform multiple rewrites, each separated by a vertical bar.  For instance,
here is a second proof that addition is commutative, relying on rewrites rather
than chains of equalities:
{:/}

我们可以多次使用重写，以竖线隔开。举个例子，这里是加法交换律的第二个证明，使用重写而不是等式串：

{% raw %}<pre class="Agda"><a id="+-comm′"></a><a id="17224" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17224" class="Function">+-comm′</a> <a id="17232" class="Symbol">:</a> <a id="17234" class="Symbol">∀</a> <a id="17236" class="Symbol">(</a><a id="17237" href="plfa.Equality.html#17237" class="Bound">m</a> <a id="17239" href="plfa.Equality.html#17239" class="Bound">n</a> <a id="17241" class="Symbol">:</a> <a id="17243" href="plfa.Equality.html#11008" class="Datatype">ℕ</a><a id="17244" class="Symbol">)</a> <a id="17246" class="Symbol">→</a> <a id="17248" href="plfa.Equality.html#17237" class="Bound">m</a> <a id="17250" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="17252" href="plfa.Equality.html#17239" class="Bound">n</a> <a id="17254" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="17256" href="plfa.Equality.html#17239" class="Bound">n</a> <a id="17258" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="17260" href="plfa.Equality.html#17237" class="Bound">m</a>
<a id="17262" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17224" class="Function">+-comm′</a> <a id="17270" href="plfa.Equality.html#11024" class="InductiveConstructor">zero</a>    <a id="17278" href="plfa.Equality.html#17278" class="Bound">n</a>  <a id="17281" class="Keyword">rewrite</a> <a id="17289" href="plfa.Equality.html#11244" class="Postulate">+-identity</a> <a id="17300" href="plfa.Equality.html#17278" class="Bound">n</a>             <a id="17314" class="Symbol">=</a>  <a id="17317" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>
<a id="17322" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17224" class="Function">+-comm′</a> <a id="17330" class="Symbol">(</a><a id="17331" href="plfa.Equality.html#11035" class="InductiveConstructor">suc</a> <a id="17335" href="plfa.Equality.html#17335" class="Bound">m</a><a id="17336" class="Symbol">)</a> <a id="17338" href="plfa.Equality.html#17338" class="Bound">n</a>  <a id="17341" class="Keyword">rewrite</a> <a id="17349" href="plfa.Equality.html#11284" class="Postulate">+-suc</a> <a id="17355" href="plfa.Equality.html#17338" class="Bound">n</a> <a id="17357" href="plfa.Equality.html#17335" class="Bound">m</a> <a id="17359" class="Symbol">|</a> <a id="17361" href="plfa.Equality.html#17224" class="Function">+-comm′</a> <a id="17369" href="plfa.Equality.html#17335" class="Bound">m</a> <a id="17371" href="plfa.Equality.html#17338" class="Bound">n</a>  <a id="17374" class="Symbol">=</a>  <a id="17377" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
This is far more compact.  Among other things, whereas the previous
proof required `cong suc (+-comm m n)` as the justification to invoke
the inductive hypothesis, here it is sufficient to rewrite with
`+-comm m n`, as rewriting automatically takes congruence into
account.  Although proofs with rewriting are shorter, proofs as chains
of equalities are easier to follow, and we will stick with the latter
when feasible.
{:/}

这个证明更加的简短。之前的证明用 `cong suc (+-comm m n)` 作为使用归纳假设的说明，
而这里我们使用 `+-comm m n` 来重写就足够了，因为重写可以将合同性考虑在其中。尽管使用重写的证明更加的简短，
使用等式串的证明能容易理解，我们将尽可能的使用后者。


{::comment}
## Rewriting expanded
{:/}

## 深入重写

{::comment}
The `rewrite` notation is in fact shorthand for an appropriate use of `with`
abstraction:
{:/}

`rewrite` 记法实际上是 `with` 抽象的一种应用：

{% raw %}<pre class="Agda"><a id="even-comm′"></a><a id="18165" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18165" class="Function">even-comm′</a> <a id="18176" class="Symbol">:</a> <a id="18178" class="Symbol">∀</a> <a id="18180" class="Symbol">(</a><a id="18181" href="plfa.Equality.html#18181" class="Bound">m</a> <a id="18183" href="plfa.Equality.html#18183" class="Bound">n</a> <a id="18185" class="Symbol">:</a> <a id="18187" href="plfa.Equality.html#11008" class="Datatype">ℕ</a><a id="18188" class="Symbol">)</a>
  <a id="18192" class="Symbol">→</a> <a id="18194" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13930" class="Datatype">even</a> <a id="18199" class="Symbol">(</a><a id="18200" href="plfa.Equality.html#18181" class="Bound">m</a> <a id="18202" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="18204" href="plfa.Equality.html#18183" class="Bound">n</a><a id="18205" class="Symbol">)</a>
    <a id="18211" class="Comment">------------</a>
  <a id="18226" class="Symbol">→</a> <a id="18228" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13930" class="Datatype">even</a> <a id="18233" class="Symbol">(</a><a id="18234" href="plfa.Equality.html#18183" class="Bound">n</a> <a id="18236" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="18238" href="plfa.Equality.html#18181" class="Bound">m</a><a id="18239" class="Symbol">)</a>
<a id="18241" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18165" class="Function">even-comm′</a> <a id="18252" href="plfa.Equality.html#18252" class="Bound">m</a> <a id="18254" href="plfa.Equality.html#18254" class="Bound">n</a> <a id="18256" href="plfa.Equality.html#18256" class="Bound">ev</a> <a id="18259" class="Keyword">with</a>   <a id="18266" href="plfa.Equality.html#18252" class="Bound">m</a> <a id="18268" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="18270" href="plfa.Equality.html#18254" class="Bound">n</a>  <a id="18273" class="Symbol">|</a> <a id="18275" href="plfa.Equality.html#11841" class="Function">+-comm</a> <a id="18282" href="plfa.Equality.html#18252" class="Bound">m</a> <a id="18284" href="plfa.Equality.html#18254" class="Bound">n</a>
<a id="18286" class="Symbol">...</a>                  <a id="18307" class="Symbol">|</a> <a id="18309" class="DottedPattern Symbol">.(</a><a id="18311" class="DottedPattern Bound">n</a> <a id="18313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11049" class="DottedPattern Function Operator">+</a> <a id="18315" class="DottedPattern Bound">m</a><a id="18316" class="DottedPattern Symbol">)</a> <a id="18318" class="Symbol">|</a> <a id="18320" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>       <a id="18331" class="Symbol">=</a> <a id="18333" class="Bound">ev</a>
</pre>{% endraw %}
{::comment}
In general, one can follow `with` by any number of expressions,
separated by bars, where each following equation has the same number
of patterns.  We often write expressions and the corresponding
patterns so they line up in columns, as above. Here the first column
asserts that `m + n` and `n + m` are identical, and the second column
justifies that assertion with evidence of the appropriate equality.
Note also the use of the _dot pattern_, `.(n + m)`.  A dot pattern
consists of a dot followed by an expression, and is used when other
information forces the value matched to be equal to the value of the
expression in the dot pattern.  In this case, the identification of
`m + n` and `n + m` is justified by the subsequent matching of
`+-comm m n` against `refl`.  One might think that the first clause is
redundant as the information is inherent in the second clause, but in
fact Agda is rather picky on this point: omitting the first clause or
reversing the order of the clauses will cause Agda to report an error.
(Try it and see!)
{:/}

总的来着，我们可以在 `with` 后面跟上任何数量的表达式，用竖线分隔开，并且在每个等式中使用相同个数的模式。
我们经常将表达式和模式如上对齐。这个第一列表明了 `m + n` 和 `n + m` 是相同的，第二列使用相应等式来证明的前述的断言。
注意在这里使用的*点模式*（Dot Pattern），`.(n + m)`。点模式由一个点和一个表达式组成，
在其他信息迫使这个值和点模式中的值相等时使用。在这里，`m + n` 和 `n + m` 由后续的
`+-comm m n` 与 `refl` 的匹配来识别。我们可能会认为第一种情况是多余的，因为第二种情况中才蕴涵了需要的信息。
但实际上 Agda 在这件事上很挑剔——省略第一条或者更换顺序会让 Agda 报告一个错误。（试一试你就知道！）

{::comment}
In this case, we can avoid rewrite by simply applying the substitution
function defined earlier:
{:/}

在这种情况中，我们也可以使用之前定义的替换函数来避免使用重写：

{% raw %}<pre class="Agda"><a id="even-comm″"></a><a id="19902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#19902" class="Function">even-comm″</a> <a id="19913" class="Symbol">:</a> <a id="19915" class="Symbol">∀</a> <a id="19917" class="Symbol">(</a><a id="19918" href="plfa.Equality.html#19918" class="Bound">m</a> <a id="19920" href="plfa.Equality.html#19920" class="Bound">n</a> <a id="19922" class="Symbol">:</a> <a id="19924" href="plfa.Equality.html#11008" class="Datatype">ℕ</a><a id="19925" class="Symbol">)</a>
  <a id="19929" class="Symbol">→</a> <a id="19931" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13930" class="Datatype">even</a> <a id="19936" class="Symbol">(</a><a id="19937" href="plfa.Equality.html#19918" class="Bound">m</a> <a id="19939" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="19941" href="plfa.Equality.html#19920" class="Bound">n</a><a id="19942" class="Symbol">)</a>
    <a id="19948" class="Comment">------------</a>
  <a id="19963" class="Symbol">→</a> <a id="19965" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13930" class="Datatype">even</a> <a id="19970" class="Symbol">(</a><a id="19971" href="plfa.Equality.html#19920" class="Bound">n</a> <a id="19973" href="plfa.Equality.html#11049" class="Function Operator">+</a> <a id="19975" href="plfa.Equality.html#19918" class="Bound">m</a><a id="19976" class="Symbol">)</a>
<a id="19978" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#19902" class="Function">even-comm″</a> <a id="19989" href="plfa.Equality.html#19989" class="Bound">m</a> <a id="19991" href="plfa.Equality.html#19991" class="Bound">n</a>  <a id="19994" class="Symbol">=</a>  <a id="19997" href="plfa.Equality.html#6673" class="Function">subst</a> <a id="20003" href="plfa.Equality.html#13930" class="Datatype">even</a> <a id="20008" class="Symbol">(</a><a id="20009" href="plfa.Equality.html#11841" class="Function">+-comm</a> <a id="20016" href="plfa.Equality.html#19989" class="Bound">m</a> <a id="20018" href="plfa.Equality.html#19991" class="Bound">n</a><a id="20019" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Nonetheless, rewrite is a vital part of the Agda toolkit.  We will use
it sparingly, but it is occasionally essential.
{:/}

尽管如此，重写是 Agda 工具箱中很重要的一部分。我们会偶尔使用它，但是它有的时候是必要的。


{::comment}
## Leibniz equality
{:/}

## 莱布尼兹（Leibniz）相等性

{::comment}
The form of asserting equality that we have used is due to Martin
Löf, and was published in 1975.  An older form is due to Leibniz, and
was published in 1686.  Leibniz asserted the _identity of
indiscernibles_: two objects are equal if and only if they satisfy the
same properties. This principle sometimes goes by the name Leibniz'
Law, and is closely related to Spock's Law, "A difference that makes
no difference is no difference".  Here we define Leibniz equality,
and show that two terms satisfy Leibniz equality if and only if they
satisfy Martin Löf equality.
{:/}

我们使用的相等性断言的形式源于 Martin Löf，于 1975 年发表。一个更早的形式源于莱布尼兹，
于 1686 年发表。莱布尼兹断言的相等性表示*不可分辨的实体*（Identity of Indiscernibles）：
两个对象相等当且仅当它们满足完全相同的性质。这条原理有时被称作莱布尼兹定律（Leibniz' Law），
与史波克定律紧密相关：“一个不造成区别的区别不是区别”。我们在这里定义莱布尼兹相等性，
并证明两个项满足莱布尼兹相等性当且仅当其满足 Martin Löf 相等性。

{::comment}
Leibniz equality is usually formalised to state that `x ≐ y` holds if
every property `P` that holds of `x` also holds of `y`.  Perhaps
surprisingly, this definition is sufficient to also ensure the
converse, that every property `P` that holds of `y` also holds of `x`.
{:/}

莱布尼兹不等式一般如下来定义：`x ≐ y` 当每个对于 `x` 成立的性质 `P` 对于 `y` 也成立时成立。
可能这有些出乎意料，但是这个定义亦足够保证其相反的命题：每个对于 `y` 成立的性质 `P` 对于 `x` 也成立。

{::comment}
Let `x` and `y` be objects of type `A`. We say that `x ≐ y` holds if
for every predicate `P` over type `A` we have that `P x` implies `P y`:
{:/}

令 `x` 和 `y` 为类型 `A` 的对象。我们定义 `x ≐ y` 成立，当每个对于类型 `A` 成立的谓词 `P`，
我们有 `P x` 蕴涵了 `P y`：

{% raw %}<pre class="Agda"><a id="_≐_"></a><a id="21762" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21762" class="Function Operator">_≐_</a> <a id="21766" class="Symbol">:</a> <a id="21768" class="Symbol">∀</a> <a id="21770" class="Symbol">{</a><a id="21771" href="plfa.Equality.html#21771" class="Bound">A</a> <a id="21773" class="Symbol">:</a> <a id="21775" class="PrimitiveType">Set</a><a id="21778" class="Symbol">}</a> <a id="21780" class="Symbol">(</a><a id="21781" href="plfa.Equality.html#21781" class="Bound">x</a> <a id="21783" href="plfa.Equality.html#21783" class="Bound">y</a> <a id="21785" class="Symbol">:</a> <a id="21787" href="plfa.Equality.html#21771" class="Bound">A</a><a id="21788" class="Symbol">)</a> <a id="21790" class="Symbol">→</a> <a id="21792" class="PrimitiveType">Set₁</a>
<a id="21797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21762" class="Function Operator">_≐_</a> <a id="21801" class="Symbol">{</a><a id="21802" href="plfa.Equality.html#21802" class="Bound">A</a><a id="21803" class="Symbol">}</a> <a id="21805" href="plfa.Equality.html#21805" class="Bound">x</a> <a id="21807" href="plfa.Equality.html#21807" class="Bound">y</a> <a id="21809" class="Symbol">=</a> <a id="21811" class="Symbol">∀</a> <a id="21813" class="Symbol">(</a><a id="21814" href="plfa.Equality.html#21814" class="Bound">P</a> <a id="21816" class="Symbol">:</a> <a id="21818" href="plfa.Equality.html#21802" class="Bound">A</a> <a id="21820" class="Symbol">→</a> <a id="21822" class="PrimitiveType">Set</a><a id="21825" class="Symbol">)</a> <a id="21827" class="Symbol">→</a> <a id="21829" href="plfa.Equality.html#21814" class="Bound">P</a> <a id="21831" href="plfa.Equality.html#21805" class="Bound">x</a> <a id="21833" class="Symbol">→</a> <a id="21835" href="plfa.Equality.html#21814" class="Bound">P</a> <a id="21837" href="plfa.Equality.html#21807" class="Bound">y</a>
</pre>{% endraw %}
{::comment}
We cannot write the left-hand side of the equation as `x ≐ y`,
and instead we write `_≐_ {A} x y` to provide access to the implicit
parameter `A` which appears on the right-hand side.
{:/}

我们不能在左手边使用 `x ≐ y`，取而代之我们使用 `_≐_ {A} x y` 来提供隐式参数 `A`，这样 `A`
可以出现在右手边。

{::comment}
This is our first use of _levels_.  We cannot assign `Set` the type
`Set`, since this would lead to contradictions such as Russell's
Paradox and Girard's Paradox.  Instead, there is a hierarchy of types,
where `Set : Set₁`, `Set₁ : Set₂`, and so on.  In fact, `Set` itself
is just an abbreviation for `Set₀`.  Since the equation defining `_≐_`
mentions `Set` on the right-hand side, the corresponding signature
must use `Set₁`.  We say a bit more about levels below.
{:/}

这是我们第一次使用*等级*（Levels）。我们不能将 `Set` 赋予类型 `Set`，因为这会导致自相矛盾，
比如罗素悖论（Russell's Paradox）或者 Girard 悖论。不同的是，我们有一个阶级的类型：其中
`Set : Set₁`，`Set₁ : Set₂`，以此类推。实际上，`Set` 本身就是 `Set₀` 的缩写。定义
`_≐_` 的等式在右手边提到了 `Set`，因此签名中必须使用 `Set₁`。我们稍后将进一步介绍等级。

{::comment}
Leibniz equality is reflexive and transitive,
where the first follows by a variant of the identity function
and the second by a variant of function composition:
{:/}

莱布尼兹相等性是自反和传递的。自反性由恒等函数的变种得来，传递性由函数组合的变种得来：

{% raw %}<pre class="Agda"><a id="refl-≐"></a><a id="23061" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23061" class="Function">refl-≐</a> <a id="23068" class="Symbol">:</a> <a id="23070" class="Symbol">∀</a> <a id="23072" class="Symbol">{</a><a id="23073" href="plfa.Equality.html#23073" class="Bound">A</a> <a id="23075" class="Symbol">:</a> <a id="23077" class="PrimitiveType">Set</a><a id="23080" class="Symbol">}</a> <a id="23082" class="Symbol">{</a><a id="23083" href="plfa.Equality.html#23083" class="Bound">x</a> <a id="23085" class="Symbol">:</a> <a id="23087" href="plfa.Equality.html#23073" class="Bound">A</a><a id="23088" class="Symbol">}</a>
  <a id="23092" class="Symbol">→</a> <a id="23094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23083" class="Bound">x</a> <a id="23096" href="plfa.Equality.html#21762" class="Function Operator">≐</a> <a id="23098" href="plfa.Equality.html#23083" class="Bound">x</a>
<a id="23100" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23061" class="Function">refl-≐</a> <a id="23107" href="plfa.Equality.html#23107" class="Bound">P</a> <a id="23109" href="plfa.Equality.html#23109" class="Bound">Px</a>  <a id="23113" class="Symbol">=</a>  <a id="23116" href="plfa.Equality.html#23109" class="Bound">Px</a>

<a id="trans-≐"></a><a id="23120" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23120" class="Function">trans-≐</a> <a id="23128" class="Symbol">:</a> <a id="23130" class="Symbol">∀</a> <a id="23132" class="Symbol">{</a><a id="23133" href="plfa.Equality.html#23133" class="Bound">A</a> <a id="23135" class="Symbol">:</a> <a id="23137" class="PrimitiveType">Set</a><a id="23140" class="Symbol">}</a> <a id="23142" class="Symbol">{</a><a id="23143" href="plfa.Equality.html#23143" class="Bound">x</a> <a id="23145" href="plfa.Equality.html#23145" class="Bound">y</a> <a id="23147" href="plfa.Equality.html#23147" class="Bound">z</a> <a id="23149" class="Symbol">:</a> <a id="23151" href="plfa.Equality.html#23133" class="Bound">A</a><a id="23152" class="Symbol">}</a>
  <a id="23156" class="Symbol">→</a> <a id="23158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23143" class="Bound">x</a> <a id="23160" href="plfa.Equality.html#21762" class="Function Operator">≐</a> <a id="23162" href="plfa.Equality.html#23145" class="Bound">y</a>
  <a id="23166" class="Symbol">→</a> <a id="23168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23145" class="Bound">y</a> <a id="23170" href="plfa.Equality.html#21762" class="Function Operator">≐</a> <a id="23172" href="plfa.Equality.html#23147" class="Bound">z</a>
    <a id="23178" class="Comment">-----</a>
  <a id="23186" class="Symbol">→</a> <a id="23188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23143" class="Bound">x</a> <a id="23190" href="plfa.Equality.html#21762" class="Function Operator">≐</a> <a id="23192" href="plfa.Equality.html#23147" class="Bound">z</a>
<a id="23194" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23120" class="Function">trans-≐</a> <a id="23202" href="plfa.Equality.html#23202" class="Bound">x≐y</a> <a id="23206" href="plfa.Equality.html#23206" class="Bound">y≐z</a> <a id="23210" href="plfa.Equality.html#23210" class="Bound">P</a> <a id="23212" href="plfa.Equality.html#23212" class="Bound">Px</a>  <a id="23216" class="Symbol">=</a>  <a id="23219" href="plfa.Equality.html#23206" class="Bound">y≐z</a> <a id="23223" href="plfa.Equality.html#23210" class="Bound">P</a> <a id="23225" class="Symbol">(</a><a id="23226" href="plfa.Equality.html#23202" class="Bound">x≐y</a> <a id="23230" href="plfa.Equality.html#23210" class="Bound">P</a> <a id="23232" href="plfa.Equality.html#23212" class="Bound">Px</a><a id="23234" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Symmetry is less obvious.  We have to show that if `P x` implies `P y`
for all predicates `P`, then the implication holds the other way round
as well:
{:/}

对称性就没有那么显然了。我们需要证明如果对于所有谓词 `P`，`P x` 蕴涵 `P y`，
那么反方向的蕴涵也成立。

{% raw %}<pre class="Agda"><a id="sym-≐"></a><a id="23475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23475" class="Function">sym-≐</a> <a id="23481" class="Symbol">:</a> <a id="23483" class="Symbol">∀</a> <a id="23485" class="Symbol">{</a><a id="23486" href="plfa.Equality.html#23486" class="Bound">A</a> <a id="23488" class="Symbol">:</a> <a id="23490" class="PrimitiveType">Set</a><a id="23493" class="Symbol">}</a> <a id="23495" class="Symbol">{</a><a id="23496" href="plfa.Equality.html#23496" class="Bound">x</a> <a id="23498" href="plfa.Equality.html#23498" class="Bound">y</a> <a id="23500" class="Symbol">:</a> <a id="23502" href="plfa.Equality.html#23486" class="Bound">A</a><a id="23503" class="Symbol">}</a>
  <a id="23507" class="Symbol">→</a> <a id="23509" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23496" class="Bound">x</a> <a id="23511" href="plfa.Equality.html#21762" class="Function Operator">≐</a> <a id="23513" href="plfa.Equality.html#23498" class="Bound">y</a>
    <a id="23519" class="Comment">-----</a>
  <a id="23527" class="Symbol">→</a> <a id="23529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23498" class="Bound">y</a> <a id="23531" href="plfa.Equality.html#21762" class="Function Operator">≐</a> <a id="23533" href="plfa.Equality.html#23496" class="Bound">x</a>
<a id="23535" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23475" class="Function">sym-≐</a> <a id="23541" class="Symbol">{</a><a id="23542" href="plfa.Equality.html#23542" class="Bound">A</a><a id="23543" class="Symbol">}</a> <a id="23545" class="Symbol">{</a><a id="23546" href="plfa.Equality.html#23546" class="Bound">x</a><a id="23547" class="Symbol">}</a> <a id="23549" class="Symbol">{</a><a id="23550" href="plfa.Equality.html#23550" class="Bound">y</a><a id="23551" class="Symbol">}</a> <a id="23553" href="plfa.Equality.html#23553" class="Bound">x≐y</a> <a id="23557" href="plfa.Equality.html#23557" class="Bound">P</a>  <a id="23560" class="Symbol">=</a>  <a id="23563" href="plfa.Equality.html#23645" class="Function">Qy</a>
  <a id="23568" class="Keyword">where</a>
    <a id="23578" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23578" class="Function">Q</a> <a id="23580" class="Symbol">:</a> <a id="23582" href="plfa.Equality.html#23542" class="Bound">A</a> <a id="23584" class="Symbol">→</a> <a id="23586" class="PrimitiveType">Set</a>
    <a id="23594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23578" class="Function">Q</a> <a id="23596" href="plfa.Equality.html#23596" class="Bound">z</a> <a id="23598" class="Symbol">=</a> <a id="23600" href="plfa.Equality.html#23557" class="Bound">P</a> <a id="23602" href="plfa.Equality.html#23596" class="Bound">z</a> <a id="23604" class="Symbol">→</a> <a id="23606" href="plfa.Equality.html#23557" class="Bound">P</a> <a id="23608" href="plfa.Equality.html#23546" class="Bound">x</a>
    <a id="23614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23614" class="Function">Qx</a> <a id="23617" class="Symbol">:</a> <a id="23619" href="plfa.Equality.html#23578" class="Function">Q</a> <a id="23621" href="plfa.Equality.html#23546" class="Bound">x</a>
    <a id="23627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23614" class="Function">Qx</a> <a id="23630" class="Symbol">=</a> <a id="23632" href="plfa.Equality.html#23061" class="Function">refl-≐</a> <a id="23639" href="plfa.Equality.html#23557" class="Bound">P</a>
    <a id="23645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23645" class="Function">Qy</a> <a id="23648" class="Symbol">:</a> <a id="23650" href="plfa.Equality.html#23578" class="Function">Q</a> <a id="23652" href="plfa.Equality.html#23550" class="Bound">y</a>
    <a id="23658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23645" class="Function">Qy</a> <a id="23661" class="Symbol">=</a> <a id="23663" href="plfa.Equality.html#23553" class="Bound">x≐y</a> <a id="23667" href="plfa.Equality.html#23578" class="Function">Q</a> <a id="23669" href="plfa.Equality.html#23614" class="Function">Qx</a>
</pre>{% endraw %}
{::comment}
Given `x ≐ y`, a specific `P`, we have to construct a proof that `P y`
implies `P x`.  To do so, we instantiate the equality with a predicate
`Q` such that `Q z` holds if `P z` implies `P x`.  The property `Q x`
is trivial by reflexivity, and hence `Q y` follows from `x ≐ y`.  But
`Q y` is exactly a proof of what we require, that `P y` implies `P x`.
{:/}

给定 `x ≐ y` 和一个特定的 `P`，我们需要构造一个 `P y` 蕴涵 `P x` 的证明。
我们首先用一个谓词 `Q` 将相等性实例化，使得 `Q z` 在 `P z` 蕴涵 `P x` 时成立。
`Q x` 这个性质是显然的，由自反性可以得出，由此通过 `x ≐ y` 就能推出 `Q y` 成立。而 `Q y`
正是我们需要的证明，即 `P y` 蕴涵 `P x`。

{::comment}
We now show that Martin Löf equality implies
Leibniz equality, and vice versa.  In the forward direction, if we know
`x ≡ y` we need for any `P` to take evidence of `P x` to evidence of `P y`,
which is easy since equality of `x` and `y` implies that any proof
of `P x` is also a proof of `P y`:
{:/}

我们现在来证明 Martin Löf 相等性蕴涵了莱布尼兹相等性，以及其逆命题。在正方向上，
如果我们已知 `x ≡ y`，我们需要对于任意的 `P`，将 `P x` 的证明转换为 `P y` 的证明。
我们很容易就可以做到这一点，因为 `x` 与 `y` 相等意味着任何 `P x` 的证明即是 `P y` 的证明。

{% raw %}<pre class="Agda"><a id="≡-implies-≐"></a><a id="24718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24718" class="Function">≡-implies-≐</a> <a id="24730" class="Symbol">:</a> <a id="24732" class="Symbol">∀</a> <a id="24734" class="Symbol">{</a><a id="24735" href="plfa.Equality.html#24735" class="Bound">A</a> <a id="24737" class="Symbol">:</a> <a id="24739" class="PrimitiveType">Set</a><a id="24742" class="Symbol">}</a> <a id="24744" class="Symbol">{</a><a id="24745" href="plfa.Equality.html#24745" class="Bound">x</a> <a id="24747" href="plfa.Equality.html#24747" class="Bound">y</a> <a id="24749" class="Symbol">:</a> <a id="24751" href="plfa.Equality.html#24735" class="Bound">A</a><a id="24752" class="Symbol">}</a>
  <a id="24756" class="Symbol">→</a> <a id="24758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24745" class="Bound">x</a> <a id="24760" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="24762" href="plfa.Equality.html#24747" class="Bound">y</a>
    <a id="24768" class="Comment">-----</a>
  <a id="24776" class="Symbol">→</a> <a id="24778" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24745" class="Bound">x</a> <a id="24780" href="plfa.Equality.html#21762" class="Function Operator">≐</a> <a id="24782" href="plfa.Equality.html#24747" class="Bound">y</a>
<a id="24784" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24718" class="Function">≡-implies-≐</a> <a id="24796" href="plfa.Equality.html#24796" class="Bound">x≡y</a> <a id="24800" href="plfa.Equality.html#24800" class="Bound">P</a>  <a id="24803" class="Symbol">=</a>  <a id="24806" href="plfa.Equality.html#6673" class="Function">subst</a> <a id="24812" href="plfa.Equality.html#24800" class="Bound">P</a> <a id="24814" href="plfa.Equality.html#24796" class="Bound">x≡y</a>
</pre>{% endraw %}
{::comment}
This direction follows from substitution, which we showed earlier.
{:/}

因为这个方向由替换性可以得来，如之前证明的那样。

{::comment}
In the reverse direction, given that for any `P` we can take a proof of `P x`
to a proof of `P y` we need to show `x ≡ y`:
{:/}

在反方向上，我们已知对于任何 `P`，我们可以将 `P x` 的证明转换成 `P y` 的证明，
我们需要证明 `x ≡ y`：

{% raw %}<pre class="Agda"><a id="≐-implies-≡"></a><a id="25145" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25145" class="Function">≐-implies-≡</a> <a id="25157" class="Symbol">:</a> <a id="25159" class="Symbol">∀</a> <a id="25161" class="Symbol">{</a><a id="25162" href="plfa.Equality.html#25162" class="Bound">A</a> <a id="25164" class="Symbol">:</a> <a id="25166" class="PrimitiveType">Set</a><a id="25169" class="Symbol">}</a> <a id="25171" class="Symbol">{</a><a id="25172" href="plfa.Equality.html#25172" class="Bound">x</a> <a id="25174" href="plfa.Equality.html#25174" class="Bound">y</a> <a id="25176" class="Symbol">:</a> <a id="25178" href="plfa.Equality.html#25162" class="Bound">A</a><a id="25179" class="Symbol">}</a>
  <a id="25183" class="Symbol">→</a> <a id="25185" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25172" class="Bound">x</a> <a id="25187" href="plfa.Equality.html#21762" class="Function Operator">≐</a> <a id="25189" href="plfa.Equality.html#25174" class="Bound">y</a>
    <a id="25195" class="Comment">-----</a>
  <a id="25203" class="Symbol">→</a> <a id="25205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25172" class="Bound">x</a> <a id="25207" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="25209" href="plfa.Equality.html#25174" class="Bound">y</a>
<a id="25211" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25145" class="Function">≐-implies-≡</a> <a id="25223" class="Symbol">{</a><a id="25224" href="plfa.Equality.html#25224" class="Bound">A</a><a id="25225" class="Symbol">}</a> <a id="25227" class="Symbol">{</a><a id="25228" href="plfa.Equality.html#25228" class="Bound">x</a><a id="25229" class="Symbol">}</a> <a id="25231" class="Symbol">{</a><a id="25232" href="plfa.Equality.html#25232" class="Bound">y</a><a id="25233" class="Symbol">}</a> <a id="25235" href="plfa.Equality.html#25235" class="Bound">x≐y</a>  <a id="25240" class="Symbol">=</a>  <a id="25243" href="plfa.Equality.html#25317" class="Function">Qy</a>
  <a id="25248" class="Keyword">where</a>
    <a id="25258" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25258" class="Function">Q</a> <a id="25260" class="Symbol">:</a> <a id="25262" href="plfa.Equality.html#25224" class="Bound">A</a> <a id="25264" class="Symbol">→</a> <a id="25266" class="PrimitiveType">Set</a>
    <a id="25274" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25258" class="Function">Q</a> <a id="25276" href="plfa.Equality.html#25276" class="Bound">z</a> <a id="25278" class="Symbol">=</a> <a id="25280" href="plfa.Equality.html#25228" class="Bound">x</a> <a id="25282" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="25284" href="plfa.Equality.html#25276" class="Bound">z</a>
    <a id="25290" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25290" class="Function">Qx</a> <a id="25293" class="Symbol">:</a> <a id="25295" href="plfa.Equality.html#25258" class="Function">Q</a> <a id="25297" href="plfa.Equality.html#25228" class="Bound">x</a>
    <a id="25303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25290" class="Function">Qx</a> <a id="25306" class="Symbol">=</a> <a id="25308" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>
    <a id="25317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25317" class="Function">Qy</a> <a id="25320" class="Symbol">:</a> <a id="25322" href="plfa.Equality.html#25258" class="Function">Q</a> <a id="25324" href="plfa.Equality.html#25232" class="Bound">y</a>
    <a id="25330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25317" class="Function">Qy</a> <a id="25333" class="Symbol">=</a> <a id="25335" href="plfa.Equality.html#25235" class="Bound">x≐y</a> <a id="25339" href="plfa.Equality.html#25258" class="Function">Q</a> <a id="25341" href="plfa.Equality.html#25290" class="Function">Qx</a>
</pre>{% endraw %}
{::comment}
The proof is similar to that for symmetry of Leibniz equality. We take
`Q` to be the predicate that holds of `z` if `x ≡ z`. Then `Q x` is
trivial by reflexivity of Martin Löf equality, and hence `Q y`
follows from `x ≐ y`.  But `Q y` is exactly a proof of what we
require, that `x ≡ y`.
{:/}

此证明与莱布尼兹相等性的对称性证明相似。我们取谓词 `Q`，使得 `Q z` 在 `x ≡ z` 成立时成立。
那么 `Q x` 是显然的，由 Martin Löf 相等性的自反性得来。从而 `Q y` 由 `x ≐ y` 可得，
而 `Q y` 即是我们所需要的 `x ≡ y` 的证明。

{::comment}
(Parts of this section are adapted from *≐≃≡: Leibniz Equality is
Isomorphic to Martin-Löf Identity, Parametrically*, by Andreas Abel,
Jesper Cockx, Dominique Devries, Andreas Nuyts, and Philip Wadler,
draft, 2017.)
{:/}

（本部分的内容由此处改编得来：
*≐≃≡: Leibniz Equality is
Isomorphic to Martin-Löf Identity, Parametrically*
作者：Andreas Abel、Jesper Cockx、Dominique Devries、Andreas Nuyts 与 Philip Wadler，
草稿，2017）


{::comment}
## Universe polymorphism {#unipoly}
{:/}

## 全体多态 {#unipoly}

{::comment}
As we have seen, not every type belongs to `Set`, but instead every
type belongs somewhere in the hierarchy `Set₀`, `Set₁`, `Set₂`, and so on,
where `Set` abbreviates `Set₀`, and `Set₀ : Set₁`, `Set₁ : Set₂`, and so on.
The definition of equality given above is fine if we want to compare two
values of a type that belongs to `Set`, but what if we want to compare
two values of a type that belongs to `Set ℓ` for some arbitrary level `ℓ`?
{:/}

正如我们之前看到的那样，不是每个类型都属于 `Set`，但是每个类型都属于类型阶级的某处，
`Set₀`、`Set₁`、`Set₂`等等。其中 `Set` 是 `Set₀` 的缩写，此外 `Set₀ : Set₁`，`Set₁ : Set₂`，以此类推。
当我们需要比较两个属于 `Set` 的类型的值时，我们之前给出的定义是足够的，
但如果我们需要比较对于任何等级 `ℓ`，两个属于 `Set ℓ` 的类型的值该怎么办呢？

{::comment}
The answer is _universe polymorphism_, where a definition is made
with respect to an arbitrary level `ℓ`. To make use of levels, we
first import the following:
{:/}

答案是*全体多态*（Universe Polymorphism），一个定义可以根据任何等级 `ℓ` 来做出。
为了使用等级，我们首先导入下列内容：

{% raw %}<pre class="Agda"><a id="27220" class="Keyword">open</a> <a id="27225" class="Keyword">import</a> <a id="27232" href="https://agda.github.io/agda-stdlib/v1.1/Level.html" class="Module">Level</a> <a id="27238" class="Keyword">using</a> <a id="27244" class="Symbol">(</a><a id="27245" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Primitive.html#408" class="Postulate">Level</a><a id="27250" class="Symbol">;</a> <a id="27252" href="Agda.Primitive.html#657" class="Primitive Operator">_⊔_</a><a id="27255" class="Symbol">)</a> <a id="27257" class="Keyword">renaming</a> <a id="27266" class="Symbol">(</a><a id="27267" href="Agda.Primitive.html#611" class="Primitive">zero</a> <a id="27272" class="Symbol">to</a> <a id="27275" href="Agda.Primitive.html#611" class="Primitive">lzero</a><a id="27280" class="Symbol">;</a> <a id="27282" href="Agda.Primitive.html#627" class="Primitive">suc</a> <a id="27286" class="Symbol">to</a> <a id="27289" href="Agda.Primitive.html#627" class="Primitive">lsuc</a><a id="27293" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
We rename constructors `zero` and `suc` to `lzero` and `lsuc` to avoid confusion
between levels and naturals.
{:/}

我们将构造器 `zero` 和 `suc` 重命名至 `lzero` 和 `lsuc`，为了防止自然数和等级之间的混淆。

{::comment}
Levels are isomorphic to natural numbers, and have similar constructors:
{:/}

等级与自然数是同构的，有相似的构造器：

    lzero : Level
    lsuc  : Level → Level

{::comment}
The names `Set₀`, `Set₁`, `Set₂`, and so on, are abbreviations for
{:/}

`Set₀`、`Set₁`、`Set₂` 等名称，是下列的简写：

    Set lzero
    Set (lsuc lzero)
    Set (lsuc (lsuc lzero))

{::comment}
and so on. There is also an operator
{:/}

以此类推。我们还有一个运算符：

    _⊔_ : Level → Level → Level

{::comment}
that given two levels returns the larger of the two.
{:/}

给定两个等级，返回两者中较大的那个。

{::comment}
Here is the definition of equality, generalised to an arbitrary level:
{:/}

下面是相等性的定义，推广到任意等级：

{% raw %}<pre class="Agda"><a id="28139" class="Keyword">data</a> <a id="_≡′_"></a><a id="28144" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28144" class="Datatype Operator">_≡′_</a> <a id="28149" class="Symbol">{</a><a id="28150" href="plfa.Equality.html#28150" class="Bound">ℓ</a> <a id="28152" class="Symbol">:</a> <a id="28154" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Primitive.html#408" class="Postulate">Level</a><a id="28159" class="Symbol">}</a> <a id="28161" class="Symbol">{</a><a id="28162" href="plfa.Equality.html#28162" class="Bound">A</a> <a id="28164" class="Symbol">:</a> <a id="28166" class="PrimitiveType">Set</a> <a id="28170" href="plfa.Equality.html#28150" class="Bound">ℓ</a><a id="28171" class="Symbol">}</a> <a id="28173" class="Symbol">(</a><a id="28174" href="plfa.Equality.html#28174" class="Bound">x</a> <a id="28176" class="Symbol">:</a> <a id="28178" href="plfa.Equality.html#28162" class="Bound">A</a><a id="28179" class="Symbol">)</a> <a id="28181" class="Symbol">:</a> <a id="28183" href="plfa.Equality.html#28162" class="Bound">A</a> <a id="28185" class="Symbol">→</a> <a id="28187" class="PrimitiveType">Set</a> <a id="28191" href="plfa.Equality.html#28150" class="Bound">ℓ</a> <a id="28193" class="Keyword">where</a>
  <a id="_≡′_.refl′"></a><a id="28201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28201" class="InductiveConstructor">refl′</a> <a id="28207" class="Symbol">:</a> <a id="28209" href="plfa.Equality.html#28174" class="Bound">x</a> <a id="28211" href="plfa.Equality.html#28144" class="Datatype Operator">≡′</a> <a id="28214" href="plfa.Equality.html#28174" class="Bound">x</a>
</pre>{% endraw %}
{::comment}
Similarly, here is the generalised definition of symmetry:
{:/}

相似的，下面是对称性的推广定义：

{% raw %}<pre class="Agda"><a id="sym′"></a><a id="28320" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28320" class="Function">sym′</a> <a id="28325" class="Symbol">:</a> <a id="28327" class="Symbol">∀</a> <a id="28329" class="Symbol">{</a><a id="28330" href="plfa.Equality.html#28330" class="Bound">ℓ</a> <a id="28332" class="Symbol">:</a> <a id="28334" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Primitive.html#408" class="Postulate">Level</a><a id="28339" class="Symbol">}</a> <a id="28341" class="Symbol">{</a><a id="28342" href="plfa.Equality.html#28342" class="Bound">A</a> <a id="28344" class="Symbol">:</a> <a id="28346" class="PrimitiveType">Set</a> <a id="28350" href="plfa.Equality.html#28330" class="Bound">ℓ</a><a id="28351" class="Symbol">}</a> <a id="28353" class="Symbol">{</a><a id="28354" href="plfa.Equality.html#28354" class="Bound">x</a> <a id="28356" href="plfa.Equality.html#28356" class="Bound">y</a> <a id="28358" class="Symbol">:</a> <a id="28360" href="plfa.Equality.html#28342" class="Bound">A</a><a id="28361" class="Symbol">}</a>
  <a id="28365" class="Symbol">→</a> <a id="28367" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28354" class="Bound">x</a> <a id="28369" href="plfa.Equality.html#28144" class="Datatype Operator">≡′</a> <a id="28372" href="plfa.Equality.html#28356" class="Bound">y</a>
    <a id="28378" class="Comment">------</a>
  <a id="28387" class="Symbol">→</a> <a id="28389" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28356" class="Bound">y</a> <a id="28391" href="plfa.Equality.html#28144" class="Datatype Operator">≡′</a> <a id="28394" href="plfa.Equality.html#28354" class="Bound">x</a>
<a id="28396" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28320" class="Function">sym′</a> <a id="28401" href="plfa.Equality.html#28201" class="InductiveConstructor">refl′</a> <a id="28407" class="Symbol">=</a> <a id="28409" href="plfa.Equality.html#28201" class="InductiveConstructor">refl′</a>
</pre>{% endraw %}
{::comment}
For simplicity, we avoid universe polymorphism in the definitions given in
the text, but most definitions in the standard library, including those for
equality, are generalised to arbitrary levels as above.
{:/}

为了简介，我们在本书中给出的定义将避免使用全体多态，但是大多数标准库中的定义，
包括相等性的定义，都推广到了任意等级，如上所示。

{::comment}
Here is the generalised definition of Leibniz equality:
{:/}

下面是莱布尼兹相等性的推广定义：

{% raw %}<pre class="Agda"><a id="_≐′_"></a><a id="28807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28807" class="Function Operator">_≐′_</a> <a id="28812" class="Symbol">:</a> <a id="28814" class="Symbol">∀</a> <a id="28816" class="Symbol">{</a><a id="28817" href="plfa.Equality.html#28817" class="Bound">ℓ</a> <a id="28819" class="Symbol">:</a> <a id="28821" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Primitive.html#408" class="Postulate">Level</a><a id="28826" class="Symbol">}</a> <a id="28828" class="Symbol">{</a><a id="28829" href="plfa.Equality.html#28829" class="Bound">A</a> <a id="28831" class="Symbol">:</a> <a id="28833" class="PrimitiveType">Set</a> <a id="28837" href="plfa.Equality.html#28817" class="Bound">ℓ</a><a id="28838" class="Symbol">}</a> <a id="28840" class="Symbol">(</a><a id="28841" href="plfa.Equality.html#28841" class="Bound">x</a> <a id="28843" href="plfa.Equality.html#28843" class="Bound">y</a> <a id="28845" class="Symbol">:</a> <a id="28847" href="plfa.Equality.html#28829" class="Bound">A</a><a id="28848" class="Symbol">)</a> <a id="28850" class="Symbol">→</a> <a id="28852" class="PrimitiveType">Set</a> <a id="28856" class="Symbol">(</a><a id="28857" href="Agda.Primitive.html#627" class="Primitive">lsuc</a> <a id="28862" href="plfa.Equality.html#28817" class="Bound">ℓ</a><a id="28863" class="Symbol">)</a>
<a id="28865" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28807" class="Function Operator">_≐′_</a> <a id="28870" class="Symbol">{</a><a id="28871" href="plfa.Equality.html#28871" class="Bound">ℓ</a><a id="28872" class="Symbol">}</a> <a id="28874" class="Symbol">{</a><a id="28875" href="plfa.Equality.html#28875" class="Bound">A</a><a id="28876" class="Symbol">}</a> <a id="28878" href="plfa.Equality.html#28878" class="Bound">x</a> <a id="28880" href="plfa.Equality.html#28880" class="Bound">y</a> <a id="28882" class="Symbol">=</a> <a id="28884" class="Symbol">∀</a> <a id="28886" class="Symbol">(</a><a id="28887" href="plfa.Equality.html#28887" class="Bound">P</a> <a id="28889" class="Symbol">:</a> <a id="28891" href="plfa.Equality.html#28875" class="Bound">A</a> <a id="28893" class="Symbol">→</a> <a id="28895" class="PrimitiveType">Set</a> <a id="28899" href="plfa.Equality.html#28871" class="Bound">ℓ</a><a id="28900" class="Symbol">)</a> <a id="28902" class="Symbol">→</a> <a id="28904" href="plfa.Equality.html#28887" class="Bound">P</a> <a id="28906" href="plfa.Equality.html#28878" class="Bound">x</a> <a id="28908" class="Symbol">→</a> <a id="28910" href="plfa.Equality.html#28887" class="Bound">P</a> <a id="28912" href="plfa.Equality.html#28880" class="Bound">y</a>
</pre>{% endraw %}
{::comment}
Before the signature used `Set₁` as the type of a term that includes
`Set`, whereas here the signature uses `Set (lsuc ℓ)` as the type of a
term that includes `Set ℓ`.
{:/}

之前，签名中使用了 `Set₁` 来作为一个值包括了 `Set` 的类型；而此处，我们使用
`Set (lsuc ℓ)` 来作为一个值包括了 `Set ℓ` 的类型。

{::comment}
Further information on levels can be found in the [Agda Wiki][wiki].
{:/}

更多的关于等级的信息可以从[Agda 维基（英文）][wiki]中查询。

[wiki]: http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.UniversePolymorphism


{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the
standard library:
{:/}

标准库中可以找到与本章节中相似的定义：

{% raw %}<pre class="Agda"><a id="29583" class="Comment">-- import Relation.Binary.PropositionalEquality as Eq</a>
<a id="29637" class="Comment">-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)</a>
<a id="29701" class="Comment">-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)</a>
</pre>{% endraw %}
{::comment}
Here the imports are shown as comments rather than code to avoid
collisions, as mentioned in the introduction.
{:/}

这里的导入以注释的形式给出，以防止冲突，如引言中解释的那样。


## Unicode

{::comment}
This chapter uses the following unicode:

    ≡  U+2261  IDENTICAL TO (\==, \equiv)
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)
    ≐  U+2250  APPROACHES THE LIMIT (\.=)
    ℓ  U+2113  SCRIPT SMALL L (\ell)
    ⊔  U+2294  SQUARE CUP (\lub)
    ₀  U+2080  SUBSCRIPT ZERO (\_0)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
{:/}

本章节使用下列 Unicode：

    ≡  U+2261  等同于 (\==, \equiv)
    ⟨  U+27E8  数学左尖括号 (\<)
    ⟩  U+27E9  数学右尖括号 (\>)
    ∎  U+220E  证毕 (\qed)
    ≐  U+2250  接近于极限 (\.=)
    ℓ  U+2113  手写小写 L (\ell)
    ⊔  U+2294  正方形向上开口 (\lub)
    ₀  U+2080  下标 0 (\_0)
    ₁  U+2081  下标 1 (\_1)
    ₂  U+2082  下标 2 (\_2)
