---
src: ./src/plfa/Relations.lagda.md
title     : "Relations: 关系的归纳定义"
layout    : page
prev      : /Induction/
permalink : /Relations/
next      : /Equality/
translators : ["Fangyi Zhou"]
progress  : 100
---

{% raw %}<pre class="Agda"><a id="181" class="Keyword">module</a> <a id="188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}" class="Module">plfa.Relations</a> <a id="203" class="Keyword">where</a>
</pre>{% endraw %}
{::comment}
After having defined operations such as addition and multiplication,
the next step is to define relations, such as _less than or equal_.
{:/}

在定义了加法和乘法等运算以后，下一步我们来定义**关系（Relation）**，比如说**小于等于**。


{::comment}
## Imports
{:/}

## 导入

{% raw %}<pre class="Agda"><a id="464" class="Keyword">import</a> <a id="471" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="509" class="Symbol">as</a> <a id="512" class="Module">Eq</a>
<a id="515" class="Keyword">open</a> <a id="520" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="523" class="Keyword">using</a> <a id="529" class="Symbol">(</a><a id="530" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="533" class="Symbol">;</a> <a id="535" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="539" class="Symbol">;</a> <a id="541" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="545" class="Symbol">)</a>
<a id="547" class="Keyword">open</a> <a id="552" class="Keyword">import</a> <a id="559" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="568" class="Keyword">using</a> <a id="574" class="Symbol">(</a><a id="575" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="576" class="Symbol">;</a> <a id="578" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="582" class="Symbol">;</a> <a id="584" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="587" class="Symbol">;</a> <a id="589" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="592" class="Symbol">)</a>
<a id="594" class="Keyword">open</a> <a id="599" class="Keyword">import</a> <a id="606" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="626" class="Keyword">using</a> <a id="632" class="Symbol">(</a><a id="633" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="639" class="Symbol">)</a>
</pre>{% endraw %}

{::comment}
## Defining relations
{:/}

## 定义关系

{::comment}
The relation _less than or equal_ has an infinite number of
instances.  Here are a few of them:
{:/}

小于等于这个关系有无穷个实例，如下所示：


    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

{::comment}
And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:
{:/}

但是，我们仍然可以用几行有限的定义来表示所有的实例，如下文所示的一对推理规则：

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

{::comment}
And here is the definition in Agda:
{:/}

以及其 Agda 定义：

{% raw %}<pre class="Agda"><a id="1456" class="Keyword">data</a> <a id="_≤_"></a><a id="1461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1461" class="Datatype Operator">_≤_</a> <a id="1465" class="Symbol">:</a> <a id="1467" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="1469" class="Symbol">→</a> <a id="1471" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="1473" class="Symbol">→</a> <a id="1475" class="PrimitiveType">Set</a> <a id="1479" class="Keyword">where</a>

  <a id="_≤_.z≤n"></a><a id="1488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1488" class="InductiveConstructor">z≤n</a> <a id="1492" class="Symbol">:</a> <a id="1494" class="Symbol">∀</a> <a id="1496" class="Symbol">{</a><a id="1497" href="plfa.Relations.html#1497" class="Bound">n</a> <a id="1499" class="Symbol">:</a> <a id="1501" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1502" class="Symbol">}</a>
      <a id="1510" class="Comment">--------</a>
    <a id="1523" class="Symbol">→</a> <a id="1525" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="1530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1461" class="Datatype Operator">≤</a> <a id="1532" href="plfa.Relations.html#1497" class="Bound">n</a>

  <a id="_≤_.s≤s"></a><a id="1537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1537" class="InductiveConstructor">s≤s</a> <a id="1541" class="Symbol">:</a> <a id="1543" class="Symbol">∀</a> <a id="1545" class="Symbol">{</a><a id="1546" href="plfa.Relations.html#1546" class="Bound">m</a> <a id="1548" href="plfa.Relations.html#1548" class="Bound">n</a> <a id="1550" class="Symbol">:</a> <a id="1552" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1553" class="Symbol">}</a>
    <a id="1559" class="Symbol">→</a> <a id="1561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1546" class="Bound">m</a> <a id="1563" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="1565" href="plfa.Relations.html#1548" class="Bound">n</a>
      <a id="1573" class="Comment">-------------</a>
    <a id="1591" class="Symbol">→</a> <a id="1593" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1546" class="Bound">m</a> <a id="1599" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="1601" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1605" href="plfa.Relations.html#1548" class="Bound">n</a>
</pre>{% endraw %}
{::comment}
Here `z≤n` and `s≤s` (with no spaces) are constructor names, while
`zero ≤ n`, and `m ≤ n` and `suc m ≤ suc n` (with spaces) are types.
This is our first use of an _indexed_ datatype, where the type `m ≤ n`
is indexed by two naturals, `m` and `n`.  In Agda any line beginning
with two or more dashes is a comment, and here we have exploited that
convention to write our Agda code in a form that resembles the
corresponding inference rules, a trick we will use often from now on.
{:/}

在这里，`z≤n` 和 `s≤s`（无空格）是构造器的名称，`zero ≤ n`、`m ≤ n` 和
`suc m ≤ suc n` （带空格）是类型。在这里我们第一次用到了
**索引数据类型（Indexed datatype）**。我们使用 `m` 和 `n` 这两个自然数来索引
`m ≤ n` 这个类型。在 Agda 里，由两个及以上短横线开始的行是注释行，
我们巧妙利用这一语法特性，用上述形式来表示相应的推理规则。
在后文中，我们还会继续使用这一形式。

{::comment}
Both definitions above tell us the same two things:

* _Base case_: for all naturals `n`, the proposition `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.
{:/}

这两条定义告诉我们相同的两件事：

* **起始步骤**: 对于所有的自然数 `n`，命题 `zero ≤ n` 成立。
* **归纳步骤**：对于所有的自然数 `m` 和 `n`，如果命题 `m ≤ n` 成立，
  那么命题 `suc m ≤ suc n` 成立。

{::comment}
In fact, they each give us a bit more detail:

* _Base case_: for all naturals `n`, the constructor `z≤n`
  produces evidence that `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.
{:/}

实际上，他们分别给我们更多的信息：

* **起始步骤**: 对于所有的自然数 `n`，构造器 `z≤n` 提供了 `zero ≤ n` 成立的证明。
* **归纳步骤**：对于所有的自然数 `m` 和 `n`，构造器 `s≤s` 将 `m ≤ n` 成立的证明
  转化为 `suc m ≤ suc n` 成立的证明。

{::comment}
For example, here in inference rule notation is the proof that
`2 ≤ 4`:
{:/}

例如，我们在这里以推理规则的形式写出 `2 ≤ 4` 的证明：

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

{::comment}
And here is the corresponding Agda proof:
{:/}

下面是对应的 Agda 证明：

{% raw %}<pre class="Agda"><a id="3535" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3535" class="Function">_</a> <a id="3537" class="Symbol">:</a> <a id="3539" class="Number">2</a> <a id="3541" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="3543" class="Number">4</a>
<a id="3545" class="Symbol">_</a> <a id="3547" class="Symbol">=</a> <a id="3549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1537" class="InductiveConstructor">s≤s</a> <a id="3553" class="Symbol">(</a><a id="3554" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="3558" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a><a id="3561" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
## Implicit arguments
{:/}

## 隐式参数

{::comment}
This is our first use of implicit arguments.  In the definition of
inequality, the two lines defining the constructors use `∀`, very
similar to our use of `∀` in propositions such as:
{:/}

这是我们第一次使用隐式参数。定义不等式时，构造器的定义中使用了 `∀`，
就像我们在下面的命题中使用 `∀` 一样：

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

{::comment}
However, here the declarations are surrounded by curly braces `{ }`
rather than parentheses `( )`.  This means that the arguments are
_implicit_ and need not be written explicitly; instead, they are
_inferred_ by Agda's typechecker. Thus, we write `+-comm m n` for the
proof that `m + n ≡ n + m`, but `z≤n` for the proof that `zero ≤ n`,
leaving `n` implicit.  Similarly, if `m≤n` is evidence that `m ≤ n`,
we write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving both `m`
and `n` implicit.
{:/}

但是我们这里的定义使用了花括号 `{ }`，而不是小括号 `( )`。
这意味着参数是**隐式的（Implicit）**，不需要额外声明。实际上，Agda 的类型检查器
会**推导（Infer）**出它们。因此，我们在 `m + n ≡ n + m` 的证明中需要写出 `+-comm m n`，
在 `zero ≤ n` 的证明中可以省略 `n`。同理，如果 `m≤n` 是 `m ≤ n`的证明，
那么我们写出 `s≤s m≤n` 作为 `suc m ≤ suc n` 的证明，无需声明 `m` 和 `n`。

{::comment}
If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit:
{:/}

如果有希望的话，我们也可以在大括号里显式声明隐式参数。例如，下面是 `2 ≤ 4` 的 Agda
证明，包括了显式声明了的隐式参数：

{% raw %}<pre class="Agda"><a id="5001" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5001" class="Function">_</a> <a id="5003" class="Symbol">:</a> <a id="5005" class="Number">2</a> <a id="5007" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="5009" class="Number">4</a>
<a id="5011" class="Symbol">_</a> <a id="5013" class="Symbol">=</a> <a id="5015" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1537" class="InductiveConstructor">s≤s</a> <a id="5019" class="Symbol">{</a><a id="5020" class="Number">1</a><a id="5021" class="Symbol">}</a> <a id="5023" class="Symbol">{</a><a id="5024" class="Number">3</a><a id="5025" class="Symbol">}</a> <a id="5027" class="Symbol">(</a><a id="5028" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="5032" class="Symbol">{</a><a id="5033" class="Number">0</a><a id="5034" class="Symbol">}</a> <a id="5036" class="Symbol">{</a><a id="5037" class="Number">2</a><a id="5038" class="Symbol">}</a> <a id="5040" class="Symbol">(</a><a id="5041" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a> <a id="5045" class="Symbol">{</a><a id="5046" class="Number">2</a><a id="5047" class="Symbol">}))</a>
</pre>{% endraw %}
{::comment}
One may also identify implicit arguments by name:
{:/}

也可以额外加上参数的名字：

{% raw %}<pre class="Agda"><a id="5143" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5143" class="Function">_</a> <a id="5145" class="Symbol">:</a> <a id="5147" class="Number">2</a> <a id="5149" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="5151" class="Number">4</a>
<a id="5153" class="Symbol">_</a> <a id="5155" class="Symbol">=</a> <a id="5157" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1537" class="InductiveConstructor">s≤s</a> <a id="5161" class="Symbol">{</a><a id="5162" class="Argument">m</a> <a id="5164" class="Symbol">=</a> <a id="5166" class="Number">1</a><a id="5167" class="Symbol">}</a> <a id="5169" class="Symbol">{</a><a id="5170" class="Argument">n</a> <a id="5172" class="Symbol">=</a> <a id="5174" class="Number">3</a><a id="5175" class="Symbol">}</a> <a id="5177" class="Symbol">(</a><a id="5178" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="5182" class="Symbol">{</a><a id="5183" class="Argument">m</a> <a id="5185" class="Symbol">=</a> <a id="5187" class="Number">0</a><a id="5188" class="Symbol">}</a> <a id="5190" class="Symbol">{</a><a id="5191" class="Argument">n</a> <a id="5193" class="Symbol">=</a> <a id="5195" class="Number">2</a><a id="5196" class="Symbol">}</a> <a id="5198" class="Symbol">(</a><a id="5199" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a> <a id="5203" class="Symbol">{</a><a id="5204" class="Argument">n</a> <a id="5206" class="Symbol">=</a> <a id="5208" class="Number">2</a><a id="5209" class="Symbol">}))</a>
</pre>{% endraw %}
{::comment}
In the latter format, you may only supply some implicit arguments:
{:/}

在后者的形式中，也可以只声明一部分隐式参数：

{% raw %}<pre class="Agda"><a id="5331" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5331" class="Function">_</a> <a id="5333" class="Symbol">:</a> <a id="5335" class="Number">2</a> <a id="5337" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="5339" class="Number">4</a>
<a id="5341" class="Symbol">_</a> <a id="5343" class="Symbol">=</a> <a id="5345" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1537" class="InductiveConstructor">s≤s</a> <a id="5349" class="Symbol">{</a><a id="5350" class="Argument">n</a> <a id="5352" class="Symbol">=</a> <a id="5354" class="Number">3</a><a id="5355" class="Symbol">}</a> <a id="5357" class="Symbol">(</a><a id="5358" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="5362" class="Symbol">{</a><a id="5363" class="Argument">n</a> <a id="5365" class="Symbol">=</a> <a id="5367" class="Number">2</a><a id="5368" class="Symbol">}</a> <a id="5370" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a><a id="5373" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
It is not permitted to swap implicit arguments, even when named.
{:/}

但是不可以改变隐式参数的顺序，即便加上了名字。


{::comment}
## Precedence
{:/}

## 优先级

{::comment}
We declare the precedence for comparison as follows:
{:/}

我们如下定义比较的优先级：

{% raw %}<pre class="Agda"><a id="5619" class="Keyword">infix</a> <a id="5625" class="Number">4</a> <a id="5627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1461" class="Datatype Operator">_≤_</a>
</pre>{% endraw %}
{::comment}
We set the precedence of `_≤_` at level 4, so it binds less tightly
than `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.
{:/}

我们将 `_≤_` 的优先级设置为 4，所以它比优先级为 6 的 `_+_` 结合的更紧，此外，
`1 + 2 ≤ 3` 将被解析为 `(1 + 2) ≤ 3`。我们用 `infix` 来表示运算符既不是左结合的，
也不是右结合的。因为 `1 ≤ 2 ≤ 3` 解析为 `(1 ≤ 2) ≤ 3` 或者 `1 ≤ (2 ≤ 3)` 都没有意义。


{::comment}
## Decidability
{:/}

## 可决定性

{::comment}
Given two numbers, it is straightforward to compute whether or not the
first is less than or equal to the second.  We don't give the code for
doing so here, but will return to this point in
Chapter [Decidable][plfa.Decidable].
{:/}

给定两个数，我们可以很直接地决定第一个数是不是小于等于第二个数。我们在此处不给出说明的代码，
但我们会在 [Decidable][plfa.Decidable] 章节重新讨论这个问题。


{::comment}
## Inversion
{:/}

## 反演

{::comment}
In our defintions, we go from smaller things to larger things.
For instance, form `m ≤ n` we can conclude `suc m ≤ suc n`,
where `suc m` is bigger than `m` (that is, the former contains
the latter), and `suc n` is bigger than `n`. But sometimes we
want to go from bigger things to smaller things.
{:/}

在我们的定义中，我们从更小的东西得到更大的东西。例如，我们可以从
`m ≤ n` 得出 `suc m ≤ suc n` 的结论，这里的 `suc m` 比 `m` 更大
（也就是说，前者包含后者），`suc n` 也比 `n` 更大。但有时我们也
需要从更大的东西得到更小的东西。

{::comment}
There is only one way to prove that `suc m ≤ suc n`, for any `m`
and `n`.  This lets us invert our previous rule.
{:/}

只有一种方式能够证明对于任意 `m` 和 `n` 有 `suc m ≤ suc n`。
这让我们能够反演（invert）之前的规则。

{% raw %}<pre class="Agda"><a id="inv-s≤s"></a><a id="7227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7227" class="Function">inv-s≤s</a> <a id="7235" class="Symbol">:</a> <a id="7237" class="Symbol">∀</a> <a id="7239" class="Symbol">{</a><a id="7240" href="plfa.Relations.html#7240" class="Bound">m</a> <a id="7242" href="plfa.Relations.html#7242" class="Bound">n</a> <a id="7244" class="Symbol">:</a> <a id="7246" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="7247" class="Symbol">}</a>
  <a id="7251" class="Symbol">→</a> <a id="7253" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7240" class="Bound">m</a> <a id="7259" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="7261" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7265" href="plfa.Relations.html#7242" class="Bound">n</a>
    <a id="7271" class="Comment">-------------</a>
  <a id="7287" class="Symbol">→</a> <a id="7289" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7240" class="Bound">m</a> <a id="7291" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="7293" href="plfa.Relations.html#7242" class="Bound">n</a>
<a id="7295" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7227" class="Function">inv-s≤s</a> <a id="7303" class="Symbol">(</a><a id="7304" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="7308" href="plfa.Relations.html#7308" class="Bound">m≤n</a><a id="7311" class="Symbol">)</a> <a id="7313" class="Symbol">=</a> <a id="7315" href="plfa.Relations.html#7308" class="Bound">m≤n</a>
</pre>{% endraw %}
{::comment}
Not every rule is invertible; indeed, the rule for `z≤n` has
no non-implicit hypotheses, so there is nothing to invert.
But often inversions of this kind hold.
{:/}

并不是所有规则都可以反演。实际上，`z≤n` 的规则没有非隐式的假设，
因此它没有可以被反演的规则。但这种反演通常是成立的。

{::comment}
Another example of inversion is showing that there is
only one way a number can be less than or equal to zero.
{:/}

反演的另一个例子是证明只存在一种情况使得一个数字能够小于或等于零。

{% raw %}<pre class="Agda"><a id="inv-z≤n"></a><a id="7734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7734" class="Function">inv-z≤n</a> <a id="7742" class="Symbol">:</a> <a id="7744" class="Symbol">∀</a> <a id="7746" class="Symbol">{</a><a id="7747" href="plfa.Relations.html#7747" class="Bound">m</a> <a id="7749" class="Symbol">:</a> <a id="7751" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="7752" class="Symbol">}</a>
  <a id="7756" class="Symbol">→</a> <a id="7758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7747" class="Bound">m</a> <a id="7760" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="7762" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
    <a id="7771" class="Comment">--------</a>
  <a id="7782" class="Symbol">→</a> <a id="7784" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7747" class="Bound">m</a> <a id="7786" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="7788" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
<a id="7793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7734" class="Function">inv-z≤n</a> <a id="7801" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a> <a id="7805" class="Symbol">=</a> <a id="7807" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
## Properties of ordering relations
{:/}

## 序关系的性质

{::comment}
Relations pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Reflexive_. For all `n`, the relation `n ≤ n` holds.
* _Transitive_. For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
* _Anti-symmetric_. For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
* _Total_. For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.
{:/}

数学家对于关系的常见性质给出了约定的名称。

* **自反（Reflexive）**：对于所有的 `n`，关系 `n ≤ n` 成立。
* **传递（Transitive）**：对于所有的 `m`、 `n` 和 `p`，如果 `m ≤ n` 和 `n ≤ p`
  成立，那么 `m ≤ p` 也成立。
* **反对称（Anti-symmetric）**：对于所有的 `m` 和 `n`，如果 `m ≤ n` 和 `n ≤ m`
  同时成立，那么 `m ≡ n` 成立。
* **完全（Total）**：对于所有的 `m` 和 `n`，`m ≤ n` 或者 `n ≤ m` 成立。

{::comment}
The relation `_≤_` satisfies all four of these properties.
{:/}

`_≤_` 关系满足上述四条性质。

{::comment}
There are also names for some combinations of these properties.

* _Preorder_. Any relation that is reflexive and transitive.
* _Partial order_. Any preorder that is also anti-symmetric.
* _Total order_. Any partial order that is also total.
{:/}

对于上述性质的组合也有约定的名称。

* **预序（Preorder）**：满足自反和传递的关系。
* **偏序（Partial Order）**：满足反对称的预序。
* **全序（Total Order）**：满足完全的偏序。

{::comment}
If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.
{:/}

如果你进入了关于关系的聚会，你现在知道怎么样和人讨论了，可以讨论关于自反、传递、反对称和完全，
或者问一问这是不是预序、偏序或者全序。

{::comment}
Less frivolously, if you ever bump into a relation while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it is a preorder, partial order, or total order.  A
careful author will often call out these properties---or their
lack---for instance by saying that a newly introduced relation is a
partial order but not a total order.
{:/}

更认真的来说，如果你在阅读论文时碰到了一个关系，本文的介绍让你可以对关系有基本的了解和判断，
来判断这个关系是不是预序、偏序或者全序。一个认真的作者一般会在文章指出这个关系具有（或者缺少）
上述性质，比如说指出新定义的关系是一个偏序而不是全序。

{::comment}
#### Exercise `orderings` {#orderings}
{:/}

#### 练习 `orderings` {#orderings}

{::comment}
Give an example of a preorder that is not a partial order.
{:/}

给出一个不是偏序的预序的例子。

{::comment}
{% raw %}<pre class="Agda"><a id="10128" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="10165" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
Give an example of a partial order that is not a total order.
{:/}

给出一个不是全序的偏序的例子。

{::comment}
{% raw %}<pre class="Agda"><a id="10296" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="10333" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
## Reflexivity
{:/}

## 自反性

{::comment}
The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.  We follow the
convention in the standard library and make the argument implicit,
as that will make it easier to invoke reflexivity:
{:/}

我们第一个来证明的性质是自反性：对于任意自然数 `n`，关系 `n ≤ n` 成立。我们使用标准库
的惯例来隐式申明参数，在使用自反性的证明时这样可以更加方便。

{% raw %}<pre class="Agda"><a id="≤-refl"></a><a id="10749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10749" class="Function">≤-refl</a> <a id="10756" class="Symbol">:</a> <a id="10758" class="Symbol">∀</a> <a id="10760" class="Symbol">{</a><a id="10761" href="plfa.Relations.html#10761" class="Bound">n</a> <a id="10763" class="Symbol">:</a> <a id="10765" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10766" class="Symbol">}</a>
    <a id="10772" class="Comment">-----</a>
  <a id="10780" class="Symbol">→</a> <a id="10782" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10761" class="Bound">n</a> <a id="10784" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="10786" href="plfa.Relations.html#10761" class="Bound">n</a>
<a id="10788" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10749" class="Function">≤-refl</a> <a id="10795" class="Symbol">{</a><a id="10796" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="10800" class="Symbol">}</a> <a id="10802" class="Symbol">=</a> <a id="10804" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>
<a id="10808" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10749" class="Function">≤-refl</a> <a id="10815" class="Symbol">{</a><a id="10816" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="10820" href="plfa.Relations.html#10820" class="Bound">n</a><a id="10821" class="Symbol">}</a> <a id="10823" class="Symbol">=</a> <a id="10825" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="10829" href="plfa.Relations.html#10749" class="Function">≤-refl</a>
</pre>{% endraw %}
{::comment}
The proof is a straightforward induction on the implicit argument `n`.
In the base case, `zero ≤ zero` holds by `z≤n`.  In the inductive
case, the inductive hypothesis `≤-refl {n}` gives us a proof of `n ≤
n`, and applying `s≤s` to that yields a proof of `suc n ≤ suc n`.
{:/}

这个证明直接在 `n` 上进行归纳。在起始步骤中，`zero ≤ zero` 由 `z≤n` 证明；在归纳步骤中，
归纳假设 `≤-refl {n}` 给我们带来了 `n ≤ n` 的证明，我们只需要使用 `s≤s`，就可以获得
`suc n ≤ suc n` 的证明。

{::comment}
It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.
{:/}

在 Emacs 中来交互式地证明自反性是一个很好的练习，可以使用洞，以及 `C-c C-c`、
`C-c C-,` 和 `C-c C-r` 命令。


{::comment}
## Transitivity
{:/}

## 传递性

{::comment}
The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤ p`
hold, then `m ≤ p` holds.  Again, `m`, `n`, and `p` are implicit:
{:/}

我们第二个证明的性质是传递性：对于任意自然数 `m` 和 `n`，如果 `m ≤ n` 和 `n ≤ p`
成立，那么 `m ≤ p` 成立。同样，`m`、`n` 和 `p` 是隐式参数：

{% raw %}<pre class="Agda"><a id="≤-trans"></a><a id="11852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11852" class="Function">≤-trans</a> <a id="11860" class="Symbol">:</a> <a id="11862" class="Symbol">∀</a> <a id="11864" class="Symbol">{</a><a id="11865" href="plfa.Relations.html#11865" class="Bound">m</a> <a id="11867" href="plfa.Relations.html#11867" class="Bound">n</a> <a id="11869" href="plfa.Relations.html#11869" class="Bound">p</a> <a id="11871" class="Symbol">:</a> <a id="11873" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11874" class="Symbol">}</a>
  <a id="11878" class="Symbol">→</a> <a id="11880" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11865" class="Bound">m</a> <a id="11882" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="11884" href="plfa.Relations.html#11867" class="Bound">n</a>
  <a id="11888" class="Symbol">→</a> <a id="11890" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11867" class="Bound">n</a> <a id="11892" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="11894" href="plfa.Relations.html#11869" class="Bound">p</a>
    <a id="11900" class="Comment">-----</a>
  <a id="11908" class="Symbol">→</a> <a id="11910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11865" class="Bound">m</a> <a id="11912" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="11914" href="plfa.Relations.html#11869" class="Bound">p</a>
<a id="11916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11852" class="Function">≤-trans</a> <a id="11924" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>       <a id="11934" class="Symbol">_</a>          <a id="11945" class="Symbol">=</a>  <a id="11948" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>
<a id="11952" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11852" class="Function">≤-trans</a> <a id="11960" class="Symbol">(</a><a id="11961" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="11965" href="plfa.Relations.html#11965" class="Bound">m≤n</a><a id="11968" class="Symbol">)</a> <a id="11970" class="Symbol">(</a><a id="11971" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="11975" href="plfa.Relations.html#11975" class="Bound">n≤p</a><a id="11978" class="Symbol">)</a>  <a id="11981" class="Symbol">=</a>  <a id="11984" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="11988" class="Symbol">(</a><a id="11989" href="plfa.Relations.html#11852" class="Function">≤-trans</a> <a id="11997" href="plfa.Relations.html#11965" class="Bound">m≤n</a> <a id="12001" href="plfa.Relations.html#11975" class="Bound">n≤p</a><a id="12004" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Here the proof is by induction on the _evidence_ that `m ≤ n`.  In the
base case, the first inequality holds by `z≤n` and must show `zero ≤
p`, which follows immediately by `z≤n`.  In this case, the fact that
`n ≤ p` is irrelevant, and we write `_` as the pattern to indicate
that the corresponding evidence is unused.
{:/}

这里我们在 `m ≤ n` 的**证据（Evidence）**上进行归纳。在起始步骤里，第一个不等式因为 `z≤n` 而成立，
那么结论亦可由 `z≤n` 而得出。在这里，`n ≤ p` 的证明是不需要的，我们用 `_` 来表示这个
证明没有被使用。

{::comment}
In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.
{:/}

在归纳步骤中，第一个不等式因为 `s≤s m≤n` 而成立，第二个不等式因为 `s≤s n≤p` 而成立，
所以我们已知 `suc m ≤ suc n` 和 `suc n ≤ suc p`，求证 `suc m ≤ suc p`。
通过归纳假设 `≤-trans m≤n n≤p`，我们得知 `m ≤ p`，在此之上使用 `s≤s` 即可证。

{::comment}
The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that such a
case cannot arise, and does not require (or permit) it to be listed.
{:/}

`≤-trans (s≤s m≤n) z≤n` 不可能发生，因为第一个不等式告诉我们中间的数是一个 `suc n`，
而第二个不等式告诉我们中间的书是 `zero`。Agda 可以推断这样的情况不可能发现，所以我们不需要
（也不可以）列出这种情况。

{::comment}
Alternatively, we could make the implicit parameters explicit:
{:/}

我们也可以将隐式参数显式地声明。

{% raw %}<pre class="Agda"><a id="≤-trans′"></a><a id="13478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13478" class="Function">≤-trans′</a> <a id="13487" class="Symbol">:</a> <a id="13489" class="Symbol">∀</a> <a id="13491" class="Symbol">(</a><a id="13492" href="plfa.Relations.html#13492" class="Bound">m</a> <a id="13494" href="plfa.Relations.html#13494" class="Bound">n</a> <a id="13496" href="plfa.Relations.html#13496" class="Bound">p</a> <a id="13498" class="Symbol">:</a> <a id="13500" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="13501" class="Symbol">)</a>
  <a id="13505" class="Symbol">→</a> <a id="13507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13492" class="Bound">m</a> <a id="13509" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="13511" href="plfa.Relations.html#13494" class="Bound">n</a>
  <a id="13515" class="Symbol">→</a> <a id="13517" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13494" class="Bound">n</a> <a id="13519" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="13521" href="plfa.Relations.html#13496" class="Bound">p</a>
    <a id="13527" class="Comment">-----</a>
  <a id="13535" class="Symbol">→</a> <a id="13537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13492" class="Bound">m</a> <a id="13539" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="13541" href="plfa.Relations.html#13496" class="Bound">p</a>
<a id="13543" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13478" class="Function">≤-trans′</a> <a id="13552" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="13560" class="Symbol">_</a>       <a id="13568" class="Symbol">_</a>       <a id="13576" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>       <a id="13586" class="Symbol">_</a>          <a id="13597" class="Symbol">=</a>  <a id="13600" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>
<a id="13604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13478" class="Function">≤-trans′</a> <a id="13613" class="Symbol">(</a><a id="13614" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13618" href="plfa.Relations.html#13618" class="Bound">m</a><a id="13619" class="Symbol">)</a> <a id="13621" class="Symbol">(</a><a id="13622" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13626" href="plfa.Relations.html#13626" class="Bound">n</a><a id="13627" class="Symbol">)</a> <a id="13629" class="Symbol">(</a><a id="13630" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13634" href="plfa.Relations.html#13634" class="Bound">p</a><a id="13635" class="Symbol">)</a> <a id="13637" class="Symbol">(</a><a id="13638" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="13642" href="plfa.Relations.html#13642" class="Bound">m≤n</a><a id="13645" class="Symbol">)</a> <a id="13647" class="Symbol">(</a><a id="13648" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="13652" href="plfa.Relations.html#13652" class="Bound">n≤p</a><a id="13655" class="Symbol">)</a>  <a id="13658" class="Symbol">=</a>  <a id="13661" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="13665" class="Symbol">(</a><a id="13666" href="plfa.Relations.html#13478" class="Function">≤-trans′</a> <a id="13675" href="plfa.Relations.html#13618" class="Bound">m</a> <a id="13677" href="plfa.Relations.html#13626" class="Bound">n</a> <a id="13679" href="plfa.Relations.html#13634" class="Bound">p</a> <a id="13681" href="plfa.Relations.html#13642" class="Bound">m≤n</a> <a id="13685" href="plfa.Relations.html#13652" class="Bound">n≤p</a><a id="13688" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.
{:/}

有人说这样的证明更加的清晰，也有人说这个更长的证明让人难以抓住证明的重点。
我们一般选择使用简短的证明。

{::comment}
The technique of induction on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on
values of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.
{:/}

对于性质成立证明进行的归纳（如上文中对于 `m ≤ n` 的证明进行归纳），相比于对于性质成立的值进行的归纳
（如对于 `m` 进行归纳），有非常大的价值。我们会经常使用这样的方法。

{::comment}
Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.
{:/}

同样，在 Emacs 中来交互式地证明传递性是一个很好的练习，可以使用洞，以及 `C-c C-c`、
`C-c C-,` 和 `C-c C-r` 命令。


{::comment}
## Anti-symmetry
{:/}

## 反对称性

{::comment}
The third property to prove about comparison is that it is
antisymmetric: for all naturals `m` and `n`, if both `m ≤ n` and `n ≤
m` hold, then `m ≡ n` holds:
{:/}

我们证明的第三个性质是反对称性：对于所有的自然数 `m` 和 `n`，如果 `m ≤ n` 和 `n ≤ m`
同时成立，那么 `m ≡ n` 成立：

{% raw %}<pre class="Agda"><a id="≤-antisym"></a><a id="14831" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14831" class="Function">≤-antisym</a> <a id="14841" class="Symbol">:</a> <a id="14843" class="Symbol">∀</a> <a id="14845" class="Symbol">{</a><a id="14846" href="plfa.Relations.html#14846" class="Bound">m</a> <a id="14848" href="plfa.Relations.html#14848" class="Bound">n</a> <a id="14850" class="Symbol">:</a> <a id="14852" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="14853" class="Symbol">}</a>
  <a id="14857" class="Symbol">→</a> <a id="14859" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14846" class="Bound">m</a> <a id="14861" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="14863" href="plfa.Relations.html#14848" class="Bound">n</a>
  <a id="14867" class="Symbol">→</a> <a id="14869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14848" class="Bound">n</a> <a id="14871" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="14873" href="plfa.Relations.html#14846" class="Bound">m</a>
    <a id="14879" class="Comment">-----</a>
  <a id="14887" class="Symbol">→</a> <a id="14889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14846" class="Bound">m</a> <a id="14891" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="14893" href="plfa.Relations.html#14848" class="Bound">n</a>
<a id="14895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14831" class="Function">≤-antisym</a> <a id="14905" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>       <a id="14915" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>        <a id="14926" class="Symbol">=</a>  <a id="14929" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="14934" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14831" class="Function">≤-antisym</a> <a id="14944" class="Symbol">(</a><a id="14945" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="14949" href="plfa.Relations.html#14949" class="Bound">m≤n</a><a id="14952" class="Symbol">)</a> <a id="14954" class="Symbol">(</a><a id="14955" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="14959" href="plfa.Relations.html#14959" class="Bound">n≤m</a><a id="14962" class="Symbol">)</a>  <a id="14965" class="Symbol">=</a>  <a id="14968" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="14973" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14977" class="Symbol">(</a><a id="14978" href="plfa.Relations.html#14831" class="Function">≤-antisym</a> <a id="14988" href="plfa.Relations.html#14949" class="Bound">m≤n</a> <a id="14992" href="plfa.Relations.html#14959" class="Bound">n≤m</a><a id="14995" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold.
{:/}

同样，我们对于 `m ≤ n` 和 `n ≤ m` 的证明进行归纳。

{::comment}
In the base case, both inequalities hold by `z≤n`, and so we are given
`zero ≤ zero` and `zero ≤ zero` and must show `zero ≡ zero`, which
follows by reflexivity.  (Reflexivity of equality, that is, not
reflexivity of inequality.)
{:/}

在起始步骤中，两个不等式都因为 `z≤n` 而成立。因此我们已知 `zero ≤ zero` 和 `zero ≤ zero`，
求证 `zero ≡ zero`，由自反性可证。（注：由等式的自反性可证，而不是不等式的自反性）

{::comment}
In the inductive case, the first inequality holds by `s≤s m≤n` and the
second inequality holds by `s≤s n≤m`, and so we are given `suc m ≤ suc n`
and `suc n ≤ suc m` and must show `suc m ≡ suc n`.  The inductive
hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`, and our goal
follows by congruence.

{::comment}

在归纳步骤中，第一个不等式因为 `s≤s m≤n` 而成立，第二个等式因为 `s≤s n≤m` 而成立。因此我们已知
`suc m ≤ suc n` 和 `suc n ≤ suc m`，求证 `suc m ≡ suc n`。归纳假设 `≤-antisym m≤n n≤m`
可以证明 `m ≡ n`，因此我们可以使用同余性完成证明。


{::comment}
#### Exercise `≤-antisym-cases` {#leq-antisym-cases}
{:/}

#### 练习 `≤-antisym-cases` {#leq-antisym-cases}

{::comment}
The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?
{:/}

上面的证明中省略了一个参数是 `z≤n`，另一个参数是 `s≤s` 的情况。为什么可以省略这种情况？

{::comment}
{% raw %}<pre class="Agda"><a id="16315" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="16352" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
## Total
{:/}

## 完全性

{::comment}
The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.
{:/}

我们证明的第四个性质是完全性：对于任何自然数 `m` 和 `n`，`m ≤ n` 或者 `n ≤ m` 成立。
在 `m` 和 `n` 相等时，两者同时成立。

{::comment}
We specify what it means for inequality to be total:
{:/}

我们首先来说明怎么样不等式才是完全的：

{% raw %}<pre class="Agda"><a id="16758" class="Keyword">data</a> <a id="Total"></a><a id="16763" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16763" class="Datatype">Total</a> <a id="16769" class="Symbol">(</a><a id="16770" href="plfa.Relations.html#16770" class="Bound">m</a> <a id="16772" href="plfa.Relations.html#16772" class="Bound">n</a> <a id="16774" class="Symbol">:</a> <a id="16776" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16777" class="Symbol">)</a> <a id="16779" class="Symbol">:</a> <a id="16781" class="PrimitiveType">Set</a> <a id="16785" class="Keyword">where</a>

  <a id="Total.forward"></a><a id="16794" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16794" class="InductiveConstructor">forward</a> <a id="16802" class="Symbol">:</a>
      <a id="16810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16770" class="Bound">m</a> <a id="16812" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="16814" href="plfa.Relations.html#16772" class="Bound">n</a>
      <a id="16822" class="Comment">---------</a>
    <a id="16836" class="Symbol">→</a> <a id="16838" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16763" class="Datatype">Total</a> <a id="16844" href="plfa.Relations.html#16770" class="Bound">m</a> <a id="16846" href="plfa.Relations.html#16772" class="Bound">n</a>

  <a id="Total.flipped"></a><a id="16851" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16851" class="InductiveConstructor">flipped</a> <a id="16859" class="Symbol">:</a>
      <a id="16867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16772" class="Bound">n</a> <a id="16869" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="16871" href="plfa.Relations.html#16770" class="Bound">m</a>
      <a id="16879" class="Comment">---------</a>
    <a id="16893" class="Symbol">→</a> <a id="16895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16763" class="Datatype">Total</a> <a id="16901" href="plfa.Relations.html#16770" class="Bound">m</a> <a id="16903" href="plfa.Relations.html#16772" class="Bound">n</a>
</pre>{% endraw %}
{::comment}
Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.
{:/}

`Total m n` 成立的证明有两种形式：`forward m≤n` 或者 `flipped n≤m`，其中
`m≤n` 和 `n≤m` 分别是 `m ≤ n` 和 `n ≤ m` 的证明。

{::comment}
(For those familiar with logic, the above definition
could also be written as a disjunction. Disjunctions will
be introduced in Chapter [Connectives][plfa.Connectives].)
{:/}

（如果你对于逻辑学有所了解，上面的定义可以由析取（Disjunction）表示。
我们会在 [Connectives][plfa.Connectives] 章节介绍析取。）

{::comment}
This is our first use of a datatype with _parameters_,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype:
{:/}

这是我们第一次使用带*参数*的数据类型，这里 `m` 和 `n` 是参数。这等同于下面的索引数据类型：

{% raw %}<pre class="Agda"><a id="17670" class="Keyword">data</a> <a id="Total′"></a><a id="17675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17675" class="Datatype">Total′</a> <a id="17682" class="Symbol">:</a> <a id="17684" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="17686" class="Symbol">→</a> <a id="17688" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="17690" class="Symbol">→</a> <a id="17692" class="PrimitiveType">Set</a> <a id="17696" class="Keyword">where</a>

  <a id="Total′.forward′"></a><a id="17705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17705" class="InductiveConstructor">forward′</a> <a id="17714" class="Symbol">:</a> <a id="17716" class="Symbol">∀</a> <a id="17718" class="Symbol">{</a><a id="17719" href="plfa.Relations.html#17719" class="Bound">m</a> <a id="17721" href="plfa.Relations.html#17721" class="Bound">n</a> <a id="17723" class="Symbol">:</a> <a id="17725" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="17726" class="Symbol">}</a>
    <a id="17732" class="Symbol">→</a> <a id="17734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17719" class="Bound">m</a> <a id="17736" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="17738" href="plfa.Relations.html#17721" class="Bound">n</a>
      <a id="17746" class="Comment">----------</a>
    <a id="17761" class="Symbol">→</a> <a id="17763" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17675" class="Datatype">Total′</a> <a id="17770" href="plfa.Relations.html#17719" class="Bound">m</a> <a id="17772" href="plfa.Relations.html#17721" class="Bound">n</a>

  <a id="Total′.flipped′"></a><a id="17777" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17777" class="InductiveConstructor">flipped′</a> <a id="17786" class="Symbol">:</a> <a id="17788" class="Symbol">∀</a> <a id="17790" class="Symbol">{</a><a id="17791" href="plfa.Relations.html#17791" class="Bound">m</a> <a id="17793" href="plfa.Relations.html#17793" class="Bound">n</a> <a id="17795" class="Symbol">:</a> <a id="17797" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="17798" class="Symbol">}</a>
    <a id="17804" class="Symbol">→</a> <a id="17806" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17793" class="Bound">n</a> <a id="17808" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="17810" href="plfa.Relations.html#17791" class="Bound">m</a>
      <a id="17818" class="Comment">----------</a>
    <a id="17833" class="Symbol">→</a> <a id="17835" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17675" class="Datatype">Total′</a> <a id="17842" href="plfa.Relations.html#17791" class="Bound">m</a> <a id="17844" href="plfa.Relations.html#17793" class="Bound">n</a>
</pre>{% endraw %}
{::comment}
Each parameter of the type translates as an implicit parameter of each
constructor.  Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised datatype
the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and
occasionally aid Agda's termination checker, so we will use them in
preference to indexed types when possible.
{:/}

类型里的每个参数都转换成构造器的一个隐式参数。索引数据类型中的索引可以变化，正如在
`zero ≤ n` 和 `suc m ≤ suc n` 中那样，而参数化数据类型不一样，其参数必须保持相同，
正如在 `Total m n` 中那样。参数化的声明更短，更易于阅读，而且有时可以帮助到 Agda 的
终结检查器，所以我们尽可能地使用它们，而不是索引数据类型。

{::comment}
With that preliminary out of the way, we specify and prove totality:
{:/}

在上述准备工作完成后，我们定义并证明完全性。

{% raw %}<pre class="Agda"><a id="≤-total"></a><a id="18604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18604" class="Function">≤-total</a> <a id="18612" class="Symbol">:</a> <a id="18614" class="Symbol">∀</a> <a id="18616" class="Symbol">(</a><a id="18617" href="plfa.Relations.html#18617" class="Bound">m</a> <a id="18619" href="plfa.Relations.html#18619" class="Bound">n</a> <a id="18621" class="Symbol">:</a> <a id="18623" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18624" class="Symbol">)</a> <a id="18626" class="Symbol">→</a> <a id="18628" href="plfa.Relations.html#16763" class="Datatype">Total</a> <a id="18634" href="plfa.Relations.html#18617" class="Bound">m</a> <a id="18636" href="plfa.Relations.html#18619" class="Bound">n</a>
<a id="18638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18604" class="Function">≤-total</a> <a id="18646" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="18654" href="plfa.Relations.html#18654" class="Bound">n</a>                         <a id="18680" class="Symbol">=</a>  <a id="18683" href="plfa.Relations.html#16794" class="InductiveConstructor">forward</a> <a id="18691" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>
<a id="18695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18604" class="Function">≤-total</a> <a id="18703" class="Symbol">(</a><a id="18704" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18708" href="plfa.Relations.html#18708" class="Bound">m</a><a id="18709" class="Symbol">)</a> <a id="18711" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>                      <a id="18737" class="Symbol">=</a>  <a id="18740" href="plfa.Relations.html#16851" class="InductiveConstructor">flipped</a> <a id="18748" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>
<a id="18752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18604" class="Function">≤-total</a> <a id="18760" class="Symbol">(</a><a id="18761" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18765" href="plfa.Relations.html#18765" class="Bound">m</a><a id="18766" class="Symbol">)</a> <a id="18768" class="Symbol">(</a><a id="18769" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18773" href="plfa.Relations.html#18773" class="Bound">n</a><a id="18774" class="Symbol">)</a> <a id="18776" class="Keyword">with</a> <a id="18781" href="plfa.Relations.html#18604" class="Function">≤-total</a> <a id="18789" href="plfa.Relations.html#18765" class="Bound">m</a> <a id="18791" href="plfa.Relations.html#18773" class="Bound">n</a>
<a id="18793" class="Symbol">...</a>                        <a id="18820" class="Symbol">|</a> <a id="18822" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16794" class="InductiveConstructor">forward</a> <a id="18830" href="plfa.Relations.html#18830" class="Bound">m≤n</a>  <a id="18835" class="Symbol">=</a>  <a id="18838" href="plfa.Relations.html#16794" class="InductiveConstructor">forward</a> <a id="18846" class="Symbol">(</a><a id="18847" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="18851" href="plfa.Relations.html#18830" class="Bound">m≤n</a><a id="18854" class="Symbol">)</a>
<a id="18856" class="Symbol">...</a>                        <a id="18883" class="Symbol">|</a> <a id="18885" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16851" class="InductiveConstructor">flipped</a> <a id="18893" href="plfa.Relations.html#18893" class="Bound">n≤m</a>  <a id="18898" class="Symbol">=</a>  <a id="18901" href="plfa.Relations.html#16851" class="InductiveConstructor">flipped</a> <a id="18909" class="Symbol">(</a><a id="18910" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="18914" href="plfa.Relations.html#18893" class="Bound">n≤m</a><a id="18917" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

* _First base case_: If the first argument is `zero` and the
  second argument is `n` then the forward case holds,
  with `z≤n` as evidence that `zero ≤ n`.

* _Second base case_: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

* _Inductive case_: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  + The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  + The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.
{:/}

这里，我们的证明在两个参数上进行归纳，并按照情况分析：

* **第一起始步骤**：如果第一个参数是 `zero`，第二个参数是 `n`，那么 forward
  条件成立，我们使用 `z≤n` 作为 `zero ≤ n` 的证明。

* **第二起始步骤**：如果第一个参数是 `suc m`，第二个参数是 `zero`，那么 flipped
  条件成立，我们使用 `z≤n` 作为 `zero ≤ suc m` 的证明。

* **归纳步骤**：如果第一个参数是 `suc m`，第二个参数是 `suc n`，那么归纳假设
  `≤-total m n` 可以给出如下推断：

  + 归纳假设的 forward 条件成立，以 `m≤n` 作为 `m ≤ n` 的证明。以此我们可以使用
    `s≤s m≤n` 作为 `suc m ≤ suc n` 来证明 forward 条件成立。

  + 归纳假设的 flipped 条件成立，以 `n≤m` 作为 `n ≤ m` 的证明。以此我们可以使用
    `s≤s n≤m` 作为 `suc n ≤ suc m` 来证明 flipped 条件成立。

{::comment}
This is our first use of the `with` clause in https://agda.github.io/agda-stdlib/v1.1/Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.
{:/}

这是我们第一次在 Agda 中使用 `with` 语句。`with` 关键字后面有一个表达式和一或多行。
每行以省略号（`...`）和一个竖线（`|`）开头，后面跟着用来匹配表达式的模式，和等式的右手边。

{::comment}
Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following:
{:/}

使用 `with` 语句等同于定义一个辅助函数。比如说，上面的定义和下面的等价：

{% raw %}<pre class="Agda"><a id="≤-total′"></a><a id="21114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21114" class="Function">≤-total′</a> <a id="21123" class="Symbol">:</a> <a id="21125" class="Symbol">∀</a> <a id="21127" class="Symbol">(</a><a id="21128" href="plfa.Relations.html#21128" class="Bound">m</a> <a id="21130" href="plfa.Relations.html#21130" class="Bound">n</a> <a id="21132" class="Symbol">:</a> <a id="21134" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="21135" class="Symbol">)</a> <a id="21137" class="Symbol">→</a> <a id="21139" href="plfa.Relations.html#16763" class="Datatype">Total</a> <a id="21145" href="plfa.Relations.html#21128" class="Bound">m</a> <a id="21147" href="plfa.Relations.html#21130" class="Bound">n</a>
<a id="21149" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21114" class="Function">≤-total′</a> <a id="21158" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="21166" href="plfa.Relations.html#21166" class="Bound">n</a>        <a id="21175" class="Symbol">=</a>  <a id="21178" href="plfa.Relations.html#16794" class="InductiveConstructor">forward</a> <a id="21186" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>
<a id="21190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21114" class="Function">≤-total′</a> <a id="21199" class="Symbol">(</a><a id="21200" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21204" href="plfa.Relations.html#21204" class="Bound">m</a><a id="21205" class="Symbol">)</a> <a id="21207" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>     <a id="21216" class="Symbol">=</a>  <a id="21219" href="plfa.Relations.html#16851" class="InductiveConstructor">flipped</a> <a id="21227" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>
<a id="21231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21114" class="Function">≤-total′</a> <a id="21240" class="Symbol">(</a><a id="21241" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21245" href="plfa.Relations.html#21245" class="Bound">m</a><a id="21246" class="Symbol">)</a> <a id="21248" class="Symbol">(</a><a id="21249" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21253" href="plfa.Relations.html#21253" class="Bound">n</a><a id="21254" class="Symbol">)</a>  <a id="21257" class="Symbol">=</a>  <a id="21260" href="plfa.Relations.html#21292" class="Function">helper</a> <a id="21267" class="Symbol">(</a><a id="21268" href="plfa.Relations.html#21114" class="Function">≤-total′</a> <a id="21277" href="plfa.Relations.html#21245" class="Bound">m</a> <a id="21279" href="plfa.Relations.html#21253" class="Bound">n</a><a id="21280" class="Symbol">)</a>
  <a id="21284" class="Keyword">where</a>
  <a id="21292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21292" class="Function">helper</a> <a id="21299" class="Symbol">:</a> <a id="21301" href="plfa.Relations.html#16763" class="Datatype">Total</a> <a id="21307" href="plfa.Relations.html#21245" class="Bound">m</a> <a id="21309" href="plfa.Relations.html#21253" class="Bound">n</a> <a id="21311" class="Symbol">→</a> <a id="21313" href="plfa.Relations.html#16763" class="Datatype">Total</a> <a id="21319" class="Symbol">(</a><a id="21320" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21324" href="plfa.Relations.html#21245" class="Bound">m</a><a id="21325" class="Symbol">)</a> <a id="21327" class="Symbol">(</a><a id="21328" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21332" href="plfa.Relations.html#21253" class="Bound">n</a><a id="21333" class="Symbol">)</a>
  <a id="21337" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21292" class="Function">helper</a> <a id="21344" class="Symbol">(</a><a id="21345" href="plfa.Relations.html#16794" class="InductiveConstructor">forward</a> <a id="21353" href="plfa.Relations.html#21353" class="Bound">m≤n</a><a id="21356" class="Symbol">)</a>  <a id="21359" class="Symbol">=</a>  <a id="21362" href="plfa.Relations.html#16794" class="InductiveConstructor">forward</a> <a id="21370" class="Symbol">(</a><a id="21371" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="21375" href="plfa.Relations.html#21353" class="Bound">m≤n</a><a id="21378" class="Symbol">)</a>
  <a id="21382" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21292" class="Function">helper</a> <a id="21389" class="Symbol">(</a><a id="21390" href="plfa.Relations.html#16851" class="InductiveConstructor">flipped</a> <a id="21398" href="plfa.Relations.html#21398" class="Bound">n≤m</a><a id="21401" class="Symbol">)</a>  <a id="21404" class="Symbol">=</a>  <a id="21407" href="plfa.Relations.html#16851" class="InductiveConstructor">flipped</a> <a id="21415" class="Symbol">(</a><a id="21416" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="21420" href="plfa.Relations.html#21398" class="Bound">n≤m</a><a id="21423" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
This is also our first use of a `where` clause in https://agda.github.io/agda-stdlib/v1.1/Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound on the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.
{:/}

这也是我们第一次在 Agda 中使用 `where` 语句。`where` 关键字后面有一或多条定义，其必须被缩进。
之前等式左手边的约束变量（此例中的 `m` 和 `n`）在嵌套的定义中仍然在作用域内。
在嵌套定义中的约束标识符（此例中的 `helper` ）在等式的右手边的作用域内。

{::comment}
If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case:
{:/}

如果两个参数相同，那么两个情况同时成立，我们可以返回任一证明。上面的代码中我们返回 forward 条件，
但是我们也可以返回 flipped 条件，如下：

{% raw %}<pre class="Agda"><a id="≤-total″"></a><a id="22307" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22307" class="Function">≤-total″</a> <a id="22316" class="Symbol">:</a> <a id="22318" class="Symbol">∀</a> <a id="22320" class="Symbol">(</a><a id="22321" href="plfa.Relations.html#22321" class="Bound">m</a> <a id="22323" href="plfa.Relations.html#22323" class="Bound">n</a> <a id="22325" class="Symbol">:</a> <a id="22327" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="22328" class="Symbol">)</a> <a id="22330" class="Symbol">→</a> <a id="22332" href="plfa.Relations.html#16763" class="Datatype">Total</a> <a id="22338" href="plfa.Relations.html#22321" class="Bound">m</a> <a id="22340" href="plfa.Relations.html#22323" class="Bound">n</a>
<a id="22342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22307" class="Function">≤-total″</a> <a id="22351" href="plfa.Relations.html#22351" class="Bound">m</a>       <a id="22359" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>                      <a id="22385" class="Symbol">=</a>  <a id="22388" href="plfa.Relations.html#16851" class="InductiveConstructor">flipped</a> <a id="22396" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>
<a id="22400" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22307" class="Function">≤-total″</a> <a id="22409" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="22417" class="Symbol">(</a><a id="22418" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="22422" href="plfa.Relations.html#22422" class="Bound">n</a><a id="22423" class="Symbol">)</a>                   <a id="22443" class="Symbol">=</a>  <a id="22446" href="plfa.Relations.html#16794" class="InductiveConstructor">forward</a> <a id="22454" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>
<a id="22458" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22307" class="Function">≤-total″</a> <a id="22467" class="Symbol">(</a><a id="22468" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="22472" href="plfa.Relations.html#22472" class="Bound">m</a><a id="22473" class="Symbol">)</a> <a id="22475" class="Symbol">(</a><a id="22476" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="22480" href="plfa.Relations.html#22480" class="Bound">n</a><a id="22481" class="Symbol">)</a> <a id="22483" class="Keyword">with</a> <a id="22488" href="plfa.Relations.html#22307" class="Function">≤-total″</a> <a id="22497" href="plfa.Relations.html#22472" class="Bound">m</a> <a id="22499" href="plfa.Relations.html#22480" class="Bound">n</a>
<a id="22501" class="Symbol">...</a>                        <a id="22528" class="Symbol">|</a> <a id="22530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16794" class="InductiveConstructor">forward</a> <a id="22538" href="plfa.Relations.html#22538" class="Bound">m≤n</a>   <a id="22544" class="Symbol">=</a>  <a id="22547" href="plfa.Relations.html#16794" class="InductiveConstructor">forward</a> <a id="22555" class="Symbol">(</a><a id="22556" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="22560" href="plfa.Relations.html#22538" class="Bound">m≤n</a><a id="22563" class="Symbol">)</a>
<a id="22565" class="Symbol">...</a>                        <a id="22592" class="Symbol">|</a> <a id="22594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16851" class="InductiveConstructor">flipped</a> <a id="22602" href="plfa.Relations.html#22602" class="Bound">n≤m</a>   <a id="22608" class="Symbol">=</a>  <a id="22611" href="plfa.Relations.html#16851" class="InductiveConstructor">flipped</a> <a id="22619" class="Symbol">(</a><a id="22620" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="22624" href="plfa.Relations.html#22602" class="Bound">n≤m</a><a id="22627" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
It differs from the original code in that it pattern
matches on the second argument before the first argument.
{:/}

两者的区别在于上述代码在对于第一个参数进行模式匹配之前先对于第二个参数先进行模式匹配。


{::comment}
## Monotonicity
{:/}

## 单调性

{::comment}
If one bumps into both an operator and an ordering at a party, one may ask if
the operator is _monotonic_ with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning:
{:/}

如果在聚会中碰到了一个运算符和一个序，那么有人可能会问这个运算符对于这个序是不是
**单调的（Monotonic）**。比如说，加法对于小于等于是单调的，这意味着：

    ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

{::comment}
The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right:
{:/}

这个证明可以用我们学会的方法，很直接的来完成。我们最好把它分成三个部分，首先我们证明加法对于
小于等于在右手边是单调的：

{% raw %}<pre class="Agda"><a id="+-monoʳ-≤"></a><a id="23485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23485" class="Function">+-monoʳ-≤</a> <a id="23495" class="Symbol">:</a> <a id="23497" class="Symbol">∀</a> <a id="23499" class="Symbol">(</a><a id="23500" href="plfa.Relations.html#23500" class="Bound">n</a> <a id="23502" href="plfa.Relations.html#23502" class="Bound">p</a> <a id="23504" href="plfa.Relations.html#23504" class="Bound">q</a> <a id="23506" class="Symbol">:</a> <a id="23508" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="23509" class="Symbol">)</a>
  <a id="23513" class="Symbol">→</a> <a id="23515" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23502" class="Bound">p</a> <a id="23517" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="23519" href="plfa.Relations.html#23504" class="Bound">q</a>
    <a id="23525" class="Comment">-------------</a>
  <a id="23541" class="Symbol">→</a> <a id="23543" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23500" class="Bound">n</a> <a id="23545" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23547" href="plfa.Relations.html#23502" class="Bound">p</a> <a id="23549" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="23551" href="plfa.Relations.html#23500" class="Bound">n</a> <a id="23553" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23555" href="plfa.Relations.html#23504" class="Bound">q</a>
<a id="23557" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23485" class="Function">+-monoʳ-≤</a> <a id="23567" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="23575" href="plfa.Relations.html#23575" class="Bound">p</a> <a id="23577" href="plfa.Relations.html#23577" class="Bound">q</a> <a id="23579" href="plfa.Relations.html#23579" class="Bound">p≤q</a>  <a id="23584" class="Symbol">=</a>  <a id="23587" href="plfa.Relations.html#23579" class="Bound">p≤q</a>
<a id="23591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23485" class="Function">+-monoʳ-≤</a> <a id="23601" class="Symbol">(</a><a id="23602" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23606" href="plfa.Relations.html#23606" class="Bound">n</a><a id="23607" class="Symbol">)</a> <a id="23609" href="plfa.Relations.html#23609" class="Bound">p</a> <a id="23611" href="plfa.Relations.html#23611" class="Bound">q</a> <a id="23613" href="plfa.Relations.html#23613" class="Bound">p≤q</a>  <a id="23618" class="Symbol">=</a>  <a id="23621" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="23625" class="Symbol">(</a><a id="23626" href="plfa.Relations.html#23485" class="Function">+-monoʳ-≤</a> <a id="23636" href="plfa.Relations.html#23606" class="Bound">n</a> <a id="23638" href="plfa.Relations.html#23609" class="Bound">p</a> <a id="23640" href="plfa.Relations.html#23611" class="Bound">q</a> <a id="23642" href="plfa.Relations.html#23613" class="Bound">p≤q</a><a id="23645" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
The proof is by induction on the first argument.

* _Base case_: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

* _Inductive case_: The first argument is `suc n`, in which case
  `suc n + p ≤ suc n + q` simplifies to `suc (n + p) ≤ suc (n + q)`.
  The inductive hypothesis `+-monoʳ-≤ n p q p≤q` establishes that
  `n + p ≤ n + q`, and our goal follows by applying `s≤s`.
{:/}

我们对于第一个参数进行归纳。

* **起始步骤**：第一个参数是 `zero`，那么 `zero + p ≤ zero + q` 可以化简为 `p ≤ q`，
  其证明由 `p≤q` 给出。

* **归纳步骤**：第一个参数是 `suc n`，那么 `suc n + p ≤ suc n + q` 可以化简为
  `suc (n + p) ≤ suc (n + q)`。归纳假设 `+-monoʳ-≤ n p q p≤q` 可以证明
  `n + p ≤ n + q`，我们在此之上使用 `s≤s` 即可得证。

{::comment}
Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition:
{:/}

接下来，我们证明加法对于小于等于在左手边是单调的。我们可以用之前的结论和加法的交换律来证明：

{% raw %}<pre class="Agda"><a id="+-monoˡ-≤"></a><a id="24629" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#24629" class="Function">+-monoˡ-≤</a> <a id="24639" class="Symbol">:</a> <a id="24641" class="Symbol">∀</a> <a id="24643" class="Symbol">(</a><a id="24644" href="plfa.Relations.html#24644" class="Bound">m</a> <a id="24646" href="plfa.Relations.html#24646" class="Bound">n</a> <a id="24648" href="plfa.Relations.html#24648" class="Bound">p</a> <a id="24650" class="Symbol">:</a> <a id="24652" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="24653" class="Symbol">)</a>
  <a id="24657" class="Symbol">→</a> <a id="24659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#24644" class="Bound">m</a> <a id="24661" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="24663" href="plfa.Relations.html#24646" class="Bound">n</a>
    <a id="24669" class="Comment">-------------</a>
  <a id="24685" class="Symbol">→</a> <a id="24687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#24644" class="Bound">m</a> <a id="24689" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="24691" href="plfa.Relations.html#24648" class="Bound">p</a> <a id="24693" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="24695" href="plfa.Relations.html#24646" class="Bound">n</a> <a id="24697" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="24699" href="plfa.Relations.html#24648" class="Bound">p</a>
<a id="24701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#24629" class="Function">+-monoˡ-≤</a> <a id="24711" href="plfa.Relations.html#24711" class="Bound">m</a> <a id="24713" href="plfa.Relations.html#24713" class="Bound">n</a> <a id="24715" href="plfa.Relations.html#24715" class="Bound">p</a> <a id="24717" href="plfa.Relations.html#24717" class="Bound">m≤n</a>  <a id="24722" class="Keyword">rewrite</a> <a id="24730" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a> <a id="24737" href="plfa.Relations.html#24711" class="Bound">m</a> <a id="24739" href="plfa.Relations.html#24715" class="Bound">p</a> <a id="24741" class="Symbol">|</a> <a id="24743" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a> <a id="24750" href="plfa.Relations.html#24713" class="Bound">n</a> <a id="24752" href="plfa.Relations.html#24715" class="Bound">p</a>  <a id="24755" class="Symbol">=</a> <a id="24757" href="plfa.Relations.html#23485" class="Function">+-monoʳ-≤</a> <a id="24767" href="plfa.Relations.html#24715" class="Bound">p</a> <a id="24769" href="plfa.Relations.html#24711" class="Bound">m</a> <a id="24771" href="plfa.Relations.html#24713" class="Bound">n</a> <a id="24773" href="plfa.Relations.html#24717" class="Bound">m≤n</a>
</pre>{% endraw %}
{::comment}
Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.
{:/}

用 `+-comm m p` 和 `+-comm n p` 来重写，可以让 `m + p ≤ n + p` 转换成 `p + n ≤ p + m`，
而我们可以用 `+-moroʳ-≤ p m n m≤n` 来证明。

{::comment}
Third, we combine the two previous results:
{:/}

最后，我们把前两步的结论结合起来：

{% raw %}<pre class="Agda"><a id="+-mono-≤"></a><a id="25136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25136" class="Function">+-mono-≤</a> <a id="25145" class="Symbol">:</a> <a id="25147" class="Symbol">∀</a> <a id="25149" class="Symbol">(</a><a id="25150" href="plfa.Relations.html#25150" class="Bound">m</a> <a id="25152" href="plfa.Relations.html#25152" class="Bound">n</a> <a id="25154" href="plfa.Relations.html#25154" class="Bound">p</a> <a id="25156" href="plfa.Relations.html#25156" class="Bound">q</a> <a id="25158" class="Symbol">:</a> <a id="25160" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="25161" class="Symbol">)</a>
  <a id="25165" class="Symbol">→</a> <a id="25167" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25150" class="Bound">m</a> <a id="25169" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="25171" href="plfa.Relations.html#25152" class="Bound">n</a>
  <a id="25175" class="Symbol">→</a> <a id="25177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25154" class="Bound">p</a> <a id="25179" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="25181" href="plfa.Relations.html#25156" class="Bound">q</a>
    <a id="25187" class="Comment">-------------</a>
  <a id="25203" class="Symbol">→</a> <a id="25205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25150" class="Bound">m</a> <a id="25207" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25209" href="plfa.Relations.html#25154" class="Bound">p</a> <a id="25211" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="25213" href="plfa.Relations.html#25152" class="Bound">n</a> <a id="25215" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25217" href="plfa.Relations.html#25156" class="Bound">q</a>
<a id="25219" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25136" class="Function">+-mono-≤</a> <a id="25228" href="plfa.Relations.html#25228" class="Bound">m</a> <a id="25230" href="plfa.Relations.html#25230" class="Bound">n</a> <a id="25232" href="plfa.Relations.html#25232" class="Bound">p</a> <a id="25234" href="plfa.Relations.html#25234" class="Bound">q</a> <a id="25236" href="plfa.Relations.html#25236" class="Bound">m≤n</a> <a id="25240" href="plfa.Relations.html#25240" class="Bound">p≤q</a>  <a id="25245" class="Symbol">=</a>  <a id="25248" href="plfa.Relations.html#11852" class="Function">≤-trans</a> <a id="25256" class="Symbol">(</a><a id="25257" href="plfa.Relations.html#24629" class="Function">+-monoˡ-≤</a> <a id="25267" href="plfa.Relations.html#25228" class="Bound">m</a> <a id="25269" href="plfa.Relations.html#25230" class="Bound">n</a> <a id="25271" href="plfa.Relations.html#25232" class="Bound">p</a> <a id="25273" href="plfa.Relations.html#25236" class="Bound">m≤n</a><a id="25276" class="Symbol">)</a> <a id="25278" class="Symbol">(</a><a id="25279" href="plfa.Relations.html#23485" class="Function">+-monoʳ-≤</a> <a id="25289" href="plfa.Relations.html#25230" class="Bound">n</a> <a id="25291" href="plfa.Relations.html#25232" class="Bound">p</a> <a id="25293" href="plfa.Relations.html#25234" class="Bound">q</a> <a id="25295" href="plfa.Relations.html#25240" class="Bound">p≤q</a><a id="25298" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.
{:/}

使用 `+-monoˡ-≤ m n p m≤n` 可以证明 `m + p ≤ n + p`，
使用 `+-monoʳ-≤ n p q p≤q` 可以证明 `n + p ≤ n + q`，用传递性把两者连接起来，
我们可以获得 `m + p ≤ n + q` 的证明，如上所示。

{::comment}
#### Exercise `*-mono-≤` (stretch)
{:/}

#### 练习 `*-mono-≤` （延伸）

{::comment}
Show that multiplication is monotonic with regard to inequality.
{:/}

证明乘法对于小于等于是单调的。

{::comment}
{% raw %}<pre class="Agda"><a id="25852" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="25889" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
## Strict inequality {#strict-inequality}
{:/}

## 严格不等关系 {#strict-inequality}

{::comment}
We can define strict inequality similarly to inequality:
{:/}

我们可以用类似于定义不等关系的方法来定义严格不等关系。

{% raw %}<pre class="Agda"><a id="26108" class="Keyword">infix</a> <a id="26114" class="Number">4</a> <a id="26116" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26126" class="Datatype Operator">_&lt;_</a>

<a id="26121" class="Keyword">data</a> <a id="_&lt;_"></a><a id="26126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26126" class="Datatype Operator">_&lt;_</a> <a id="26130" class="Symbol">:</a> <a id="26132" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="26134" class="Symbol">→</a> <a id="26136" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="26138" class="Symbol">→</a> <a id="26140" class="PrimitiveType">Set</a> <a id="26144" class="Keyword">where</a>

  <a id="_&lt;_.z&lt;s"></a><a id="26153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26153" class="InductiveConstructor">z&lt;s</a> <a id="26157" class="Symbol">:</a> <a id="26159" class="Symbol">∀</a> <a id="26161" class="Symbol">{</a><a id="26162" href="plfa.Relations.html#26162" class="Bound">n</a> <a id="26164" class="Symbol">:</a> <a id="26166" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="26167" class="Symbol">}</a>
      <a id="26175" class="Comment">------------</a>
    <a id="26192" class="Symbol">→</a> <a id="26194" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="26199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26126" class="Datatype Operator">&lt;</a> <a id="26201" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="26205" href="plfa.Relations.html#26162" class="Bound">n</a>

  <a id="_&lt;_.s&lt;s"></a><a id="26210" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26210" class="InductiveConstructor">s&lt;s</a> <a id="26214" class="Symbol">:</a> <a id="26216" class="Symbol">∀</a> <a id="26218" class="Symbol">{</a><a id="26219" href="plfa.Relations.html#26219" class="Bound">m</a> <a id="26221" href="plfa.Relations.html#26221" class="Bound">n</a> <a id="26223" class="Symbol">:</a> <a id="26225" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="26226" class="Symbol">}</a>
    <a id="26232" class="Symbol">→</a> <a id="26234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26219" class="Bound">m</a> <a id="26236" href="plfa.Relations.html#26126" class="Datatype Operator">&lt;</a> <a id="26238" href="plfa.Relations.html#26221" class="Bound">n</a>
      <a id="26246" class="Comment">-------------</a>
    <a id="26264" class="Symbol">→</a> <a id="26266" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="26270" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26219" class="Bound">m</a> <a id="26272" href="plfa.Relations.html#26126" class="Datatype Operator">&lt;</a> <a id="26274" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="26278" href="plfa.Relations.html#26221" class="Bound">n</a>
</pre>{% endraw %}
{::comment}
The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.
{:/}

严格不等关系与不等关系最重要的区别在于，0 小于任何数的后继，而不小于 0。

{::comment}
Clearly, strict inequality is not reflexive. However it is
_irreflexive_ in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
_trichotomy_: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly when `n < m`).
It is also monotonic with regards to addition and multiplication.
{:/}

显然，严格不等关系不是自反的，而是**非自反的（Irreflexive）**，表示 `n < n` 对于
任何值 `n` 都不成立。和不等关系一样，严格不等关系是传递的。严格不等关系不是完全的，但是满足
一个相似的性质：*三分律*（Trichotomy）：对于任意的 `m` 和 `n`，`m < n`、`m ≡ n` 或者
`m > n` 三者有且仅有一者成立。（我们定义 `m > n` 当且仅当 `n < m` 成立时成立）
严格不等关系对于加法和乘法也是单调的。

{::comment}
Most of the above are considered in exercises below.  Irreflexivity
requires negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred to
Chapter [Negation][plfa.Negation].
{:/}

我们把一部分上述性质作为习题。非自反性需要逻辑非，三分律需要证明三者是互斥的，因此这两个性质
暂不做为习题。我们会在 [Negation][plfa.Negation] 章节来重新讨论。

{::comment}
It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by
exploiting the corresponding properties of inequality.
{:/}

我们可以直接地来证明 `suc m ≤ n` 蕴涵了 `m < n`，及其逆命题。
因此我们亦可从不等关系的性质中，使用此性质来证明严格不等关系的性质。


{::comment}
#### Exercise `<-trans` (recommended) {#less-trans}
{:/}

#### 练习 `<-trans` （推荐） {#less-trans}

{::comment}
Show that strict inequality is transitive.
{:/}

证明严格不等是传递的。

{::comment}
{% raw %}<pre class="Agda"><a id="28049" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="28086" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
#### Exercise `trichotomy` {#trichotomy}
{:/}

#### 练习 `trichotomy` {#trichotomy}

{::comment}
Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`.
{:/}

证明严格不等关系满足弱化的三元律，证明对于任意 `m` 和 `n`，下列命题有一条成立：

  * `m < n`，
  * `m ≡ n`，或者
  * `m > n`。

{::comment}
Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation][plfa.Negation].)
{:/}

定义 `m > n` 为 `n < m`。你需要一个合适的数据类型声明，如同我们在证明完全性中使用的那样。
（我们会在介绍[逻辑非][plfa.Negation]以后证明三者是互斥的）

{::comment}
{% raw %}<pre class="Agda"><a id="28831" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="28868" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
#### Exercise `+-mono-<` {#plus-mono-less}
{:/}

#### 练习 `+-mono-<` {#plus-mono-less}

{::comment}
Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.
{:/}

证明加法对于严格不等关系是单调的。正如不等关系中那样，你可以需要额外的定义。

{::comment}
{% raw %}<pre class="Agda"><a id="29192" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="29229" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}
{:/}

#### 练习 `≤-iff-<` (推荐) {#leq-iff-less}

{::comment}
Show that `suc m ≤ n` implies `m < n`, and conversely.
{:/}

证明 `suc m ≤ n` 蕴涵了 `m < n`，及其逆命题。

{::comment}
{% raw %}<pre class="Agda"><a id="29484" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="29521" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
#### Exercise `<-trans-revisited` {#less-trans-revisited}
{:/}

#### 练习 `<-trans-revisited` {#less-trans-revisited}

{::comment}
Give an alternative proof that strict inequality is transitive,
using the relation between strict inequality and inequality and
the fact that inequality is transitive.
{:/}

用另外一种方法证明严格不等是传递的，使用之前证明的不等关系和严格不等关系的联系，
以及不等关系的传递性。

{::comment}
{% raw %}<pre class="Agda"><a id="29925" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="29962" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
## Even and odd
{:/}

## 奇和偶

{::comment}
As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are _binary relations_, while even and odd are
_unary relations_, sometimes called _predicates_:
{:/}

作为一个额外的例子，我们来定义奇数和偶数。不等关系和严格不等关系是**二元关系**，而奇偶性
是**一元关系**，有时也被叫做**谓词（Predicate）**：

{% raw %}<pre class="Agda"><a id="30317" class="Keyword">data</a> <a id="even"></a><a id="30322" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30322" class="Datatype">even</a> <a id="30327" class="Symbol">:</a> <a id="30329" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="30331" class="Symbol">→</a> <a id="30333" class="PrimitiveType">Set</a>
<a id="30337" class="Keyword">data</a> <a id="odd"></a><a id="30342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30342" class="Datatype">odd</a>  <a id="30347" class="Symbol">:</a> <a id="30349" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="30351" class="Symbol">→</a> <a id="30353" class="PrimitiveType">Set</a>

<a id="30358" class="Keyword">data</a> <a id="30363" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30322" class="Datatype">even</a> <a id="30368" class="Keyword">where</a>

  <a id="even.zero"></a><a id="30377" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30377" class="InductiveConstructor">zero</a> <a id="30382" class="Symbol">:</a>
      <a id="30390" class="Comment">---------</a>
      <a id="30406" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30322" class="Datatype">even</a> <a id="30411" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>

  <a id="even.suc"></a><a id="30419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30419" class="InductiveConstructor">suc</a>  <a id="30424" class="Symbol">:</a> <a id="30426" class="Symbol">∀</a> <a id="30428" class="Symbol">{</a><a id="30429" href="plfa.Relations.html#30429" class="Bound">n</a> <a id="30431" class="Symbol">:</a> <a id="30433" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="30434" class="Symbol">}</a>
    <a id="30440" class="Symbol">→</a> <a id="30442" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30342" class="Datatype">odd</a> <a id="30446" href="plfa.Relations.html#30429" class="Bound">n</a>
      <a id="30454" class="Comment">------------</a>
    <a id="30471" class="Symbol">→</a> <a id="30473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30322" class="Datatype">even</a> <a id="30478" class="Symbol">(</a><a id="30479" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="30483" href="plfa.Relations.html#30429" class="Bound">n</a><a id="30484" class="Symbol">)</a>

<a id="30487" class="Keyword">data</a> <a id="30492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30342" class="Datatype">odd</a> <a id="30496" class="Keyword">where</a>

  <a id="odd.suc"></a><a id="30505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30505" class="InductiveConstructor">suc</a>   <a id="30511" class="Symbol">:</a> <a id="30513" class="Symbol">∀</a> <a id="30515" class="Symbol">{</a><a id="30516" href="plfa.Relations.html#30516" class="Bound">n</a> <a id="30518" class="Symbol">:</a> <a id="30520" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="30521" class="Symbol">}</a>
    <a id="30527" class="Symbol">→</a> <a id="30529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30322" class="Datatype">even</a> <a id="30534" href="plfa.Relations.html#30516" class="Bound">n</a>
      <a id="30542" class="Comment">-----------</a>
    <a id="30558" class="Symbol">→</a> <a id="30560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30342" class="Datatype">odd</a> <a id="30564" class="Symbol">(</a><a id="30565" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="30569" href="plfa.Relations.html#30516" class="Bound">n</a><a id="30570" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.
{:/}

一个数是偶数，如果它是 0，或者是奇数的后继。一个数是奇数，如果它是偶数的后继。

{::comment}
This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).
{:/}

这是我们第一次定义一个相互递归的数据类型。因为每个标识符必须在使用前声明，所以
我们首先声明索引数据类型 `even` 和 `odd` （省略 `where` 关键字和其构造器的定义），
然后声明其构造器（省略其签名 `ℕ → Set`，因为在之前已经给出）。

{::comment}
This is also our first use of _overloaded_ constructors,
that is, using the same name for constructors of different types.
Here `suc` means one of three constructors:
{:/}

这也是我们第一次使用 **重载（Overloaded）**的构造器。这意味着不同类型的构造器
拥有相同的名字。在这里 `suc` 表示下面三种构造器其中之一：

    suc : ℕ → ℕ

    suc : ∀ {n : ℕ}
      → odd n
        ------------
      → even (suc n)

    suc : ∀ {n : ℕ}
      → even n
        -----------
      → odd (suc n)

{::comment}
Similarly, `zero` refers to one of two constructors. Due to how it
does type inference, Agda does not allow overloading of defined names,
but does allow overloading of constructors.  It is recommended that
one restrict overloading to related meanings, as we have done here,
but it is not required.
{:/}

同理，`zero` 表示两种构造器的一种。因为类型推导的限制，Agda 不允许重载已定义的名字，
但是允许重载构造器。我们推荐将重载限制在有关联的定义中，如我们所做的这样，但这不是必须的。

{::comment}
We show that the sum of two even numbers is even:
{:/}

我们证明两个偶数之和是偶数：

{% raw %}<pre class="Agda"><a id="e+e≡e"></a><a id="32184" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32184" class="Function">e+e≡e</a> <a id="32190" class="Symbol">:</a> <a id="32192" class="Symbol">∀</a> <a id="32194" class="Symbol">{</a><a id="32195" href="plfa.Relations.html#32195" class="Bound">m</a> <a id="32197" href="plfa.Relations.html#32197" class="Bound">n</a> <a id="32199" class="Symbol">:</a> <a id="32201" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="32202" class="Symbol">}</a>
  <a id="32206" class="Symbol">→</a> <a id="32208" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30322" class="Datatype">even</a> <a id="32213" href="plfa.Relations.html#32195" class="Bound">m</a>
  <a id="32217" class="Symbol">→</a> <a id="32219" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30322" class="Datatype">even</a> <a id="32224" href="plfa.Relations.html#32197" class="Bound">n</a>
    <a id="32230" class="Comment">------------</a>
  <a id="32245" class="Symbol">→</a> <a id="32247" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30322" class="Datatype">even</a> <a id="32252" class="Symbol">(</a><a id="32253" href="plfa.Relations.html#32195" class="Bound">m</a> <a id="32255" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="32257" href="plfa.Relations.html#32197" class="Bound">n</a><a id="32258" class="Symbol">)</a>

<a id="o+e≡o"></a><a id="32261" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32261" class="Function">o+e≡o</a> <a id="32267" class="Symbol">:</a> <a id="32269" class="Symbol">∀</a> <a id="32271" class="Symbol">{</a><a id="32272" href="plfa.Relations.html#32272" class="Bound">m</a> <a id="32274" href="plfa.Relations.html#32274" class="Bound">n</a> <a id="32276" class="Symbol">:</a> <a id="32278" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="32279" class="Symbol">}</a>
  <a id="32283" class="Symbol">→</a> <a id="32285" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30342" class="Datatype">odd</a> <a id="32289" href="plfa.Relations.html#32272" class="Bound">m</a>
  <a id="32293" class="Symbol">→</a> <a id="32295" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30322" class="Datatype">even</a> <a id="32300" href="plfa.Relations.html#32274" class="Bound">n</a>
    <a id="32306" class="Comment">-----------</a>
  <a id="32320" class="Symbol">→</a> <a id="32322" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30342" class="Datatype">odd</a> <a id="32326" class="Symbol">(</a><a id="32327" href="plfa.Relations.html#32272" class="Bound">m</a> <a id="32329" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="32331" href="plfa.Relations.html#32274" class="Bound">n</a><a id="32332" class="Symbol">)</a>

<a id="32335" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32184" class="Function">e+e≡e</a> <a id="32341" href="plfa.Relations.html#30377" class="InductiveConstructor">zero</a>     <a id="32350" href="plfa.Relations.html#32350" class="Bound">en</a>  <a id="32354" class="Symbol">=</a>  <a id="32357" href="plfa.Relations.html#32350" class="Bound">en</a>
<a id="32360" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32184" class="Function">e+e≡e</a> <a id="32366" class="Symbol">(</a><a id="32367" href="plfa.Relations.html#30419" class="InductiveConstructor">suc</a> <a id="32371" href="plfa.Relations.html#32371" class="Bound">om</a><a id="32373" class="Symbol">)</a> <a id="32375" href="plfa.Relations.html#32375" class="Bound">en</a>  <a id="32379" class="Symbol">=</a>  <a id="32382" href="plfa.Relations.html#30419" class="InductiveConstructor">suc</a> <a id="32386" class="Symbol">(</a><a id="32387" href="plfa.Relations.html#32261" class="Function">o+e≡o</a> <a id="32393" href="plfa.Relations.html#32371" class="Bound">om</a> <a id="32396" href="plfa.Relations.html#32375" class="Bound">en</a><a id="32398" class="Symbol">)</a>

<a id="32401" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32261" class="Function">o+e≡o</a> <a id="32407" class="Symbol">(</a><a id="32408" href="plfa.Relations.html#30505" class="InductiveConstructor">suc</a> <a id="32412" href="plfa.Relations.html#32412" class="Bound">em</a><a id="32414" class="Symbol">)</a> <a id="32416" href="plfa.Relations.html#32416" class="Bound">en</a>  <a id="32420" class="Symbol">=</a>  <a id="32423" href="plfa.Relations.html#30505" class="InductiveConstructor">suc</a> <a id="32427" class="Symbol">(</a><a id="32428" href="plfa.Relations.html#32184" class="Function">e+e≡e</a> <a id="32434" href="plfa.Relations.html#32412" class="Bound">em</a> <a id="32437" href="plfa.Relations.html#32416" class="Bound">en</a><a id="32439" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.
{:/}

与相互递归的定义对应，我们用两个相互递归的函数，一个证明两个偶数之和是偶数，另一个证明
一个奇数与一个偶数之和是奇数。

{::comment}
This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.
{:/}

这是我们第一次使用相互递归的函数。因为每个标识符必须在使用前声明，我们先给出两个函数的签名，
然后再给出其定义。

{::comment}
To show that the sum of two even numbers is even, consider the
evidence that the first number is even. If it is because it is zero,
then the sum is even because the second number is even.  If it is
because it is the successor of an odd number, then the result is even
because it is the successor of the sum of an odd and an even number,
which is odd.
{:/}

要证明两个偶数之和为偶，我们考虑第一个数为偶数的证明。如果是因为第一个数为 0，
那么第二个数为偶数的证明即为和为偶数的证明。如果是因为第一个数为奇数的后继，
那么和为偶数是因为他是一个奇数和一个偶数的和的后续，而这个和是一个奇数。


{::comment}
To show that the sum of an odd and even number is odd, consider the
evidence that the first number is odd. If it is because it is the
successor of an even number, then the result is odd because it is the
successor of the sum of two even numbers, which is even.
{:/}

要证明一个奇数和一个偶数的和是奇数，我们考虑第一个数是奇数的证明。
如果是因为它是一个偶数的后继，那么和为奇数，因为它是两个偶数之和的后继，
而这个和是一个偶数。


{::comment}
#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}
{:/}

#### 练习 `o+o≡e` (延伸) {#odd-plus-odd}

{::comment}
Show that the sum of two odd numbers is even.
{:/}

证明两个奇数之和为偶数。

{::comment}
{% raw %}<pre class="Agda"><a id="34066" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="34103" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}
{:/}

#### 练习 `Bin-predicates` (延伸) {#Bin-predicates}

{::comment}
Recall that
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following:
{:/}

回忆我们在练习 [Bin][plfa.Naturals#Bin] 中定义了一个数据类型 `Bin` 来用二进制字符串表示自然数。
这个表达方法不是唯一的，因为我们在开头加任意个 0。因此，11 可以由以下方法表示：

    x1 x1 x0 x1 nil
    x1 x1 x0 x1 x0 x0 nil

{::comment}
Define a predicate
{:/}

定义一个谓词

    Can : Bin → Set

{::comment}
over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate
{:/}

其在一个二进制字符串的表示是标准的（Canonical）时成立，表示它没有开头的 0。在两个 11 的表达方式中，
第一个是标准的，而第二个不是。在定义这个谓词时，你需要一个辅助谓词：

    One : Bin → Set

{::comment}
that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).
{:/}

其仅在一个二进制字符串开头为 1 时成立。一个二进制字符串是标准的，如果它开头是 1 （表示一个正数），
或者它仅是一个 0 （表示 0）。

{::comment}
Show that increment preserves canonical bitstrings:
{:/}

证明递增可以保持标准性。

    Can x
    ------------
    Can (inc x)

{::comment}
Show that converting a natural to a bitstring always yields a
canonical bitstring:
{:/}

证明从自然数转换成的二进制字符串是标准的。

    ----------
    Can (to n)

{::comment}
Show that converting a canonical bitstring to a natural
and back is the identity:
{:/}

证明将一个标准的二进制字符串转换成自然数之后，再转换回二进制字符串与原二进制字符串相同。

    Can x
    ---------------
    to (from x) ≡ x

{::comment}
(Hint: For each of these, you may first need to prove related
properties of `One`.)
{:/}

（提示：对于每一条习题，先从 `One` 的性质开始）

{::comment}
{% raw %}<pre class="Agda"><a id="35980" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="36017" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

标准库中有类似于本章介绍的定义：

{% raw %}<pre class="Agda"><a id="36205" class="Keyword">import</a> <a id="36212" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="36221" class="Keyword">using</a> <a id="36227" class="Symbol">(</a><a id="36228" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="36231" class="Symbol">;</a> <a id="36233" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="36236" class="Symbol">;</a> <a id="36238" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="36241" class="Symbol">)</a>
<a id="36243" class="Keyword">import</a> <a id="36250" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="36270" class="Keyword">using</a> <a id="36276" class="Symbol">(</a><a id="36277" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3632" class="Function">≤-refl</a><a id="36283" class="Symbol">;</a> <a id="36285" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3815" class="Function">≤-trans</a><a id="36292" class="Symbol">;</a> <a id="36294" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3682" class="Function">≤-antisym</a><a id="36303" class="Symbol">;</a> <a id="36305" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3927" class="Function">≤-total</a><a id="36312" class="Symbol">;</a>
                                  <a id="36348" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15619" class="Function">+-monoʳ-≤</a><a id="36357" class="Symbol">;</a> <a id="36359" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15529" class="Function">+-monoˡ-≤</a><a id="36368" class="Symbol">;</a> <a id="36370" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15373" class="Function">+-mono-≤</a><a id="36378" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in
Chapter [Connectives][plfa.Connectives]),
and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` are proved differently than here,
and more arguments are implicit.
{:/}

在标准库中，`≤-total` 是使用析取定义的（我们将在 [Connectives][plfa.Connectives] 章节定义）。
`+-monoʳ-≤`、`+-monoˡ-≤` 和 `+-mono-≤` 的证明方法和本书不同。
更多的参数是隐式申明的。


## Unicode

{::comment}
This chapter uses the following unicode:

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
{:/}

本章使用了如下 Unicode 符号：

    ≤  U+2264  小于等于 (\<=, \le)
    ≥  U+2265  大于等于 (\>=, \ge)
    ˡ  U+02E1  小写字母 L 标识符 (\^l)
    ʳ  U+02B3  小写字母 R 标识符 (\^r)

{::comment}
The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows in addition to superscript letters `l` and `r`.
{:/}

`\^l` 和 `\^r` 命令给出了左右箭头，以及上标字母 `l` 和 `r`。
