---
src: ./src/plfa/Lambda.lagda.md
title     : "Lambda: Introduction to Lambda Calculus"
layout    : page
prev      : /Lists/
permalink : /Lambda/
next      : /Properties/
---

{% raw %}<pre class="Agda"><a id="151" class="Keyword">module</a> <a id="158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}" class="Module">plfa.Lambda</a> <a id="170" class="Keyword">where</a>
</pre>{% endraw %}
The _lambda-calculus_, first published by the logician Alonzo Church in
1932, is a core calculus with only three syntactic constructs:
variables, abstraction, and application.  It captures the key concept of
_functional abstraction_, which appears in pretty much every programming
language, in the form of either functions, procedures, or methods.
The _simply-typed lambda calculus_ (or STLC) is a variant of the
lambda calculus published by Church in 1940.  It has the three
constructs above for function types, plus whatever else is required
for base types. Church had a minimal base type with no operations.
We will instead echo Plotkin's _Programmable Computable
Functions_ (PCF), and add operations on natural numbers and
recursive function definitions.

This chapter formalises the simply-typed lambda calculus, giving its
syntax, small-step semantics, and typing rules.  The next chapter
[Properties][plfa.Properties]
proves its main properties, including
progress and preservation.  Following chapters will look at a number
of variants of lambda calculus.

Be aware that the approach we take here is _not_ our recommended
approach to formalisation.  Using de Bruijn indices and
inherently-typed terms, as we will do in
Chapter [DeBruijn][plfa.DeBruijn],
leads to a more compact formulation.  Nonetheless, we begin with named
variables, partly because such terms are easier to read and partly
because the development is more traditional.

The development in this chapter was inspired by the corresponding
development in Chapter _Stlc_ of _Software Foundations_
(_Programming Language Foundations_).  We differ by
representing contexts explicitly (as lists pairing identifiers with
types) rather than as partial maps (which take identifiers to types),
which corresponds better to our subsequent development of DeBruijn
notation. We also differ by taking natural numbers as the base type
rather than booleans, allowing more sophisticated examples. In
particular, we will be able to show (twice!) that two plus two is
four.

## Imports

{% raw %}<pre class="Agda"><a id="2226" class="Keyword">open</a> <a id="2231" class="Keyword">import</a> <a id="2238" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="2276" class="Keyword">using</a> <a id="2282" class="Symbol">(</a><a id="2283" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="2286" class="Symbol">;</a> <a id="2288" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#799" class="Function Operator">_≢_</a><a id="2291" class="Symbol">;</a> <a id="2293" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="2297" class="Symbol">)</a>
<a id="2299" class="Keyword">open</a> <a id="2304" class="Keyword">import</a> <a id="2311" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.html" class="Module">Data.String</a> <a id="2323" class="Keyword">using</a> <a id="2329" class="Symbol">(</a><a id="2330" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.String.html#206" class="Postulate">String</a><a id="2336" class="Symbol">;</a> <a id="2338" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">_≟_</a><a id="2341" class="Symbol">)</a>
<a id="2343" class="Keyword">open</a> <a id="2348" class="Keyword">import</a> <a id="2355" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="2364" class="Keyword">using</a> <a id="2370" class="Symbol">(</a><a id="2371" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="2372" class="Symbol">;</a> <a id="2374" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="2378" class="Symbol">;</a> <a id="2380" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="2383" class="Symbol">)</a>
<a id="2385" class="Keyword">open</a> <a id="2390" class="Keyword">import</a> <a id="2397" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="2408" class="Keyword">using</a> <a id="2414" class="Symbol">(</a><a id="2415" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="2416" class="Symbol">;</a> <a id="2418" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="2424" class="Symbol">)</a>
<a id="2426" class="Keyword">open</a> <a id="2431" class="Keyword">import</a> <a id="2438" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="2455" class="Keyword">using</a> <a id="2461" class="Symbol">(</a><a id="2462" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a><a id="2465" class="Symbol">;</a> <a id="2467" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a><a id="2470" class="Symbol">;</a> <a id="2472" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a><a id="2474" class="Symbol">;</a> <a id="2476" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="2478" class="Symbol">)</a>
<a id="2480" class="Keyword">open</a> <a id="2485" class="Keyword">import</a> <a id="2492" href="https://agda.github.io/agda-stdlib/v1.1/Data.List.html" class="Module">Data.List</a> <a id="2502" class="Keyword">using</a> <a id="2508" class="Symbol">(</a><a id="2509" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.List.html#121" class="Datatype">List</a><a id="2513" class="Symbol">;</a> <a id="2515" href="Agda.Builtin.List.html#173" class="InductiveConstructor Operator">_∷_</a><a id="2518" class="Symbol">;</a> <a id="2520" href="https://agda.github.io/agda-stdlib/v1.1/Data.List.Base.html#8786" class="InductiveConstructor">[]</a><a id="2522" class="Symbol">)</a>
</pre>{% endraw %}
## Syntax of terms

Terms have seven constructs. Three are for the core lambda calculus:

  * Variables `` ` x ``
  * Abstractions `ƛ x ⇒ N`
  * Applications `L · M`

Three are for the naturals:

  * Zero `` `zero ``
  * Successor `` `suc ``
  * Case `` case L [zero⇒ M |suc x ⇒ N ] ``

And one is for recursion:

  * Fixpoint `μ x ⇒ M`

Abstraction is also called _lambda abstraction_, and is the construct
from which the calculus takes its name.

With the exception of variables and fixpoints, each term
form either constructs a value of a given type (abstractions yield functions,
zero and successor yield natural numbers) or deconstructs it (applications use functions,
case terms use naturals). We will see this again when we come
to the rules for assigning types to terms, where constructors
correspond to introduction rules and deconstructors to eliminators.

Here is the syntax of terms in Backus-Naur Form (BNF):

    L, M, N  ::=
      ` x  |  ƛ x ⇒ N  |  L · M  |
      `zero  |  `suc M  |  case L [zero⇒ M |suc x ⇒ N]  |
      μ x ⇒ M

And here it is formalised in Agda:
{% raw %}<pre class="Agda"><a id="Id"></a><a id="3616" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3616" class="Function">Id</a> <a id="3619" class="Symbol">:</a> <a id="3621" class="PrimitiveType">Set</a>
<a id="3625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3616" class="Function">Id</a> <a id="3628" class="Symbol">=</a> <a id="3630" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.String.html#206" class="Postulate">String</a>

<a id="3638" class="Keyword">infix</a>  <a id="3645" class="Number">5</a>  <a id="3648" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3775" class="InductiveConstructor Operator">ƛ_⇒_</a>
<a id="3653" class="Keyword">infix</a>  <a id="3660" class="Number">5</a>  <a id="3663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4004" class="InductiveConstructor Operator">μ_⇒_</a>
<a id="3668" class="Keyword">infixl</a> <a id="3675" class="Number">7</a>  <a id="3678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33590" class="InductiveConstructor Operator">_·_</a>
<a id="3682" class="Keyword">infix</a>  <a id="3689" class="Number">8</a>  <a id="3692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3903" class="InductiveConstructor Operator">`suc_</a>
<a id="3698" class="Keyword">infix</a>  <a id="3705" class="Number">9</a>  <a id="3708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3736" class="InductiveConstructor Operator">`_</a>

<a id="3712" class="Keyword">data</a> <a id="Term"></a><a id="3717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3717" class="Datatype">Term</a> <a id="3722" class="Symbol">:</a> <a id="3724" class="PrimitiveType">Set</a> <a id="3728" class="Keyword">where</a>
  <a id="Term.`_"></a><a id="3736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3736" class="InductiveConstructor Operator">`_</a>                      <a id="3760" class="Symbol">:</a>  <a id="3763" href="plfa.Lambda.html#3616" class="Function">Id</a> <a id="3766" class="Symbol">→</a> <a id="3768" href="plfa.Lambda.html#3717" class="Datatype">Term</a>
  <a id="Term.ƛ_⇒_"></a><a id="3775" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3775" class="InductiveConstructor Operator">ƛ_⇒_</a>                    <a id="3799" class="Symbol">:</a>  <a id="3802" href="plfa.Lambda.html#3616" class="Function">Id</a> <a id="3805" class="Symbol">→</a> <a id="3807" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="3812" class="Symbol">→</a> <a id="3814" href="plfa.Lambda.html#3717" class="Datatype">Term</a>
  <a id="Term._·_"></a><a id="3821" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3821" class="InductiveConstructor Operator">_·_</a>                     <a id="3845" class="Symbol">:</a>  <a id="3848" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="3853" class="Symbol">→</a> <a id="3855" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="3860" class="Symbol">→</a> <a id="3862" href="plfa.Lambda.html#3717" class="Datatype">Term</a>
  <a id="Term.`zero"></a><a id="3869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3869" class="InductiveConstructor">`zero</a>                   <a id="3893" class="Symbol">:</a>  <a id="3896" href="plfa.Lambda.html#3717" class="Datatype">Term</a>
  <a id="Term.`suc_"></a><a id="3903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3903" class="InductiveConstructor Operator">`suc_</a>                   <a id="3927" class="Symbol">:</a>  <a id="3930" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="3935" class="Symbol">→</a> <a id="3937" href="plfa.Lambda.html#3717" class="Datatype">Term</a>
  <a id="Term.case_[zero⇒_|suc_⇒_]"></a><a id="3944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3944" class="InductiveConstructor Operator">case_[zero⇒_|suc_⇒_]</a>    <a id="3968" class="Symbol">:</a>  <a id="3971" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="3976" class="Symbol">→</a> <a id="3978" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="3983" class="Symbol">→</a> <a id="3985" href="plfa.Lambda.html#3616" class="Function">Id</a> <a id="3988" class="Symbol">→</a> <a id="3990" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="3995" class="Symbol">→</a> <a id="3997" href="plfa.Lambda.html#3717" class="Datatype">Term</a>
  <a id="Term.μ_⇒_"></a><a id="4004" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4004" class="InductiveConstructor Operator">μ_⇒_</a>                    <a id="4028" class="Symbol">:</a>  <a id="4031" href="plfa.Lambda.html#3616" class="Function">Id</a> <a id="4034" class="Symbol">→</a> <a id="4036" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="4041" class="Symbol">→</a> <a id="4043" href="plfa.Lambda.html#3717" class="Datatype">Term</a>
</pre>{% endraw %}We represent identifiers by strings.  We choose precedence so that
lambda abstraction and fixpoint bind least tightly, then application,
then successor, and tightest of all is the constructor for variables.
Case expressions are self-bracketing.


### Example terms

Here are some example terms: the natural number two,
a function that adds naturals,
and a term that computes two plus two:
{% raw %}<pre class="Agda"><a id="two"></a><a id="4445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4445" class="Function">two</a> <a id="4449" class="Symbol">:</a> <a id="4451" href="plfa.Lambda.html#3717" class="Datatype">Term</a>
<a id="4456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4445" class="Function">two</a> <a id="4460" class="Symbol">=</a> <a id="4462" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="4467" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="4472" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a>

<a id="plus"></a><a id="4479" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4479" class="Function">plus</a> <a id="4484" class="Symbol">:</a> <a id="4486" href="plfa.Lambda.html#3717" class="Datatype">Term</a>
<a id="4491" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4479" class="Function">plus</a> <a id="4496" class="Symbol">=</a> <a id="4498" href="plfa.Lambda.html#4004" class="InductiveConstructor Operator">μ</a> <a id="4500" class="String">&quot;+&quot;</a> <a id="4504" href="plfa.Lambda.html#4004" class="InductiveConstructor Operator">⇒</a> <a id="4506" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="4508" class="String">&quot;m&quot;</a> <a id="4512" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="4514" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="4516" class="String">&quot;n&quot;</a> <a id="4520" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a>
         <a id="4531" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3944" class="InductiveConstructor Operator">case</a> <a id="4536" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="4538" class="String">&quot;m&quot;</a>
           <a id="4553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3944" class="InductiveConstructor Operator">[zero⇒</a> <a id="4560" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="4562" class="String">&quot;n&quot;</a>
           <a id="4577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3944" class="InductiveConstructor Operator">|suc</a> <a id="4582" class="String">&quot;m&quot;</a> <a id="4586" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">⇒</a> <a id="4588" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="4593" class="Symbol">(</a><a id="4594" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="4596" class="String">&quot;+&quot;</a> <a id="4600" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="4602" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="4604" class="String">&quot;m&quot;</a> <a id="4608" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="4610" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="4612" class="String">&quot;n&quot;</a><a id="4615" class="Symbol">)</a> <a id="4617" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">]</a>
</pre>{% endraw %}The recursive definition of addition is similar to our original
definition of `_+_` for naturals, as given in
Chapter [Naturals][plfa.Naturals#plus].
Here variable "m" is bound twice, once in a lambda abstraction and once in
the successor branch of the case; the first use of "m" refers to
the former and the second to the latter.  Any use of "m" in the successor branch
must refer to the latter binding, and so we say that the latter binding _shadows_
the former.  Later we will confirm that two plus two is four, in other words that
the term

    plus · two · two

reduces to `` `suc `suc `suc `suc `zero ``.

As a second example, we use higher-order functions to represent
natural numbers.  In particular, the number _n_ is represented by a
function that accepts two arguments and applies the first _n_ times to the
second.  This is called the _Church representation_ of the
naturals.  Here are some example terms: the Church numeral two, a
function that adds Church numerals, a function to compute successor,
and a term that computes two plus two:
{% raw %}<pre class="Agda"><a id="twoᶜ"></a><a id="5679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5679" class="Function">twoᶜ</a> <a id="5684" class="Symbol">:</a> <a id="5686" href="plfa.Lambda.html#3717" class="Datatype">Term</a>
<a id="5691" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5679" class="Function">twoᶜ</a> <a id="5696" class="Symbol">=</a>  <a id="5699" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="5701" class="String">&quot;s&quot;</a> <a id="5705" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="5707" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="5709" class="String">&quot;z&quot;</a> <a id="5713" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="5715" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="5717" class="String">&quot;s&quot;</a> <a id="5721" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="5723" class="Symbol">(</a><a id="5724" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="5726" class="String">&quot;s&quot;</a> <a id="5730" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="5732" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="5734" class="String">&quot;z&quot;</a><a id="5737" class="Symbol">)</a>

<a id="plusᶜ"></a><a id="5740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5740" class="Function">plusᶜ</a> <a id="5746" class="Symbol">:</a> <a id="5748" href="plfa.Lambda.html#3717" class="Datatype">Term</a>
<a id="5753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5740" class="Function">plusᶜ</a> <a id="5759" class="Symbol">=</a>  <a id="5762" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="5764" class="String">&quot;m&quot;</a> <a id="5768" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="5770" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="5772" class="String">&quot;n&quot;</a> <a id="5776" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="5778" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="5780" class="String">&quot;s&quot;</a> <a id="5784" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="5786" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="5788" class="String">&quot;z&quot;</a> <a id="5792" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a>
         <a id="5803" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3736" class="InductiveConstructor Operator">`</a> <a id="5805" class="String">&quot;m&quot;</a> <a id="5809" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="5811" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="5813" class="String">&quot;s&quot;</a> <a id="5817" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="5819" class="Symbol">(</a><a id="5820" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="5822" class="String">&quot;n&quot;</a> <a id="5826" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="5828" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="5830" class="String">&quot;s&quot;</a> <a id="5834" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="5836" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="5838" class="String">&quot;z&quot;</a><a id="5841" class="Symbol">)</a>

<a id="sucᶜ"></a><a id="5844" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5844" class="Function">sucᶜ</a> <a id="5849" class="Symbol">:</a> <a id="5851" href="plfa.Lambda.html#3717" class="Datatype">Term</a>
<a id="5856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5844" class="Function">sucᶜ</a> <a id="5861" class="Symbol">=</a> <a id="5863" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="5865" class="String">&quot;n&quot;</a> <a id="5869" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="5871" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="5876" class="Symbol">(</a><a id="5877" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="5879" class="String">&quot;n&quot;</a><a id="5882" class="Symbol">)</a>
</pre>{% endraw %}The Church numeral for two takes two arguments `s` and `z`
and applies `s` twice to `z`.
Addition takes two numerals `m` and `n`, a
function `s` and an argument `z`, and it uses `m` to apply `s` to the
result of using `n` to apply `s` to `z`; hence `s` is applied `m` plus
`n` times to `z`, yielding the Church numeral for the sum of `m` and
`n`.  For convenience, we define a function that computes successor.
To convert a Church numeral to the corresponding natural, we apply
it to the `sucᶜ` function and the natural number zero.
Again, later we will confirm that two plus two is four,
in other words that the term

    plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero

reduces to `` `suc `suc `suc `suc `zero ``.


#### Exercise `mul` (recommended)

Write out the definition of a lambda term that multiplies
two natural numbers.  Your definition may use `plus` as
defined earlier.

{% raw %}<pre class="Agda"><a id="6764" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `mulᶜ`

Write out the definition of a lambda term that multiplies
two natural numbers represented as Church numerals. Your
definition may use `plusᶜ` as defined earlier (or may not
— there are nice definitions both ways).

{% raw %}<pre class="Agda"><a id="7034" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `primed` (stretch)

Some people find it annoying to write `` ` "x" `` instead of `x`.
We can make examples with lambda terms slightly easier to write
by adding the following definitions:
{% raw %}<pre class="Agda"><a id="ƛ′_⇒_"></a><a id="7268" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7268" class="Function Operator">ƛ′_⇒_</a> <a id="7274" class="Symbol">:</a> <a id="7276" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="7281" class="Symbol">→</a> <a id="7283" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="7288" class="Symbol">→</a> <a id="7290" href="plfa.Lambda.html#3717" class="Datatype">Term</a>
<a id="7295" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7268" class="Function Operator">ƛ′</a> <a id="7298" class="Symbol">(</a><a id="7299" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="7301" href="plfa.Lambda.html#7301" class="Bound">x</a><a id="7302" class="Symbol">)</a> <a id="7304" href="plfa.Lambda.html#7268" class="Function Operator">⇒</a> <a id="7306" href="plfa.Lambda.html#7306" class="Bound">N</a>  <a id="7309" class="Symbol">=</a>  <a id="7312" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="7314" href="plfa.Lambda.html#7301" class="Bound">x</a> <a id="7316" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="7318" href="plfa.Lambda.html#7306" class="Bound">N</a>
<a id="7320" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7268" class="CatchallClause Function Operator">ƛ′</a><a id="7322" class="CatchallClause"> </a><a id="7323" class="CatchallClause Symbol">_</a><a id="7324" class="CatchallClause"> </a><a id="7325" href="plfa.Lambda.html#7268" class="CatchallClause Function Operator">⇒</a><a id="7326" class="CatchallClause"> </a><a id="7327" class="CatchallClause Symbol">_</a>      <a id="7334" class="Symbol">=</a>  <a id="7337" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="7344" href="plfa.Lambda.html#7373" class="Postulate">impossible</a>
  <a id="7357" class="Keyword">where</a> <a id="7363" class="Keyword">postulate</a> <a id="7373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7373" class="Postulate">impossible</a> <a id="7384" class="Symbol">:</a> <a id="7386" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>

<a id="case′_[zero⇒_|suc_⇒_]"></a><a id="7389" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7389" class="Function Operator">case′_[zero⇒_|suc_⇒_]</a> <a id="7411" class="Symbol">:</a> <a id="7413" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="7418" class="Symbol">→</a> <a id="7420" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="7425" class="Symbol">→</a> <a id="7427" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="7432" class="Symbol">→</a> <a id="7434" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="7439" class="Symbol">→</a> <a id="7441" href="plfa.Lambda.html#3717" class="Datatype">Term</a>
<a id="7446" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7389" class="Function Operator">case′</a> <a id="7452" href="plfa.Lambda.html#7452" class="Bound">L</a> <a id="7454" href="plfa.Lambda.html#7389" class="Function Operator">[zero⇒</a> <a id="7461" href="plfa.Lambda.html#7461" class="Bound">M</a> <a id="7463" href="plfa.Lambda.html#7389" class="Function Operator">|suc</a> <a id="7468" class="Symbol">(</a><a id="7469" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="7471" href="plfa.Lambda.html#7471" class="Bound">x</a><a id="7472" class="Symbol">)</a> <a id="7474" href="plfa.Lambda.html#7389" class="Function Operator">⇒</a> <a id="7476" href="plfa.Lambda.html#7476" class="Bound">N</a> <a id="7478" href="plfa.Lambda.html#7389" class="Function Operator">]</a>  <a id="7481" class="Symbol">=</a>  <a id="7484" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">case</a> <a id="7489" href="plfa.Lambda.html#7452" class="Bound">L</a> <a id="7491" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">[zero⇒</a> <a id="7498" href="plfa.Lambda.html#7461" class="Bound">M</a> <a id="7500" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">|suc</a> <a id="7505" href="plfa.Lambda.html#7471" class="Bound">x</a> <a id="7507" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">⇒</a> <a id="7509" href="plfa.Lambda.html#7476" class="Bound">N</a> <a id="7511" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">]</a>
<a id="7513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7389" class="CatchallClause Function Operator">case′</a><a id="7518" class="CatchallClause"> </a><a id="7519" class="CatchallClause Symbol">_</a><a id="7520" class="CatchallClause"> </a><a id="7521" href="plfa.Lambda.html#7389" class="CatchallClause Function Operator">[zero⇒</a><a id="7527" class="CatchallClause"> </a><a id="7528" class="CatchallClause Symbol">_</a><a id="7529" class="CatchallClause"> </a><a id="7530" href="plfa.Lambda.html#7389" class="CatchallClause Function Operator">|suc</a><a id="7534" class="CatchallClause"> </a><a id="7535" class="CatchallClause Symbol">_</a><a id="7536" class="CatchallClause"> </a><a id="7537" href="plfa.Lambda.html#7389" class="CatchallClause Function Operator">⇒</a><a id="7538" class="CatchallClause"> </a><a id="7539" class="CatchallClause Symbol">_</a><a id="7540" class="CatchallClause"> </a><a id="7541" href="plfa.Lambda.html#7389" class="CatchallClause Function Operator">]</a>      <a id="7548" class="Symbol">=</a>  <a id="7551" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="7558" href="plfa.Lambda.html#7587" class="Postulate">impossible</a>
  <a id="7571" class="Keyword">where</a> <a id="7577" class="Keyword">postulate</a> <a id="7587" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7587" class="Postulate">impossible</a> <a id="7598" class="Symbol">:</a> <a id="7600" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>

<a id="μ′_⇒_"></a><a id="7603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7603" class="Function Operator">μ′_⇒_</a> <a id="7609" class="Symbol">:</a> <a id="7611" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="7616" class="Symbol">→</a> <a id="7618" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="7623" class="Symbol">→</a> <a id="7625" href="plfa.Lambda.html#3717" class="Datatype">Term</a>
<a id="7630" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7603" class="Function Operator">μ′</a> <a id="7633" class="Symbol">(</a><a id="7634" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="7636" href="plfa.Lambda.html#7636" class="Bound">x</a><a id="7637" class="Symbol">)</a> <a id="7639" href="plfa.Lambda.html#7603" class="Function Operator">⇒</a> <a id="7641" href="plfa.Lambda.html#7641" class="Bound">N</a>  <a id="7644" class="Symbol">=</a>  <a id="7647" href="plfa.Lambda.html#4004" class="InductiveConstructor Operator">μ</a> <a id="7649" href="plfa.Lambda.html#7636" class="Bound">x</a> <a id="7651" href="plfa.Lambda.html#4004" class="InductiveConstructor Operator">⇒</a> <a id="7653" href="plfa.Lambda.html#7641" class="Bound">N</a>
<a id="7655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7603" class="CatchallClause Function Operator">μ′</a><a id="7657" class="CatchallClause"> </a><a id="7658" class="CatchallClause Symbol">_</a><a id="7659" class="CatchallClause"> </a><a id="7660" href="plfa.Lambda.html#7603" class="CatchallClause Function Operator">⇒</a><a id="7661" class="CatchallClause"> </a><a id="7662" class="CatchallClause Symbol">_</a>      <a id="7669" class="Symbol">=</a>  <a id="7672" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="7679" href="plfa.Lambda.html#7708" class="Postulate">impossible</a>
  <a id="7692" class="Keyword">where</a> <a id="7698" class="Keyword">postulate</a> <a id="7708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7708" class="Postulate">impossible</a> <a id="7719" class="Symbol">:</a> <a id="7721" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
</pre>{% endraw %}The definition of `plus` can now be written as follows:
{% raw %}<pre class="Agda"><a id="plus′"></a><a id="7787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7787" class="Function">plus′</a> <a id="7793" class="Symbol">:</a> <a id="7795" href="plfa.Lambda.html#3717" class="Datatype">Term</a>
<a id="7800" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7787" class="Function">plus′</a> <a id="7806" class="Symbol">=</a> <a id="7808" href="plfa.Lambda.html#7603" class="Function Operator">μ′</a> <a id="7811" href="plfa.Lambda.html#7918" class="Function">+</a> <a id="7813" href="plfa.Lambda.html#7603" class="Function Operator">⇒</a> <a id="7815" href="plfa.Lambda.html#7268" class="Function Operator">ƛ′</a> <a id="7818" href="plfa.Lambda.html#7932" class="Function">m</a> <a id="7820" href="plfa.Lambda.html#7268" class="Function Operator">⇒</a> <a id="7822" href="plfa.Lambda.html#7268" class="Function Operator">ƛ′</a> <a id="7825" href="plfa.Lambda.html#7946" class="Function">n</a> <a id="7827" href="plfa.Lambda.html#7268" class="Function Operator">⇒</a>
          <a id="7839" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7389" class="Function Operator">case′</a> <a id="7845" href="plfa.Lambda.html#7932" class="Function">m</a>
            <a id="7859" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7389" class="Function Operator">[zero⇒</a> <a id="7866" href="plfa.Lambda.html#7946" class="Function">n</a>
            <a id="7880" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7389" class="Function Operator">|suc</a> <a id="7885" href="plfa.Lambda.html#7932" class="Function">m</a> <a id="7887" href="plfa.Lambda.html#7389" class="Function Operator">⇒</a> <a id="7889" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="7894" class="Symbol">(</a><a id="7895" href="plfa.Lambda.html#7918" class="Function">+</a> <a id="7897" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="7899" href="plfa.Lambda.html#7932" class="Function">m</a> <a id="7901" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="7903" href="plfa.Lambda.html#7946" class="Function">n</a><a id="7904" class="Symbol">)</a> <a id="7906" href="plfa.Lambda.html#7389" class="Function Operator">]</a>
  <a id="7910" class="Keyword">where</a>
  <a id="7918" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7918" class="Function">+</a>  <a id="7921" class="Symbol">=</a>  <a id="7924" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="7926" class="String">&quot;+&quot;</a>
  <a id="7932" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7932" class="Function">m</a>  <a id="7935" class="Symbol">=</a>  <a id="7938" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="7940" class="String">&quot;m&quot;</a>
  <a id="7946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7946" class="Function">n</a>  <a id="7949" class="Symbol">=</a>  <a id="7952" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="7954" class="String">&quot;n&quot;</a>
</pre>{% endraw %}Write out the definition of multiplication in the same style.


### Formal vs informal

In informal presentation of formal semantics, one uses choice of
variable name to disambiguate and writes `x` rather than `` ` x ``
for a term that is a variable. Agda requires we distinguish.

Similarly, informal presentation often use the same notation for
function types, lambda abstraction, and function application in both
the _object language_ (the language one is describing) and the
_meta-language_ (the language in which the description is written),
trusting readers can use context to distinguish the two.  Agda is
not quite so forgiving, so here we use `ƛ x ⇒ N` and `L · M` for the
object language, as compared to `λ x → N` and `L M` in our
meta-language, https://agda.github.io/agda-stdlib/v1.1/Agda.


### Bound and free variables

In an abstraction `ƛ x ⇒ N` we call `x` the _bound_ variable
and `N` the _body_ of the abstraction.  A central feature
of lambda calculus is that consistent renaming of bound variables
leaves the meaning of a term unchanged.  Thus the five terms

* `` ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
* `` ƛ "f" ⇒ ƛ "x" ⇒ ` "f" · (` "f" · ` "x") ``
* `` ƛ "sam" ⇒ ƛ "zelda" ⇒ ` "sam" · (` "sam" · ` "zelda") ``
* `` ƛ "z" ⇒ ƛ "s" ⇒ ` "z" · (` "z" · ` "s") ``
* `` ƛ "😇" ⇒ ƛ "😈" ⇒ ` "😇" · (` "😇" · ` "😈" ) ``

are all considered equivalent.  Following the convention introduced
by Haskell Curry, who used the Greek letter `α` (_alpha_) to label such rules,
this equivalence relation is called _alpha renaming_.

As we descend from a term into its subterms, variables
that are bound may become free.  Consider the following terms:

* `` ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
  has both `s` and `z` as bound variables.

* `` ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
  has `z` bound and `s` free.

* `` ` "s" · (` "s" · ` "z") ``
  has both `s` and `z` as free variables.

We say that a term with no free variables is _closed_; otherwise it is
_open_.  Of the three terms above, the first is closed and the other
two are open.  We will focus on reduction of closed terms.

Different occurrences of a variable may be bound and free.
In the term

    (ƛ "x" ⇒ ` "x") · ` "x"

the inner occurrence of `x` is bound while the outer occurrence is free.
By alpha renaming, the term above is equivalent to

    (ƛ "y" ⇒ ` "y") · ` "x"

in which `y` is bound and `x` is free.  A common convention, called the
_Barendregt convention_, is to use alpha renaming to ensure that the bound
variables in a term are distinct from the free variables, which can
avoid confusions that may arise if bound and free variables have the
same names.

Case and recursion also introduce bound variables, which are also subject
to alpha renaming. In the term

    μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m"
        [zero⇒ ` "n"
        |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

notice that there are two binding occurrences of `m`, one in the first
line and one in the last line.  It is equivalent to the following term,

    μ "plus" ⇒ ƛ "x" ⇒ ƛ "y" ⇒
      case ` "x"
        [zero⇒ ` "y"
        |suc "x′" ⇒ `suc (` "plus" · ` "x′" · ` "y") ]

where the two binding occurrences corresponding to `m` now have distinct
names, `x` and `x′`.


## Values

A _value_ is a term that corresponds to an answer.
Thus, `` `suc `suc `suc `suc `zero `` is a value,
while `` plus · two · two `` is not.
Following convention, we treat all function abstractions
as values; thus, `` plus `` by itself is considered a value.

The predicate `Value M` holds if term `M` is a value:

{% raw %}<pre class="Agda"><a id="11485" class="Keyword">data</a> <a id="Value"></a><a id="11490" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11490" class="Datatype">Value</a> <a id="11496" class="Symbol">:</a> <a id="11498" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="11503" class="Symbol">→</a> <a id="11505" class="PrimitiveType">Set</a> <a id="11509" class="Keyword">where</a>

  <a id="Value.V-ƛ"></a><a id="11518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11518" class="InductiveConstructor">V-ƛ</a> <a id="11522" class="Symbol">:</a> <a id="11524" class="Symbol">∀</a> <a id="11526" class="Symbol">{</a><a id="11527" href="plfa.Lambda.html#11527" class="Bound">x</a> <a id="11529" href="plfa.Lambda.html#11529" class="Bound">N</a><a id="11530" class="Symbol">}</a>
      <a id="11538" class="Comment">---------------</a>
    <a id="11558" class="Symbol">→</a> <a id="11560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11490" class="Datatype">Value</a> <a id="11566" class="Symbol">(</a><a id="11567" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="11569" href="plfa.Lambda.html#11527" class="Bound">x</a> <a id="11571" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="11573" href="plfa.Lambda.html#11529" class="Bound">N</a><a id="11574" class="Symbol">)</a>

  <a id="Value.V-zero"></a><a id="11579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11579" class="InductiveConstructor">V-zero</a> <a id="11586" class="Symbol">:</a>
      <a id="11594" class="Comment">-----------</a>
      <a id="11612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11490" class="Datatype">Value</a> <a id="11618" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a>

  <a id="Value.V-suc"></a><a id="11627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11627" class="InductiveConstructor">V-suc</a> <a id="11633" class="Symbol">:</a> <a id="11635" class="Symbol">∀</a> <a id="11637" class="Symbol">{</a><a id="11638" href="plfa.Lambda.html#11638" class="Bound">V</a><a id="11639" class="Symbol">}</a>
    <a id="11645" class="Symbol">→</a> <a id="11647" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11490" class="Datatype">Value</a> <a id="11653" href="plfa.Lambda.html#11638" class="Bound">V</a>
      <a id="11661" class="Comment">--------------</a>
    <a id="11680" class="Symbol">→</a> <a id="11682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11490" class="Datatype">Value</a> <a id="11688" class="Symbol">(</a><a id="11689" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="11694" href="plfa.Lambda.html#11638" class="Bound">V</a><a id="11695" class="Symbol">)</a>
</pre>{% endraw %}
In what follows, we let `V` and `W` range over values.


### Formal vs informal

In informal presentations of formal semantics, using
`V` as the name of a metavariable is sufficient to
indicate that it is a value. In Agda, we must explicitly
invoke the `Value` predicate.

### Other approaches

An alternative is not to focus on closed terms,
to treat variables as values, and to treat
`ƛ x ⇒ N` as a value only if `N` is a value.
Indeed, this is how Agda normalises terms.
We consider this approach in
Chapter [Untyped][plfa.Untyped].


## Substitution

The heart of lambda calculus is the operation of
substituting one term for a variable in another term.
Substitution plays a key role in defining the
operational semantics of function application.
For instance, we have

      (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) · sucᶜ · `zero
    —→
      (ƛ "z" ⇒ sucᶜ · (sucᶜ · "z")) · `zero
    —→
      sucᶜ · (sucᶜ · `zero)

where we substitute `sucᶜ` for `` ` "s" `` and `` `zero `` for `` ` "z" ``
in the body of the function abstraction.

We write substitution as `N [ x := V ]`, meaning
"substitute term `V` for free occurrences of variable `x` in term `N`",
or, more compactly, "substitute `V` for `x` in `N`",
or equivalently, "in `N` replace `x` by `V`".
Substitution works if `V` is any closed term;
it need not be a value, but we use `V` since in fact we
usually substitute values.

Here are some examples:

* `` (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] `` yields
  `` ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z") ``.
* `` (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] `` yields
  `` sucᶜ · (sucᶜ · `zero) ``.
* `` (ƛ "x" ⇒ ` "y") [ "y" := `zero ] `` yields `` ƛ "x" ⇒ `zero ``.
* `` (ƛ "x" ⇒ ` "x") [ "x" := `zero ] `` yields `` ƛ "x" ⇒ ` "x" ``.
* `` (ƛ "y" ⇒ ` "y") [ "x" := `zero ] `` yields `` ƛ "y" ⇒ ` "y" ``.

In the last but one example, substituting `` `zero `` for `x` in
`` ƛ "x" ⇒ ` "x" `` does _not_ yield `` ƛ "x" ⇒ `zero ``,
since `x` is bound in the lambda abstraction.
The choice of bound names is irrelevant: both
`` ƛ "x" ⇒ ` "x" `` and `` ƛ "y" ⇒ ` "y" `` stand for the
identity function.  One way to think of this is that `x` within
the body of the abstraction stands for a _different_ variable than
`x` outside the abstraction, they just happen to have the same name.

We will give a definition of substitution that is only valid
when term substituted for the variable is closed. This is because
substitution by terms that are _not_ closed may require renaming
of bound variables. For example:

* `` (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero] `` should not yield <br/>
  `` (ƛ "x" ⇒ ` "x" · (` "x" · `zero)) ``.

Instead, we should rename the bound variable to avoid capture:

* `` (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero ] `` should yield <br/>
  `` ƛ "x′" ⇒ ` "x′" · (` "x" · `zero) ``.

Here `x′` is a fresh variable distinct from `x`.
Formal definition of substitution with suitable renaming is considerably
more complex, so we avoid it by restricting to substitution by closed terms,
which will be adequate for our purposes.

Here is the formal definition of substitution by closed terms in Agda:

{% raw %}<pre class="Agda"><a id="14841" class="Keyword">infix</a> <a id="14847" class="Number">9</a> <a id="14849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#14858" class="Function Operator">_[_:=_]</a>

<a id="_[_:=_]"></a><a id="14858" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#14858" class="Function Operator">_[_:=_]</a> <a id="14866" class="Symbol">:</a> <a id="14868" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="14873" class="Symbol">→</a> <a id="14875" href="plfa.Lambda.html#3616" class="Function">Id</a> <a id="14878" class="Symbol">→</a> <a id="14880" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="14885" class="Symbol">→</a> <a id="14887" href="plfa.Lambda.html#3717" class="Datatype">Term</a>
<a id="14892" class="Symbol">(</a><a id="14893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3736" class="InductiveConstructor Operator">`</a> <a id="14895" href="plfa.Lambda.html#14895" class="Bound">x</a><a id="14896" class="Symbol">)</a> <a id="14898" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="14900" href="plfa.Lambda.html#14900" class="Bound">y</a> <a id="14902" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="14905" href="plfa.Lambda.html#14905" class="Bound">V</a> <a id="14907" href="plfa.Lambda.html#14858" class="Function Operator">]</a> <a id="14909" class="Keyword">with</a> <a id="14914" href="plfa.Lambda.html#14895" class="Bound">x</a> <a id="14916" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="14918" href="plfa.Lambda.html#14900" class="Bound">y</a>
<a id="14920" class="Symbol">...</a> <a id="14924" class="Symbol">|</a> <a id="14926" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="14930" class="Symbol">_</a>          <a id="14941" class="Symbol">=</a>  <a id="14944" class="Bound">V</a>
<a id="14946" class="Symbol">...</a> <a id="14950" class="Symbol">|</a> <a id="14952" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="14956" class="Symbol">_</a>          <a id="14967" class="Symbol">=</a>  <a id="14970" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3736" class="InductiveConstructor Operator">`</a> <a id="14972" class="Bound">x</a>
<a id="14974" class="Symbol">(</a><a id="14975" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3775" class="InductiveConstructor Operator">ƛ</a> <a id="14977" href="plfa.Lambda.html#14977" class="Bound">x</a> <a id="14979" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="14981" href="plfa.Lambda.html#14981" class="Bound">N</a><a id="14982" class="Symbol">)</a> <a id="14984" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="14986" href="plfa.Lambda.html#14986" class="Bound">y</a> <a id="14988" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="14991" href="plfa.Lambda.html#14991" class="Bound">V</a> <a id="14993" href="plfa.Lambda.html#14858" class="Function Operator">]</a> <a id="14995" class="Keyword">with</a> <a id="15000" href="plfa.Lambda.html#14977" class="Bound">x</a> <a id="15002" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15004" href="plfa.Lambda.html#14986" class="Bound">y</a>
<a id="15006" class="Symbol">...</a> <a id="15010" class="Symbol">|</a> <a id="15012" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15016" class="Symbol">_</a>          <a id="15027" class="Symbol">=</a>  <a id="15030" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3775" class="InductiveConstructor Operator">ƛ</a> <a id="15032" class="Bound">x</a> <a id="15034" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="15036" class="Bound">N</a>
<a id="15038" class="Symbol">...</a> <a id="15042" class="Symbol">|</a> <a id="15044" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15048" class="Symbol">_</a>          <a id="15059" class="Symbol">=</a>  <a id="15062" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3775" class="InductiveConstructor Operator">ƛ</a> <a id="15064" class="Bound">x</a> <a id="15066" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="15068" class="Bound">N</a> <a id="15070" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="15072" class="Bound">y</a> <a id="15074" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="15077" class="Bound">V</a> <a id="15079" href="plfa.Lambda.html#14858" class="Function Operator">]</a>
<a id="15081" class="Symbol">(</a><a id="15082" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#15082" class="Bound">L</a> <a id="15084" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="15086" href="plfa.Lambda.html#15086" class="Bound">M</a><a id="15087" class="Symbol">)</a> <a id="15089" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="15091" href="plfa.Lambda.html#15091" class="Bound">y</a> <a id="15093" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="15096" href="plfa.Lambda.html#15096" class="Bound">V</a> <a id="15098" href="plfa.Lambda.html#14858" class="Function Operator">]</a>   <a id="15102" class="Symbol">=</a>  <a id="15105" href="plfa.Lambda.html#15082" class="Bound">L</a> <a id="15107" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="15109" href="plfa.Lambda.html#15091" class="Bound">y</a> <a id="15111" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="15114" href="plfa.Lambda.html#15096" class="Bound">V</a> <a id="15116" href="plfa.Lambda.html#14858" class="Function Operator">]</a> <a id="15118" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="15120" href="plfa.Lambda.html#15086" class="Bound">M</a> <a id="15122" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="15124" href="plfa.Lambda.html#15091" class="Bound">y</a> <a id="15126" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="15129" href="plfa.Lambda.html#15096" class="Bound">V</a> <a id="15131" href="plfa.Lambda.html#14858" class="Function Operator">]</a>
<a id="15133" class="Symbol">(</a><a id="15134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3869" class="InductiveConstructor">`zero</a><a id="15139" class="Symbol">)</a> <a id="15141" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="15143" href="plfa.Lambda.html#15143" class="Bound">y</a> <a id="15145" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="15148" href="plfa.Lambda.html#15148" class="Bound">V</a> <a id="15150" href="plfa.Lambda.html#14858" class="Function Operator">]</a>   <a id="15154" class="Symbol">=</a>  <a id="15157" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a>
<a id="15163" class="Symbol">(</a><a id="15164" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3903" class="InductiveConstructor Operator">`suc</a> <a id="15169" href="plfa.Lambda.html#15169" class="Bound">M</a><a id="15170" class="Symbol">)</a> <a id="15172" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="15174" href="plfa.Lambda.html#15174" class="Bound">y</a> <a id="15176" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="15179" href="plfa.Lambda.html#15179" class="Bound">V</a> <a id="15181" href="plfa.Lambda.html#14858" class="Function Operator">]</a>  <a id="15184" class="Symbol">=</a>  <a id="15187" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="15192" href="plfa.Lambda.html#15169" class="Bound">M</a> <a id="15194" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="15196" href="plfa.Lambda.html#15174" class="Bound">y</a> <a id="15198" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="15201" href="plfa.Lambda.html#15179" class="Bound">V</a> <a id="15203" href="plfa.Lambda.html#14858" class="Function Operator">]</a>
<a id="15205" class="Symbol">(</a><a id="15206" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3944" class="InductiveConstructor Operator">case</a> <a id="15211" href="plfa.Lambda.html#15211" class="Bound">L</a> <a id="15213" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">[zero⇒</a> <a id="15220" href="plfa.Lambda.html#15220" class="Bound">M</a> <a id="15222" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">|suc</a> <a id="15227" href="plfa.Lambda.html#15227" class="Bound">x</a> <a id="15229" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">⇒</a> <a id="15231" href="plfa.Lambda.html#15231" class="Bound">N</a> <a id="15233" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">]</a><a id="15234" class="Symbol">)</a> <a id="15236" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="15238" href="plfa.Lambda.html#15238" class="Bound">y</a> <a id="15240" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="15243" href="plfa.Lambda.html#15243" class="Bound">V</a> <a id="15245" href="plfa.Lambda.html#14858" class="Function Operator">]</a> <a id="15247" class="Keyword">with</a> <a id="15252" href="plfa.Lambda.html#15227" class="Bound">x</a> <a id="15254" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15256" href="plfa.Lambda.html#15238" class="Bound">y</a>
<a id="15258" class="Symbol">...</a> <a id="15262" class="Symbol">|</a> <a id="15264" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15268" class="Symbol">_</a>          <a id="15279" class="Symbol">=</a>  <a id="15282" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3944" class="InductiveConstructor Operator">case</a> <a id="15287" class="Bound">L</a> <a id="15289" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="15291" class="Bound">y</a> <a id="15293" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="15296" class="Bound">V</a> <a id="15298" href="plfa.Lambda.html#14858" class="Function Operator">]</a> <a id="15300" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">[zero⇒</a> <a id="15307" class="Bound">M</a> <a id="15309" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="15311" class="Bound">y</a> <a id="15313" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="15316" class="Bound">V</a> <a id="15318" href="plfa.Lambda.html#14858" class="Function Operator">]</a> <a id="15320" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">|suc</a> <a id="15325" class="Bound">x</a> <a id="15327" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">⇒</a> <a id="15329" class="Bound">N</a> <a id="15331" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">]</a>
<a id="15333" class="Symbol">...</a> <a id="15337" class="Symbol">|</a> <a id="15339" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15343" class="Symbol">_</a>          <a id="15354" class="Symbol">=</a>  <a id="15357" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3944" class="InductiveConstructor Operator">case</a> <a id="15362" class="Bound">L</a> <a id="15364" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="15366" class="Bound">y</a> <a id="15368" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="15371" class="Bound">V</a> <a id="15373" href="plfa.Lambda.html#14858" class="Function Operator">]</a> <a id="15375" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">[zero⇒</a> <a id="15382" class="Bound">M</a> <a id="15384" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="15386" class="Bound">y</a> <a id="15388" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="15391" class="Bound">V</a> <a id="15393" href="plfa.Lambda.html#14858" class="Function Operator">]</a> <a id="15395" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">|suc</a> <a id="15400" class="Bound">x</a> <a id="15402" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">⇒</a> <a id="15404" class="Bound">N</a> <a id="15406" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="15408" class="Bound">y</a> <a id="15410" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="15413" class="Bound">V</a> <a id="15415" href="plfa.Lambda.html#14858" class="Function Operator">]</a> <a id="15417" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">]</a>
<a id="15419" class="Symbol">(</a><a id="15420" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4004" class="InductiveConstructor Operator">μ</a> <a id="15422" href="plfa.Lambda.html#15422" class="Bound">x</a> <a id="15424" href="plfa.Lambda.html#4004" class="InductiveConstructor Operator">⇒</a> <a id="15426" href="plfa.Lambda.html#15426" class="Bound">N</a><a id="15427" class="Symbol">)</a> <a id="15429" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="15431" href="plfa.Lambda.html#15431" class="Bound">y</a> <a id="15433" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="15436" href="plfa.Lambda.html#15436" class="Bound">V</a> <a id="15438" href="plfa.Lambda.html#14858" class="Function Operator">]</a> <a id="15440" class="Keyword">with</a> <a id="15445" href="plfa.Lambda.html#15422" class="Bound">x</a> <a id="15447" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15449" href="plfa.Lambda.html#15431" class="Bound">y</a>
<a id="15451" class="Symbol">...</a> <a id="15455" class="Symbol">|</a> <a id="15457" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15461" class="Symbol">_</a>          <a id="15472" class="Symbol">=</a>  <a id="15475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4004" class="InductiveConstructor Operator">μ</a> <a id="15477" class="Bound">x</a> <a id="15479" href="plfa.Lambda.html#4004" class="InductiveConstructor Operator">⇒</a> <a id="15481" class="Bound">N</a>
<a id="15483" class="Symbol">...</a> <a id="15487" class="Symbol">|</a> <a id="15489" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15493" class="Symbol">_</a>          <a id="15504" class="Symbol">=</a>  <a id="15507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4004" class="InductiveConstructor Operator">μ</a> <a id="15509" class="Bound">x</a> <a id="15511" href="plfa.Lambda.html#4004" class="InductiveConstructor Operator">⇒</a> <a id="15513" class="Bound">N</a> <a id="15515" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="15517" class="Bound">y</a> <a id="15519" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="15522" class="Bound">V</a> <a id="15524" href="plfa.Lambda.html#14858" class="Function Operator">]</a>
</pre>{% endraw %}
Let's unpack the first three cases:

* For variables, we compare `y`, the substituted variable,
with `x`, the variable in the term. If they are the same,
we yield `V`, otherwise we yield `x` unchanged.

* For abstractions, we compare `y`, the substituted variable,
with `x`, the variable bound in the abstraction. If they are the same,
we yield the abstraction unchanged, otherwise we substitute inside the body.

* For application, we recursively substitute in the function
and the argument.

Case expressions and recursion also have bound variables that are
treated similarly to those in lambda abstractions.  Otherwise we
simply push substitution recursively into the subterms.


### Examples

Here is confirmation that the examples above are correct:

{% raw %}<pre class="Agda"><a id="16291" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#16291" class="Function">_</a> <a id="16293" class="Symbol">:</a> <a id="16295" class="Symbol">(</a><a id="16296" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="16298" class="String">&quot;z&quot;</a> <a id="16302" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="16304" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="16306" class="String">&quot;s&quot;</a> <a id="16310" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="16312" class="Symbol">(</a><a id="16313" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="16315" class="String">&quot;s&quot;</a> <a id="16319" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="16321" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="16323" class="String">&quot;z&quot;</a><a id="16326" class="Symbol">))</a> <a id="16329" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="16331" class="String">&quot;s&quot;</a> <a id="16335" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="16338" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="16343" href="plfa.Lambda.html#14858" class="Function Operator">]</a> <a id="16345" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16347" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="16349" class="String">&quot;z&quot;</a> <a id="16353" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="16355" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="16360" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="16362" class="Symbol">(</a><a id="16363" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="16368" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="16370" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="16372" class="String">&quot;z&quot;</a><a id="16375" class="Symbol">)</a>
<a id="16377" class="Symbol">_</a> <a id="16379" class="Symbol">=</a> <a id="16381" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="16387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#16387" class="Function">_</a> <a id="16389" class="Symbol">:</a> <a id="16391" class="Symbol">(</a><a id="16392" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="16397" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="16399" class="Symbol">(</a><a id="16400" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="16405" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="16407" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="16409" class="String">&quot;z&quot;</a><a id="16412" class="Symbol">))</a> <a id="16415" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="16417" class="String">&quot;z&quot;</a> <a id="16421" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="16424" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a> <a id="16430" href="plfa.Lambda.html#14858" class="Function Operator">]</a> <a id="16432" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16434" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="16439" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="16441" class="Symbol">(</a><a id="16442" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="16447" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="16449" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a><a id="16454" class="Symbol">)</a>
<a id="16456" class="Symbol">_</a> <a id="16458" class="Symbol">=</a> <a id="16460" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="16466" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#16466" class="Function">_</a> <a id="16468" class="Symbol">:</a> <a id="16470" class="Symbol">(</a><a id="16471" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="16473" class="String">&quot;x&quot;</a> <a id="16477" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="16479" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="16481" class="String">&quot;y&quot;</a><a id="16484" class="Symbol">)</a> <a id="16486" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="16488" class="String">&quot;y&quot;</a> <a id="16492" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="16495" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a> <a id="16501" href="plfa.Lambda.html#14858" class="Function Operator">]</a> <a id="16503" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16505" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="16507" class="String">&quot;x&quot;</a> <a id="16511" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="16513" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a>
<a id="16519" class="Symbol">_</a> <a id="16521" class="Symbol">=</a> <a id="16523" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="16529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#16529" class="Function">_</a> <a id="16531" class="Symbol">:</a> <a id="16533" class="Symbol">(</a><a id="16534" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="16536" class="String">&quot;x&quot;</a> <a id="16540" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="16542" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="16544" class="String">&quot;x&quot;</a><a id="16547" class="Symbol">)</a> <a id="16549" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="16551" class="String">&quot;x&quot;</a> <a id="16555" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="16558" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a> <a id="16564" href="plfa.Lambda.html#14858" class="Function Operator">]</a> <a id="16566" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16568" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="16570" class="String">&quot;x&quot;</a> <a id="16574" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="16576" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="16578" class="String">&quot;x&quot;</a>
<a id="16582" class="Symbol">_</a> <a id="16584" class="Symbol">=</a> <a id="16586" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="16592" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#16592" class="Function">_</a> <a id="16594" class="Symbol">:</a> <a id="16596" class="Symbol">(</a><a id="16597" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="16599" class="String">&quot;y&quot;</a> <a id="16603" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="16605" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="16607" class="String">&quot;y&quot;</a><a id="16610" class="Symbol">)</a> <a id="16612" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="16614" class="String">&quot;x&quot;</a> <a id="16618" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="16621" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a> <a id="16627" href="plfa.Lambda.html#14858" class="Function Operator">]</a> <a id="16629" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16631" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="16633" class="String">&quot;y&quot;</a> <a id="16637" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="16639" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="16641" class="String">&quot;y&quot;</a>
<a id="16645" class="Symbol">_</a> <a id="16647" class="Symbol">=</a> <a id="16649" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}

#### Quiz

What is the result of the following substitution?

    (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ]

1. `` (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) ``
2. `` (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ `zero)) ``
3. `` (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ ` "x")) ``
4. `` (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ `zero)) ``


#### Exercise `_[_:=_]′` (stretch)

The definition of substitution above has three clauses (`ƛ`, `case`,
and `μ`) that invoke a `with` clause to deal with bound variables.
Rewrite the definition to factor the common part of these three
clauses into a single function, defined by mutual recursion with
substitution.

{% raw %}<pre class="Agda"><a id="17272" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Reduction

We give the reduction rules for call-by-value lambda calculus.  To
reduce an application, first we reduce the left-hand side until it
becomes a value (which must be an abstraction); then we reduce the
right-hand side until it becomes a value; and finally we substitute
the argument for the variable in the abstraction.

In an informal presentation of the operational semantics,
the rules for reduction of applications are written as follows:

    L —→ L′
    --------------- ξ-·₁
    L · M —→ L′ · M

    M —→ M′
    --------------- ξ-·₂
    V · M —→ V · M′

    ----------------------------- β-ƛ
    (ƛ x ⇒ N) · V —→ N [ x := V ]

The Agda version of the rules below will be similar, except that universal
quantifications are made explicit, and so are the predicates that indicate
which terms are values.

The rules break into two sorts. Compatibility rules direct us to
reduce some part of a term.  We give them names starting with the
Greek letter `ξ` (_xi_).  Once a term is sufficiently reduced, it will
consist of a constructor and a deconstructor, in our case `ƛ` and `·`,
which reduces directly.  We give them names starting with the Greek
letter `β` (_beta_) and such rules are traditionally called _beta rules_.

A bit of terminology: A term that matches the left-hand side of a
reduction rule is called a _redex_. In the redex `(ƛ x ⇒ N) · V`, we
may refer to `x` as the _formal parameter_ of the function, and `V`
as the _actual parameter_ of the function application.  Beta reduction
replaces the formal parameter by the actual parameter.

If a term is a value, then no reduction applies; conversely,
if a reduction applies to a term then it is not a value.
We will show in the next chapter that 
this exhausts the possibilities: every well-typed term
either reduces or is a value.

For numbers, zero does not reduce and successor reduces the subterm.
A case expression reduces its argument to a number, and then chooses
the zero or successor branch as appropriate.  A fixpoint replaces
the bound variable by the entire fixpoint term; this is the one
case where we substitute by a term that is not a value.

Here are the rules formalised in Agda:

{% raw %}<pre class="Agda"><a id="19480" class="Keyword">infix</a> <a id="19486" class="Number">4</a> <a id="19488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19499" class="Datatype Operator">_—→_</a>

<a id="19494" class="Keyword">data</a> <a id="_—→_"></a><a id="19499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19499" class="Datatype Operator">_—→_</a> <a id="19504" class="Symbol">:</a> <a id="19506" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="19511" class="Symbol">→</a> <a id="19513" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="19518" class="Symbol">→</a> <a id="19520" class="PrimitiveType">Set</a> <a id="19524" class="Keyword">where</a>

  <a id="_—→_.ξ-·₁"></a><a id="19533" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19533" class="InductiveConstructor">ξ-·₁</a> <a id="19538" class="Symbol">:</a> <a id="19540" class="Symbol">∀</a> <a id="19542" class="Symbol">{</a><a id="19543" href="plfa.Lambda.html#19543" class="Bound">L</a> <a id="19545" href="plfa.Lambda.html#19545" class="Bound">L′</a> <a id="19548" href="plfa.Lambda.html#19548" class="Bound">M</a><a id="19549" class="Symbol">}</a>
    <a id="19555" class="Symbol">→</a> <a id="19557" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19543" class="Bound">L</a> <a id="19559" href="plfa.Lambda.html#19499" class="Datatype Operator">—→</a> <a id="19562" href="plfa.Lambda.html#19545" class="Bound">L′</a>
      <a id="19571" class="Comment">-----------------</a>
    <a id="19593" class="Symbol">→</a> <a id="19595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19543" class="Bound">L</a> <a id="19597" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="19599" href="plfa.Lambda.html#19548" class="Bound">M</a> <a id="19601" href="plfa.Lambda.html#19499" class="Datatype Operator">—→</a> <a id="19604" href="plfa.Lambda.html#19545" class="Bound">L′</a> <a id="19607" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="19609" href="plfa.Lambda.html#19548" class="Bound">M</a>

  <a id="_—→_.ξ-·₂"></a><a id="19614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19614" class="InductiveConstructor">ξ-·₂</a> <a id="19619" class="Symbol">:</a> <a id="19621" class="Symbol">∀</a> <a id="19623" class="Symbol">{</a><a id="19624" href="plfa.Lambda.html#19624" class="Bound">V</a> <a id="19626" href="plfa.Lambda.html#19626" class="Bound">M</a> <a id="19628" href="plfa.Lambda.html#19628" class="Bound">M′</a><a id="19630" class="Symbol">}</a>
    <a id="19636" class="Symbol">→</a> <a id="19638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11490" class="Datatype">Value</a> <a id="19644" href="plfa.Lambda.html#19624" class="Bound">V</a>
    <a id="19650" class="Symbol">→</a> <a id="19652" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19626" class="Bound">M</a> <a id="19654" href="plfa.Lambda.html#19499" class="Datatype Operator">—→</a> <a id="19657" href="plfa.Lambda.html#19628" class="Bound">M′</a>
      <a id="19666" class="Comment">-----------------</a>
    <a id="19688" class="Symbol">→</a> <a id="19690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19624" class="Bound">V</a> <a id="19692" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="19694" href="plfa.Lambda.html#19626" class="Bound">M</a> <a id="19696" href="plfa.Lambda.html#19499" class="Datatype Operator">—→</a> <a id="19699" href="plfa.Lambda.html#19624" class="Bound">V</a> <a id="19701" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="19703" href="plfa.Lambda.html#19628" class="Bound">M′</a>

  <a id="_—→_.β-ƛ"></a><a id="19709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19709" class="InductiveConstructor">β-ƛ</a> <a id="19713" class="Symbol">:</a> <a id="19715" class="Symbol">∀</a> <a id="19717" class="Symbol">{</a><a id="19718" href="plfa.Lambda.html#19718" class="Bound">x</a> <a id="19720" href="plfa.Lambda.html#19720" class="Bound">N</a> <a id="19722" href="plfa.Lambda.html#19722" class="Bound">V</a><a id="19723" class="Symbol">}</a>
    <a id="19729" class="Symbol">→</a> <a id="19731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11490" class="Datatype">Value</a> <a id="19737" href="plfa.Lambda.html#19722" class="Bound">V</a>
      <a id="19745" class="Comment">------------------------------</a>
    <a id="19780" class="Symbol">→</a> <a id="19782" class="Symbol">(</a><a id="19783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3775" class="InductiveConstructor Operator">ƛ</a> <a id="19785" href="plfa.Lambda.html#19718" class="Bound">x</a> <a id="19787" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="19789" href="plfa.Lambda.html#19720" class="Bound">N</a><a id="19790" class="Symbol">)</a> <a id="19792" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="19794" href="plfa.Lambda.html#19722" class="Bound">V</a> <a id="19796" href="plfa.Lambda.html#19499" class="Datatype Operator">—→</a> <a id="19799" href="plfa.Lambda.html#19720" class="Bound">N</a> <a id="19801" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="19803" href="plfa.Lambda.html#19718" class="Bound">x</a> <a id="19805" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="19808" href="plfa.Lambda.html#19722" class="Bound">V</a> <a id="19810" href="plfa.Lambda.html#14858" class="Function Operator">]</a>

  <a id="_—→_.ξ-suc"></a><a id="19815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19815" class="InductiveConstructor">ξ-suc</a> <a id="19821" class="Symbol">:</a> <a id="19823" class="Symbol">∀</a> <a id="19825" class="Symbol">{</a><a id="19826" href="plfa.Lambda.html#19826" class="Bound">M</a> <a id="19828" href="plfa.Lambda.html#19828" class="Bound">M′</a><a id="19830" class="Symbol">}</a>
    <a id="19836" class="Symbol">→</a> <a id="19838" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19826" class="Bound">M</a> <a id="19840" href="plfa.Lambda.html#19499" class="Datatype Operator">—→</a> <a id="19843" href="plfa.Lambda.html#19828" class="Bound">M′</a>
      <a id="19852" class="Comment">------------------</a>
    <a id="19875" class="Symbol">→</a> <a id="19877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3903" class="InductiveConstructor Operator">`suc</a> <a id="19882" href="plfa.Lambda.html#19826" class="Bound">M</a> <a id="19884" href="plfa.Lambda.html#19499" class="Datatype Operator">—→</a> <a id="19887" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="19892" href="plfa.Lambda.html#19828" class="Bound">M′</a>

  <a id="_—→_.ξ-case"></a><a id="19898" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19898" class="InductiveConstructor">ξ-case</a> <a id="19905" class="Symbol">:</a> <a id="19907" class="Symbol">∀</a> <a id="19909" class="Symbol">{</a><a id="19910" href="plfa.Lambda.html#19910" class="Bound">x</a> <a id="19912" href="plfa.Lambda.html#19912" class="Bound">L</a> <a id="19914" href="plfa.Lambda.html#19914" class="Bound">L′</a> <a id="19917" href="plfa.Lambda.html#19917" class="Bound">M</a> <a id="19919" href="plfa.Lambda.html#19919" class="Bound">N</a><a id="19920" class="Symbol">}</a>
    <a id="19926" class="Symbol">→</a> <a id="19928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19912" class="Bound">L</a> <a id="19930" href="plfa.Lambda.html#19499" class="Datatype Operator">—→</a> <a id="19933" href="plfa.Lambda.html#19914" class="Bound">L′</a>
      <a id="19942" class="Comment">-----------------------------------------------------------------</a>
    <a id="20012" class="Symbol">→</a> <a id="20014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3944" class="InductiveConstructor Operator">case</a> <a id="20019" href="plfa.Lambda.html#19912" class="Bound">L</a> <a id="20021" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">[zero⇒</a> <a id="20028" href="plfa.Lambda.html#19917" class="Bound">M</a> <a id="20030" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">|suc</a> <a id="20035" href="plfa.Lambda.html#19910" class="Bound">x</a> <a id="20037" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">⇒</a> <a id="20039" href="plfa.Lambda.html#19919" class="Bound">N</a> <a id="20041" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">]</a> <a id="20043" href="plfa.Lambda.html#19499" class="Datatype Operator">—→</a> <a id="20046" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">case</a> <a id="20051" href="plfa.Lambda.html#19914" class="Bound">L′</a> <a id="20054" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">[zero⇒</a> <a id="20061" href="plfa.Lambda.html#19917" class="Bound">M</a> <a id="20063" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">|suc</a> <a id="20068" href="plfa.Lambda.html#19910" class="Bound">x</a> <a id="20070" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">⇒</a> <a id="20072" href="plfa.Lambda.html#19919" class="Bound">N</a> <a id="20074" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">]</a>

  <a id="_—→_.β-zero"></a><a id="20079" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#20079" class="InductiveConstructor">β-zero</a> <a id="20086" class="Symbol">:</a> <a id="20088" class="Symbol">∀</a> <a id="20090" class="Symbol">{</a><a id="20091" href="plfa.Lambda.html#20091" class="Bound">x</a> <a id="20093" href="plfa.Lambda.html#20093" class="Bound">M</a> <a id="20095" href="plfa.Lambda.html#20095" class="Bound">N</a><a id="20096" class="Symbol">}</a>
      <a id="20104" class="Comment">----------------------------------------</a>
    <a id="20149" class="Symbol">→</a> <a id="20151" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3944" class="InductiveConstructor Operator">case</a> <a id="20156" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a> <a id="20162" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">[zero⇒</a> <a id="20169" href="plfa.Lambda.html#20093" class="Bound">M</a> <a id="20171" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">|suc</a> <a id="20176" href="plfa.Lambda.html#20091" class="Bound">x</a> <a id="20178" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">⇒</a> <a id="20180" href="plfa.Lambda.html#20095" class="Bound">N</a> <a id="20182" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">]</a> <a id="20184" href="plfa.Lambda.html#19499" class="Datatype Operator">—→</a> <a id="20187" href="plfa.Lambda.html#20093" class="Bound">M</a>

  <a id="_—→_.β-suc"></a><a id="20192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#20192" class="InductiveConstructor">β-suc</a> <a id="20198" class="Symbol">:</a> <a id="20200" class="Symbol">∀</a> <a id="20202" class="Symbol">{</a><a id="20203" href="plfa.Lambda.html#20203" class="Bound">x</a> <a id="20205" href="plfa.Lambda.html#20205" class="Bound">V</a> <a id="20207" href="plfa.Lambda.html#20207" class="Bound">M</a> <a id="20209" href="plfa.Lambda.html#20209" class="Bound">N</a><a id="20210" class="Symbol">}</a>
    <a id="20216" class="Symbol">→</a> <a id="20218" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11490" class="Datatype">Value</a> <a id="20224" href="plfa.Lambda.html#20205" class="Bound">V</a>
      <a id="20232" class="Comment">---------------------------------------------------</a>
    <a id="20288" class="Symbol">→</a> <a id="20290" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3944" class="InductiveConstructor Operator">case</a> <a id="20295" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="20300" href="plfa.Lambda.html#20205" class="Bound">V</a> <a id="20302" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">[zero⇒</a> <a id="20309" href="plfa.Lambda.html#20207" class="Bound">M</a> <a id="20311" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">|suc</a> <a id="20316" href="plfa.Lambda.html#20203" class="Bound">x</a> <a id="20318" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">⇒</a> <a id="20320" href="plfa.Lambda.html#20209" class="Bound">N</a> <a id="20322" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">]</a> <a id="20324" href="plfa.Lambda.html#19499" class="Datatype Operator">—→</a> <a id="20327" href="plfa.Lambda.html#20209" class="Bound">N</a> <a id="20329" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="20331" href="plfa.Lambda.html#20203" class="Bound">x</a> <a id="20333" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="20336" href="plfa.Lambda.html#20205" class="Bound">V</a> <a id="20338" href="plfa.Lambda.html#14858" class="Function Operator">]</a>

  <a id="_—→_.β-μ"></a><a id="20343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#20343" class="InductiveConstructor">β-μ</a> <a id="20347" class="Symbol">:</a> <a id="20349" class="Symbol">∀</a> <a id="20351" class="Symbol">{</a><a id="20352" href="plfa.Lambda.html#20352" class="Bound">x</a> <a id="20354" href="plfa.Lambda.html#20354" class="Bound">M</a><a id="20355" class="Symbol">}</a>
      <a id="20363" class="Comment">------------------------------</a>
    <a id="20398" class="Symbol">→</a> <a id="20400" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4004" class="InductiveConstructor Operator">μ</a> <a id="20402" href="plfa.Lambda.html#20352" class="Bound">x</a> <a id="20404" href="plfa.Lambda.html#4004" class="InductiveConstructor Operator">⇒</a> <a id="20406" href="plfa.Lambda.html#20354" class="Bound">M</a> <a id="20408" href="plfa.Lambda.html#19499" class="Datatype Operator">—→</a> <a id="20411" href="plfa.Lambda.html#20354" class="Bound">M</a> <a id="20413" href="plfa.Lambda.html#14858" class="Function Operator">[</a> <a id="20415" href="plfa.Lambda.html#20352" class="Bound">x</a> <a id="20417" href="plfa.Lambda.html#14858" class="Function Operator">:=</a> <a id="20420" href="plfa.Lambda.html#4004" class="InductiveConstructor Operator">μ</a> <a id="20422" href="plfa.Lambda.html#20352" class="Bound">x</a> <a id="20424" href="plfa.Lambda.html#4004" class="InductiveConstructor Operator">⇒</a> <a id="20426" href="plfa.Lambda.html#20354" class="Bound">M</a> <a id="20428" href="plfa.Lambda.html#14858" class="Function Operator">]</a>
</pre>{% endraw %}
The reduction rules are carefully designed to ensure that subterms
of a term are reduced to values before the whole term is reduced.
This is referred to as _call-by-value_ reduction.

Further, we have arranged that subterms are reduced in a
left-to-right order.  This means that reduction is _deterministic_:
for any term, there is at most one other term to which it reduces.
Put another way, our reduction relation `—→` is in fact a function.

This style of explaining the meaning of terms is called
a _small-step operational semantics_.  If `M —→ N`, we say that
term `M` _reduces_ to term `N`, or equivalently,
term `M` _steps_ to term `N`.  Each compatibility rule has
another reduction rule in its premise; so a step always consists
of a beta rule, possibly adjusted by zero or more compatibility rules.


#### Quiz

What does the following term step to?

    (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→  ???

1.  `` (ƛ "x" ⇒ ` "x") ``
2.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``
3.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``

What does the following term step to?

    (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→  ???

1.  `` (ƛ "x" ⇒ ` "x") ``
2.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``
3.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``

What does the following term step to?  (Where `twoᶜ` and `sucᶜ` are as
defined above.)

    twoᶜ · sucᶜ · `zero  —→  ???

1.  `` sucᶜ · (sucᶜ · `zero) ``
2.  `` (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero ``
3.  `` `zero ``


## Reflexive and transitive closure

A single step is only part of the story. In general, we wish to repeatedly
step a closed term until it reduces to a value.  We do this by defining
the reflexive and transitive closure `—↠` of the step relation `—→`.

We define reflexive and transitive closure as a sequence of zero or
more steps of the underlying relation, along lines similar to that for
reasoning about chains of equalities in
Chapter [Equality][plfa.Equality]:
{% raw %}<pre class="Agda"><a id="22409" class="Keyword">infix</a>  <a id="22416" class="Number">2</a> <a id="22418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22474" class="Datatype Operator">_—↠_</a>
<a id="22423" class="Keyword">infix</a>  <a id="22430" class="Number">1</a> <a id="22432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="Function Operator">begin_</a>
<a id="22439" class="Keyword">infixr</a> <a id="22446" class="Number">2</a> <a id="22448" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">_—→⟨_⟩_</a>
<a id="22456" class="Keyword">infix</a>  <a id="22463" class="Number">3</a> <a id="22465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22507" class="InductiveConstructor Operator">_∎</a>

<a id="22469" class="Keyword">data</a> <a id="_—↠_"></a><a id="22474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22474" class="Datatype Operator">_—↠_</a> <a id="22479" class="Symbol">:</a> <a id="22481" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="22486" class="Symbol">→</a> <a id="22488" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="22493" class="Symbol">→</a> <a id="22495" class="PrimitiveType">Set</a> <a id="22499" class="Keyword">where</a>
  <a id="_—↠_._∎"></a><a id="22507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22507" class="InductiveConstructor Operator">_∎</a> <a id="22510" class="Symbol">:</a> <a id="22512" class="Symbol">∀</a> <a id="22514" href="plfa.Lambda.html#22514" class="Bound">M</a>
      <a id="22522" class="Comment">---------</a>
    <a id="22536" class="Symbol">→</a> <a id="22538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22514" class="Bound">M</a> <a id="22540" href="plfa.Lambda.html#22474" class="Datatype Operator">—↠</a> <a id="22543" href="plfa.Lambda.html#22514" class="Bound">M</a>

  <a id="_—↠_._—→⟨_⟩_"></a><a id="22548" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">_—→⟨_⟩_</a> <a id="22556" class="Symbol">:</a> <a id="22558" class="Symbol">∀</a> <a id="22560" href="plfa.Lambda.html#22560" class="Bound">L</a> <a id="22562" class="Symbol">{</a><a id="22563" href="plfa.Lambda.html#22563" class="Bound">M</a> <a id="22565" href="plfa.Lambda.html#22565" class="Bound">N</a><a id="22566" class="Symbol">}</a>
    <a id="22572" class="Symbol">→</a> <a id="22574" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22560" class="Bound">L</a> <a id="22576" href="plfa.Lambda.html#19499" class="Datatype Operator">—→</a> <a id="22579" href="plfa.Lambda.html#22563" class="Bound">M</a>
    <a id="22585" class="Symbol">→</a> <a id="22587" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22563" class="Bound">M</a> <a id="22589" href="plfa.Lambda.html#22474" class="Datatype Operator">—↠</a> <a id="22592" href="plfa.Lambda.html#22565" class="Bound">N</a>
      <a id="22600" class="Comment">---------</a>
    <a id="22614" class="Symbol">→</a> <a id="22616" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22560" class="Bound">L</a> <a id="22618" href="plfa.Lambda.html#22474" class="Datatype Operator">—↠</a> <a id="22621" href="plfa.Lambda.html#22565" class="Bound">N</a>

<a id="begin_"></a><a id="22624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="Function Operator">begin_</a> <a id="22631" class="Symbol">:</a> <a id="22633" class="Symbol">∀</a> <a id="22635" class="Symbol">{</a><a id="22636" href="plfa.Lambda.html#22636" class="Bound">M</a> <a id="22638" href="plfa.Lambda.html#22638" class="Bound">N</a><a id="22639" class="Symbol">}</a>
  <a id="22643" class="Symbol">→</a> <a id="22645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22636" class="Bound">M</a> <a id="22647" href="plfa.Lambda.html#22474" class="Datatype Operator">—↠</a> <a id="22650" href="plfa.Lambda.html#22638" class="Bound">N</a>
    <a id="22656" class="Comment">------</a>
  <a id="22665" class="Symbol">→</a> <a id="22667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22636" class="Bound">M</a> <a id="22669" href="plfa.Lambda.html#22474" class="Datatype Operator">—↠</a> <a id="22672" href="plfa.Lambda.html#22638" class="Bound">N</a>
<a id="22674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="Function Operator">begin</a> <a id="22680" href="plfa.Lambda.html#22680" class="Bound">M—↠N</a> <a id="22685" class="Symbol">=</a> <a id="22687" href="plfa.Lambda.html#22680" class="Bound">M—↠N</a>
</pre>{% endraw %}We can read this as follows:

* From term `M`, we can take no steps, giving a step of type `M —↠ M`.
  It is written `M ∎`.

* From term `L` we can take a single step of type `L —→ M` followed by zero
  or more steps of type `M —↠ N`, giving a step of type `L —↠ N`. It is
  written `L —→⟨ L—→M ⟩ M—↠N`, where `L—→M` and `M—↠N` are steps of the
  appropriate type.

The notation is chosen to allow us to lay out example reductions in an
appealing way, as we will see in the next section.

An alternative is to define reflexive and transitive closure directly,
as the smallest relation that includes `—→` and is also reflexive
and transitive.  We could do so as follows:
{% raw %}<pre class="Agda"><a id="23370" class="Keyword">data</a> <a id="_—↠′_"></a><a id="23375" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#23375" class="Datatype Operator">_—↠′_</a> <a id="23381" class="Symbol">:</a> <a id="23383" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="23388" class="Symbol">→</a> <a id="23390" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="23395" class="Symbol">→</a> <a id="23397" class="PrimitiveType">Set</a> <a id="23401" class="Keyword">where</a>

  <a id="_—↠′_.step′"></a><a id="23410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#23410" class="InductiveConstructor">step′</a> <a id="23416" class="Symbol">:</a> <a id="23418" class="Symbol">∀</a> <a id="23420" class="Symbol">{</a><a id="23421" href="plfa.Lambda.html#23421" class="Bound">M</a> <a id="23423" href="plfa.Lambda.html#23423" class="Bound">N</a><a id="23424" class="Symbol">}</a>
    <a id="23430" class="Symbol">→</a> <a id="23432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#23421" class="Bound">M</a> <a id="23434" href="plfa.Lambda.html#19499" class="Datatype Operator">—→</a> <a id="23437" href="plfa.Lambda.html#23423" class="Bound">N</a>
      <a id="23445" class="Comment">-------</a>
    <a id="23457" class="Symbol">→</a> <a id="23459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#23421" class="Bound">M</a> <a id="23461" href="plfa.Lambda.html#23375" class="Datatype Operator">—↠′</a> <a id="23465" href="plfa.Lambda.html#23423" class="Bound">N</a>

  <a id="_—↠′_.refl′"></a><a id="23470" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#23470" class="InductiveConstructor">refl′</a> <a id="23476" class="Symbol">:</a> <a id="23478" class="Symbol">∀</a> <a id="23480" class="Symbol">{</a><a id="23481" href="plfa.Lambda.html#23481" class="Bound">M</a><a id="23482" class="Symbol">}</a>
      <a id="23490" class="Comment">-------</a>
    <a id="23502" class="Symbol">→</a> <a id="23504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#23481" class="Bound">M</a> <a id="23506" href="plfa.Lambda.html#23375" class="Datatype Operator">—↠′</a> <a id="23510" href="plfa.Lambda.html#23481" class="Bound">M</a>

  <a id="_—↠′_.trans′"></a><a id="23515" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#23515" class="InductiveConstructor">trans′</a> <a id="23522" class="Symbol">:</a> <a id="23524" class="Symbol">∀</a> <a id="23526" class="Symbol">{</a><a id="23527" href="plfa.Lambda.html#23527" class="Bound">L</a> <a id="23529" href="plfa.Lambda.html#23529" class="Bound">M</a> <a id="23531" href="plfa.Lambda.html#23531" class="Bound">N</a><a id="23532" class="Symbol">}</a>
    <a id="23538" class="Symbol">→</a> <a id="23540" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#23527" class="Bound">L</a> <a id="23542" href="plfa.Lambda.html#23375" class="Datatype Operator">—↠′</a> <a id="23546" href="plfa.Lambda.html#23529" class="Bound">M</a>
    <a id="23552" class="Symbol">→</a> <a id="23554" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#23529" class="Bound">M</a> <a id="23556" href="plfa.Lambda.html#23375" class="Datatype Operator">—↠′</a> <a id="23560" href="plfa.Lambda.html#23531" class="Bound">N</a>
      <a id="23568" class="Comment">-------</a>
    <a id="23580" class="Symbol">→</a> <a id="23582" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#23527" class="Bound">L</a> <a id="23584" href="plfa.Lambda.html#23375" class="Datatype Operator">—↠′</a> <a id="23588" href="plfa.Lambda.html#23531" class="Bound">N</a>
</pre>{% endraw %}The three constructors specify, respectively, that `—↠′` includes `—→`
and is reflexive and transitive.  A good exercise is to show that
the two definitions are equivalent (indeed, one embeds in the other).

#### Exercise `—↠≲—↠′`

Show that the first notion of reflexive and transitive closure
above embeds into the second. Why are they not isomorphic?

{% raw %}<pre class="Agda"><a id="23953" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Confluence

One important property a reduction relation might satisfy is
to be _confluent_.  If term `L` reduces to two other terms,
`M` and `N`, then both of these reduce to a common term `P`.
It can be illustrated as follows:

               L
              / \
             /   \
            /     \
           M       N
            \     /
             \   /
              \ /
               P

Here `L`, `M`, `N` are universally quantified while `P`
is existentially quantified.  If each line stands for zero
or more reduction steps, this is called confluence,
while if the top two lines stand for a single reduction
step and the bottom two stand for zero or more reduction
steps it is called the diamond property. In symbols:

    confluence : ∀ {L M N} → ∃[ P ]
      ( ((L —↠ M) × (L —↠ N))
        --------------------
      → ((M —↠ P) × (N —↠ P)) )

    diamond : ∀ {L M N} → ∃[ P ]
      ( ((L —→ M) × (L —→ N))
        --------------------
      → ((M —↠ P) × (N —↠ P)) )

All of the reduction systems studied in this text are deterministic.
In symbols:

    deterministic : ∀ {L M N}
      → L —→ M
      → L —→ N
        ------
      → M ≡ N

It is easy to show that every deterministic relation satisfies
the diamond property, and that every relation that satisfies
the diamond property is confluent.  Hence, all the reduction
systems studied in this text are trivially confluent.


## Examples

We start with a simple example. The Church numeral two applied to the
successor function and zero yields the natural number two:
{% raw %}<pre class="Agda"><a id="25529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#25529" class="Function">_</a> <a id="25531" class="Symbol">:</a> <a id="25533" href="plfa.Lambda.html#5679" class="Function">twoᶜ</a> <a id="25538" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="25540" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="25545" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="25547" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a> <a id="25553" href="plfa.Lambda.html#22474" class="Datatype Operator">—↠</a> <a id="25556" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="25561" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="25566" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a>
<a id="25572" class="Symbol">_</a> <a id="25574" class="Symbol">=</a>
  <a id="25578" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="Function Operator">begin</a>
    <a id="25588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5679" class="Function">twoᶜ</a> <a id="25593" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="25595" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="25600" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="25602" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a>
  <a id="25610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="25614" href="plfa.Lambda.html#19533" class="InductiveConstructor">ξ-·₁</a> <a id="25619" class="Symbol">(</a><a id="25620" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="25624" href="plfa.Lambda.html#11518" class="InductiveConstructor">V-ƛ</a><a id="25627" class="Symbol">)</a> <a id="25629" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="25635" class="Symbol">(</a><a id="25636" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3775" class="InductiveConstructor Operator">ƛ</a> <a id="25638" class="String">&quot;z&quot;</a> <a id="25642" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="25644" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="25649" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="25651" class="Symbol">(</a><a id="25652" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="25657" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="25659" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="25661" class="String">&quot;z&quot;</a><a id="25664" class="Symbol">))</a> <a id="25667" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="25669" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a>
  <a id="25677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="25681" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="25685" href="plfa.Lambda.html#11579" class="InductiveConstructor">V-zero</a> <a id="25692" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="25698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5844" class="Function">sucᶜ</a> <a id="25703" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="25705" class="Symbol">(</a><a id="25706" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="25711" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="25713" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a><a id="25718" class="Symbol">)</a>
  <a id="25722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="25726" href="plfa.Lambda.html#19614" class="InductiveConstructor">ξ-·₂</a> <a id="25731" href="plfa.Lambda.html#11518" class="InductiveConstructor">V-ƛ</a> <a id="25735" class="Symbol">(</a><a id="25736" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="25740" href="plfa.Lambda.html#11579" class="InductiveConstructor">V-zero</a><a id="25746" class="Symbol">)</a> <a id="25748" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="25754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5844" class="Function">sucᶜ</a> <a id="25759" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="25761" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="25766" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a>
  <a id="25774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="25778" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="25782" class="Symbol">(</a><a id="25783" href="plfa.Lambda.html#11627" class="InductiveConstructor">V-suc</a> <a id="25789" href="plfa.Lambda.html#11579" class="InductiveConstructor">V-zero</a><a id="25795" class="Symbol">)</a> <a id="25797" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="25803" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3903" class="InductiveConstructor Operator">`suc</a> <a id="25808" class="Symbol">(</a><a id="25809" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="25814" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a><a id="25819" class="Symbol">)</a>
  <a id="25823" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22507" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
Here is a sample reduction demonstrating that two plus two is four:
{% raw %}<pre class="Agda"><a id="25902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#25902" class="Function">_</a> <a id="25904" class="Symbol">:</a> <a id="25906" href="plfa.Lambda.html#4479" class="Function">plus</a> <a id="25911" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="25913" href="plfa.Lambda.html#4445" class="Function">two</a> <a id="25917" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="25919" href="plfa.Lambda.html#4445" class="Function">two</a> <a id="25923" href="plfa.Lambda.html#22474" class="Datatype Operator">—↠</a> <a id="25926" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="25931" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="25936" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="25941" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="25946" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a>
<a id="25952" class="Symbol">_</a> <a id="25954" class="Symbol">=</a>
  <a id="25958" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="Function Operator">begin</a>
    <a id="25968" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4479" class="Function">plus</a> <a id="25973" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="25975" href="plfa.Lambda.html#4445" class="Function">two</a> <a id="25979" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="25981" href="plfa.Lambda.html#4445" class="Function">two</a>
  <a id="25987" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="25991" href="plfa.Lambda.html#19533" class="InductiveConstructor">ξ-·₁</a> <a id="25996" class="Symbol">(</a><a id="25997" href="plfa.Lambda.html#19533" class="InductiveConstructor">ξ-·₁</a> <a id="26002" href="plfa.Lambda.html#20343" class="InductiveConstructor">β-μ</a><a id="26005" class="Symbol">)</a> <a id="26007" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="26013" class="Symbol">(</a><a id="26014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3775" class="InductiveConstructor Operator">ƛ</a> <a id="26016" class="String">&quot;m&quot;</a> <a id="26020" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="26022" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="26024" class="String">&quot;n&quot;</a> <a id="26028" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a>
      <a id="26036" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3944" class="InductiveConstructor Operator">case</a> <a id="26041" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="26043" class="String">&quot;m&quot;</a> <a id="26047" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">[zero⇒</a> <a id="26054" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="26056" class="String">&quot;n&quot;</a> <a id="26060" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">|suc</a> <a id="26065" class="String">&quot;m&quot;</a> <a id="26069" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">⇒</a> <a id="26071" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="26076" class="Symbol">(</a><a id="26077" href="plfa.Lambda.html#4479" class="Function">plus</a> <a id="26082" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="26084" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="26086" class="String">&quot;m&quot;</a> <a id="26090" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="26092" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="26094" class="String">&quot;n&quot;</a><a id="26097" class="Symbol">)</a> <a id="26099" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">]</a><a id="26100" class="Symbol">)</a>
        <a id="26110" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3821" class="InductiveConstructor Operator">·</a> <a id="26112" href="plfa.Lambda.html#4445" class="Function">two</a> <a id="26116" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="26118" href="plfa.Lambda.html#4445" class="Function">two</a>
  <a id="26124" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="26128" href="plfa.Lambda.html#19533" class="InductiveConstructor">ξ-·₁</a> <a id="26133" class="Symbol">(</a><a id="26134" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="26138" class="Symbol">(</a><a id="26139" href="plfa.Lambda.html#11627" class="InductiveConstructor">V-suc</a> <a id="26145" class="Symbol">(</a><a id="26146" href="plfa.Lambda.html#11627" class="InductiveConstructor">V-suc</a> <a id="26152" href="plfa.Lambda.html#11579" class="InductiveConstructor">V-zero</a><a id="26158" class="Symbol">)))</a> <a id="26162" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="26168" class="Symbol">(</a><a id="26169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3775" class="InductiveConstructor Operator">ƛ</a> <a id="26171" class="String">&quot;n&quot;</a> <a id="26175" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a>
      <a id="26183" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3944" class="InductiveConstructor Operator">case</a> <a id="26188" href="plfa.Lambda.html#4445" class="Function">two</a> <a id="26192" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">[zero⇒</a> <a id="26199" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="26201" class="String">&quot;n&quot;</a> <a id="26205" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">|suc</a> <a id="26210" class="String">&quot;m&quot;</a> <a id="26214" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">⇒</a> <a id="26216" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="26221" class="Symbol">(</a><a id="26222" href="plfa.Lambda.html#4479" class="Function">plus</a> <a id="26227" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="26229" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="26231" class="String">&quot;m&quot;</a> <a id="26235" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="26237" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="26239" class="String">&quot;n&quot;</a><a id="26242" class="Symbol">)</a> <a id="26244" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">]</a><a id="26245" class="Symbol">)</a>
         <a id="26256" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3821" class="InductiveConstructor Operator">·</a> <a id="26258" href="plfa.Lambda.html#4445" class="Function">two</a>
  <a id="26264" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="26268" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="26272" class="Symbol">(</a><a id="26273" href="plfa.Lambda.html#11627" class="InductiveConstructor">V-suc</a> <a id="26279" class="Symbol">(</a><a id="26280" href="plfa.Lambda.html#11627" class="InductiveConstructor">V-suc</a> <a id="26286" href="plfa.Lambda.html#11579" class="InductiveConstructor">V-zero</a><a id="26292" class="Symbol">))</a> <a id="26295" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="26301" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3944" class="InductiveConstructor Operator">case</a> <a id="26306" href="plfa.Lambda.html#4445" class="Function">two</a> <a id="26310" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">[zero⇒</a> <a id="26317" href="plfa.Lambda.html#4445" class="Function">two</a> <a id="26321" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">|suc</a> <a id="26326" class="String">&quot;m&quot;</a> <a id="26330" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">⇒</a> <a id="26332" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="26337" class="Symbol">(</a><a id="26338" href="plfa.Lambda.html#4479" class="Function">plus</a> <a id="26343" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="26345" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="26347" class="String">&quot;m&quot;</a> <a id="26351" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="26353" href="plfa.Lambda.html#4445" class="Function">two</a><a id="26356" class="Symbol">)</a> <a id="26358" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">]</a>
  <a id="26362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="26366" href="plfa.Lambda.html#20192" class="InductiveConstructor">β-suc</a> <a id="26372" class="Symbol">(</a><a id="26373" href="plfa.Lambda.html#11627" class="InductiveConstructor">V-suc</a> <a id="26379" href="plfa.Lambda.html#11579" class="InductiveConstructor">V-zero</a><a id="26385" class="Symbol">)</a> <a id="26387" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="26393" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3903" class="InductiveConstructor Operator">`suc</a> <a id="26398" class="Symbol">(</a><a id="26399" href="plfa.Lambda.html#4479" class="Function">plus</a> <a id="26404" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="26406" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="26411" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a> <a id="26417" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="26419" href="plfa.Lambda.html#4445" class="Function">two</a><a id="26422" class="Symbol">)</a>
  <a id="26426" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="26430" href="plfa.Lambda.html#19815" class="InductiveConstructor">ξ-suc</a> <a id="26436" class="Symbol">(</a><a id="26437" href="plfa.Lambda.html#19533" class="InductiveConstructor">ξ-·₁</a> <a id="26442" class="Symbol">(</a><a id="26443" href="plfa.Lambda.html#19533" class="InductiveConstructor">ξ-·₁</a> <a id="26448" href="plfa.Lambda.html#20343" class="InductiveConstructor">β-μ</a><a id="26451" class="Symbol">))</a> <a id="26454" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="26460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3903" class="InductiveConstructor Operator">`suc</a> <a id="26465" class="Symbol">((</a><a id="26467" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="26469" class="String">&quot;m&quot;</a> <a id="26473" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="26475" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="26477" class="String">&quot;n&quot;</a> <a id="26481" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a>
      <a id="26489" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3944" class="InductiveConstructor Operator">case</a> <a id="26494" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="26496" class="String">&quot;m&quot;</a> <a id="26500" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">[zero⇒</a> <a id="26507" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="26509" class="String">&quot;n&quot;</a> <a id="26513" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">|suc</a> <a id="26518" class="String">&quot;m&quot;</a> <a id="26522" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">⇒</a> <a id="26524" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="26529" class="Symbol">(</a><a id="26530" href="plfa.Lambda.html#4479" class="Function">plus</a> <a id="26535" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="26537" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="26539" class="String">&quot;m&quot;</a> <a id="26543" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="26545" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="26547" class="String">&quot;n&quot;</a><a id="26550" class="Symbol">)</a> <a id="26552" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">]</a><a id="26553" class="Symbol">)</a>
        <a id="26563" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3821" class="InductiveConstructor Operator">·</a> <a id="26565" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="26570" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a> <a id="26576" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="26578" href="plfa.Lambda.html#4445" class="Function">two</a><a id="26581" class="Symbol">)</a>
  <a id="26585" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="26589" href="plfa.Lambda.html#19815" class="InductiveConstructor">ξ-suc</a> <a id="26595" class="Symbol">(</a><a id="26596" href="plfa.Lambda.html#19533" class="InductiveConstructor">ξ-·₁</a> <a id="26601" class="Symbol">(</a><a id="26602" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="26606" class="Symbol">(</a><a id="26607" href="plfa.Lambda.html#11627" class="InductiveConstructor">V-suc</a> <a id="26613" href="plfa.Lambda.html#11579" class="InductiveConstructor">V-zero</a><a id="26619" class="Symbol">)))</a> <a id="26623" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="26629" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3903" class="InductiveConstructor Operator">`suc</a> <a id="26634" class="Symbol">((</a><a id="26636" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="26638" class="String">&quot;n&quot;</a> <a id="26642" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a>
      <a id="26650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3944" class="InductiveConstructor Operator">case</a> <a id="26655" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="26660" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a> <a id="26666" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">[zero⇒</a> <a id="26673" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="26675" class="String">&quot;n&quot;</a> <a id="26679" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">|suc</a> <a id="26684" class="String">&quot;m&quot;</a> <a id="26688" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">⇒</a> <a id="26690" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="26695" class="Symbol">(</a><a id="26696" href="plfa.Lambda.html#4479" class="Function">plus</a> <a id="26701" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="26703" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="26705" class="String">&quot;m&quot;</a> <a id="26709" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="26711" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="26713" class="String">&quot;n&quot;</a><a id="26716" class="Symbol">)</a> <a id="26718" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">]</a><a id="26719" class="Symbol">)</a>
        <a id="26729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3821" class="InductiveConstructor Operator">·</a> <a id="26731" href="plfa.Lambda.html#4445" class="Function">two</a><a id="26734" class="Symbol">)</a>
  <a id="26738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="26742" href="plfa.Lambda.html#19815" class="InductiveConstructor">ξ-suc</a> <a id="26748" class="Symbol">(</a><a id="26749" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="26753" class="Symbol">(</a><a id="26754" href="plfa.Lambda.html#11627" class="InductiveConstructor">V-suc</a> <a id="26760" class="Symbol">(</a><a id="26761" href="plfa.Lambda.html#11627" class="InductiveConstructor">V-suc</a> <a id="26767" href="plfa.Lambda.html#11579" class="InductiveConstructor">V-zero</a><a id="26773" class="Symbol">)))</a> <a id="26777" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="26783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3903" class="InductiveConstructor Operator">`suc</a> <a id="26788" class="Symbol">(</a><a id="26789" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">case</a> <a id="26794" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="26799" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a> <a id="26805" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">[zero⇒</a> <a id="26812" href="plfa.Lambda.html#4445" class="Function">two</a> <a id="26816" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">|suc</a> <a id="26821" class="String">&quot;m&quot;</a> <a id="26825" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">⇒</a> <a id="26827" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="26832" class="Symbol">(</a><a id="26833" href="plfa.Lambda.html#4479" class="Function">plus</a> <a id="26838" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="26840" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="26842" class="String">&quot;m&quot;</a> <a id="26846" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="26848" href="plfa.Lambda.html#4445" class="Function">two</a><a id="26851" class="Symbol">)</a> <a id="26853" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">]</a><a id="26854" class="Symbol">)</a>
  <a id="26858" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="26862" href="plfa.Lambda.html#19815" class="InductiveConstructor">ξ-suc</a> <a id="26868" class="Symbol">(</a><a id="26869" href="plfa.Lambda.html#20192" class="InductiveConstructor">β-suc</a> <a id="26875" href="plfa.Lambda.html#11579" class="InductiveConstructor">V-zero</a><a id="26881" class="Symbol">)</a> <a id="26883" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="26889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3903" class="InductiveConstructor Operator">`suc</a> <a id="26894" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="26899" class="Symbol">(</a><a id="26900" href="plfa.Lambda.html#4479" class="Function">plus</a> <a id="26905" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="26907" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a> <a id="26913" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="26915" href="plfa.Lambda.html#4445" class="Function">two</a><a id="26918" class="Symbol">)</a>
  <a id="26922" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="26926" href="plfa.Lambda.html#19815" class="InductiveConstructor">ξ-suc</a> <a id="26932" class="Symbol">(</a><a id="26933" href="plfa.Lambda.html#19815" class="InductiveConstructor">ξ-suc</a> <a id="26939" class="Symbol">(</a><a id="26940" href="plfa.Lambda.html#19533" class="InductiveConstructor">ξ-·₁</a> <a id="26945" class="Symbol">(</a><a id="26946" href="plfa.Lambda.html#19533" class="InductiveConstructor">ξ-·₁</a> <a id="26951" href="plfa.Lambda.html#20343" class="InductiveConstructor">β-μ</a><a id="26954" class="Symbol">)))</a> <a id="26958" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="26964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3903" class="InductiveConstructor Operator">`suc</a> <a id="26969" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="26974" class="Symbol">((</a><a id="26976" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="26978" class="String">&quot;m&quot;</a> <a id="26982" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="26984" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="26986" class="String">&quot;n&quot;</a> <a id="26990" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a>
      <a id="26998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3944" class="InductiveConstructor Operator">case</a> <a id="27003" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="27005" class="String">&quot;m&quot;</a> <a id="27009" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">[zero⇒</a> <a id="27016" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="27018" class="String">&quot;n&quot;</a> <a id="27022" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">|suc</a> <a id="27027" class="String">&quot;m&quot;</a> <a id="27031" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">⇒</a> <a id="27033" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="27038" class="Symbol">(</a><a id="27039" href="plfa.Lambda.html#4479" class="Function">plus</a> <a id="27044" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27046" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="27048" class="String">&quot;m&quot;</a> <a id="27052" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27054" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="27056" class="String">&quot;n&quot;</a><a id="27059" class="Symbol">)</a> <a id="27061" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">]</a><a id="27062" class="Symbol">)</a>
        <a id="27072" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3821" class="InductiveConstructor Operator">·</a> <a id="27074" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a> <a id="27080" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27082" href="plfa.Lambda.html#4445" class="Function">two</a><a id="27085" class="Symbol">)</a>
  <a id="27089" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="27093" href="plfa.Lambda.html#19815" class="InductiveConstructor">ξ-suc</a> <a id="27099" class="Symbol">(</a><a id="27100" href="plfa.Lambda.html#19815" class="InductiveConstructor">ξ-suc</a> <a id="27106" class="Symbol">(</a><a id="27107" href="plfa.Lambda.html#19533" class="InductiveConstructor">ξ-·₁</a> <a id="27112" class="Symbol">(</a><a id="27113" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="27117" href="plfa.Lambda.html#11579" class="InductiveConstructor">V-zero</a><a id="27123" class="Symbol">)))</a> <a id="27127" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="27133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3903" class="InductiveConstructor Operator">`suc</a> <a id="27138" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="27143" class="Symbol">((</a><a id="27145" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="27147" class="String">&quot;n&quot;</a> <a id="27151" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a>
      <a id="27159" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3944" class="InductiveConstructor Operator">case</a> <a id="27164" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a> <a id="27170" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">[zero⇒</a> <a id="27177" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="27179" class="String">&quot;n&quot;</a> <a id="27183" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">|suc</a> <a id="27188" class="String">&quot;m&quot;</a> <a id="27192" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">⇒</a> <a id="27194" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="27199" class="Symbol">(</a><a id="27200" href="plfa.Lambda.html#4479" class="Function">plus</a> <a id="27205" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27207" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="27209" class="String">&quot;m&quot;</a> <a id="27213" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27215" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="27217" class="String">&quot;n&quot;</a><a id="27220" class="Symbol">)</a> <a id="27222" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">]</a><a id="27223" class="Symbol">)</a>
        <a id="27233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3821" class="InductiveConstructor Operator">·</a> <a id="27235" href="plfa.Lambda.html#4445" class="Function">two</a><a id="27238" class="Symbol">)</a>
  <a id="27242" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="27246" href="plfa.Lambda.html#19815" class="InductiveConstructor">ξ-suc</a> <a id="27252" class="Symbol">(</a><a id="27253" href="plfa.Lambda.html#19815" class="InductiveConstructor">ξ-suc</a> <a id="27259" class="Symbol">(</a><a id="27260" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="27264" class="Symbol">(</a><a id="27265" href="plfa.Lambda.html#11627" class="InductiveConstructor">V-suc</a> <a id="27271" class="Symbol">(</a><a id="27272" href="plfa.Lambda.html#11627" class="InductiveConstructor">V-suc</a> <a id="27278" href="plfa.Lambda.html#11579" class="InductiveConstructor">V-zero</a><a id="27284" class="Symbol">))))</a> <a id="27289" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="27295" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3903" class="InductiveConstructor Operator">`suc</a> <a id="27300" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="27305" class="Symbol">(</a><a id="27306" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">case</a> <a id="27311" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a> <a id="27317" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">[zero⇒</a> <a id="27324" href="plfa.Lambda.html#4445" class="Function">two</a> <a id="27328" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">|suc</a> <a id="27333" class="String">&quot;m&quot;</a> <a id="27337" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">⇒</a> <a id="27339" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="27344" class="Symbol">(</a><a id="27345" href="plfa.Lambda.html#4479" class="Function">plus</a> <a id="27350" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27352" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="27354" class="String">&quot;m&quot;</a> <a id="27358" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27360" href="plfa.Lambda.html#4445" class="Function">two</a><a id="27363" class="Symbol">)</a> <a id="27365" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">]</a><a id="27366" class="Symbol">)</a>
  <a id="27370" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="27374" href="plfa.Lambda.html#19815" class="InductiveConstructor">ξ-suc</a> <a id="27380" class="Symbol">(</a><a id="27381" href="plfa.Lambda.html#19815" class="InductiveConstructor">ξ-suc</a> <a id="27387" href="plfa.Lambda.html#20079" class="InductiveConstructor">β-zero</a><a id="27393" class="Symbol">)</a> <a id="27395" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="27401" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3903" class="InductiveConstructor Operator">`suc</a> <a id="27406" class="Symbol">(</a><a id="27407" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="27412" class="Symbol">(</a><a id="27413" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="27418" class="Symbol">(</a><a id="27419" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="27424" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a><a id="27429" class="Symbol">)))</a>
  <a id="27435" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22507" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
And here is a similar sample reduction for Church numerals:
{% raw %}<pre class="Agda"><a id="27506" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#27506" class="Function">_</a> <a id="27508" class="Symbol">:</a> <a id="27510" href="plfa.Lambda.html#5740" class="Function">plusᶜ</a> <a id="27516" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27518" href="plfa.Lambda.html#5679" class="Function">twoᶜ</a> <a id="27523" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27525" href="plfa.Lambda.html#5679" class="Function">twoᶜ</a> <a id="27530" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27532" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="27537" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27539" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a> <a id="27545" href="plfa.Lambda.html#22474" class="Datatype Operator">—↠</a> <a id="27548" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="27553" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="27558" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="27563" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="27568" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a>
<a id="27574" class="Symbol">_</a> <a id="27576" class="Symbol">=</a>
  <a id="27580" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="Function Operator">begin</a>
    <a id="27590" class="Symbol">(</a><a id="27591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3775" class="InductiveConstructor Operator">ƛ</a> <a id="27593" class="String">&quot;m&quot;</a> <a id="27597" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="27599" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="27601" class="String">&quot;n&quot;</a> <a id="27605" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="27607" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="27609" class="String">&quot;s&quot;</a> <a id="27613" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="27615" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="27617" class="String">&quot;z&quot;</a> <a id="27621" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="27623" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="27625" class="String">&quot;m&quot;</a> <a id="27629" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27631" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="27633" class="String">&quot;s&quot;</a> <a id="27637" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27639" class="Symbol">(</a><a id="27640" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="27642" class="String">&quot;n&quot;</a> <a id="27646" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27648" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="27650" class="String">&quot;s&quot;</a> <a id="27654" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27656" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="27658" class="String">&quot;z&quot;</a><a id="27661" class="Symbol">))</a>
      <a id="27670" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3821" class="InductiveConstructor Operator">·</a> <a id="27672" href="plfa.Lambda.html#5679" class="Function">twoᶜ</a> <a id="27677" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27679" href="plfa.Lambda.html#5679" class="Function">twoᶜ</a> <a id="27684" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27686" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="27691" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27693" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a>
  <a id="27701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="27705" href="plfa.Lambda.html#19533" class="InductiveConstructor">ξ-·₁</a> <a id="27710" class="Symbol">(</a><a id="27711" href="plfa.Lambda.html#19533" class="InductiveConstructor">ξ-·₁</a> <a id="27716" class="Symbol">(</a><a id="27717" href="plfa.Lambda.html#19533" class="InductiveConstructor">ξ-·₁</a> <a id="27722" class="Symbol">(</a><a id="27723" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="27727" href="plfa.Lambda.html#11518" class="InductiveConstructor">V-ƛ</a><a id="27730" class="Symbol">)))</a> <a id="27734" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="27740" class="Symbol">(</a><a id="27741" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3775" class="InductiveConstructor Operator">ƛ</a> <a id="27743" class="String">&quot;n&quot;</a> <a id="27747" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="27749" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="27751" class="String">&quot;s&quot;</a> <a id="27755" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="27757" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="27759" class="String">&quot;z&quot;</a> <a id="27763" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="27765" href="plfa.Lambda.html#5679" class="Function">twoᶜ</a> <a id="27770" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27772" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="27774" class="String">&quot;s&quot;</a> <a id="27778" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27780" class="Symbol">(</a><a id="27781" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="27783" class="String">&quot;n&quot;</a> <a id="27787" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27789" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="27791" class="String">&quot;s&quot;</a> <a id="27795" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27797" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="27799" class="String">&quot;z&quot;</a><a id="27802" class="Symbol">))</a>
      <a id="27811" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3821" class="InductiveConstructor Operator">·</a> <a id="27813" href="plfa.Lambda.html#5679" class="Function">twoᶜ</a> <a id="27818" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27820" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="27825" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27827" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a>
  <a id="27835" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="27839" href="plfa.Lambda.html#19533" class="InductiveConstructor">ξ-·₁</a> <a id="27844" class="Symbol">(</a><a id="27845" href="plfa.Lambda.html#19533" class="InductiveConstructor">ξ-·₁</a> <a id="27850" class="Symbol">(</a><a id="27851" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="27855" href="plfa.Lambda.html#11518" class="InductiveConstructor">V-ƛ</a><a id="27858" class="Symbol">))</a> <a id="27861" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="27867" class="Symbol">(</a><a id="27868" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3775" class="InductiveConstructor Operator">ƛ</a> <a id="27870" class="String">&quot;s&quot;</a> <a id="27874" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="27876" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="27878" class="String">&quot;z&quot;</a> <a id="27882" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="27884" href="plfa.Lambda.html#5679" class="Function">twoᶜ</a> <a id="27889" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27891" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="27893" class="String">&quot;s&quot;</a> <a id="27897" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27899" class="Symbol">(</a><a id="27900" href="plfa.Lambda.html#5679" class="Function">twoᶜ</a> <a id="27905" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27907" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="27909" class="String">&quot;s&quot;</a> <a id="27913" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27915" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="27917" class="String">&quot;z&quot;</a><a id="27920" class="Symbol">))</a> <a id="27923" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27925" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="27930" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27932" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a>
  <a id="27940" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="27944" href="plfa.Lambda.html#19533" class="InductiveConstructor">ξ-·₁</a> <a id="27949" class="Symbol">(</a><a id="27950" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="27954" href="plfa.Lambda.html#11518" class="InductiveConstructor">V-ƛ</a><a id="27957" class="Symbol">)</a> <a id="27959" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="27965" class="Symbol">(</a><a id="27966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3775" class="InductiveConstructor Operator">ƛ</a> <a id="27968" class="String">&quot;z&quot;</a> <a id="27972" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="27974" href="plfa.Lambda.html#5679" class="Function">twoᶜ</a> <a id="27979" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27981" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="27986" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27988" class="Symbol">(</a><a id="27989" href="plfa.Lambda.html#5679" class="Function">twoᶜ</a> <a id="27994" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="27996" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="28001" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28003" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="28005" class="String">&quot;z&quot;</a><a id="28008" class="Symbol">))</a> <a id="28011" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28013" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a>
  <a id="28021" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="28025" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="28029" href="plfa.Lambda.html#11579" class="InductiveConstructor">V-zero</a> <a id="28036" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="28042" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5679" class="Function">twoᶜ</a> <a id="28047" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28049" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="28054" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28056" class="Symbol">(</a><a id="28057" href="plfa.Lambda.html#5679" class="Function">twoᶜ</a> <a id="28062" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28064" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="28069" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28071" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a><a id="28076" class="Symbol">)</a>
  <a id="28080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="28084" href="plfa.Lambda.html#19533" class="InductiveConstructor">ξ-·₁</a> <a id="28089" class="Symbol">(</a><a id="28090" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="28094" href="plfa.Lambda.html#11518" class="InductiveConstructor">V-ƛ</a><a id="28097" class="Symbol">)</a> <a id="28099" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="28105" class="Symbol">(</a><a id="28106" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3775" class="InductiveConstructor Operator">ƛ</a> <a id="28108" class="String">&quot;z&quot;</a> <a id="28112" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="28114" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="28119" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28121" class="Symbol">(</a><a id="28122" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="28127" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28129" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="28131" class="String">&quot;z&quot;</a><a id="28134" class="Symbol">))</a> <a id="28137" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28139" class="Symbol">(</a><a id="28140" href="plfa.Lambda.html#5679" class="Function">twoᶜ</a> <a id="28145" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28147" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="28152" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28154" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a><a id="28159" class="Symbol">)</a>
  <a id="28163" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="28167" href="plfa.Lambda.html#19614" class="InductiveConstructor">ξ-·₂</a> <a id="28172" href="plfa.Lambda.html#11518" class="InductiveConstructor">V-ƛ</a> <a id="28176" class="Symbol">(</a><a id="28177" href="plfa.Lambda.html#19533" class="InductiveConstructor">ξ-·₁</a> <a id="28182" class="Symbol">(</a><a id="28183" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="28187" href="plfa.Lambda.html#11518" class="InductiveConstructor">V-ƛ</a><a id="28190" class="Symbol">))</a> <a id="28193" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="28199" class="Symbol">(</a><a id="28200" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3775" class="InductiveConstructor Operator">ƛ</a> <a id="28202" class="String">&quot;z&quot;</a> <a id="28206" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="28208" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="28213" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28215" class="Symbol">(</a><a id="28216" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="28221" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28223" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="28225" class="String">&quot;z&quot;</a><a id="28228" class="Symbol">))</a> <a id="28231" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28233" class="Symbol">((</a><a id="28235" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="28237" class="String">&quot;z&quot;</a> <a id="28241" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="28243" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="28248" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28250" class="Symbol">(</a><a id="28251" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="28256" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28258" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="28260" class="String">&quot;z&quot;</a><a id="28263" class="Symbol">))</a> <a id="28266" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28268" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a><a id="28273" class="Symbol">)</a>
  <a id="28277" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="28281" href="plfa.Lambda.html#19614" class="InductiveConstructor">ξ-·₂</a> <a id="28286" href="plfa.Lambda.html#11518" class="InductiveConstructor">V-ƛ</a> <a id="28290" class="Symbol">(</a><a id="28291" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="28295" href="plfa.Lambda.html#11579" class="InductiveConstructor">V-zero</a><a id="28301" class="Symbol">)</a> <a id="28303" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="28309" class="Symbol">(</a><a id="28310" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3775" class="InductiveConstructor Operator">ƛ</a> <a id="28312" class="String">&quot;z&quot;</a> <a id="28316" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="28318" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="28323" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28325" class="Symbol">(</a><a id="28326" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="28331" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28333" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="28335" class="String">&quot;z&quot;</a><a id="28338" class="Symbol">))</a> <a id="28341" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28343" class="Symbol">(</a><a id="28344" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="28349" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28351" class="Symbol">(</a><a id="28352" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="28357" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28359" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a><a id="28364" class="Symbol">))</a>
  <a id="28369" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="28373" href="plfa.Lambda.html#19614" class="InductiveConstructor">ξ-·₂</a> <a id="28378" href="plfa.Lambda.html#11518" class="InductiveConstructor">V-ƛ</a> <a id="28382" class="Symbol">(</a><a id="28383" href="plfa.Lambda.html#19614" class="InductiveConstructor">ξ-·₂</a> <a id="28388" href="plfa.Lambda.html#11518" class="InductiveConstructor">V-ƛ</a> <a id="28392" class="Symbol">(</a><a id="28393" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="28397" href="plfa.Lambda.html#11579" class="InductiveConstructor">V-zero</a><a id="28403" class="Symbol">))</a> <a id="28406" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="28412" class="Symbol">(</a><a id="28413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3775" class="InductiveConstructor Operator">ƛ</a> <a id="28415" class="String">&quot;z&quot;</a> <a id="28419" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="28421" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="28426" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28428" class="Symbol">(</a><a id="28429" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="28434" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28436" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="28438" class="String">&quot;z&quot;</a><a id="28441" class="Symbol">))</a> <a id="28444" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28446" class="Symbol">(</a><a id="28447" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="28452" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28454" class="Symbol">(</a><a id="28455" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="28460" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a><a id="28465" class="Symbol">))</a>
  <a id="28470" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="28474" href="plfa.Lambda.html#19614" class="InductiveConstructor">ξ-·₂</a> <a id="28479" href="plfa.Lambda.html#11518" class="InductiveConstructor">V-ƛ</a> <a id="28483" class="Symbol">(</a><a id="28484" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="28488" class="Symbol">(</a><a id="28489" href="plfa.Lambda.html#11627" class="InductiveConstructor">V-suc</a> <a id="28495" href="plfa.Lambda.html#11579" class="InductiveConstructor">V-zero</a><a id="28501" class="Symbol">))</a> <a id="28504" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="28510" class="Symbol">(</a><a id="28511" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3775" class="InductiveConstructor Operator">ƛ</a> <a id="28513" class="String">&quot;z&quot;</a> <a id="28517" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="28519" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="28524" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28526" class="Symbol">(</a><a id="28527" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="28532" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28534" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="28536" class="String">&quot;z&quot;</a><a id="28539" class="Symbol">))</a> <a id="28542" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28544" class="Symbol">(</a><a id="28545" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="28550" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="28555" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a><a id="28560" class="Symbol">)</a>
  <a id="28564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="28568" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="28572" class="Symbol">(</a><a id="28573" href="plfa.Lambda.html#11627" class="InductiveConstructor">V-suc</a> <a id="28579" class="Symbol">(</a><a id="28580" href="plfa.Lambda.html#11627" class="InductiveConstructor">V-suc</a> <a id="28586" href="plfa.Lambda.html#11579" class="InductiveConstructor">V-zero</a><a id="28592" class="Symbol">))</a> <a id="28595" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="28601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5844" class="Function">sucᶜ</a> <a id="28606" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28608" class="Symbol">(</a><a id="28609" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="28614" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28616" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="28621" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="28626" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a><a id="28631" class="Symbol">)</a>
  <a id="28635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="28639" href="plfa.Lambda.html#19614" class="InductiveConstructor">ξ-·₂</a> <a id="28644" href="plfa.Lambda.html#11518" class="InductiveConstructor">V-ƛ</a> <a id="28648" class="Symbol">(</a><a id="28649" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="28653" class="Symbol">(</a><a id="28654" href="plfa.Lambda.html#11627" class="InductiveConstructor">V-suc</a> <a id="28660" class="Symbol">(</a><a id="28661" href="plfa.Lambda.html#11627" class="InductiveConstructor">V-suc</a> <a id="28667" href="plfa.Lambda.html#11579" class="InductiveConstructor">V-zero</a><a id="28673" class="Symbol">)))</a> <a id="28677" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
    <a id="28683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5844" class="Function">sucᶜ</a> <a id="28688" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="28690" class="Symbol">(</a><a id="28691" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="28696" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="28701" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="28706" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a><a id="28711" class="Symbol">)</a>
  <a id="28715" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22548" class="InductiveConstructor Operator">—→⟨</a> <a id="28719" href="plfa.Lambda.html#19709" class="InductiveConstructor">β-ƛ</a> <a id="28723" class="Symbol">(</a><a id="28724" href="plfa.Lambda.html#11627" class="InductiveConstructor">V-suc</a> <a id="28730" class="Symbol">(</a><a id="28731" href="plfa.Lambda.html#11627" class="InductiveConstructor">V-suc</a> <a id="28737" class="Symbol">(</a><a id="28738" href="plfa.Lambda.html#11627" class="InductiveConstructor">V-suc</a> <a id="28744" href="plfa.Lambda.html#11579" class="InductiveConstructor">V-zero</a><a id="28750" class="Symbol">)))</a> <a id="28754" href="plfa.Lambda.html#22548" class="InductiveConstructor Operator">⟩</a>
   <a id="28759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3903" class="InductiveConstructor Operator">`suc</a> <a id="28764" class="Symbol">(</a><a id="28765" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="28770" class="Symbol">(</a><a id="28771" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="28776" class="Symbol">(</a><a id="28777" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="28782" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a><a id="28787" class="Symbol">)))</a>
  <a id="28793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22507" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
In the next chapter, we will see how to compute such reduction sequences.


#### Exercise `plus-example`

Write out the reduction sequence demonstrating that one plus one is two.

{% raw %}<pre class="Agda"><a id="28984" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Syntax of types

We have just two types:

  * Functions, `A ⇒ B`
  * Naturals, `` `ℕ ``

As before, to avoid overlap we use variants of the names used by https://agda.github.io/agda-stdlib/v1.1/Agda.

Here is the syntax of types in BNF:

    A, B, C  ::=  A ⇒ B | `ℕ

And here it is formalised in Agda:

{% raw %}<pre class="Agda"><a id="29284" class="Keyword">infixr</a> <a id="29291" class="Number">7</a> <a id="29293" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#29322" class="InductiveConstructor Operator">_⇒_</a>

<a id="29298" class="Keyword">data</a> <a id="Type"></a><a id="29303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#29303" class="Datatype">Type</a> <a id="29308" class="Symbol">:</a> <a id="29310" class="PrimitiveType">Set</a> <a id="29314" class="Keyword">where</a>
  <a id="Type._⇒_"></a><a id="29322" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#29322" class="InductiveConstructor Operator">_⇒_</a> <a id="29326" class="Symbol">:</a> <a id="29328" href="plfa.Lambda.html#29303" class="Datatype">Type</a> <a id="29333" class="Symbol">→</a> <a id="29335" href="plfa.Lambda.html#29303" class="Datatype">Type</a> <a id="29340" class="Symbol">→</a> <a id="29342" href="plfa.Lambda.html#29303" class="Datatype">Type</a>
  <a id="Type.`ℕ"></a><a id="29349" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#29349" class="InductiveConstructor">`ℕ</a> <a id="29352" class="Symbol">:</a> <a id="29354" href="plfa.Lambda.html#29303" class="Datatype">Type</a>
</pre>{% endraw %}
### Precedence

As in Agda, functions of two or more arguments are represented via
currying. This is made more convenient by declaring `_⇒_` to
associate to the right and `_·_` to associate to the left.
Thus:

* ``(`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ`` stands for ``((`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ))``.
* `plus · two · two` stands for `(plus · two) · two`.

### Quiz

* What is the type of the following term?

    `` ƛ "s" ⇒ ` "s" · (` "s"  · `zero) ``

  1. `` (`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ) ``
  2. `` (`ℕ ⇒ `ℕ) ⇒ `ℕ ``
  3. `` `ℕ ⇒ (`ℕ ⇒ `ℕ) ``
  4. `` `ℕ ⇒ `ℕ ⇒ `ℕ ``
  5. `` `ℕ ⇒ `ℕ ``
  6. `` `ℕ ``

  Give more than one answer if appropriate.

* What is the type of the following term?

    `` (ƛ "s" ⇒ ` "s" · (` "s"  · `zero)) · sucᶜ ``

  1. `` (`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ) ``
  2. `` (`ℕ ⇒ `ℕ) ⇒ `ℕ ``
  3. `` `ℕ ⇒ (`ℕ ⇒ `ℕ) ``
  4. `` `ℕ ⇒ `ℕ ⇒ `ℕ ``
  5. `` `ℕ ⇒ `ℕ ``
  6. `` `ℕ ``

  Give more than one answer if appropriate.


## Typing

### Contexts

While reduction considers only closed terms, typing must
consider terms with free variables.  To type a term,
we must first type its subterms, and in particular in the
body of an abstraction its bound variable may appear free.

A _context_ associates variables with types.  We let `Γ` and `Δ` range
over contexts.  We write `∅` for the empty context, and `Γ , x ⦂ A`
for the context that extends `Γ` by mapping variable `x` to type `A`.
For example,

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ``

is the context that associates variable `` "s" `` with type `` `ℕ ⇒ `ℕ ``,
and variable `` "z" `` with type `` `ℕ ``.

Contexts are formalised as follows:

{% raw %}<pre class="Agda"><a id="30939" class="Keyword">infixl</a> <a id="30946" class="Number">5</a>  <a id="30949" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#31001" class="InductiveConstructor Operator">_,_⦂_</a>

<a id="30956" class="Keyword">data</a> <a id="Context"></a><a id="30961" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#30961" class="Datatype">Context</a> <a id="30969" class="Symbol">:</a> <a id="30971" class="PrimitiveType">Set</a> <a id="30975" class="Keyword">where</a>
  <a id="Context.∅"></a><a id="30983" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#30983" class="InductiveConstructor">∅</a>     <a id="30989" class="Symbol">:</a> <a id="30991" href="plfa.Lambda.html#30961" class="Datatype">Context</a>
  <a id="Context._,_⦂_"></a><a id="31001" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#31001" class="InductiveConstructor Operator">_,_⦂_</a> <a id="31007" class="Symbol">:</a> <a id="31009" href="plfa.Lambda.html#30961" class="Datatype">Context</a> <a id="31017" class="Symbol">→</a> <a id="31019" href="plfa.Lambda.html#3616" class="Function">Id</a> <a id="31022" class="Symbol">→</a> <a id="31024" href="plfa.Lambda.html#29303" class="Datatype">Type</a> <a id="31029" class="Symbol">→</a> <a id="31031" href="plfa.Lambda.html#30961" class="Datatype">Context</a>
</pre>{% endraw %}

#### Exercise `Context-≃`

Show that `Context` is isomorphic to `List (Id × Type)`.
For instance, the isomorphism relates the context

    ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ

to the list

    [ ⟨ "z" , `ℕ ⟩ , ⟨ "s" , `ℕ ⇒ `ℕ ⟩ ]

{% raw %}<pre class="Agda"><a id="31273" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
### Lookup judgment

We have two forms of _judgment_.  The first is written

    Γ ∋ x ⦂ A

and indicates in context `Γ` that variable `x` has type `A`.
It is called _lookup_.
For example,

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "z" ⦂ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "s" ⦂ `ℕ ⇒ `ℕ ``

give us the types associated with variables `` "z" `` and `` "s" ``,
respectively.  The symbol `∋` (pronounced "ni", for "in"
backwards) is chosen because checking that `Γ ∋ x ⦂ A` is analogous to
checking whether `x ⦂ A` appears in a list corresponding to `Γ`.

If two variables in a context have the same name, then lookup
should return the most recently bound variable, which _shadows_
the other variables.  For example,

* `` ∅ , "x" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ∋ "x" ⦂ `ℕ ``.

Here `` "x" ⦂ `ℕ ⇒ `ℕ `` is shadowed by `` "x" ⦂ `ℕ ``.

Lookup is formalised as follows:
{% raw %}<pre class="Agda"><a id="32162" class="Keyword">infix</a>  <a id="32169" class="Number">4</a>  <a id="32172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#32184" class="Datatype Operator">_∋_⦂_</a>

<a id="32179" class="Keyword">data</a> <a id="_∋_⦂_"></a><a id="32184" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#32184" class="Datatype Operator">_∋_⦂_</a> <a id="32190" class="Symbol">:</a> <a id="32192" href="plfa.Lambda.html#30961" class="Datatype">Context</a> <a id="32200" class="Symbol">→</a> <a id="32202" href="plfa.Lambda.html#3616" class="Function">Id</a> <a id="32205" class="Symbol">→</a> <a id="32207" href="plfa.Lambda.html#29303" class="Datatype">Type</a> <a id="32212" class="Symbol">→</a> <a id="32214" class="PrimitiveType">Set</a> <a id="32218" class="Keyword">where</a>

  <a id="_∋_⦂_.Z"></a><a id="32227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#32227" class="InductiveConstructor">Z</a> <a id="32229" class="Symbol">:</a> <a id="32231" class="Symbol">∀</a> <a id="32233" class="Symbol">{</a><a id="32234" href="plfa.Lambda.html#32234" class="Bound">Γ</a> <a id="32236" href="plfa.Lambda.html#32236" class="Bound">x</a> <a id="32238" href="plfa.Lambda.html#32238" class="Bound">A</a><a id="32239" class="Symbol">}</a>
      <a id="32247" class="Comment">------------------</a>
    <a id="32270" class="Symbol">→</a> <a id="32272" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#32234" class="Bound">Γ</a> <a id="32274" href="plfa.Lambda.html#31001" class="InductiveConstructor Operator">,</a> <a id="32276" href="plfa.Lambda.html#32236" class="Bound">x</a> <a id="32278" href="plfa.Lambda.html#31001" class="InductiveConstructor Operator">⦂</a> <a id="32280" href="plfa.Lambda.html#32238" class="Bound">A</a> <a id="32282" href="plfa.Lambda.html#32184" class="Datatype Operator">∋</a> <a id="32284" href="plfa.Lambda.html#32236" class="Bound">x</a> <a id="32286" href="plfa.Lambda.html#32184" class="Datatype Operator">⦂</a> <a id="32288" href="plfa.Lambda.html#32238" class="Bound">A</a>

  <a id="_∋_⦂_.S"></a><a id="32293" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#32293" class="InductiveConstructor">S</a> <a id="32295" class="Symbol">:</a> <a id="32297" class="Symbol">∀</a> <a id="32299" class="Symbol">{</a><a id="32300" href="plfa.Lambda.html#32300" class="Bound">Γ</a> <a id="32302" href="plfa.Lambda.html#32302" class="Bound">x</a> <a id="32304" href="plfa.Lambda.html#32304" class="Bound">y</a> <a id="32306" href="plfa.Lambda.html#32306" class="Bound">A</a> <a id="32308" href="plfa.Lambda.html#32308" class="Bound">B</a><a id="32309" class="Symbol">}</a>
    <a id="32315" class="Symbol">→</a> <a id="32317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#32302" class="Bound">x</a> <a id="32319" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#799" class="Function Operator">≢</a> <a id="32321" href="plfa.Lambda.html#32304" class="Bound">y</a>
    <a id="32327" class="Symbol">→</a> <a id="32329" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#32300" class="Bound">Γ</a> <a id="32331" href="plfa.Lambda.html#32184" class="Datatype Operator">∋</a> <a id="32333" href="plfa.Lambda.html#32302" class="Bound">x</a> <a id="32335" href="plfa.Lambda.html#32184" class="Datatype Operator">⦂</a> <a id="32337" href="plfa.Lambda.html#32306" class="Bound">A</a>
      <a id="32345" class="Comment">------------------</a>
    <a id="32368" class="Symbol">→</a> <a id="32370" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#32300" class="Bound">Γ</a> <a id="32372" href="plfa.Lambda.html#31001" class="InductiveConstructor Operator">,</a> <a id="32374" href="plfa.Lambda.html#32304" class="Bound">y</a> <a id="32376" href="plfa.Lambda.html#31001" class="InductiveConstructor Operator">⦂</a> <a id="32378" href="plfa.Lambda.html#32308" class="Bound">B</a> <a id="32380" href="plfa.Lambda.html#32184" class="Datatype Operator">∋</a> <a id="32382" href="plfa.Lambda.html#32302" class="Bound">x</a> <a id="32384" href="plfa.Lambda.html#32184" class="Datatype Operator">⦂</a> <a id="32386" href="plfa.Lambda.html#32306" class="Bound">A</a>
</pre>{% endraw %}
The constructors `Z` and `S` correspond roughly to the constructors
`here` and `there` for the element-of relation `_∈_` on lists.
Constructor `S` takes an additional parameter, which ensures that
when we look up a variable that it is not _shadowed_ by another
variable with the same name to its left in the list.

### Typing judgment

The second judgment is written

    Γ ⊢ M ⦂ A

and indicates in context `Γ` that term `M` has type `A`.
Context `Γ` provides types for all the free variables in `M`.
For example:

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "z" ⦂ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" ⦂ `ℕ ⇒ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · ` "z" ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · (` "s" · ` "z") ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂  `ℕ ⇒ `ℕ ``
* `` ∅ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂  (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ ``

Typing is formalised as follows:
{% raw %}<pre class="Agda"><a id="33326" class="Keyword">infix</a>  <a id="33333" class="Number">4</a>  <a id="33336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33348" class="Datatype Operator">_⊢_⦂_</a>

<a id="33343" class="Keyword">data</a> <a id="_⊢_⦂_"></a><a id="33348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33348" class="Datatype Operator">_⊢_⦂_</a> <a id="33354" class="Symbol">:</a> <a id="33356" href="plfa.Lambda.html#30961" class="Datatype">Context</a> <a id="33364" class="Symbol">→</a> <a id="33366" href="plfa.Lambda.html#3717" class="Datatype">Term</a> <a id="33371" class="Symbol">→</a> <a id="33373" href="plfa.Lambda.html#29303" class="Datatype">Type</a> <a id="33378" class="Symbol">→</a> <a id="33380" class="PrimitiveType">Set</a> <a id="33384" class="Keyword">where</a>

  <a id="33393" class="Comment">-- Axiom</a>
  <a id="_⊢_⦂_.⊢`"></a><a id="33404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33404" class="InductiveConstructor">⊢`</a> <a id="33407" class="Symbol">:</a> <a id="33409" class="Symbol">∀</a> <a id="33411" class="Symbol">{</a><a id="33412" href="plfa.Lambda.html#33412" class="Bound">Γ</a> <a id="33414" href="plfa.Lambda.html#33414" class="Bound">x</a> <a id="33416" href="plfa.Lambda.html#33416" class="Bound">A</a><a id="33417" class="Symbol">}</a>
    <a id="33423" class="Symbol">→</a> <a id="33425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33412" class="Bound">Γ</a> <a id="33427" href="plfa.Lambda.html#32184" class="Datatype Operator">∋</a> <a id="33429" href="plfa.Lambda.html#33414" class="Bound">x</a> <a id="33431" href="plfa.Lambda.html#32184" class="Datatype Operator">⦂</a> <a id="33433" href="plfa.Lambda.html#33416" class="Bound">A</a>
      <a id="33441" class="Comment">-----------</a>
    <a id="33457" class="Symbol">→</a> <a id="33459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33412" class="Bound">Γ</a> <a id="33461" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="33463" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="33465" href="plfa.Lambda.html#33414" class="Bound">x</a> <a id="33467" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="33469" href="plfa.Lambda.html#33416" class="Bound">A</a>

  <a id="33474" class="Comment">-- ⇒-I</a>
  <a id="_⊢_⦂_.⊢ƛ"></a><a id="33483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33483" class="InductiveConstructor">⊢ƛ</a> <a id="33486" class="Symbol">:</a> <a id="33488" class="Symbol">∀</a> <a id="33490" class="Symbol">{</a><a id="33491" href="plfa.Lambda.html#33491" class="Bound">Γ</a> <a id="33493" href="plfa.Lambda.html#33493" class="Bound">x</a> <a id="33495" href="plfa.Lambda.html#33495" class="Bound">N</a> <a id="33497" href="plfa.Lambda.html#33497" class="Bound">A</a> <a id="33499" href="plfa.Lambda.html#33499" class="Bound">B</a><a id="33500" class="Symbol">}</a>
    <a id="33506" class="Symbol">→</a> <a id="33508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33491" class="Bound">Γ</a> <a id="33510" href="plfa.Lambda.html#31001" class="InductiveConstructor Operator">,</a> <a id="33512" href="plfa.Lambda.html#33493" class="Bound">x</a> <a id="33514" href="plfa.Lambda.html#31001" class="InductiveConstructor Operator">⦂</a> <a id="33516" href="plfa.Lambda.html#33497" class="Bound">A</a> <a id="33518" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="33520" href="plfa.Lambda.html#33495" class="Bound">N</a> <a id="33522" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="33524" href="plfa.Lambda.html#33499" class="Bound">B</a>
      <a id="33532" class="Comment">-------------------</a>
    <a id="33556" class="Symbol">→</a> <a id="33558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33491" class="Bound">Γ</a> <a id="33560" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="33562" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="33564" href="plfa.Lambda.html#33493" class="Bound">x</a> <a id="33566" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="33568" href="plfa.Lambda.html#33495" class="Bound">N</a> <a id="33570" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="33572" href="plfa.Lambda.html#33497" class="Bound">A</a> <a id="33574" href="plfa.Lambda.html#29322" class="InductiveConstructor Operator">⇒</a> <a id="33576" href="plfa.Lambda.html#33499" class="Bound">B</a>

  <a id="33581" class="Comment">-- ⇒-E</a>
  <a id="_⊢_⦂_._·_"></a><a id="33590" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33590" class="InductiveConstructor Operator">_·_</a> <a id="33594" class="Symbol">:</a> <a id="33596" class="Symbol">∀</a> <a id="33598" class="Symbol">{</a><a id="33599" href="plfa.Lambda.html#33599" class="Bound">Γ</a> <a id="33601" href="plfa.Lambda.html#33601" class="Bound">L</a> <a id="33603" href="plfa.Lambda.html#33603" class="Bound">M</a> <a id="33605" href="plfa.Lambda.html#33605" class="Bound">A</a> <a id="33607" href="plfa.Lambda.html#33607" class="Bound">B</a><a id="33608" class="Symbol">}</a>
    <a id="33614" class="Symbol">→</a> <a id="33616" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33599" class="Bound">Γ</a> <a id="33618" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="33620" href="plfa.Lambda.html#33601" class="Bound">L</a> <a id="33622" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="33624" href="plfa.Lambda.html#33605" class="Bound">A</a> <a id="33626" href="plfa.Lambda.html#29322" class="InductiveConstructor Operator">⇒</a> <a id="33628" href="plfa.Lambda.html#33607" class="Bound">B</a>
    <a id="33634" class="Symbol">→</a> <a id="33636" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33599" class="Bound">Γ</a> <a id="33638" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="33640" href="plfa.Lambda.html#33603" class="Bound">M</a> <a id="33642" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="33644" href="plfa.Lambda.html#33605" class="Bound">A</a>
      <a id="33652" class="Comment">-------------</a>
    <a id="33670" class="Symbol">→</a> <a id="33672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33599" class="Bound">Γ</a> <a id="33674" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="33676" href="plfa.Lambda.html#33601" class="Bound">L</a> <a id="33678" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="33680" href="plfa.Lambda.html#33603" class="Bound">M</a> <a id="33682" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="33684" href="plfa.Lambda.html#33607" class="Bound">B</a>

  <a id="33689" class="Comment">-- ℕ-I₁</a>
  <a id="_⊢_⦂_.⊢zero"></a><a id="33699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33699" class="InductiveConstructor">⊢zero</a> <a id="33705" class="Symbol">:</a> <a id="33707" class="Symbol">∀</a> <a id="33709" class="Symbol">{</a><a id="33710" href="plfa.Lambda.html#33710" class="Bound">Γ</a><a id="33711" class="Symbol">}</a>
      <a id="33719" class="Comment">--------------</a>
    <a id="33738" class="Symbol">→</a> <a id="33740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33710" class="Bound">Γ</a> <a id="33742" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="33744" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a> <a id="33750" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="33752" href="plfa.Lambda.html#29349" class="InductiveConstructor">`ℕ</a>

  <a id="33758" class="Comment">-- ℕ-I₂</a>
  <a id="_⊢_⦂_.⊢suc"></a><a id="33768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33768" class="InductiveConstructor">⊢suc</a> <a id="33773" class="Symbol">:</a> <a id="33775" class="Symbol">∀</a> <a id="33777" class="Symbol">{</a><a id="33778" href="plfa.Lambda.html#33778" class="Bound">Γ</a> <a id="33780" href="plfa.Lambda.html#33780" class="Bound">M</a><a id="33781" class="Symbol">}</a>
    <a id="33787" class="Symbol">→</a> <a id="33789" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33778" class="Bound">Γ</a> <a id="33791" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="33793" href="plfa.Lambda.html#33780" class="Bound">M</a> <a id="33795" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="33797" href="plfa.Lambda.html#29349" class="InductiveConstructor">`ℕ</a>
      <a id="33806" class="Comment">---------------</a>
    <a id="33826" class="Symbol">→</a> <a id="33828" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33778" class="Bound">Γ</a> <a id="33830" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="33832" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="33837" href="plfa.Lambda.html#33780" class="Bound">M</a> <a id="33839" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="33841" href="plfa.Lambda.html#29349" class="InductiveConstructor">`ℕ</a>

  <a id="33847" class="Comment">-- ℕ-E</a>
  <a id="_⊢_⦂_.⊢case"></a><a id="33856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33856" class="InductiveConstructor">⊢case</a> <a id="33862" class="Symbol">:</a> <a id="33864" class="Symbol">∀</a> <a id="33866" class="Symbol">{</a><a id="33867" href="plfa.Lambda.html#33867" class="Bound">Γ</a> <a id="33869" href="plfa.Lambda.html#33869" class="Bound">L</a> <a id="33871" href="plfa.Lambda.html#33871" class="Bound">M</a> <a id="33873" href="plfa.Lambda.html#33873" class="Bound">x</a> <a id="33875" href="plfa.Lambda.html#33875" class="Bound">N</a> <a id="33877" href="plfa.Lambda.html#33877" class="Bound">A</a><a id="33878" class="Symbol">}</a>
    <a id="33884" class="Symbol">→</a> <a id="33886" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33867" class="Bound">Γ</a> <a id="33888" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="33890" href="plfa.Lambda.html#33869" class="Bound">L</a> <a id="33892" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="33894" href="plfa.Lambda.html#29349" class="InductiveConstructor">`ℕ</a>
    <a id="33901" class="Symbol">→</a> <a id="33903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33867" class="Bound">Γ</a> <a id="33905" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="33907" href="plfa.Lambda.html#33871" class="Bound">M</a> <a id="33909" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="33911" href="plfa.Lambda.html#33877" class="Bound">A</a>
    <a id="33917" class="Symbol">→</a> <a id="33919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33867" class="Bound">Γ</a> <a id="33921" href="plfa.Lambda.html#31001" class="InductiveConstructor Operator">,</a> <a id="33923" href="plfa.Lambda.html#33873" class="Bound">x</a> <a id="33925" href="plfa.Lambda.html#31001" class="InductiveConstructor Operator">⦂</a> <a id="33927" href="plfa.Lambda.html#29349" class="InductiveConstructor">`ℕ</a> <a id="33930" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="33932" href="plfa.Lambda.html#33875" class="Bound">N</a> <a id="33934" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="33936" href="plfa.Lambda.html#33877" class="Bound">A</a>
      <a id="33944" class="Comment">-------------------------------------</a>
    <a id="33986" class="Symbol">→</a> <a id="33988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33867" class="Bound">Γ</a> <a id="33990" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="33992" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">case</a> <a id="33997" href="plfa.Lambda.html#33869" class="Bound">L</a> <a id="33999" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">[zero⇒</a> <a id="34006" href="plfa.Lambda.html#33871" class="Bound">M</a> <a id="34008" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">|suc</a> <a id="34013" href="plfa.Lambda.html#33873" class="Bound">x</a> <a id="34015" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">⇒</a> <a id="34017" href="plfa.Lambda.html#33875" class="Bound">N</a> <a id="34019" href="plfa.Lambda.html#3944" class="InductiveConstructor Operator">]</a> <a id="34021" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="34023" href="plfa.Lambda.html#33877" class="Bound">A</a>

  <a id="_⊢_⦂_.⊢μ"></a><a id="34028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#34028" class="InductiveConstructor">⊢μ</a> <a id="34031" class="Symbol">:</a> <a id="34033" class="Symbol">∀</a> <a id="34035" class="Symbol">{</a><a id="34036" href="plfa.Lambda.html#34036" class="Bound">Γ</a> <a id="34038" href="plfa.Lambda.html#34038" class="Bound">x</a> <a id="34040" href="plfa.Lambda.html#34040" class="Bound">M</a> <a id="34042" href="plfa.Lambda.html#34042" class="Bound">A</a><a id="34043" class="Symbol">}</a>
    <a id="34049" class="Symbol">→</a> <a id="34051" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#34036" class="Bound">Γ</a> <a id="34053" href="plfa.Lambda.html#31001" class="InductiveConstructor Operator">,</a> <a id="34055" href="plfa.Lambda.html#34038" class="Bound">x</a> <a id="34057" href="plfa.Lambda.html#31001" class="InductiveConstructor Operator">⦂</a> <a id="34059" href="plfa.Lambda.html#34042" class="Bound">A</a> <a id="34061" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="34063" href="plfa.Lambda.html#34040" class="Bound">M</a> <a id="34065" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="34067" href="plfa.Lambda.html#34042" class="Bound">A</a>
      <a id="34075" class="Comment">-----------------</a>
    <a id="34097" class="Symbol">→</a> <a id="34099" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#34036" class="Bound">Γ</a> <a id="34101" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="34103" href="plfa.Lambda.html#4004" class="InductiveConstructor Operator">μ</a> <a id="34105" href="plfa.Lambda.html#34038" class="Bound">x</a> <a id="34107" href="plfa.Lambda.html#4004" class="InductiveConstructor Operator">⇒</a> <a id="34109" href="plfa.Lambda.html#34040" class="Bound">M</a> <a id="34111" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="34113" href="plfa.Lambda.html#34042" class="Bound">A</a>
</pre>{% endraw %}
Each type rule is named after the constructor for the
corresponding term.

Most of the rules have a second name, derived from a convention in
logic, whereby the rule is named after the type connective that it
concerns; rules to introduce and to eliminate each connective are
labeled `-I` and `-E`, respectively. As we read the rules from top to
bottom, introduction and elimination rules do what they say on the
tin: the first _introduces_ a formula for the connective, which
appears in the conclusion but not in the premises; while the second
_eliminates_ a formula for the connective, which appears in a premise
but not in the conclusion. An introduction rule describes how to
construct a value of the type (abstractions yield functions, successor
and zero yield naturals), while an elimination rule describes how to
deconstruct a value of the given type (applications use functions,
case expressions use naturals).

Note also the three places (in `⊢ƛ`, `⊢case`, and `⊢μ`) where the
context is extended with `x` and an appropriate type, corresponding to
the three places where a bound variable is introduced.

The rules are deterministic, in that at most one rule applies to every term.


### Checking inequality and postulating the impossible {#impossible}

The following function makes it convenient to assert an inequality:
{% raw %}<pre class="Agda"><a id="_≠_"></a><a id="35453" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#35453" class="Function Operator">_≠_</a> <a id="35457" class="Symbol">:</a> <a id="35459" class="Symbol">∀</a> <a id="35461" class="Symbol">(</a><a id="35462" href="plfa.Lambda.html#35462" class="Bound">x</a> <a id="35464" href="plfa.Lambda.html#35464" class="Bound">y</a> <a id="35466" class="Symbol">:</a> <a id="35468" href="plfa.Lambda.html#3616" class="Function">Id</a><a id="35470" class="Symbol">)</a> <a id="35472" class="Symbol">→</a> <a id="35474" href="plfa.Lambda.html#35462" class="Bound">x</a> <a id="35476" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#799" class="Function Operator">≢</a> <a id="35478" href="plfa.Lambda.html#35464" class="Bound">y</a>
<a id="35480" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#35480" class="Bound">x</a> <a id="35482" href="plfa.Lambda.html#35453" class="Function Operator">≠</a> <a id="35484" href="plfa.Lambda.html#35484" class="Bound">y</a>  <a id="35487" class="Keyword">with</a> <a id="35492" href="plfa.Lambda.html#35480" class="Bound">x</a> <a id="35494" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="35496" href="plfa.Lambda.html#35484" class="Bound">y</a>
<a id="35498" class="Symbol">...</a>       <a id="35508" class="Symbol">|</a> <a id="35510" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="35514" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#35514" class="Bound">x≢y</a>  <a id="35519" class="Symbol">=</a>  <a id="35522" href="plfa.Lambda.html#35514" class="Bound">x≢y</a>
<a id="35526" class="Symbol">...</a>       <a id="35536" class="Symbol">|</a> <a id="35538" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="35542" class="Symbol">_</a>    <a id="35547" class="Symbol">=</a>  <a id="35550" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="35557" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#35586" class="Postulate">impossible</a>
  <a id="35570" class="Keyword">where</a> <a id="35576" class="Keyword">postulate</a> <a id="35586" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#35586" class="Postulate">impossible</a> <a id="35597" class="Symbol">:</a> <a id="35599" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
</pre>{% endraw %}Here `_≟_` is the function that tests two identifiers for equality.
We intend to apply the function only when the
two arguments are indeed unequal, and indicate that the second
case should never arise by postulating a term `impossible` of
the empty type `⊥`.  If we use C-c C-n to normalise the term

    "a" ≠ "a"

Agda will return an answer warning us that the impossible has occurred:

    ⊥-elim (.plfa.Lambda.impossible "a" "a" refl)

While postulating the impossible is a useful technique, it must be
used with care, since such postulation could allow us to provide
evidence of _any_ proposition whatsoever, regardless of its truth.


### Example type derivations {#derivation}

Type derivations correspond to trees. In informal notation, here
is a type derivation for the Church numeral two,

                            ∋s                     ∋z
                            ------------------ ⊢`  -------------- ⊢`
    ∋s                      Γ₂ ⊢ ` "s" ⦂ A ⇒ A     Γ₂ ⊢ ` "z" ⦂ A
    ------------------ ⊢`   ------------------------------------- _·_
    Γ₂ ⊢ ` "s" ⦂ A ⇒ A      Γ₂ ⊢ ` "s" · ` "z" ⦂ A
    ---------------------------------------------- _·_
    Γ₂ ⊢ ` "s" · (` "s" · ` "z") ⦂ A
    -------------------------------------------- ⊢ƛ
    Γ₁ ⊢ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂ A ⇒ A
    ------------------------------------------------------------- ⊢ƛ
    Γ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂ (A ⇒ A) ⇒ A ⇒ A

where `∋s` and `∋z` abbreviate the two derivations,

                 ---------------- Z
    "s" ≢ "z"    Γ₁ ∋ "s" ⦂ A ⇒ A
    ----------------------------- S       ------------- Z
    Γ₂ ∋ "s" ⦂ A ⇒ A                       Γ₂ ∋ "z" ⦂ A

and where `Γ₁ = Γ , "s" ⦂ A ⇒ A` and `Γ₂ = Γ , "s" ⦂ A ⇒ A , "z" ⦂ A`.
The typing derivation is valid for any `Γ` and `A`, for instance,
we might take `Γ` to be `∅` and `A` to be `` `ℕ ``.

Here is the above typing derivation formalised in Agda:
{% raw %}<pre class="Agda"><a id="Ch"></a><a id="37532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#37532" class="Function">Ch</a> <a id="37535" class="Symbol">:</a> <a id="37537" href="plfa.Lambda.html#29303" class="Datatype">Type</a> <a id="37542" class="Symbol">→</a> <a id="37544" href="plfa.Lambda.html#29303" class="Datatype">Type</a>
<a id="37549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#37532" class="Function">Ch</a> <a id="37552" href="plfa.Lambda.html#37552" class="Bound">A</a> <a id="37554" class="Symbol">=</a> <a id="37556" class="Symbol">(</a><a id="37557" href="plfa.Lambda.html#37552" class="Bound">A</a> <a id="37559" href="plfa.Lambda.html#29322" class="InductiveConstructor Operator">⇒</a> <a id="37561" href="plfa.Lambda.html#37552" class="Bound">A</a><a id="37562" class="Symbol">)</a> <a id="37564" href="plfa.Lambda.html#29322" class="InductiveConstructor Operator">⇒</a> <a id="37566" href="plfa.Lambda.html#37552" class="Bound">A</a> <a id="37568" href="plfa.Lambda.html#29322" class="InductiveConstructor Operator">⇒</a> <a id="37570" href="plfa.Lambda.html#37552" class="Bound">A</a>

<a id="⊢twoᶜ"></a><a id="37573" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#37573" class="Function">⊢twoᶜ</a> <a id="37579" class="Symbol">:</a> <a id="37581" class="Symbol">∀</a> <a id="37583" class="Symbol">{</a><a id="37584" href="plfa.Lambda.html#37584" class="Bound">Γ</a> <a id="37586" href="plfa.Lambda.html#37586" class="Bound">A</a><a id="37587" class="Symbol">}</a> <a id="37589" class="Symbol">→</a> <a id="37591" href="plfa.Lambda.html#37584" class="Bound">Γ</a> <a id="37593" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="37595" href="plfa.Lambda.html#5679" class="Function">twoᶜ</a> <a id="37600" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="37602" href="plfa.Lambda.html#37532" class="Function">Ch</a> <a id="37605" href="plfa.Lambda.html#37586" class="Bound">A</a>
<a id="37607" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#37573" class="Function">⊢twoᶜ</a> <a id="37613" class="Symbol">=</a> <a id="37615" href="plfa.Lambda.html#33483" class="InductiveConstructor">⊢ƛ</a> <a id="37618" class="Symbol">(</a><a id="37619" href="plfa.Lambda.html#33483" class="InductiveConstructor">⊢ƛ</a> <a id="37622" class="Symbol">(</a><a id="37623" href="plfa.Lambda.html#33404" class="InductiveConstructor">⊢`</a> <a id="37626" href="plfa.Lambda.html#37659" class="Function">∋s</a> <a id="37629" href="plfa.Lambda.html#33590" class="InductiveConstructor Operator">·</a> <a id="37631" class="Symbol">(</a><a id="37632" href="plfa.Lambda.html#33404" class="InductiveConstructor">⊢`</a> <a id="37635" href="plfa.Lambda.html#37659" class="Function">∋s</a> <a id="37638" href="plfa.Lambda.html#33590" class="InductiveConstructor Operator">·</a> <a id="37640" href="plfa.Lambda.html#33404" class="InductiveConstructor">⊢`</a> <a id="37643" href="plfa.Lambda.html#37682" class="Function">∋z</a><a id="37645" class="Symbol">)))</a>
  <a id="37651" class="Keyword">where</a>
  <a id="37659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#37659" class="Function">∋s</a> <a id="37662" class="Symbol">=</a> <a id="37664" href="plfa.Lambda.html#32293" class="InductiveConstructor">S</a> <a id="37666" class="Symbol">(</a><a id="37667" class="String">&quot;s&quot;</a> <a id="37671" href="plfa.Lambda.html#35453" class="Function Operator">≠</a> <a id="37673" class="String">&quot;z&quot;</a><a id="37676" class="Symbol">)</a> <a id="37678" href="plfa.Lambda.html#32227" class="InductiveConstructor">Z</a>
  <a id="37682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#37682" class="Function">∋z</a> <a id="37685" class="Symbol">=</a> <a id="37687" href="plfa.Lambda.html#32227" class="InductiveConstructor">Z</a>
</pre>{% endraw %}
Here are the typings corresponding to computing two plus two:
{% raw %}<pre class="Agda"><a id="⊢two"></a><a id="37760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#37760" class="Function">⊢two</a> <a id="37765" class="Symbol">:</a> <a id="37767" class="Symbol">∀</a> <a id="37769" class="Symbol">{</a><a id="37770" href="plfa.Lambda.html#37770" class="Bound">Γ</a><a id="37771" class="Symbol">}</a> <a id="37773" class="Symbol">→</a> <a id="37775" href="plfa.Lambda.html#37770" class="Bound">Γ</a> <a id="37777" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="37779" href="plfa.Lambda.html#4445" class="Function">two</a> <a id="37783" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="37785" href="plfa.Lambda.html#29349" class="InductiveConstructor">`ℕ</a>
<a id="37788" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#37760" class="Function">⊢two</a> <a id="37793" class="Symbol">=</a> <a id="37795" href="plfa.Lambda.html#33768" class="InductiveConstructor">⊢suc</a> <a id="37800" class="Symbol">(</a><a id="37801" href="plfa.Lambda.html#33768" class="InductiveConstructor">⊢suc</a> <a id="37806" href="plfa.Lambda.html#33699" class="InductiveConstructor">⊢zero</a><a id="37811" class="Symbol">)</a>

<a id="⊢plus"></a><a id="37814" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#37814" class="Function">⊢plus</a> <a id="37820" class="Symbol">:</a> <a id="37822" class="Symbol">∀</a> <a id="37824" class="Symbol">{</a><a id="37825" href="plfa.Lambda.html#37825" class="Bound">Γ</a><a id="37826" class="Symbol">}</a> <a id="37828" class="Symbol">→</a> <a id="37830" href="plfa.Lambda.html#37825" class="Bound">Γ</a> <a id="37832" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="37834" href="plfa.Lambda.html#4479" class="Function">plus</a> <a id="37839" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="37841" href="plfa.Lambda.html#29349" class="InductiveConstructor">`ℕ</a> <a id="37844" href="plfa.Lambda.html#29322" class="InductiveConstructor Operator">⇒</a> <a id="37846" href="plfa.Lambda.html#29349" class="InductiveConstructor">`ℕ</a> <a id="37849" href="plfa.Lambda.html#29322" class="InductiveConstructor Operator">⇒</a> <a id="37851" href="plfa.Lambda.html#29349" class="InductiveConstructor">`ℕ</a>
<a id="37854" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#37814" class="Function">⊢plus</a> <a id="37860" class="Symbol">=</a> <a id="37862" href="plfa.Lambda.html#34028" class="InductiveConstructor">⊢μ</a> <a id="37865" class="Symbol">(</a><a id="37866" href="plfa.Lambda.html#33483" class="InductiveConstructor">⊢ƛ</a> <a id="37869" class="Symbol">(</a><a id="37870" href="plfa.Lambda.html#33483" class="InductiveConstructor">⊢ƛ</a> <a id="37873" class="Symbol">(</a><a id="37874" href="plfa.Lambda.html#33856" class="InductiveConstructor">⊢case</a> <a id="37880" class="Symbol">(</a><a id="37881" href="plfa.Lambda.html#33404" class="InductiveConstructor">⊢`</a> <a id="37884" href="plfa.Lambda.html#38009" class="Function">∋m</a><a id="37886" class="Symbol">)</a> <a id="37888" class="Symbol">(</a><a id="37889" href="plfa.Lambda.html#33404" class="InductiveConstructor">⊢`</a> <a id="37892" href="plfa.Lambda.html#38035" class="Function">∋n</a><a id="37894" class="Symbol">)</a>
         <a id="37905" class="Symbol">(</a><a id="37906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33768" class="InductiveConstructor">⊢suc</a> <a id="37911" class="Symbol">(</a><a id="37912" href="plfa.Lambda.html#33404" class="InductiveConstructor">⊢`</a> <a id="37915" href="plfa.Lambda.html#37951" class="Function">∋+</a> <a id="37918" href="plfa.Lambda.html#33590" class="InductiveConstructor Operator">·</a> <a id="37920" href="plfa.Lambda.html#33404" class="InductiveConstructor">⊢`</a> <a id="37923" href="plfa.Lambda.html#38045" class="Function">∋m′</a> <a id="37927" href="plfa.Lambda.html#33590" class="InductiveConstructor Operator">·</a> <a id="37929" href="plfa.Lambda.html#33404" class="InductiveConstructor">⊢`</a> <a id="37932" href="plfa.Lambda.html#38055" class="Function">∋n′</a><a id="37935" class="Symbol">)))))</a>
  <a id="37943" class="Keyword">where</a>
  <a id="37951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#37951" class="Function">∋+</a>  <a id="37955" class="Symbol">=</a> <a id="37957" class="Symbol">(</a><a id="37958" href="plfa.Lambda.html#32293" class="InductiveConstructor">S</a> <a id="37960" class="Symbol">(</a><a id="37961" class="String">&quot;+&quot;</a> <a id="37965" href="plfa.Lambda.html#35453" class="Function Operator">≠</a> <a id="37967" class="String">&quot;m&quot;</a><a id="37970" class="Symbol">)</a> <a id="37972" class="Symbol">(</a><a id="37973" href="plfa.Lambda.html#32293" class="InductiveConstructor">S</a> <a id="37975" class="Symbol">(</a><a id="37976" class="String">&quot;+&quot;</a> <a id="37980" href="plfa.Lambda.html#35453" class="Function Operator">≠</a> <a id="37982" class="String">&quot;n&quot;</a><a id="37985" class="Symbol">)</a> <a id="37987" class="Symbol">(</a><a id="37988" href="plfa.Lambda.html#32293" class="InductiveConstructor">S</a> <a id="37990" class="Symbol">(</a><a id="37991" class="String">&quot;+&quot;</a> <a id="37995" href="plfa.Lambda.html#35453" class="Function Operator">≠</a> <a id="37997" class="String">&quot;m&quot;</a><a id="38000" class="Symbol">)</a> <a id="38002" href="plfa.Lambda.html#32227" class="InductiveConstructor">Z</a><a id="38003" class="Symbol">)))</a>
  <a id="38009" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#38009" class="Function">∋m</a>  <a id="38013" class="Symbol">=</a> <a id="38015" class="Symbol">(</a><a id="38016" href="plfa.Lambda.html#32293" class="InductiveConstructor">S</a> <a id="38018" class="Symbol">(</a><a id="38019" class="String">&quot;m&quot;</a> <a id="38023" href="plfa.Lambda.html#35453" class="Function Operator">≠</a> <a id="38025" class="String">&quot;n&quot;</a><a id="38028" class="Symbol">)</a> <a id="38030" href="plfa.Lambda.html#32227" class="InductiveConstructor">Z</a><a id="38031" class="Symbol">)</a>
  <a id="38035" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#38035" class="Function">∋n</a>  <a id="38039" class="Symbol">=</a> <a id="38041" href="plfa.Lambda.html#32227" class="InductiveConstructor">Z</a>
  <a id="38045" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#38045" class="Function">∋m′</a> <a id="38049" class="Symbol">=</a> <a id="38051" href="plfa.Lambda.html#32227" class="InductiveConstructor">Z</a>
  <a id="38055" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#38055" class="Function">∋n′</a> <a id="38059" class="Symbol">=</a> <a id="38061" class="Symbol">(</a><a id="38062" href="plfa.Lambda.html#32293" class="InductiveConstructor">S</a> <a id="38064" class="Symbol">(</a><a id="38065" class="String">&quot;n&quot;</a> <a id="38069" href="plfa.Lambda.html#35453" class="Function Operator">≠</a> <a id="38071" class="String">&quot;m&quot;</a><a id="38074" class="Symbol">)</a> <a id="38076" href="plfa.Lambda.html#32227" class="InductiveConstructor">Z</a><a id="38077" class="Symbol">)</a>

<a id="⊢2+2"></a><a id="38080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#38080" class="Function">⊢2+2</a> <a id="38085" class="Symbol">:</a> <a id="38087" href="plfa.Lambda.html#30983" class="InductiveConstructor">∅</a> <a id="38089" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="38091" href="plfa.Lambda.html#4479" class="Function">plus</a> <a id="38096" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="38098" href="plfa.Lambda.html#4445" class="Function">two</a> <a id="38102" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="38104" href="plfa.Lambda.html#4445" class="Function">two</a> <a id="38108" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="38110" href="plfa.Lambda.html#29349" class="InductiveConstructor">`ℕ</a>
<a id="38113" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#38080" class="Function">⊢2+2</a> <a id="38118" class="Symbol">=</a> <a id="38120" href="plfa.Lambda.html#37814" class="Function">⊢plus</a> <a id="38126" href="plfa.Lambda.html#33590" class="InductiveConstructor Operator">·</a> <a id="38128" href="plfa.Lambda.html#37760" class="Function">⊢two</a> <a id="38133" href="plfa.Lambda.html#33590" class="InductiveConstructor Operator">·</a> <a id="38135" href="plfa.Lambda.html#37760" class="Function">⊢two</a>
</pre>{% endraw %}In contrast to our earlier examples, here we have typed `two` and `plus`
in an arbitrary context rather than the empty context; this makes it easy
to use them inside other binding contexts as well as at the top level.
Here the two lookup judgments `∋m` and `∋m′` refer to two different
bindings of variables named `"m"`.  In contrast, the two judgments `∋n` and
`∋n′` both refer to the same binding of `"n"` but accessed in different
contexts, the first where "n" is the last binding in the context, and
the second after "m" is bound in the successor branch of the case.

And here are typings for the remainder of the Church example:
{% raw %}<pre class="Agda"><a id="⊢plusᶜ"></a><a id="38782" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#38782" class="Function">⊢plusᶜ</a> <a id="38789" class="Symbol">:</a> <a id="38791" class="Symbol">∀</a> <a id="38793" class="Symbol">{</a><a id="38794" href="plfa.Lambda.html#38794" class="Bound">Γ</a> <a id="38796" href="plfa.Lambda.html#38796" class="Bound">A</a><a id="38797" class="Symbol">}</a> <a id="38799" class="Symbol">→</a> <a id="38801" href="plfa.Lambda.html#38794" class="Bound">Γ</a>  <a id="38804" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="38806" href="plfa.Lambda.html#5740" class="Function">plusᶜ</a> <a id="38812" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="38814" href="plfa.Lambda.html#37532" class="Function">Ch</a> <a id="38817" href="plfa.Lambda.html#38796" class="Bound">A</a> <a id="38819" href="plfa.Lambda.html#29322" class="InductiveConstructor Operator">⇒</a> <a id="38821" href="plfa.Lambda.html#37532" class="Function">Ch</a> <a id="38824" href="plfa.Lambda.html#38796" class="Bound">A</a> <a id="38826" href="plfa.Lambda.html#29322" class="InductiveConstructor Operator">⇒</a> <a id="38828" href="plfa.Lambda.html#37532" class="Function">Ch</a> <a id="38831" href="plfa.Lambda.html#38796" class="Bound">A</a>
<a id="38833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#38782" class="Function">⊢plusᶜ</a> <a id="38840" class="Symbol">=</a> <a id="38842" href="plfa.Lambda.html#33483" class="InductiveConstructor">⊢ƛ</a> <a id="38845" class="Symbol">(</a><a id="38846" href="plfa.Lambda.html#33483" class="InductiveConstructor">⊢ƛ</a> <a id="38849" class="Symbol">(</a><a id="38850" href="plfa.Lambda.html#33483" class="InductiveConstructor">⊢ƛ</a> <a id="38853" class="Symbol">(</a><a id="38854" href="plfa.Lambda.html#33483" class="InductiveConstructor">⊢ƛ</a> <a id="38857" class="Symbol">(</a><a id="38858" href="plfa.Lambda.html#33404" class="InductiveConstructor">⊢`</a> <a id="38861" href="plfa.Lambda.html#38912" class="Function">∋m</a> <a id="38864" href="plfa.Lambda.html#33590" class="InductiveConstructor Operator">·</a> <a id="38866" href="plfa.Lambda.html#33404" class="InductiveConstructor">⊢`</a> <a id="38869" href="plfa.Lambda.html#39006" class="Function">∋s</a> <a id="38872" href="plfa.Lambda.html#33590" class="InductiveConstructor Operator">·</a> <a id="38874" class="Symbol">(</a><a id="38875" href="plfa.Lambda.html#33404" class="InductiveConstructor">⊢`</a> <a id="38878" href="plfa.Lambda.html#38967" class="Function">∋n</a> <a id="38881" href="plfa.Lambda.html#33590" class="InductiveConstructor Operator">·</a> <a id="38883" href="plfa.Lambda.html#33404" class="InductiveConstructor">⊢`</a> <a id="38886" href="plfa.Lambda.html#39006" class="Function">∋s</a> <a id="38889" href="plfa.Lambda.html#33590" class="InductiveConstructor Operator">·</a> <a id="38891" href="plfa.Lambda.html#33404" class="InductiveConstructor">⊢`</a> <a id="38894" href="plfa.Lambda.html#39029" class="Function">∋z</a><a id="38896" class="Symbol">)))))</a>
  <a id="38904" class="Keyword">where</a>
  <a id="38912" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#38912" class="Function">∋m</a> <a id="38915" class="Symbol">=</a> <a id="38917" href="plfa.Lambda.html#32293" class="InductiveConstructor">S</a> <a id="38919" class="Symbol">(</a><a id="38920" class="String">&quot;m&quot;</a> <a id="38924" href="plfa.Lambda.html#35453" class="Function Operator">≠</a> <a id="38926" class="String">&quot;z&quot;</a><a id="38929" class="Symbol">)</a> <a id="38931" class="Symbol">(</a><a id="38932" href="plfa.Lambda.html#32293" class="InductiveConstructor">S</a> <a id="38934" class="Symbol">(</a><a id="38935" class="String">&quot;m&quot;</a> <a id="38939" href="plfa.Lambda.html#35453" class="Function Operator">≠</a> <a id="38941" class="String">&quot;s&quot;</a><a id="38944" class="Symbol">)</a> <a id="38946" class="Symbol">(</a><a id="38947" href="plfa.Lambda.html#32293" class="InductiveConstructor">S</a> <a id="38949" class="Symbol">(</a><a id="38950" class="String">&quot;m&quot;</a> <a id="38954" href="plfa.Lambda.html#35453" class="Function Operator">≠</a> <a id="38956" class="String">&quot;n&quot;</a><a id="38959" class="Symbol">)</a> <a id="38961" href="plfa.Lambda.html#32227" class="InductiveConstructor">Z</a><a id="38962" class="Symbol">))</a>
  <a id="38967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#38967" class="Function">∋n</a> <a id="38970" class="Symbol">=</a> <a id="38972" href="plfa.Lambda.html#32293" class="InductiveConstructor">S</a> <a id="38974" class="Symbol">(</a><a id="38975" class="String">&quot;n&quot;</a> <a id="38979" href="plfa.Lambda.html#35453" class="Function Operator">≠</a> <a id="38981" class="String">&quot;z&quot;</a><a id="38984" class="Symbol">)</a> <a id="38986" class="Symbol">(</a><a id="38987" href="plfa.Lambda.html#32293" class="InductiveConstructor">S</a> <a id="38989" class="Symbol">(</a><a id="38990" class="String">&quot;n&quot;</a> <a id="38994" href="plfa.Lambda.html#35453" class="Function Operator">≠</a> <a id="38996" class="String">&quot;s&quot;</a><a id="38999" class="Symbol">)</a> <a id="39001" href="plfa.Lambda.html#32227" class="InductiveConstructor">Z</a><a id="39002" class="Symbol">)</a>
  <a id="39006" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#39006" class="Function">∋s</a> <a id="39009" class="Symbol">=</a> <a id="39011" href="plfa.Lambda.html#32293" class="InductiveConstructor">S</a> <a id="39013" class="Symbol">(</a><a id="39014" class="String">&quot;s&quot;</a> <a id="39018" href="plfa.Lambda.html#35453" class="Function Operator">≠</a> <a id="39020" class="String">&quot;z&quot;</a><a id="39023" class="Symbol">)</a> <a id="39025" href="plfa.Lambda.html#32227" class="InductiveConstructor">Z</a>
  <a id="39029" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#39029" class="Function">∋z</a> <a id="39032" class="Symbol">=</a> <a id="39034" href="plfa.Lambda.html#32227" class="InductiveConstructor">Z</a>

<a id="⊢sucᶜ"></a><a id="39037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#39037" class="Function">⊢sucᶜ</a> <a id="39043" class="Symbol">:</a> <a id="39045" class="Symbol">∀</a> <a id="39047" class="Symbol">{</a><a id="39048" href="plfa.Lambda.html#39048" class="Bound">Γ</a><a id="39049" class="Symbol">}</a> <a id="39051" class="Symbol">→</a> <a id="39053" href="plfa.Lambda.html#39048" class="Bound">Γ</a> <a id="39055" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="39057" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="39062" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="39064" href="plfa.Lambda.html#29349" class="InductiveConstructor">`ℕ</a> <a id="39067" href="plfa.Lambda.html#29322" class="InductiveConstructor Operator">⇒</a> <a id="39069" href="plfa.Lambda.html#29349" class="InductiveConstructor">`ℕ</a>
<a id="39072" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#39037" class="Function">⊢sucᶜ</a> <a id="39078" class="Symbol">=</a> <a id="39080" href="plfa.Lambda.html#33483" class="InductiveConstructor">⊢ƛ</a> <a id="39083" class="Symbol">(</a><a id="39084" href="plfa.Lambda.html#33768" class="InductiveConstructor">⊢suc</a> <a id="39089" class="Symbol">(</a><a id="39090" href="plfa.Lambda.html#33404" class="InductiveConstructor">⊢`</a> <a id="39093" href="plfa.Lambda.html#39108" class="Function">∋n</a><a id="39095" class="Symbol">))</a>
  <a id="39100" class="Keyword">where</a>
  <a id="39108" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#39108" class="Function">∋n</a> <a id="39111" class="Symbol">=</a> <a id="39113" href="plfa.Lambda.html#32227" class="InductiveConstructor">Z</a>

<a id="⊢2+2ᶜ"></a><a id="39116" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#39116" class="Function">⊢2+2ᶜ</a> <a id="39122" class="Symbol">:</a> <a id="39124" href="plfa.Lambda.html#30983" class="InductiveConstructor">∅</a> <a id="39126" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="39128" href="plfa.Lambda.html#5740" class="Function">plusᶜ</a> <a id="39134" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="39136" href="plfa.Lambda.html#5679" class="Function">twoᶜ</a> <a id="39141" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="39143" href="plfa.Lambda.html#5679" class="Function">twoᶜ</a> <a id="39148" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="39150" href="plfa.Lambda.html#5844" class="Function">sucᶜ</a> <a id="39155" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="39157" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a> <a id="39163" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="39165" href="plfa.Lambda.html#29349" class="InductiveConstructor">`ℕ</a>
<a id="39168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#39116" class="Function">⊢2+2ᶜ</a> <a id="39174" class="Symbol">=</a> <a id="39176" href="plfa.Lambda.html#38782" class="Function">⊢plusᶜ</a> <a id="39183" href="plfa.Lambda.html#33590" class="InductiveConstructor Operator">·</a> <a id="39185" href="plfa.Lambda.html#37573" class="Function">⊢twoᶜ</a> <a id="39191" href="plfa.Lambda.html#33590" class="InductiveConstructor Operator">·</a> <a id="39193" href="plfa.Lambda.html#37573" class="Function">⊢twoᶜ</a> <a id="39199" href="plfa.Lambda.html#33590" class="InductiveConstructor Operator">·</a> <a id="39201" href="plfa.Lambda.html#39037" class="Function">⊢sucᶜ</a> <a id="39207" href="plfa.Lambda.html#33590" class="InductiveConstructor Operator">·</a> <a id="39209" href="plfa.Lambda.html#33699" class="InductiveConstructor">⊢zero</a>
</pre>{% endraw %}
### Interaction with Agda

Construction of a type derivation may be done interactively.
Start with the declaration:

    ⊢sucᶜ : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
    ⊢sucᶜ = ?

Typing C-c C-l causes Agda to create a hole and tell us its expected type:

    ⊢sucᶜ = { }0
    ?0 : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ

Now we fill in the hole by typing C-c C-r. Agda observes that
the outermost term in `sucᶜ` is `ƛ`, which is typed using `⊢ƛ`. The
`⊢ƛ` rule in turn takes one argument, which Agda leaves as a hole:

    ⊢sucᶜ = ⊢ƛ { }1
    ?1 : ∅ , "n" ⦂ `ℕ ⊢ `suc ` "n" ⦂ `ℕ

We can fill in the hole by typing C-c C-r again:

    ⊢sucᶜ = ⊢ƛ (⊢suc { }2)
    ?2 : ∅ , "n" ⦂ `ℕ ⊢ ` "n" ⦂ `ℕ

And again:

    ⊢suc′ = ⊢ƛ (⊢suc (⊢` { }3))
    ?3 : ∅ , "n" ⦂ `ℕ ∋ "n" ⦂ `ℕ

A further attempt with C-c C-r yields the message:

    Don't know which constructor to introduce of Z or S

We can fill in `Z` by hand. If we type C-c C-space, Agda will confirm we are done:

    ⊢suc′ = ⊢ƛ (⊢suc (⊢` Z))

The entire process can be automated using Agsy, invoked with C-c C-a.

Chapter [Inference][plfa.Inference]
will show how to use Agda to compute type derivations directly.


### Lookup is injective

The lookup relation `Γ ∋ x ⦂ A` is injective, in that for each `Γ` and `x`
there is at most one `A` such that the judgment holds:
{% raw %}<pre class="Agda"><a id="∋-injective"></a><a id="40510" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#40510" class="Function">∋-injective</a> <a id="40522" class="Symbol">:</a> <a id="40524" class="Symbol">∀</a> <a id="40526" class="Symbol">{</a><a id="40527" href="plfa.Lambda.html#40527" class="Bound">Γ</a> <a id="40529" href="plfa.Lambda.html#40529" class="Bound">x</a> <a id="40531" href="plfa.Lambda.html#40531" class="Bound">A</a> <a id="40533" href="plfa.Lambda.html#40533" class="Bound">B</a><a id="40534" class="Symbol">}</a> <a id="40536" class="Symbol">→</a> <a id="40538" href="plfa.Lambda.html#40527" class="Bound">Γ</a> <a id="40540" href="plfa.Lambda.html#32184" class="Datatype Operator">∋</a> <a id="40542" href="plfa.Lambda.html#40529" class="Bound">x</a> <a id="40544" href="plfa.Lambda.html#32184" class="Datatype Operator">⦂</a> <a id="40546" href="plfa.Lambda.html#40531" class="Bound">A</a> <a id="40548" class="Symbol">→</a> <a id="40550" href="plfa.Lambda.html#40527" class="Bound">Γ</a> <a id="40552" href="plfa.Lambda.html#32184" class="Datatype Operator">∋</a> <a id="40554" href="plfa.Lambda.html#40529" class="Bound">x</a> <a id="40556" href="plfa.Lambda.html#32184" class="Datatype Operator">⦂</a> <a id="40558" href="plfa.Lambda.html#40533" class="Bound">B</a> <a id="40560" class="Symbol">→</a> <a id="40562" href="plfa.Lambda.html#40531" class="Bound">A</a> <a id="40564" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="40566" href="plfa.Lambda.html#40533" class="Bound">B</a>
<a id="40568" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#40510" class="Function">∋-injective</a> <a id="40580" href="plfa.Lambda.html#32227" class="InductiveConstructor">Z</a>        <a id="40589" href="plfa.Lambda.html#32227" class="InductiveConstructor">Z</a>          <a id="40600" class="Symbol">=</a>  <a id="40603" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="40608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#40510" class="Function">∋-injective</a> <a id="40620" href="plfa.Lambda.html#32227" class="InductiveConstructor">Z</a>        <a id="40629" class="Symbol">(</a><a id="40630" href="plfa.Lambda.html#32293" class="InductiveConstructor">S</a> <a id="40632" href="plfa.Lambda.html#40632" class="Bound">x≢</a> <a id="40635" class="Symbol">_)</a>   <a id="40640" class="Symbol">=</a>  <a id="40643" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="40650" class="Symbol">(</a><a id="40651" href="plfa.Lambda.html#40632" class="Bound">x≢</a> <a id="40654" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="40658" class="Symbol">)</a>
<a id="40660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#40510" class="Function">∋-injective</a> <a id="40672" class="Symbol">(</a><a id="40673" href="plfa.Lambda.html#32293" class="InductiveConstructor">S</a> <a id="40675" href="plfa.Lambda.html#40675" class="Bound">x≢</a> <a id="40678" class="Symbol">_)</a> <a id="40681" href="plfa.Lambda.html#32227" class="InductiveConstructor">Z</a>          <a id="40692" class="Symbol">=</a>  <a id="40695" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="40702" class="Symbol">(</a><a id="40703" href="plfa.Lambda.html#40675" class="Bound">x≢</a> <a id="40706" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="40710" class="Symbol">)</a>
<a id="40712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#40510" class="Function">∋-injective</a> <a id="40724" class="Symbol">(</a><a id="40725" href="plfa.Lambda.html#32293" class="InductiveConstructor">S</a> <a id="40727" class="Symbol">_</a> <a id="40729" href="plfa.Lambda.html#40729" class="Bound">∋x</a><a id="40731" class="Symbol">)</a> <a id="40733" class="Symbol">(</a><a id="40734" href="plfa.Lambda.html#32293" class="InductiveConstructor">S</a> <a id="40736" class="Symbol">_</a> <a id="40738" href="plfa.Lambda.html#40738" class="Bound">∋x′</a><a id="40741" class="Symbol">)</a>  <a id="40744" class="Symbol">=</a>  <a id="40747" href="plfa.Lambda.html#40510" class="Function">∋-injective</a> <a id="40759" href="plfa.Lambda.html#40729" class="Bound">∋x</a> <a id="40762" href="plfa.Lambda.html#40738" class="Bound">∋x′</a>
</pre>{% endraw %}
The typing relation `Γ ⊢ M ⦂ A` is not injective. For example, in any `Γ`
the term `ƛ "x" ⇒ "x"` has type `A ⇒ A` for any type `A`.

### Non-examples

We can also show that terms are _not_ typeable.  For example, here is
a formal proof that it is not possible to type the term
`` `zero · `suc `zero ``.  It cannot be typed, because doing so
requires that the first term in the application is both a natural and
a function:

{% raw %}<pre class="Agda"><a id="nope₁"></a><a id="41199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#41199" class="Function">nope₁</a> <a id="41205" class="Symbol">:</a> <a id="41207" class="Symbol">∀</a> <a id="41209" class="Symbol">{</a><a id="41210" href="plfa.Lambda.html#41210" class="Bound">A</a><a id="41211" class="Symbol">}</a> <a id="41213" class="Symbol">→</a> <a id="41215" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="41217" class="Symbol">(</a><a id="41218" href="plfa.Lambda.html#30983" class="InductiveConstructor">∅</a> <a id="41220" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="41222" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a> <a id="41228" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="41230" href="plfa.Lambda.html#3903" class="InductiveConstructor Operator">`suc</a> <a id="41235" href="plfa.Lambda.html#3869" class="InductiveConstructor">`zero</a> <a id="41241" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="41243" href="plfa.Lambda.html#41210" class="Bound">A</a><a id="41244" class="Symbol">)</a>
<a id="41246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#41199" class="Function">nope₁</a> <a id="41252" class="Symbol">(()</a> <a id="41256" href="plfa.Lambda.html#33590" class="InductiveConstructor Operator">·</a> <a id="41258" class="Symbol">_)</a>
</pre>{% endraw %}
As a second example, here is a formal proof that it is not possible to
type `` ƛ "x" ⇒ ` "x" · ` "x" ``. It cannot be typed, because
doing so requires types `A` and `B` such that `A ⇒ B ≡ A`:

{% raw %}<pre class="Agda"><a id="nope₂"></a><a id="41463" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#41463" class="Function">nope₂</a> <a id="41469" class="Symbol">:</a> <a id="41471" class="Symbol">∀</a> <a id="41473" class="Symbol">{</a><a id="41474" href="plfa.Lambda.html#41474" class="Bound">A</a><a id="41475" class="Symbol">}</a> <a id="41477" class="Symbol">→</a> <a id="41479" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="41481" class="Symbol">(</a><a id="41482" href="plfa.Lambda.html#30983" class="InductiveConstructor">∅</a> <a id="41484" href="plfa.Lambda.html#33348" class="Datatype Operator">⊢</a> <a id="41486" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">ƛ</a> <a id="41488" class="String">&quot;x&quot;</a> <a id="41492" href="plfa.Lambda.html#3775" class="InductiveConstructor Operator">⇒</a> <a id="41494" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="41496" class="String">&quot;x&quot;</a> <a id="41500" href="plfa.Lambda.html#3821" class="InductiveConstructor Operator">·</a> <a id="41502" href="plfa.Lambda.html#3736" class="InductiveConstructor Operator">`</a> <a id="41504" class="String">&quot;x&quot;</a> <a id="41508" href="plfa.Lambda.html#33348" class="Datatype Operator">⦂</a> <a id="41510" href="plfa.Lambda.html#41474" class="Bound">A</a><a id="41511" class="Symbol">)</a>
<a id="41513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#41463" class="Function">nope₂</a> <a id="41519" class="Symbol">(</a><a id="41520" href="plfa.Lambda.html#33483" class="InductiveConstructor">⊢ƛ</a> <a id="41523" class="Symbol">(</a><a id="41524" href="plfa.Lambda.html#33404" class="InductiveConstructor">⊢`</a> <a id="41527" href="plfa.Lambda.html#41527" class="Bound">∋x</a> <a id="41530" href="plfa.Lambda.html#33590" class="InductiveConstructor Operator">·</a> <a id="41532" href="plfa.Lambda.html#33404" class="InductiveConstructor">⊢`</a> <a id="41535" href="plfa.Lambda.html#41535" class="Bound">∋x′</a><a id="41538" class="Symbol">))</a>  <a id="41542" class="Symbol">=</a>  <a id="41545" href="plfa.Lambda.html#41590" class="Function">contradiction</a> <a id="41559" class="Symbol">(</a><a id="41560" href="plfa.Lambda.html#40510" class="Function">∋-injective</a> <a id="41572" href="plfa.Lambda.html#41527" class="Bound">∋x</a> <a id="41575" href="plfa.Lambda.html#41535" class="Bound">∋x′</a><a id="41578" class="Symbol">)</a>
  <a id="41582" class="Keyword">where</a>
  <a id="41590" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#41590" class="Function">contradiction</a> <a id="41604" class="Symbol">:</a> <a id="41606" class="Symbol">∀</a> <a id="41608" class="Symbol">{</a><a id="41609" href="plfa.Lambda.html#41609" class="Bound">A</a> <a id="41611" href="plfa.Lambda.html#41611" class="Bound">B</a><a id="41612" class="Symbol">}</a> <a id="41614" class="Symbol">→</a> <a id="41616" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="41618" class="Symbol">(</a><a id="41619" href="plfa.Lambda.html#41609" class="Bound">A</a> <a id="41621" href="plfa.Lambda.html#29322" class="InductiveConstructor Operator">⇒</a> <a id="41623" href="plfa.Lambda.html#41611" class="Bound">B</a> <a id="41625" href="https://agda.github.io/agda-stdlib/v1.1/Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="41627" href="plfa.Lambda.html#41609" class="Bound">A</a><a id="41628" class="Symbol">)</a>
  <a id="41632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#41590" class="Function">contradiction</a> <a id="41646" class="Symbol">()</a>
</pre>{% endraw %}

#### Quiz

For each of the following, give a type `A` for which it is derivable,
or explain why there is no such `A`.

1. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "y" · ` "x" ⦂ A ``
2. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "x" · ` "y" ⦂ A ``
3. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "x" ⇒ ` "y" · ` "x" ⦂ A ``

For each of the following, give types `A`, `B`, and `C` for which it is derivable,
or explain why there are no such types.

1. `` ∅ , "x" ⦂ A ⊢ ` "x" · ` "x" ⦂ B ``
2. `` ∅ , "x" ⦂ A , "y" ⦂ B ⊢ ƛ "z" ⇒ ` "x" · (` "y" · ` "z") ⦂ C ``


#### Exercise `mul-type` (recommended)

Using the term `mul` you defined earlier, write out the derivation
showing that it is well-typed.

{% raw %}<pre class="Agda"><a id="42325" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `mulᶜ-type`

Using the term `mulᶜ` you defined earlier, write out the derivation
showing that it is well-typed.

{% raw %}<pre class="Agda"><a id="42485" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Unicode

This chapter uses the following unicode:

    ⇒  U+21D2  RIGHTWARDS DOUBLE ARROW (\=>)
    ƛ  U+019B  LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
    ·  U+00B7  MIDDLE DOT (\cdot)
    —  U+2014  EM DASH (\em)
    ↠  U+21A0  RIGHTWARDS TWO HEADED ARROW (\rr-)
    ξ  U+03BE  GREEK SMALL LETTER XI (\Gx or \xi)
    β  U+03B2  GREEK SMALL LETTER BETA (\Gb or \beta)
    Γ  U+0393  GREEK CAPITAL LETTER GAMMA (\GG or \Gamma)
    ≠  U+2260  NOT EQUAL TO (\=n or \ne)
    ∋  U+220B  CONTAINS AS MEMBER (\ni)
    ∅  U+2205  EMPTY SET (\0)
    ⊢  U+22A2  RIGHT TACK (\vdash or \|-)
    ⦂  U+2982  Z NOTATION TYPE COLON (\:)
    😇  U+1F607  SMILING FACE WITH HALO
    😈  U+1F608  SMILING FACE WITH HORNS

We compose reduction `—→` from an em dash `—` and an arrow `→`.
Similarly for reflexive and transitive closure `—↠`.
