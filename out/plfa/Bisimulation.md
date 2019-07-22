---
src: ./src/plfa/Bisimulation.lagda.md
title     : "Bisimulation: Relating reduction systems"
layout    : page
prev      : /More/
permalink : /Bisimulation/
next      : /Inference/
---

{% raw %}<pre class="Agda"><a id="156" class="Keyword">module</a> <a id="163" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}" class="Module">plfa.Bisimulation</a> <a id="181" class="Keyword">where</a>
</pre>{% endraw %}
Some constructs can be defined in terms of other constructs.  In the
previous chapter, we saw how _let_ terms can be rewritten as an
application of an abstraction, and how two alternative formulations of
products — one with projections and one with case — can be formulated
in terms of each other.  In this chapter, we look at how to formalise
such claims.

Given two different systems, with different terms and reduction rules,
we define what it means to claim that one _simulates_ the other.
Let's call our two systems _source_ and _target_.  Let `M`, `N` range
over terms of the source, and `M†`, `N†` range over terms of the
target.  We define a relation

    M ~ M†

between corresponding terms of the two systems. We have a
_simulation_ of the source by the target if every reduction
in the source has a corresponding reduction sequence
in the target:

_Simulation_: For every `M`, `M†`, and `N`:
If `M ~ M†` and `M —→ N`
then `M† —↠ N†` and `N ~ N†`
for some `N†`.

Or, in a diagram:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —↠ --- N†

Sometimes we will have a stronger condition, where each reduction in the source
corresponds to a reduction (rather than a reduction sequence)
in the target:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —→ --- N†

This stronger condition is known as _lock-step_ or _on the nose_ simulation.

We are particularly interested in the situation where there is also
a simulation from the target to the source: every reduction in the
target has a corresponding reduction sequence in the source.  This
situation is called a _bisimulation_.

Simulation is established by case analysis over all possible
reductions and all possible terms to which they are related.  For each
reduction step in the source we must show a corresponding reduction
sequence in the target.

For instance, the source might be lambda calculus with _let_
added, and the target the same system with `let` translated out.
The key rule defining our relation will be:

    M ~ M†
    N ~ N†
    --------------------------------
    let x = M in N ~ (ƛ x ⇒ N†) · M†

All the other rules are congruences: variables relate to
themselves, and abstractions and applications relate if their
components relate:

    -----
    x ~ x

    N ~ N†
    ------------------
    ƛ x ⇒ N ~ ƛ x ⇒ N†

    L ~ L†
    M ~ M†
    ---------------
    L · M ~ L† · M†

Covering the other constructs of our language — naturals,
fixpoints, products, and so on — would add little save length.

In this case, our relation can be specified by a function
from source to target:

    (x) †               =  x
    (ƛ x ⇒ N) †         =  ƛ x ⇒ (N †)
    (L · M) †           =  (L †) · (M †)
    (let x = M in N) †  =  (ƛ x ⇒ (N †)) · (M †)

And we have

    M † ≡ N
    -------
    M ~ N

and conversely. But in general we may have a relation without any
corresponding function.

This chapter formalises establishing that `~` as defined
above is a simulation from source to target.  We leave
establishing it in the reverse direction as an exercise.
Another exercise is to show the alternative formulations
of products in
Chapter [More][plfa.More]
are in bisimulation.


## Imports

We import our source language from
Chapter [More][plfa.More]:
{% raw %}<pre class="Agda"><a id="3589" class="Keyword">open</a> <a id="3594" class="Keyword">import</a> <a id="3601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}" class="Module">plfa.More</a>
</pre>{% endraw %}

## Simulation

The simulation is a straightforward formalisation of the rules
in the introduction:
{% raw %}<pre class="Agda"><a id="3720" class="Keyword">infix</a>  <a id="3727" class="Number">4</a> <a id="3729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3766" class="Datatype Operator">_~_</a>
<a id="3733" class="Keyword">infix</a>  <a id="3740" class="Number">5</a> <a id="3742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3873" class="InductiveConstructor Operator">~ƛ_</a>
<a id="3746" class="Keyword">infix</a>  <a id="3753" class="Number">7</a> <a id="3755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3958" class="InductiveConstructor Operator">_~·_</a>

<a id="3761" class="Keyword">data</a> <a id="_~_"></a><a id="3766" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3766" class="Datatype Operator">_~_</a> <a id="3770" class="Symbol">:</a> <a id="3772" class="Symbol">∀</a> <a id="3774" class="Symbol">{</a><a id="3775" href="plfa.Bisimulation.html#3775" class="Bound">Γ</a> <a id="3777" href="plfa.Bisimulation.html#3777" class="Bound">A</a><a id="3778" class="Symbol">}</a> <a id="3780" class="Symbol">→</a> <a id="3782" class="Symbol">(</a><a id="3783" href="plfa.Bisimulation.html#3775" class="Bound">Γ</a> <a id="3785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14917" class="Datatype Operator">⊢</a> <a id="3787" href="plfa.Bisimulation.html#3777" class="Bound">A</a><a id="3788" class="Symbol">)</a> <a id="3790" class="Symbol">→</a> <a id="3792" class="Symbol">(</a><a id="3793" href="plfa.Bisimulation.html#3775" class="Bound">Γ</a> <a id="3795" href="plfa.More.html#14917" class="Datatype Operator">⊢</a> <a id="3797" href="plfa.Bisimulation.html#3777" class="Bound">A</a><a id="3798" class="Symbol">)</a> <a id="3800" class="Symbol">→</a> <a id="3802" class="PrimitiveType">Set</a> <a id="3806" class="Keyword">where</a>

  <a id="_~_.~`"></a><a id="3815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3815" class="InductiveConstructor">~`</a> <a id="3818" class="Symbol">:</a> <a id="3820" class="Symbol">∀</a> <a id="3822" class="Symbol">{</a><a id="3823" href="plfa.Bisimulation.html#3823" class="Bound">Γ</a> <a id="3825" href="plfa.Bisimulation.html#3825" class="Bound">A</a><a id="3826" class="Symbol">}</a> <a id="3828" class="Symbol">{</a><a id="3829" href="plfa.Bisimulation.html#3829" class="Bound">x</a> <a id="3831" class="Symbol">:</a> <a id="3833" href="plfa.Bisimulation.html#3823" class="Bound">Γ</a> <a id="3835" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14726" class="Datatype Operator">∋</a> <a id="3837" href="plfa.Bisimulation.html#3825" class="Bound">A</a><a id="3838" class="Symbol">}</a>
     <a id="3845" class="Comment">---------</a>
   <a id="3858" class="Symbol">→</a> <a id="3860" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14969" class="InductiveConstructor Operator">`</a> <a id="3862" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3829" class="Bound">x</a> <a id="3864" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="3866" href="plfa.More.html#14969" class="InductiveConstructor Operator">`</a> <a id="3868" href="plfa.Bisimulation.html#3829" class="Bound">x</a>

  <a id="_~_.~ƛ_"></a><a id="3873" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3873" class="InductiveConstructor Operator">~ƛ_</a> <a id="3877" class="Symbol">:</a> <a id="3879" class="Symbol">∀</a> <a id="3881" class="Symbol">{</a><a id="3882" href="plfa.Bisimulation.html#3882" class="Bound">Γ</a> <a id="3884" href="plfa.Bisimulation.html#3884" class="Bound">A</a> <a id="3886" href="plfa.Bisimulation.html#3886" class="Bound">B</a><a id="3887" class="Symbol">}</a> <a id="3889" class="Symbol">{</a><a id="3890" href="plfa.Bisimulation.html#3890" class="Bound">N</a> <a id="3892" href="plfa.Bisimulation.html#3892" class="Bound">N†</a> <a id="3895" class="Symbol">:</a> <a id="3897" href="plfa.Bisimulation.html#3882" class="Bound">Γ</a> <a id="3899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14642" class="InductiveConstructor Operator">,</a> <a id="3901" href="plfa.Bisimulation.html#3884" class="Bound">A</a> <a id="3903" href="plfa.More.html#14917" class="Datatype Operator">⊢</a> <a id="3905" href="plfa.Bisimulation.html#3886" class="Bound">B</a><a id="3906" class="Symbol">}</a>
    <a id="3912" class="Symbol">→</a> <a id="3914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3890" class="Bound">N</a> <a id="3916" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="3918" href="plfa.Bisimulation.html#3892" class="Bound">N†</a>
      <a id="3927" class="Comment">----------</a>
    <a id="3942" class="Symbol">→</a> <a id="3944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#15037" class="InductiveConstructor Operator">ƛ</a> <a id="3946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3890" class="Bound">N</a> <a id="3948" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="3950" href="plfa.More.html#15037" class="InductiveConstructor Operator">ƛ</a> <a id="3952" href="plfa.Bisimulation.html#3892" class="Bound">N†</a>

  <a id="_~_._~·_"></a><a id="3958" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3958" class="InductiveConstructor Operator">_~·_</a> <a id="3963" class="Symbol">:</a> <a id="3965" class="Symbol">∀</a> <a id="3967" class="Symbol">{</a><a id="3968" href="plfa.Bisimulation.html#3968" class="Bound">Γ</a> <a id="3970" href="plfa.Bisimulation.html#3970" class="Bound">A</a> <a id="3972" href="plfa.Bisimulation.html#3972" class="Bound">B</a><a id="3973" class="Symbol">}</a> <a id="3975" class="Symbol">{</a><a id="3976" href="plfa.Bisimulation.html#3976" class="Bound">L</a> <a id="3978" href="plfa.Bisimulation.html#3978" class="Bound">L†</a> <a id="3981" class="Symbol">:</a> <a id="3983" href="plfa.Bisimulation.html#3968" class="Bound">Γ</a> <a id="3985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14917" class="Datatype Operator">⊢</a> <a id="3987" href="plfa.Bisimulation.html#3970" class="Bound">A</a> <a id="3989" href="plfa.More.html#14505" class="InductiveConstructor Operator">⇒</a> <a id="3991" href="plfa.Bisimulation.html#3972" class="Bound">B</a><a id="3992" class="Symbol">}</a> <a id="3994" class="Symbol">{</a><a id="3995" href="plfa.Bisimulation.html#3995" class="Bound">M</a> <a id="3997" href="plfa.Bisimulation.html#3997" class="Bound">M†</a> <a id="4000" class="Symbol">:</a> <a id="4002" href="plfa.Bisimulation.html#3968" class="Bound">Γ</a> <a id="4004" href="plfa.More.html#14917" class="Datatype Operator">⊢</a> <a id="4006" href="plfa.Bisimulation.html#3970" class="Bound">A</a><a id="4007" class="Symbol">}</a>
    <a id="4013" class="Symbol">→</a> <a id="4015" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3976" class="Bound">L</a> <a id="4017" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="4019" href="plfa.Bisimulation.html#3978" class="Bound">L†</a>
    <a id="4026" class="Symbol">→</a> <a id="4028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3995" class="Bound">M</a> <a id="4030" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="4032" href="plfa.Bisimulation.html#3997" class="Bound">M†</a>
      <a id="4041" class="Comment">---------------</a>
    <a id="4061" class="Symbol">→</a> <a id="4063" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#3976" class="Bound">L</a> <a id="4065" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#15105" class="InductiveConstructor Operator">·</a> <a id="4067" href="plfa.Bisimulation.html#3995" class="Bound">M</a> <a id="4069" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="4071" href="plfa.Bisimulation.html#3978" class="Bound">L†</a> <a id="4074" href="plfa.More.html#15105" class="InductiveConstructor Operator">·</a> <a id="4076" href="plfa.Bisimulation.html#3997" class="Bound">M†</a>

  <a id="_~_.~let"></a><a id="4082" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4082" class="InductiveConstructor">~let</a> <a id="4087" class="Symbol">:</a> <a id="4089" class="Symbol">∀</a> <a id="4091" class="Symbol">{</a><a id="4092" href="plfa.Bisimulation.html#4092" class="Bound">Γ</a> <a id="4094" href="plfa.Bisimulation.html#4094" class="Bound">A</a> <a id="4096" href="plfa.Bisimulation.html#4096" class="Bound">B</a><a id="4097" class="Symbol">}</a> <a id="4099" class="Symbol">{</a><a id="4100" href="plfa.Bisimulation.html#4100" class="Bound">M</a> <a id="4102" href="plfa.Bisimulation.html#4102" class="Bound">M†</a> <a id="4105" class="Symbol">:</a> <a id="4107" href="plfa.Bisimulation.html#4092" class="Bound">Γ</a> <a id="4109" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14917" class="Datatype Operator">⊢</a> <a id="4111" href="plfa.Bisimulation.html#4094" class="Bound">A</a><a id="4112" class="Symbol">}</a> <a id="4114" class="Symbol">{</a><a id="4115" href="plfa.Bisimulation.html#4115" class="Bound">N</a> <a id="4117" href="plfa.Bisimulation.html#4117" class="Bound">N†</a> <a id="4120" class="Symbol">:</a> <a id="4122" href="plfa.Bisimulation.html#4092" class="Bound">Γ</a> <a id="4124" href="plfa.More.html#14642" class="InductiveConstructor Operator">,</a> <a id="4126" href="plfa.Bisimulation.html#4094" class="Bound">A</a> <a id="4128" href="plfa.More.html#14917" class="Datatype Operator">⊢</a> <a id="4130" href="plfa.Bisimulation.html#4096" class="Bound">B</a><a id="4131" class="Symbol">}</a>
    <a id="4137" class="Symbol">→</a> <a id="4139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4100" class="Bound">M</a> <a id="4141" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="4143" href="plfa.Bisimulation.html#4102" class="Bound">M†</a>
    <a id="4150" class="Symbol">→</a> <a id="4152" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4115" class="Bound">N</a> <a id="4154" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="4156" href="plfa.Bisimulation.html#4117" class="Bound">N†</a>
      <a id="4165" class="Comment">----------------------</a>
    <a id="4192" class="Symbol">→</a> <a id="4194" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#15611" class="InductiveConstructor">`let</a> <a id="4199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4100" class="Bound">M</a> <a id="4201" href="plfa.Bisimulation.html#4115" class="Bound">N</a> <a id="4203" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="4205" class="Symbol">(</a><a id="4206" href="plfa.More.html#15037" class="InductiveConstructor Operator">ƛ</a> <a id="4208" href="plfa.Bisimulation.html#4117" class="Bound">N†</a><a id="4210" class="Symbol">)</a> <a id="4212" href="plfa.More.html#15105" class="InductiveConstructor Operator">·</a> <a id="4214" href="plfa.Bisimulation.html#4102" class="Bound">M†</a>
</pre>{% endraw %}The language in Chapter [More][plfa.More] has more constructs, which we could easily add.
However, leaving the simulation small let's us focus on the essence.
It's a handy technical trick that we can have a large source language,
but only bother to include in the simulation the terms of interest.

#### Exercise `_†`

Formalise the translation from source to target given in the introduction.
Show that `M † ≡ N` implies `M ~ N`, and conversely.

{% raw %}<pre class="Agda"><a id="4673" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Simulation commutes with values

We need a number of technical results. The first is that simulation
commutes with values.  That is, if `M ~ M†` and `M` is a value then
`M†` is also a value:
{% raw %}<pre class="Agda"><a id="~val"></a><a id="4900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4900" class="Function">~val</a> <a id="4905" class="Symbol">:</a> <a id="4907" class="Symbol">∀</a> <a id="4909" class="Symbol">{</a><a id="4910" href="plfa.Bisimulation.html#4910" class="Bound">Γ</a> <a id="4912" href="plfa.Bisimulation.html#4912" class="Bound">A</a><a id="4913" class="Symbol">}</a> <a id="4915" class="Symbol">{</a><a id="4916" href="plfa.Bisimulation.html#4916" class="Bound">M</a> <a id="4918" href="plfa.Bisimulation.html#4918" class="Bound">M†</a> <a id="4921" class="Symbol">:</a> <a id="4923" href="plfa.Bisimulation.html#4910" class="Bound">Γ</a> <a id="4925" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14917" class="Datatype Operator">⊢</a> <a id="4927" href="plfa.Bisimulation.html#4912" class="Bound">A</a><a id="4928" class="Symbol">}</a>
  <a id="4932" class="Symbol">→</a> <a id="4934" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4916" class="Bound">M</a> <a id="4936" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="4938" href="plfa.Bisimulation.html#4918" class="Bound">M†</a>
  <a id="4943" class="Symbol">→</a> <a id="4945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#18859" class="Datatype">Value</a> <a id="4951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4916" class="Bound">M</a>
    <a id="4957" class="Comment">--------</a>
  <a id="4968" class="Symbol">→</a> <a id="4970" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#18859" class="Datatype">Value</a> <a id="4976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4918" class="Bound">M†</a>
<a id="4979" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4900" class="Function">~val</a> <a id="4984" href="plfa.Bisimulation.html#3815" class="InductiveConstructor">~`</a>           <a id="4997" class="Symbol">()</a>
<a id="5000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4900" class="Function">~val</a> <a id="5005" class="Symbol">(</a><a id="5006" href="plfa.Bisimulation.html#3873" class="InductiveConstructor Operator">~ƛ</a> <a id="5009" href="plfa.Bisimulation.html#5009" class="Bound">~N</a><a id="5011" class="Symbol">)</a>      <a id="5018" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#18914" class="InductiveConstructor">V-ƛ</a>  <a id="5023" class="Symbol">=</a>  <a id="5026" href="plfa.More.html#18914" class="InductiveConstructor">V-ƛ</a>
<a id="5030" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4900" class="Function">~val</a> <a id="5035" class="Symbol">(</a><a id="5036" href="plfa.Bisimulation.html#5036" class="Bound">~L</a> <a id="5039" href="plfa.Bisimulation.html#3958" class="InductiveConstructor Operator">~·</a> <a id="5042" href="plfa.Bisimulation.html#5042" class="Bound">~M</a><a id="5044" class="Symbol">)</a>   <a id="5048" class="Symbol">()</a>
<a id="5051" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#4900" class="Function">~val</a> <a id="5056" class="Symbol">(</a><a id="5057" href="plfa.Bisimulation.html#4082" class="InductiveConstructor">~let</a> <a id="5062" href="plfa.Bisimulation.html#5062" class="Bound">~M</a> <a id="5065" href="plfa.Bisimulation.html#5065" class="Bound">~N</a><a id="5067" class="Symbol">)</a> <a id="5069" class="Symbol">()</a>
</pre>{% endraw %}It is a straightforward case analysis, where here the only value
of interest is a lambda abstraction.

#### Exercise `~val⁻¹`

Show that this also holds in the reverse direction: if `M ~ M†`
and `Value M†` then `Value M`.

{% raw %}<pre class="Agda"><a id="5303" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Simulation commutes with renaming

The next technical result is that simulation commutes with renaming.
That is, if `ρ` maps any judgment `Γ ∋ A` to a judgment `Δ ∋ A`,
and if `M ~ M†` then `rename ρ M ~ rename ρ M†`:

{% raw %}<pre class="Agda"><a id="~rename"></a><a id="5558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#5558" class="Function">~rename</a> <a id="5566" class="Symbol">:</a> <a id="5568" class="Symbol">∀</a> <a id="5570" class="Symbol">{</a><a id="5571" href="plfa.Bisimulation.html#5571" class="Bound">Γ</a> <a id="5573" href="plfa.Bisimulation.html#5573" class="Bound">Δ</a><a id="5574" class="Symbol">}</a>
  <a id="5578" class="Symbol">→</a> <a id="5580" class="Symbol">(</a><a id="5581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#5581" class="Bound">ρ</a> <a id="5583" class="Symbol">:</a> <a id="5585" class="Symbol">∀</a> <a id="5587" class="Symbol">{</a><a id="5588" href="plfa.Bisimulation.html#5588" class="Bound">A</a><a id="5589" class="Symbol">}</a> <a id="5591" class="Symbol">→</a> <a id="5593" href="plfa.Bisimulation.html#5571" class="Bound">Γ</a> <a id="5595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14726" class="Datatype Operator">∋</a> <a id="5597" href="plfa.Bisimulation.html#5588" class="Bound">A</a> <a id="5599" class="Symbol">→</a> <a id="5601" href="plfa.Bisimulation.html#5573" class="Bound">Δ</a> <a id="5603" href="plfa.More.html#14726" class="Datatype Operator">∋</a> <a id="5605" href="plfa.Bisimulation.html#5588" class="Bound">A</a><a id="5606" class="Symbol">)</a>
    <a id="5612" class="Comment">----------------------------------------------------------</a>
  <a id="5673" class="Symbol">→</a> <a id="5675" class="Symbol">(∀</a> <a id="5678" class="Symbol">{</a><a id="5679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#5679" class="Bound">A</a><a id="5680" class="Symbol">}</a> <a id="5682" class="Symbol">{</a><a id="5683" href="plfa.Bisimulation.html#5683" class="Bound">M</a> <a id="5685" href="plfa.Bisimulation.html#5685" class="Bound">M†</a> <a id="5688" class="Symbol">:</a> <a id="5690" href="plfa.Bisimulation.html#5571" class="Bound">Γ</a> <a id="5692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14917" class="Datatype Operator">⊢</a> <a id="5694" href="plfa.Bisimulation.html#5679" class="Bound">A</a><a id="5695" class="Symbol">}</a> <a id="5697" class="Symbol">→</a> <a id="5699" href="plfa.Bisimulation.html#5683" class="Bound">M</a> <a id="5701" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="5703" href="plfa.Bisimulation.html#5685" class="Bound">M†</a> <a id="5706" class="Symbol">→</a> <a id="5708" href="plfa.More.html#16656" class="Function">rename</a> <a id="5715" href="plfa.Bisimulation.html#5581" class="Bound">ρ</a> <a id="5717" href="plfa.Bisimulation.html#5683" class="Bound">M</a> <a id="5719" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="5721" href="plfa.More.html#16656" class="Function">rename</a> <a id="5728" href="plfa.Bisimulation.html#5581" class="Bound">ρ</a> <a id="5730" href="plfa.Bisimulation.html#5685" class="Bound">M†</a><a id="5732" class="Symbol">)</a>
<a id="5734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#5558" class="Function">~rename</a> <a id="5742" href="plfa.Bisimulation.html#5742" class="Bound">ρ</a> <a id="5744" class="Symbol">(</a><a id="5745" href="plfa.Bisimulation.html#3815" class="InductiveConstructor">~`</a><a id="5747" class="Symbol">)</a>          <a id="5758" class="Symbol">=</a>  <a id="5761" href="plfa.Bisimulation.html#3815" class="InductiveConstructor">~`</a>
<a id="5764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#5558" class="Function">~rename</a> <a id="5772" href="plfa.Bisimulation.html#5772" class="Bound">ρ</a> <a id="5774" class="Symbol">(</a><a id="5775" href="plfa.Bisimulation.html#3873" class="InductiveConstructor Operator">~ƛ</a> <a id="5778" href="plfa.Bisimulation.html#5778" class="Bound">~N</a><a id="5780" class="Symbol">)</a>       <a id="5788" class="Symbol">=</a>  <a id="5791" href="plfa.Bisimulation.html#3873" class="InductiveConstructor Operator">~ƛ</a> <a id="5794" class="Symbol">(</a><a id="5795" href="plfa.Bisimulation.html#5558" class="Function">~rename</a> <a id="5803" class="Symbol">(</a><a id="5804" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#16537" class="Function">ext</a> <a id="5808" href="plfa.Bisimulation.html#5772" class="Bound">ρ</a><a id="5809" class="Symbol">)</a> <a id="5811" href="plfa.Bisimulation.html#5778" class="Bound">~N</a><a id="5813" class="Symbol">)</a>
<a id="5815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#5558" class="Function">~rename</a> <a id="5823" href="plfa.Bisimulation.html#5823" class="Bound">ρ</a> <a id="5825" class="Symbol">(</a><a id="5826" href="plfa.Bisimulation.html#5826" class="Bound">~L</a> <a id="5829" href="plfa.Bisimulation.html#3958" class="InductiveConstructor Operator">~·</a> <a id="5832" href="plfa.Bisimulation.html#5832" class="Bound">~M</a><a id="5834" class="Symbol">)</a>    <a id="5839" class="Symbol">=</a>  <a id="5842" class="Symbol">(</a><a id="5843" href="plfa.Bisimulation.html#5558" class="Function">~rename</a> <a id="5851" href="plfa.Bisimulation.html#5823" class="Bound">ρ</a> <a id="5853" href="plfa.Bisimulation.html#5826" class="Bound">~L</a><a id="5855" class="Symbol">)</a> <a id="5857" href="plfa.Bisimulation.html#3958" class="InductiveConstructor Operator">~·</a> <a id="5860" class="Symbol">(</a><a id="5861" href="plfa.Bisimulation.html#5558" class="Function">~rename</a> <a id="5869" href="plfa.Bisimulation.html#5823" class="Bound">ρ</a> <a id="5871" href="plfa.Bisimulation.html#5832" class="Bound">~M</a><a id="5873" class="Symbol">)</a>
<a id="5875" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#5558" class="Function">~rename</a> <a id="5883" href="plfa.Bisimulation.html#5883" class="Bound">ρ</a> <a id="5885" class="Symbol">(</a><a id="5886" href="plfa.Bisimulation.html#4082" class="InductiveConstructor">~let</a> <a id="5891" href="plfa.Bisimulation.html#5891" class="Bound">~M</a> <a id="5894" href="plfa.Bisimulation.html#5894" class="Bound">~N</a><a id="5896" class="Symbol">)</a>  <a id="5899" class="Symbol">=</a>  <a id="5902" href="plfa.Bisimulation.html#4082" class="InductiveConstructor">~let</a> <a id="5907" class="Symbol">(</a><a id="5908" href="plfa.Bisimulation.html#5558" class="Function">~rename</a> <a id="5916" href="plfa.Bisimulation.html#5883" class="Bound">ρ</a> <a id="5918" href="plfa.Bisimulation.html#5891" class="Bound">~M</a><a id="5920" class="Symbol">)</a> <a id="5922" class="Symbol">(</a><a id="5923" href="plfa.Bisimulation.html#5558" class="Function">~rename</a> <a id="5931" class="Symbol">(</a><a id="5932" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#16537" class="Function">ext</a> <a id="5936" href="plfa.Bisimulation.html#5883" class="Bound">ρ</a><a id="5937" class="Symbol">)</a> <a id="5939" href="plfa.Bisimulation.html#5894" class="Bound">~N</a><a id="5941" class="Symbol">)</a>
</pre>{% endraw %}The structure of the proof is similar to the structure of renaming itself:
reconstruct each term with recursive invocation, extending the environment
where appropriate (in this case, only for the body of an abstraction).


## Simulation commutes with substitution

The third technical result is that simulation commutes with substitution.
It is more complex than substitution, because where we had one renaming map
`ρ` here we need two substitution maps, `σ` and `σ†`.

The proof first requires we establish an analogue of extension.
If `σ` and `σ†` both map any judgment `Γ ∋ A` to a judgment `Δ ⊢ A`,
such that for every `x` in `Γ ∋ A` we have `σ x ~ σ† x`,
then for any `x` in `Γ , B ∋ A` we have `exts σ x ~ exts σ† x`:
{% raw %}<pre class="Agda"><a id="~exts"></a><a id="6675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#6675" class="Function">~exts</a> <a id="6681" class="Symbol">:</a> <a id="6683" class="Symbol">∀</a> <a id="6685" class="Symbol">{</a><a id="6686" href="plfa.Bisimulation.html#6686" class="Bound">Γ</a> <a id="6688" href="plfa.Bisimulation.html#6688" class="Bound">Δ</a><a id="6689" class="Symbol">}</a>
  <a id="6693" class="Symbol">→</a> <a id="6695" class="Symbol">{</a><a id="6696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#6696" class="Bound">σ</a>  <a id="6699" class="Symbol">:</a> <a id="6701" class="Symbol">∀</a> <a id="6703" class="Symbol">{</a><a id="6704" href="plfa.Bisimulation.html#6704" class="Bound">A</a><a id="6705" class="Symbol">}</a> <a id="6707" class="Symbol">→</a> <a id="6709" href="plfa.Bisimulation.html#6686" class="Bound">Γ</a> <a id="6711" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14726" class="Datatype Operator">∋</a> <a id="6713" href="plfa.Bisimulation.html#6704" class="Bound">A</a> <a id="6715" class="Symbol">→</a> <a id="6717" href="plfa.Bisimulation.html#6688" class="Bound">Δ</a> <a id="6719" href="plfa.More.html#14917" class="Datatype Operator">⊢</a> <a id="6721" href="plfa.Bisimulation.html#6704" class="Bound">A</a><a id="6722" class="Symbol">}</a>
  <a id="6726" class="Symbol">→</a> <a id="6728" class="Symbol">{</a><a id="6729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#6729" class="Bound">σ†</a> <a id="6732" class="Symbol">:</a> <a id="6734" class="Symbol">∀</a> <a id="6736" class="Symbol">{</a><a id="6737" href="plfa.Bisimulation.html#6737" class="Bound">A</a><a id="6738" class="Symbol">}</a> <a id="6740" class="Symbol">→</a> <a id="6742" href="plfa.Bisimulation.html#6686" class="Bound">Γ</a> <a id="6744" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14726" class="Datatype Operator">∋</a> <a id="6746" href="plfa.Bisimulation.html#6737" class="Bound">A</a> <a id="6748" class="Symbol">→</a> <a id="6750" href="plfa.Bisimulation.html#6688" class="Bound">Δ</a> <a id="6752" href="plfa.More.html#14917" class="Datatype Operator">⊢</a> <a id="6754" href="plfa.Bisimulation.html#6737" class="Bound">A</a><a id="6755" class="Symbol">}</a>
  <a id="6759" class="Symbol">→</a> <a id="6761" class="Symbol">(∀</a> <a id="6764" class="Symbol">{</a><a id="6765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#6765" class="Bound">A</a><a id="6766" class="Symbol">}</a> <a id="6768" class="Symbol">→</a> <a id="6770" class="Symbol">(</a><a id="6771" href="plfa.Bisimulation.html#6771" class="Bound">x</a> <a id="6773" class="Symbol">:</a> <a id="6775" href="plfa.Bisimulation.html#6686" class="Bound">Γ</a> <a id="6777" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14726" class="Datatype Operator">∋</a> <a id="6779" href="plfa.Bisimulation.html#6765" class="Bound">A</a><a id="6780" class="Symbol">)</a> <a id="6782" class="Symbol">→</a> <a id="6784" href="plfa.Bisimulation.html#6696" class="Bound">σ</a> <a id="6786" href="plfa.Bisimulation.html#6771" class="Bound">x</a> <a id="6788" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="6790" href="plfa.Bisimulation.html#6729" class="Bound">σ†</a> <a id="6793" href="plfa.Bisimulation.html#6771" class="Bound">x</a><a id="6794" class="Symbol">)</a>
    <a id="6800" class="Comment">--------------------------------------------------</a>
  <a id="6853" class="Symbol">→</a> <a id="6855" class="Symbol">(∀</a> <a id="6858" class="Symbol">{</a><a id="6859" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#6859" class="Bound">A</a> <a id="6861" href="plfa.Bisimulation.html#6861" class="Bound">B</a><a id="6862" class="Symbol">}</a> <a id="6864" class="Symbol">→</a> <a id="6866" class="Symbol">(</a><a id="6867" href="plfa.Bisimulation.html#6867" class="Bound">x</a> <a id="6869" class="Symbol">:</a> <a id="6871" href="plfa.Bisimulation.html#6686" class="Bound">Γ</a> <a id="6873" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14642" class="InductiveConstructor Operator">,</a> <a id="6875" href="plfa.Bisimulation.html#6861" class="Bound">B</a> <a id="6877" href="plfa.More.html#14726" class="Datatype Operator">∋</a> <a id="6879" href="plfa.Bisimulation.html#6859" class="Bound">A</a><a id="6880" class="Symbol">)</a> <a id="6882" class="Symbol">→</a> <a id="6884" href="plfa.More.html#17475" class="Function">exts</a> <a id="6889" href="plfa.Bisimulation.html#6696" class="Bound">σ</a> <a id="6891" href="plfa.Bisimulation.html#6867" class="Bound">x</a> <a id="6893" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="6895" href="plfa.More.html#17475" class="Function">exts</a> <a id="6900" href="plfa.Bisimulation.html#6729" class="Bound">σ†</a> <a id="6903" href="plfa.Bisimulation.html#6867" class="Bound">x</a><a id="6904" class="Symbol">)</a>
<a id="6906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#6675" class="Function">~exts</a> <a id="6912" href="plfa.Bisimulation.html#6912" class="Bound">~σ</a> <a id="6915" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14762" class="InductiveConstructor">Z</a>      <a id="6922" class="Symbol">=</a>  <a id="6925" href="plfa.Bisimulation.html#3815" class="InductiveConstructor">~`</a>
<a id="6928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#6675" class="Function">~exts</a> <a id="6934" href="plfa.Bisimulation.html#6934" class="Bound">~σ</a> <a id="6937" class="Symbol">(</a><a id="6938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14809" class="InductiveConstructor Operator">S</a> <a id="6940" href="plfa.Bisimulation.html#6940" class="Bound">x</a><a id="6941" class="Symbol">)</a>  <a id="6944" class="Symbol">=</a>  <a id="6947" href="plfa.Bisimulation.html#5558" class="Function">~rename</a> <a id="6955" href="plfa.More.html#14809" class="InductiveConstructor Operator">S_</a> <a id="6958" class="Symbol">(</a><a id="6959" href="plfa.Bisimulation.html#6934" class="Bound">~σ</a> <a id="6962" href="plfa.Bisimulation.html#6940" class="Bound">x</a><a id="6963" class="Symbol">)</a>
</pre>{% endraw %}The structure of the proof is similar to the structure of extension itself.
The newly introduced variable trivially relates to itself, and otherwise
we apply renaming to the hypothesis.

With extension under our belts, it is straightforward to show
substitution commutes.  If `σ` and `σ†` both map any judgment `Γ ∋ A`
to a judgment `Δ ⊢ A`, such that for every `x` in `Γ ∋ A` we have `σ
x ~ σ† x`, and if `M ~ M†`, then `subst σ M ~ subst σ† M†`:
{% raw %}<pre class="Agda"><a id="~subst"></a><a id="7421" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7421" class="Function">~subst</a> <a id="7428" class="Symbol">:</a> <a id="7430" class="Symbol">∀</a> <a id="7432" class="Symbol">{</a><a id="7433" href="plfa.Bisimulation.html#7433" class="Bound">Γ</a> <a id="7435" href="plfa.Bisimulation.html#7435" class="Bound">Δ</a><a id="7436" class="Symbol">}</a>
  <a id="7440" class="Symbol">→</a> <a id="7442" class="Symbol">{</a><a id="7443" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7443" class="Bound">σ</a>  <a id="7446" class="Symbol">:</a> <a id="7448" class="Symbol">∀</a> <a id="7450" class="Symbol">{</a><a id="7451" href="plfa.Bisimulation.html#7451" class="Bound">A</a><a id="7452" class="Symbol">}</a> <a id="7454" class="Symbol">→</a> <a id="7456" href="plfa.Bisimulation.html#7433" class="Bound">Γ</a> <a id="7458" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14726" class="Datatype Operator">∋</a> <a id="7460" href="plfa.Bisimulation.html#7451" class="Bound">A</a> <a id="7462" class="Symbol">→</a> <a id="7464" href="plfa.Bisimulation.html#7435" class="Bound">Δ</a> <a id="7466" href="plfa.More.html#14917" class="Datatype Operator">⊢</a> <a id="7468" href="plfa.Bisimulation.html#7451" class="Bound">A</a><a id="7469" class="Symbol">}</a>
  <a id="7473" class="Symbol">→</a> <a id="7475" class="Symbol">{</a><a id="7476" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7476" class="Bound">σ†</a> <a id="7479" class="Symbol">:</a> <a id="7481" class="Symbol">∀</a> <a id="7483" class="Symbol">{</a><a id="7484" href="plfa.Bisimulation.html#7484" class="Bound">A</a><a id="7485" class="Symbol">}</a> <a id="7487" class="Symbol">→</a> <a id="7489" href="plfa.Bisimulation.html#7433" class="Bound">Γ</a> <a id="7491" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14726" class="Datatype Operator">∋</a> <a id="7493" href="plfa.Bisimulation.html#7484" class="Bound">A</a> <a id="7495" class="Symbol">→</a> <a id="7497" href="plfa.Bisimulation.html#7435" class="Bound">Δ</a> <a id="7499" href="plfa.More.html#14917" class="Datatype Operator">⊢</a> <a id="7501" href="plfa.Bisimulation.html#7484" class="Bound">A</a><a id="7502" class="Symbol">}</a>
  <a id="7506" class="Symbol">→</a> <a id="7508" class="Symbol">(∀</a> <a id="7511" class="Symbol">{</a><a id="7512" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7512" class="Bound">A</a><a id="7513" class="Symbol">}</a> <a id="7515" class="Symbol">→</a> <a id="7517" class="Symbol">(</a><a id="7518" href="plfa.Bisimulation.html#7518" class="Bound">x</a> <a id="7520" class="Symbol">:</a> <a id="7522" href="plfa.Bisimulation.html#7433" class="Bound">Γ</a> <a id="7524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14726" class="Datatype Operator">∋</a> <a id="7526" href="plfa.Bisimulation.html#7512" class="Bound">A</a><a id="7527" class="Symbol">)</a> <a id="7529" class="Symbol">→</a> <a id="7531" href="plfa.Bisimulation.html#7443" class="Bound">σ</a> <a id="7533" href="plfa.Bisimulation.html#7518" class="Bound">x</a> <a id="7535" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="7537" href="plfa.Bisimulation.html#7476" class="Bound">σ†</a> <a id="7540" href="plfa.Bisimulation.html#7518" class="Bound">x</a><a id="7541" class="Symbol">)</a>
    <a id="7547" class="Comment">---------------------------------------------------------</a>
  <a id="7607" class="Symbol">→</a> <a id="7609" class="Symbol">(∀</a> <a id="7612" class="Symbol">{</a><a id="7613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7613" class="Bound">A</a><a id="7614" class="Symbol">}</a> <a id="7616" class="Symbol">{</a><a id="7617" href="plfa.Bisimulation.html#7617" class="Bound">M</a> <a id="7619" href="plfa.Bisimulation.html#7619" class="Bound">M†</a> <a id="7622" class="Symbol">:</a> <a id="7624" href="plfa.Bisimulation.html#7433" class="Bound">Γ</a> <a id="7626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14917" class="Datatype Operator">⊢</a> <a id="7628" href="plfa.Bisimulation.html#7613" class="Bound">A</a><a id="7629" class="Symbol">}</a> <a id="7631" class="Symbol">→</a> <a id="7633" href="plfa.Bisimulation.html#7617" class="Bound">M</a> <a id="7635" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="7637" href="plfa.Bisimulation.html#7619" class="Bound">M†</a> <a id="7640" class="Symbol">→</a> <a id="7642" href="plfa.More.html#17607" class="Function">subst</a> <a id="7648" href="plfa.Bisimulation.html#7443" class="Bound">σ</a> <a id="7650" href="plfa.Bisimulation.html#7617" class="Bound">M</a> <a id="7652" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="7654" href="plfa.More.html#17607" class="Function">subst</a> <a id="7660" href="plfa.Bisimulation.html#7476" class="Bound">σ†</a> <a id="7663" href="plfa.Bisimulation.html#7619" class="Bound">M†</a><a id="7665" class="Symbol">)</a>
<a id="7667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7421" class="Function">~subst</a> <a id="7674" href="plfa.Bisimulation.html#7674" class="Bound">~σ</a> <a id="7677" class="Symbol">(</a><a id="7678" href="plfa.Bisimulation.html#3815" class="InductiveConstructor">~`</a> <a id="7681" class="Symbol">{</a><a id="7682" class="Argument">x</a> <a id="7684" class="Symbol">=</a> <a id="7686" href="plfa.Bisimulation.html#7686" class="Bound">x</a><a id="7687" class="Symbol">})</a>  <a id="7691" class="Symbol">=</a>  <a id="7694" href="plfa.Bisimulation.html#7674" class="Bound">~σ</a> <a id="7697" href="plfa.Bisimulation.html#7686" class="Bound">x</a>
<a id="7699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7421" class="Function">~subst</a> <a id="7706" href="plfa.Bisimulation.html#7706" class="Bound">~σ</a> <a id="7709" class="Symbol">(</a><a id="7710" href="plfa.Bisimulation.html#3873" class="InductiveConstructor Operator">~ƛ</a> <a id="7713" href="plfa.Bisimulation.html#7713" class="Bound">~N</a><a id="7715" class="Symbol">)</a>       <a id="7723" class="Symbol">=</a>  <a id="7726" href="plfa.Bisimulation.html#3873" class="InductiveConstructor Operator">~ƛ</a> <a id="7729" class="Symbol">(</a><a id="7730" href="plfa.Bisimulation.html#7421" class="Function">~subst</a> <a id="7737" class="Symbol">(</a><a id="7738" href="plfa.Bisimulation.html#6675" class="Function">~exts</a> <a id="7744" href="plfa.Bisimulation.html#7706" class="Bound">~σ</a><a id="7746" class="Symbol">)</a> <a id="7748" href="plfa.Bisimulation.html#7713" class="Bound">~N</a><a id="7750" class="Symbol">)</a>
<a id="7752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7421" class="Function">~subst</a> <a id="7759" href="plfa.Bisimulation.html#7759" class="Bound">~σ</a> <a id="7762" class="Symbol">(</a><a id="7763" href="plfa.Bisimulation.html#7763" class="Bound">~L</a> <a id="7766" href="plfa.Bisimulation.html#3958" class="InductiveConstructor Operator">~·</a> <a id="7769" href="plfa.Bisimulation.html#7769" class="Bound">~M</a><a id="7771" class="Symbol">)</a>    <a id="7776" class="Symbol">=</a>  <a id="7779" class="Symbol">(</a><a id="7780" href="plfa.Bisimulation.html#7421" class="Function">~subst</a> <a id="7787" href="plfa.Bisimulation.html#7759" class="Bound">~σ</a> <a id="7790" href="plfa.Bisimulation.html#7763" class="Bound">~L</a><a id="7792" class="Symbol">)</a> <a id="7794" href="plfa.Bisimulation.html#3958" class="InductiveConstructor Operator">~·</a> <a id="7797" class="Symbol">(</a><a id="7798" href="plfa.Bisimulation.html#7421" class="Function">~subst</a> <a id="7805" href="plfa.Bisimulation.html#7759" class="Bound">~σ</a> <a id="7808" href="plfa.Bisimulation.html#7769" class="Bound">~M</a><a id="7810" class="Symbol">)</a>
<a id="7812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#7421" class="Function">~subst</a> <a id="7819" href="plfa.Bisimulation.html#7819" class="Bound">~σ</a> <a id="7822" class="Symbol">(</a><a id="7823" href="plfa.Bisimulation.html#4082" class="InductiveConstructor">~let</a> <a id="7828" href="plfa.Bisimulation.html#7828" class="Bound">~M</a> <a id="7831" href="plfa.Bisimulation.html#7831" class="Bound">~N</a><a id="7833" class="Symbol">)</a>  <a id="7836" class="Symbol">=</a>  <a id="7839" href="plfa.Bisimulation.html#4082" class="InductiveConstructor">~let</a> <a id="7844" class="Symbol">(</a><a id="7845" href="plfa.Bisimulation.html#7421" class="Function">~subst</a> <a id="7852" href="plfa.Bisimulation.html#7819" class="Bound">~σ</a> <a id="7855" href="plfa.Bisimulation.html#7828" class="Bound">~M</a><a id="7857" class="Symbol">)</a> <a id="7859" class="Symbol">(</a><a id="7860" href="plfa.Bisimulation.html#7421" class="Function">~subst</a> <a id="7867" class="Symbol">(</a><a id="7868" href="plfa.Bisimulation.html#6675" class="Function">~exts</a> <a id="7874" href="plfa.Bisimulation.html#7819" class="Bound">~σ</a><a id="7876" class="Symbol">)</a> <a id="7878" href="plfa.Bisimulation.html#7831" class="Bound">~N</a><a id="7880" class="Symbol">)</a>
</pre>{% endraw %}Again, the structure of the proof is similar to the structure of
substitution itself: reconstruct each term with recursive invocation,
extending the environment where appropriate (in this case, only for
the body of an abstraction).

From the general case of substitution, it is also easy to derive
the required special case.  If `N ~ N†` and `M ~ M†`, then
`N [ M ] ~ N† [ M† ]`:
{% raw %}<pre class="Agda"><a id="~sub"></a><a id="8270" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8270" class="Function">~sub</a> <a id="8275" class="Symbol">:</a> <a id="8277" class="Symbol">∀</a> <a id="8279" class="Symbol">{</a><a id="8280" href="plfa.Bisimulation.html#8280" class="Bound">Γ</a> <a id="8282" href="plfa.Bisimulation.html#8282" class="Bound">A</a> <a id="8284" href="plfa.Bisimulation.html#8284" class="Bound">B</a><a id="8285" class="Symbol">}</a> <a id="8287" class="Symbol">{</a><a id="8288" href="plfa.Bisimulation.html#8288" class="Bound">N</a> <a id="8290" href="plfa.Bisimulation.html#8290" class="Bound">N†</a> <a id="8293" class="Symbol">:</a> <a id="8295" href="plfa.Bisimulation.html#8280" class="Bound">Γ</a> <a id="8297" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14642" class="InductiveConstructor Operator">,</a> <a id="8299" href="plfa.Bisimulation.html#8284" class="Bound">B</a> <a id="8301" href="plfa.More.html#14917" class="Datatype Operator">⊢</a> <a id="8303" href="plfa.Bisimulation.html#8282" class="Bound">A</a><a id="8304" class="Symbol">}</a> <a id="8306" class="Symbol">{</a><a id="8307" href="plfa.Bisimulation.html#8307" class="Bound">M</a> <a id="8309" href="plfa.Bisimulation.html#8309" class="Bound">M†</a> <a id="8312" class="Symbol">:</a> <a id="8314" href="plfa.Bisimulation.html#8280" class="Bound">Γ</a> <a id="8316" href="plfa.More.html#14917" class="Datatype Operator">⊢</a> <a id="8318" href="plfa.Bisimulation.html#8284" class="Bound">B</a><a id="8319" class="Symbol">}</a>
  <a id="8323" class="Symbol">→</a> <a id="8325" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8288" class="Bound">N</a> <a id="8327" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="8329" href="plfa.Bisimulation.html#8290" class="Bound">N†</a>
  <a id="8334" class="Symbol">→</a> <a id="8336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8307" class="Bound">M</a> <a id="8338" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="8340" href="plfa.Bisimulation.html#8309" class="Bound">M†</a>
    <a id="8347" class="Comment">-----------------------</a>
  <a id="8373" class="Symbol">→</a> <a id="8375" class="Symbol">(</a><a id="8376" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8288" class="Bound">N</a> <a id="8378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#18400" class="Function Operator">[</a> <a id="8380" href="plfa.Bisimulation.html#8307" class="Bound">M</a> <a id="8382" href="plfa.More.html#18400" class="Function Operator">]</a><a id="8383" class="Symbol">)</a> <a id="8385" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="8387" class="Symbol">(</a><a id="8388" href="plfa.Bisimulation.html#8290" class="Bound">N†</a> <a id="8391" href="plfa.More.html#18400" class="Function Operator">[</a> <a id="8393" href="plfa.Bisimulation.html#8309" class="Bound">M†</a> <a id="8396" href="plfa.More.html#18400" class="Function Operator">]</a><a id="8397" class="Symbol">)</a>
<a id="8399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8270" class="Function">~sub</a> <a id="8404" class="Symbol">{</a><a id="8405" href="plfa.Bisimulation.html#8405" class="Bound">Γ</a><a id="8406" class="Symbol">}</a> <a id="8408" class="Symbol">{</a><a id="8409" href="plfa.Bisimulation.html#8409" class="Bound">A</a><a id="8410" class="Symbol">}</a> <a id="8412" class="Symbol">{</a><a id="8413" href="plfa.Bisimulation.html#8413" class="Bound">B</a><a id="8414" class="Symbol">}</a> <a id="8416" href="plfa.Bisimulation.html#8416" class="Bound">~N</a> <a id="8419" href="plfa.Bisimulation.html#8419" class="Bound">~M</a> <a id="8422" class="Symbol">=</a> <a id="8424" href="plfa.Bisimulation.html#7421" class="Function">~subst</a> <a id="8431" class="Symbol">{</a><a id="8432" href="plfa.Bisimulation.html#8405" class="Bound">Γ</a> <a id="8434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14642" class="InductiveConstructor Operator">,</a> <a id="8436" href="plfa.Bisimulation.html#8413" class="Bound">B</a><a id="8437" class="Symbol">}</a> <a id="8439" class="Symbol">{</a><a id="8440" href="plfa.Bisimulation.html#8405" class="Bound">Γ</a><a id="8441" class="Symbol">}</a> <a id="8443" href="plfa.Bisimulation.html#8463" class="Function">~σ</a> <a id="8446" class="Symbol">{</a><a id="8447" href="plfa.Bisimulation.html#8409" class="Bound">A</a><a id="8448" class="Symbol">}</a> <a id="8450" href="plfa.Bisimulation.html#8416" class="Bound">~N</a>
  <a id="8455" class="Keyword">where</a>
  <a id="8463" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8463" class="Function">~σ</a> <a id="8466" class="Symbol">:</a> <a id="8468" class="Symbol">∀</a> <a id="8470" class="Symbol">{</a><a id="8471" href="plfa.Bisimulation.html#8471" class="Bound">A</a><a id="8472" class="Symbol">}</a> <a id="8474" class="Symbol">→</a> <a id="8476" class="Symbol">(</a><a id="8477" href="plfa.Bisimulation.html#8477" class="Bound">x</a> <a id="8479" class="Symbol">:</a> <a id="8481" href="plfa.Bisimulation.html#8405" class="Bound">Γ</a> <a id="8483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14642" class="InductiveConstructor Operator">,</a> <a id="8485" href="plfa.Bisimulation.html#8413" class="Bound">B</a> <a id="8487" href="plfa.More.html#14726" class="Datatype Operator">∋</a> <a id="8489" href="plfa.Bisimulation.html#8471" class="Bound">A</a><a id="8490" class="Symbol">)</a> <a id="8492" class="Symbol">→</a> <a id="8494" class="Symbol">_</a> <a id="8496" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="8498" class="Symbol">_</a>
  <a id="8502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8463" class="Function">~σ</a> <a id="8505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14762" class="InductiveConstructor">Z</a>      <a id="8512" class="Symbol">=</a>  <a id="8515" href="plfa.Bisimulation.html#8419" class="Bound">~M</a>
  <a id="8520" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#8463" class="Function">~σ</a> <a id="8523" class="Symbol">(</a><a id="8524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14809" class="InductiveConstructor Operator">S</a> <a id="8526" href="plfa.Bisimulation.html#8526" class="Bound">x</a><a id="8527" class="Symbol">)</a>  <a id="8530" class="Symbol">=</a>  <a id="8533" href="plfa.Bisimulation.html#3815" class="InductiveConstructor">~`</a>
</pre>{% endraw %}Once more, the structure of the proof resembles the original.


## The relation is a simulation

Finally, we can show that the relation actually is a simulation.
In fact, we will show the stronger condition of a lock-step simulation.
What we wish to show is:

_Lock-step simulation_: For every `M`, `M†`, and `N`:
If `M ~ M†` and `M —→ N`
then `M† —→ N†` and `N ~ N†`
for some `N†`.

Or, in a diagram:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —→ --- N†

We first formulate a concept corresponding to the lower leg
of the diagram, that is, its right and bottom edges:
{% raw %}<pre class="Agda"><a id="9202" class="Keyword">data</a> <a id="Leg"></a><a id="9207" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9207" class="Datatype">Leg</a> <a id="9211" class="Symbol">{</a><a id="9212" href="plfa.Bisimulation.html#9212" class="Bound">Γ</a> <a id="9214" href="plfa.Bisimulation.html#9214" class="Bound">A</a><a id="9215" class="Symbol">}</a> <a id="9217" class="Symbol">(</a><a id="9218" href="plfa.Bisimulation.html#9218" class="Bound">M†</a> <a id="9221" href="plfa.Bisimulation.html#9221" class="Bound">N</a> <a id="9223" class="Symbol">:</a> <a id="9225" href="plfa.Bisimulation.html#9212" class="Bound">Γ</a> <a id="9227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14917" class="Datatype Operator">⊢</a> <a id="9229" href="plfa.Bisimulation.html#9214" class="Bound">A</a><a id="9230" class="Symbol">)</a> <a id="9232" class="Symbol">:</a> <a id="9234" class="PrimitiveType">Set</a> <a id="9238" class="Keyword">where</a>

  <a id="Leg.leg"></a><a id="9247" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9247" class="InductiveConstructor">leg</a> <a id="9251" class="Symbol">:</a> <a id="9253" class="Symbol">∀</a> <a id="9255" class="Symbol">{</a><a id="9256" href="plfa.Bisimulation.html#9256" class="Bound">N†</a> <a id="9259" class="Symbol">:</a> <a id="9261" href="plfa.Bisimulation.html#9212" class="Bound">Γ</a> <a id="9263" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14917" class="Datatype Operator">⊢</a> <a id="9265" href="plfa.Bisimulation.html#9214" class="Bound">A</a><a id="9266" class="Symbol">}</a>
    <a id="9272" class="Symbol">→</a> <a id="9274" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9221" class="Bound">N</a> <a id="9276" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="9278" href="plfa.Bisimulation.html#9256" class="Bound">N†</a>
    <a id="9285" class="Symbol">→</a> <a id="9287" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9218" class="Bound">M†</a> <a id="9290" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19526" class="Datatype Operator">—→</a> <a id="9293" href="plfa.Bisimulation.html#9256" class="Bound">N†</a>
      <a id="9302" class="Comment">--------</a>
    <a id="9315" class="Symbol">→</a> <a id="9317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9207" class="Datatype">Leg</a> <a id="9321" href="plfa.Bisimulation.html#9218" class="Bound">M†</a> <a id="9324" href="plfa.Bisimulation.html#9221" class="Bound">N</a>
</pre>{% endraw %}For our formalisation, in this case, we can use a stronger
relation than `—↠`, replacing it by `—→`.

We can now state and prove that the relation is a simulation.
Again, in this case, we can use a stronger relation than
`—↠`, replacing it by `—→`:
{% raw %}<pre class="Agda"><a id="sim"></a><a id="9583" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9583" class="Function">sim</a> <a id="9587" class="Symbol">:</a> <a id="9589" class="Symbol">∀</a> <a id="9591" class="Symbol">{</a><a id="9592" href="plfa.Bisimulation.html#9592" class="Bound">Γ</a> <a id="9594" href="plfa.Bisimulation.html#9594" class="Bound">A</a><a id="9595" class="Symbol">}</a> <a id="9597" class="Symbol">{</a><a id="9598" href="plfa.Bisimulation.html#9598" class="Bound">M</a> <a id="9600" href="plfa.Bisimulation.html#9600" class="Bound">M†</a> <a id="9603" href="plfa.Bisimulation.html#9603" class="Bound">N</a> <a id="9605" class="Symbol">:</a> <a id="9607" href="plfa.Bisimulation.html#9592" class="Bound">Γ</a> <a id="9609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#14917" class="Datatype Operator">⊢</a> <a id="9611" href="plfa.Bisimulation.html#9594" class="Bound">A</a><a id="9612" class="Symbol">}</a>
  <a id="9616" class="Symbol">→</a> <a id="9618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9598" class="Bound">M</a> <a id="9620" href="plfa.Bisimulation.html#3766" class="Datatype Operator">~</a> <a id="9622" href="plfa.Bisimulation.html#9600" class="Bound">M†</a>
  <a id="9627" class="Symbol">→</a> <a id="9629" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9598" class="Bound">M</a> <a id="9631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19526" class="Datatype Operator">—→</a> <a id="9634" href="plfa.Bisimulation.html#9603" class="Bound">N</a>
    <a id="9640" class="Comment">---------</a>
  <a id="9652" class="Symbol">→</a> <a id="9654" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9207" class="Datatype">Leg</a>  <a id="9659" href="plfa.Bisimulation.html#9600" class="Bound">M†</a> <a id="9662" href="plfa.Bisimulation.html#9603" class="Bound">N</a>
<a id="9664" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9583" class="Function">sim</a> <a id="9668" href="plfa.Bisimulation.html#3815" class="InductiveConstructor">~`</a>              <a id="9684" class="Symbol">()</a>
<a id="9687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9583" class="Function">sim</a> <a id="9691" class="Symbol">(</a><a id="9692" href="plfa.Bisimulation.html#3873" class="InductiveConstructor Operator">~ƛ</a> <a id="9695" href="plfa.Bisimulation.html#9695" class="Bound">~N</a><a id="9697" class="Symbol">)</a>         <a id="9707" class="Symbol">()</a>
<a id="9710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9583" class="Function">sim</a> <a id="9714" class="Symbol">(</a><a id="9715" href="plfa.Bisimulation.html#9715" class="Bound">~L</a> <a id="9718" href="plfa.Bisimulation.html#3958" class="InductiveConstructor Operator">~·</a> <a id="9721" href="plfa.Bisimulation.html#9721" class="Bound">~M</a><a id="9723" class="Symbol">)</a>      <a id="9730" class="Symbol">(</a><a id="9731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19592" class="InductiveConstructor">ξ-·₁</a> <a id="9736" href="plfa.Bisimulation.html#9736" class="Bound">L—→</a><a id="9739" class="Symbol">)</a>
  <a id="9743" class="Keyword">with</a> <a id="9748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9583" class="Function">sim</a> <a id="9752" href="plfa.Bisimulation.html#9715" class="Bound">~L</a> <a id="9755" href="plfa.Bisimulation.html#9736" class="Bound">L—→</a>
<a id="9759" class="Symbol">...</a>  <a id="9764" class="Symbol">|</a> <a id="9766" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9247" class="InductiveConstructor">leg</a> <a id="9770" href="plfa.Bisimulation.html#9770" class="Bound">~L′</a> <a id="9774" href="plfa.Bisimulation.html#9774" class="Bound">L†—→</a>                 <a id="9795" class="Symbol">=</a>  <a id="9798" href="plfa.Bisimulation.html#9247" class="InductiveConstructor">leg</a> <a id="9802" class="Symbol">(</a><a id="9803" href="plfa.Bisimulation.html#9770" class="Bound">~L′</a> <a id="9807" href="plfa.Bisimulation.html#3958" class="InductiveConstructor Operator">~·</a> <a id="9810" class="Bound">~M</a><a id="9812" class="Symbol">)</a>   <a id="9816" class="Symbol">(</a><a id="9817" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19592" class="InductiveConstructor">ξ-·₁</a> <a id="9822" href="plfa.Bisimulation.html#9774" class="Bound">L†—→</a><a id="9826" class="Symbol">)</a>
<a id="9828" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9583" class="Function">sim</a> <a id="9832" class="Symbol">(</a><a id="9833" href="plfa.Bisimulation.html#9833" class="Bound">~V</a> <a id="9836" href="plfa.Bisimulation.html#3958" class="InductiveConstructor Operator">~·</a> <a id="9839" href="plfa.Bisimulation.html#9839" class="Bound">~M</a><a id="9841" class="Symbol">)</a>      <a id="9848" class="Symbol">(</a><a id="9849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19701" class="InductiveConstructor">ξ-·₂</a> <a id="9854" href="plfa.Bisimulation.html#9854" class="Bound">VV</a> <a id="9857" href="plfa.Bisimulation.html#9857" class="Bound">M—→</a><a id="9860" class="Symbol">)</a>
  <a id="9864" class="Keyword">with</a> <a id="9869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9583" class="Function">sim</a> <a id="9873" href="plfa.Bisimulation.html#9839" class="Bound">~M</a> <a id="9876" href="plfa.Bisimulation.html#9857" class="Bound">M—→</a>
<a id="9880" class="Symbol">...</a>  <a id="9885" class="Symbol">|</a> <a id="9887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9247" class="InductiveConstructor">leg</a> <a id="9891" href="plfa.Bisimulation.html#9891" class="Bound">~M′</a> <a id="9895" href="plfa.Bisimulation.html#9895" class="Bound">M†—→</a>                 <a id="9916" class="Symbol">=</a>  <a id="9919" href="plfa.Bisimulation.html#9247" class="InductiveConstructor">leg</a> <a id="9923" class="Symbol">(</a><a id="9924" class="Bound">~V</a> <a id="9927" href="plfa.Bisimulation.html#3958" class="InductiveConstructor Operator">~·</a> <a id="9930" href="plfa.Bisimulation.html#9891" class="Bound">~M′</a><a id="9933" class="Symbol">)</a>   <a id="9937" class="Symbol">(</a><a id="9938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19701" class="InductiveConstructor">ξ-·₂</a> <a id="9943" class="Symbol">(</a><a id="9944" href="plfa.Bisimulation.html#4900" class="Function">~val</a> <a id="9949" class="Bound">~V</a> <a id="9952" class="Bound">VV</a><a id="9954" class="Symbol">)</a> <a id="9956" href="plfa.Bisimulation.html#9895" class="Bound">M†—→</a><a id="9960" class="Symbol">)</a>
<a id="9962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9583" class="Function">sim</a> <a id="9966" class="Symbol">((</a><a id="9968" href="plfa.Bisimulation.html#3873" class="InductiveConstructor Operator">~ƛ</a> <a id="9971" href="plfa.Bisimulation.html#9971" class="Bound">~N</a><a id="9973" class="Symbol">)</a> <a id="9975" href="plfa.Bisimulation.html#3958" class="InductiveConstructor Operator">~·</a> <a id="9978" href="plfa.Bisimulation.html#9978" class="Bound">~V</a><a id="9980" class="Symbol">)</a> <a id="9982" class="Symbol">(</a><a id="9983" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19824" class="InductiveConstructor">β-ƛ</a> <a id="9987" href="plfa.Bisimulation.html#9987" class="Bound">VV</a><a id="9989" class="Symbol">)</a>        <a id="9998" class="Symbol">=</a>  <a id="10001" href="plfa.Bisimulation.html#9247" class="InductiveConstructor">leg</a> <a id="10005" class="Symbol">(</a><a id="10006" href="plfa.Bisimulation.html#8270" class="Function">~sub</a> <a id="10011" href="plfa.Bisimulation.html#9971" class="Bound">~N</a> <a id="10014" href="plfa.Bisimulation.html#9978" class="Bound">~V</a><a id="10016" class="Symbol">)</a>  <a id="10019" class="Symbol">(</a><a id="10020" href="plfa.More.html#19824" class="InductiveConstructor">β-ƛ</a> <a id="10024" class="Symbol">(</a><a id="10025" href="plfa.Bisimulation.html#4900" class="Function">~val</a> <a id="10030" href="plfa.Bisimulation.html#9978" class="Bound">~V</a> <a id="10033" href="plfa.Bisimulation.html#9987" class="Bound">VV</a><a id="10035" class="Symbol">))</a>
<a id="10038" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9583" class="Function">sim</a> <a id="10042" class="Symbol">(</a><a id="10043" href="plfa.Bisimulation.html#4082" class="InductiveConstructor">~let</a> <a id="10048" href="plfa.Bisimulation.html#10048" class="Bound">~M</a> <a id="10051" href="plfa.Bisimulation.html#10051" class="Bound">~N</a><a id="10053" class="Symbol">)</a>    <a id="10058" class="Symbol">(</a><a id="10059" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#20882" class="InductiveConstructor">ξ-let</a> <a id="10065" href="plfa.Bisimulation.html#10065" class="Bound">M—→</a><a id="10068" class="Symbol">)</a>
  <a id="10072" class="Keyword">with</a> <a id="10077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9583" class="Function">sim</a> <a id="10081" href="plfa.Bisimulation.html#10048" class="Bound">~M</a> <a id="10084" href="plfa.Bisimulation.html#10065" class="Bound">M—→</a>
<a id="10088" class="Symbol">...</a>  <a id="10093" class="Symbol">|</a> <a id="10095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9247" class="InductiveConstructor">leg</a> <a id="10099" href="plfa.Bisimulation.html#10099" class="Bound">~M′</a> <a id="10103" href="plfa.Bisimulation.html#10103" class="Bound">M†—→</a>                 <a id="10124" class="Symbol">=</a>  <a id="10127" href="plfa.Bisimulation.html#9247" class="InductiveConstructor">leg</a> <a id="10131" class="Symbol">(</a><a id="10132" href="plfa.Bisimulation.html#4082" class="InductiveConstructor">~let</a> <a id="10137" href="plfa.Bisimulation.html#10099" class="Bound">~M′</a> <a id="10141" class="Bound">~N</a><a id="10143" class="Symbol">)</a> <a id="10145" class="Symbol">(</a><a id="10146" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#19701" class="InductiveConstructor">ξ-·₂</a> <a id="10151" href="plfa.More.html#18914" class="InductiveConstructor">V-ƛ</a> <a id="10155" href="plfa.Bisimulation.html#10103" class="Bound">M†—→</a><a id="10159" class="Symbol">)</a>
<a id="10161" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Bisimulation.md %}{% raw %}#9583" class="Function">sim</a> <a id="10165" class="Symbol">(</a><a id="10166" href="plfa.Bisimulation.html#4082" class="InductiveConstructor">~let</a> <a id="10171" href="plfa.Bisimulation.html#10171" class="Bound">~V</a> <a id="10174" href="plfa.Bisimulation.html#10174" class="Bound">~N</a><a id="10176" class="Symbol">)</a>    <a id="10181" class="Symbol">(</a><a id="10182" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/More.md %}{% raw %}#21004" class="InductiveConstructor">β-let</a> <a id="10188" href="plfa.Bisimulation.html#10188" class="Bound">VV</a><a id="10190" class="Symbol">)</a>      <a id="10197" class="Symbol">=</a>  <a id="10200" href="plfa.Bisimulation.html#9247" class="InductiveConstructor">leg</a> <a id="10204" class="Symbol">(</a><a id="10205" href="plfa.Bisimulation.html#8270" class="Function">~sub</a> <a id="10210" href="plfa.Bisimulation.html#10174" class="Bound">~N</a> <a id="10213" href="plfa.Bisimulation.html#10171" class="Bound">~V</a><a id="10215" class="Symbol">)</a>  <a id="10218" class="Symbol">(</a><a id="10219" href="plfa.More.html#19824" class="InductiveConstructor">β-ƛ</a> <a id="10223" class="Symbol">(</a><a id="10224" href="plfa.Bisimulation.html#4900" class="Function">~val</a> <a id="10229" href="plfa.Bisimulation.html#10171" class="Bound">~V</a> <a id="10232" href="plfa.Bisimulation.html#10188" class="Bound">VV</a><a id="10234" class="Symbol">))</a>
</pre>{% endraw %}The proof is by case analysis, examining each possible instance of `M ~ M†`
and each possible instance of `M —→ M†`, using recursive invocation whenever
the reduction is by a `ξ` rule, and hence contains another reduction.
In its structure, it looks a little bit like a proof of progress:

* If the related terms are variables, no reduction applies.
* If the related terms are abstractions, no reduction applies.
* If the related terms are applications, there are three subcases:
  - The source term reduces via `ξ-·₁`, in which case the target term does as well.
    Recursive invocation gives us

        L  --- —→ ---  L′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        L† --- —→ --- L′†

    from which follows:

         L · M  --- —→ ---  L′ · M
           |                   |
           |                   |
           ~                   ~
           |                   |
           |                   |
        L† · M† --- —→ --- L′† · M†

  - The source term reduces via `ξ-·₂`, in which case the target term does as well.
    Recursive invocation gives us

        M  --- —→ ---  M′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        M† --- —→ --- M′†

    from which follows:

         V · M  --- —→ ---  V · M′
           |                  |
           |                  |
           ~                  ~
           |                  |
           |                  |
        V† · M† --- —→ --- V† · M′†

    Since simulation commutes with values and `V` is a value, `V†` is also a value.

  - The source term reduces via `β-ƛ`, in which case the target term does as well:

         (ƛ x ⇒ N) · V  --- —→ ---  N [ x := V ]
              |                           |
              |                           |
              ~                           ~
              |                           |
              |                           |
        (ƛ x ⇒ N†) · V† --- —→ --- N† [ x :=  V† ]

    Since simulation commutes with values and `V` is a value, `V†` is also a value.
    Since simulation commutes with substitution and `N ~ N†` and `V ~ V†`,
    we have `N [ x := V] ~ N† [ x := V† ]`.

* If the related terms are a let and an application of an abstraction,
  there are two subcases:

  - The source term reduces via `ξ-let`, in which case the target term
    reduces via `ξ-·₂`.  Recursive invocation gives us

        M  --- —→ ---  M′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        M† --- —→ --- M′†

    from which follows:

        let x = M in N --- —→ --- let x = M′ in N
              |                         |
              |                         |
              ~                         ~
              |                         |
              |                         |
        (ƛ x ⇒ N) · M  --- —→ --- (ƛ x ⇒ N) · M′

  - The source term reduces via `β-let`, in which case the target
    term reduces via `β-ƛ`:

        let x = V in N  --- —→ ---  N [ x := V ]
              |                         |
              |                         |
              ~                         ~
              |                         |
              |                         |
        (ƛ x ⇒ N†) · V† --- —→ --- N† [ x := V ]

    Since simulation commutes with values and `V` is a value, `V†` is also a value.
    Since simulation commutes with substitution and `N ~ N†` and `V ~ V†`,
    we have `N [ x := V] ~ N† [ x := V† ]`.


#### Exercise `sim⁻¹`

Show that we also have a simulation in the other direction, and hence that we have
a bisimulation.

{% raw %}<pre class="Agda"><a id="14002" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `products`

Show that the two formulations of products in
Chapter [More][plfa.More]
are in bisimulation.  The only constructs you need to include are
variables, and those connected to functions and products.
In this case, the simulation is _not_ lock-step.

{% raw %}<pre class="Agda"><a id="14306" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Unicode

This chapter uses the following unicode:

    †  U+2020  DAGGER (\dag)
    ⁻  U+207B  SUPERSCRIPT MINUS (\^-)
    ¹  U+00B9  SUPERSCRIPT ONE (\^1)
