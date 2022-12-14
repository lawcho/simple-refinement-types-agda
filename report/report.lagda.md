---
title: FoCAL project report
author: Lawrence Chonavel (with lots of help from Ulf Norell)
date: September 2022
geometry: margin=1cm
classoption: twocolumn
bibliography: biblio.bib
csl: ieee.csl
colorlinks: true
numbersections: true
autoSectionLabels: true
codeBlockCaptions: true
# Break long  lines in code blocks https://stackoverflow.com/a/48507868
# Put boxes round images : https://tex.stackexchange.com/a/526521
# Set up fallback font: https://tex.stackexchange.com/a/572220
header-includes: |
  ~~~{=tex}
  \usepackage{agda}
  \usepackage{fontspec}
  \usepackage{comment}

  \usepackage{fvextra}
  \DefineVerbatimEnvironment{Highlighting}{Verbatim}{breaklines,commandchars=\\\{\}}

  \usepackage[export]{adjustbox}
  \let\includegraphicsbak\includegraphics
  \renewcommand*{\includegraphics}[2][]{\includegraphicsbak[frame,#1]{#2}} 

  \usepackage{luaotfload}
  \directlua{luaotfload.add_fallback
   ("mycustomfallback",
    { "SymbolamonospacifiedforSourceCodePro:style=Regular;"
    , "NotoSansMono:style=Regular;"
    , "NotoSansMath:style=Regular;"
    }
   )}

  \defaultfontfeatures{RawFeature={fallback=mycustomfallback}}
  ~~~

abstract: |
  Type systems are intended to catch programmers' bugs, but sometimes the type systems themselves have bugs.
  I set out to find bugs in a pair of *refinement type systems* by Jhala et al. [@refinement-tut], producing along the way a *formalization* of the type systems and a *verified implementation* of their type checking and inference algorithms, all in Agda [@Agda].

---

[]: <> (Set fonts for main body of document)

\setmainfont{DejaVu Serif}
\setsansfont{DejaVu Sans}
\setmonofont{DejaVu Sans Mono}
\setmathfont{Latin Modern Math}

[]: <> (Set Agda code fonts)
[]: <> (https://agda.readthedocs.io/en/v2.6.2.2/tools/generating-latex.html)
\newfontfamily{\AgdaRegularFont}{Source Code Pro}
\newfontfamily{\AgdaMediumFont}{Source Code Pro Medium}
\newfontfamily{\AgdaLightFont}{Source Code Pro Light}
\renewcommand{\AgdaFontStyle}[1]{{\AgdaMediumFont{}#1}}
\renewcommand{\AgdaKeywordFontStyle}[1]{{\AgdaMediumFont{}#1}}
\renewcommand{\AgdaStringFontStyle}[1]{{\AgdaLightFont{}#1}}
\renewcommand{\AgdaCommentFontStyle}[1]{{\AgdaLightFont{}#1}}
\renewcommand{\AgdaBoundFontStyle}[1]{\AgdaRegularFont{}#1}


:::: hidden ::::
```agda
module report where
open import Util.All
```
::::::::::::::::


# Introduction

*Refinement type systems* allow programmers to write rich specifications for their programs by *refining* type signatures with logical predicates. For example, the annotation on `r_sq`'s return type asserts that `r_sq` produces only non-negative values.

~~~haskell
-- Compute modulus-squared of a vector
r_sq : Real ?? Real ??? Real[v | v >= 0]
r_sq (x , y) = x * x + y * y
~~~

These refinement types are automatically checked at compile-time, and can be used in proving more complicated properties, e.g. that the call to `sqrt` is safe:

~~~haskell
primitive sqrt : Real[v | v >= 0] ??? Real

-- Euclidean distance between two vectors
vec_dist : Real ?? Real ??? Real ?? Real ??? Real
vec_dist (x1 , y1) (x2 , y2) =
    sqrt $ r_sq ((x1 - x2) , (y1 - y2))
~~~

More information on programming with refinement types can be found at the LiquidHaskell website [@lh-website], we now turn to how these type systems are *implemented*.

Jhala and Vazou [@refinement-tut] give a tutorial-style presentation of the theory behind refinement type systems, starting with a minimal Simply-Typed Lambda-Calculus-like language and showing how to add features one by one.

Unfortunately, these type systems are described only semi-formally, using a combination of \LaTeX{} rules, pseudocode functions, and prose (e.g. [@fig:rules-syn; @fig:subst-defn; @fig:prose-defn]), which leave room for ambiguity and mistakes.

It's also not clear whether real (i.e. executable) implementations of the type systems (e.g. Sprite [@sprite]) correctly implement the rules in the paper.

# What have I built?

I have formalized the languages in [@refinement-tut] up to Lang-????, i.e. a simply-typed ??-calculus with refinement types, branches, and recursion. My Agda formalization includes:

An implementation of Lang-????'s *typing rules*

: e.g. the paper's type-synthesis relation in [@fig:rules-syn] is formalized as the data type in [@lst:ex-rules-syn]

A proof-producing *type-checker*

: for Lang-???? programs (@sec:a-proof-producing-type-checker)

Fixes for various *bugs* in the paper

: ([@sec:bugs-found])

Source code for this formalization (and report) can be found at <https://github.com/lawcho/simple-refinement-types-agda>


![Paper's [@refinement-tut] type-synthesis relation (defined using rule notation)](images/rules-syn.png){#fig:rules-syn}

![Paper's [@refinement-tut] "capture avoiding substitution" (defined using pseudocode)](images/subst-defn.png){#fig:subst-defn}

![Fragment of Paper's [@refinement-tut] VC semantics (defined using prose)](images/prose-defn.png){#fig:prose-defn}

:::: hidden ::::
```agda
module Example-Synth where
  open import Lang-??.Refinement
  open import Lang-??.Type
  open import Lang-??.Term
  open import Lang-??.Typing
  open import Common.Example-Solver
  open With-SMT solver hiding (_???_??????_)

```
::::::::::::::::

```agda
  data _???_??????_ (?? : Context)
    : Term ??? Type ??? Set
    where
      syn-var
          : ??? {x t ptr}
          ??? lookup x ?? ??? yes (t , ptr)
          ---------------------------
          ??? ?? ??? var x ?????? t
      syn-con
          : ???{c t}
          ??? prim c ??? t
          ---------------
          ??? ?? ??? con c ?????? t
      syn-ann
          : ???{e t k}
          ??? ?? ??? t :??? k
          ??? ?? ??? e ?????? t
          ---------------
          ??? ?? ??? e ??? t ?????? t
      syn-app
          : ??? {e x s t y}
          ??? ?? ??? e ?????? (x ??? s ???' t)
          ??? ?? ??? var y ?????? s
          -------------------------------
          ??? ?? ??? e [ y ] ?????? (t [ x := y ]???)
```

: Formalization of the `?? ??? e ??? t` relation from [@fig:rules-syn] {#lst:ex-rules-syn}

# What worked well

Bug-fixes aside, my formalization follows the paper closely, and is quite concise. This is thanks to the following design decisions:

## A Proof-Producing Type-Checker

My type-checker always gives the correct answer, and can prove it!

We can know this from its type signature:

:::: hidden ::::
```agda
module Checker-Sig where
  open import Lang-????.Typing
  open import Common.Example-Solver
  open With-SMT solver
  open import Lang-????.Term
  open import Lang-????.Sugar
  postulate
```
::::::::::::::::

```agda
    check :
      (?? : Context) ???
      (e : Term) ???
      (t : Type) ???
      Dec (?? ??? e ?????? t)
```

which says that `check` is a function that takes a context
`??`, a term `e`, and a type `t`, then
`Dec`ides `?? ??? e ?????? t`, i.e. produces either a typing
derivation for `?? ??? e ?????? t`, or a proof that no such typing
derivation exists.

:::: hidden ::::
```agda
module example1 where

  open import Lang-????.Typing
  open import Common.Example-Solver
  open With-SMT solver
  open import Lang-????.Algorithmic-Typing solver
  open import Lang-????.Refinement
  open import Lang-????.Sugar

  open import Common.VC-Syntax.Type
  open import Common.VC-Syntax.Predicate
  open import Common.VC-Syntax.Constraint
```
::::::::::::::::

Let's see it in action! Here's a Lang-???? program which is supposed to always return a non-negative number:

```agda
  abs-diff =
    ????"x"??? ????"y"???
    let??? "x???y" := "x" ?????? "y" in???
    if???   "x???y"
    then??? "y" -??? "x"
    else??? "x" -??? "y"
```

To prove that `abs-diff` has this property, we can encode the property as a type `ty`:

```agda
  ty =
    "x"??? int ?????? ???'
    "y"??? int ?????? ???'
    int ???"z"??? -1 <??? "z" ???
```

then construct a typing derivation proving that `abs-diff` has that type:

```agda
  typing-der : [] ??? abs-diff ?????? ty
```

by calling `check`, and extracting its (positive) result:

```agda
  typing-der with
    of?? der ??? proof $ check [] abs-diff ty
    = der
```

## Mocking SMT

To decide typing relations like those above, the type-`check`er depends on an external tool. Let's see how.

Following the typing rules, the type-checker breaks down the judgement `[] ??? abs-diff ?????? ty` to subtyping constraints including `_c`:

```agda
  _c =
      (raw (var "x???y" ??? == ??? true)
    ??? ("x???y"??? bool ???"b"??? var "b"
        ??? == ??? ((var "x" ??? < ??? var "y")
        ??? ??? ???   (var "x" ??? == ??? var "y"))???)
    ??? ("y"??? int ??????) ??? ("x"??? int ??????) ??? [])
    ???  int ???"v"??? var "v"
        ??? == ??? (var "y" ??? - ??? var "x")???
    ???: int ???"z"??? -1 ??? < ??? var "z"???
```

which it passes if and only if a corresponding logical formula `_vc` is valid:

```agda
  _vc =
    ?????? int ??? ?????? int ??? ?????? bool ???
      (var ???0 ??? == ???
      (     (var ???2 ??? < ???  var ???1)
      ??? ??? ??? (var ???2 ??? == ??? var ???1))) ???
        (var ???0 ??? == ??? true) ???
          ?????? int ???
            (var ???0 ??? == ???
            (var ???2 ??? - ??? var ???3)) ???
              pred (-1 ??? < ??? var ???0)

```

Notice how `_vc` is quite complex: it contains many different logical connectives, and even statements about integer arithmetic.

To efficiently decide formulas like `_vc`, the checker queries an external tool -- an *SMT solver*.
Unfortunately, existing SMT solvers are extremely complex^[
Microsoft's [Z3]{.smallcaps} [@z3github] weighs in at over 400k lines of C++:  
`curl -L https://api.codetabs.com/v1/loc?github=Z3Prover/z3`],
making formalizing them a challenge.

I avoided this problem by instead *mocking* an SMT solver -- i.e. I implemented just enough of an SMT solver to cover all the queries that the example programs make.

The mock is too verbose to present here, but can be found in `Common.Example-Solver.agda`^[e.g. the query `_vc` is covered on lines 362-386].

## Mocking SMT *Soundly* 

The SMT solver mock might not be complete, but at least it never gives wrong answers to queries (i.e. it is "sound").

We can be sure that the mock is sound because (like `check`) it does not return a `Bool`, but rather a `Dec`ision (this time for VC validity):

:::: hidden ::::
```agda
module Type-Of-solver where
  open import Common.VC-Syntax.Constraint
  open import Common.VC-Semantics.Constraint
  postulate
```
::::::::::::::::

```agda
    smt-mock : (vc : VC) ??? Dec (Valid vc)
```

## Mixed-Style VC Semantics

:::: hidden ::::
```agda
module Predicate-Denot-Sem {??} ?? where
  open import Common.VC-Syntax.Type
  open import Common.VC-Syntax.Predicate
  open import Common.VC-Semantics.Type
```
::::::::::::::::

For the SMT mock to produce VC validity (dis-)proofs, I first needed to define the type, `Valid`, of VC-validity proofs (aka the "semantics" of VCs).

This semantics is a bit unusual, since it mixes two different styles: VC constraints get a denotational semantics (i.e. a translation *function*), whereas VC predicates get a big-step semantics (i.e. a translation *relation*).

This is deliberate: the obvious denotational semantics for predicates is easy to give (@lst:vc-pred-denot-sem), but very awkward to write decision procedures for.

```agda
  ???_?????? : ??? {??} ??? Predicate ?? ?? ??? ??? ?? ??????
  ??? true ??????   = ????.true
  ??? false ??????  = ????.false
  ??? ?? p ??????    = ????.not ??? p ??????
  ??? p??? ??? < ??? p??? ?????? = does (??? p??? ?????? ???.<? ??? p??? ??????)
  ??? p??? ??? > ??? p??? ?????? = does (??? p??? ?????? ???.<? ??? p??? ??????)
  ??? p??? ??? ??? ??? p??? ?????? = ??? p??? ?????? ????.??? ??? p??? ??????
  ??? p??? ??? ??? ??? p??? ?????? = ??? p??? ?????? ????.??? ??? p??? ??????
  ??? p??? ??? + ??? p??? ?????? = ??? p??? ?????? ???.+ ??? p??? ??????
  ??? p??? ??? - ??? p??? ?????? = ??? p??? ?????? ???.- ??? p??? ??????
  ??? p??? ??? == {ty} ??? p??? ?????? with ty
  ... | int  = does (??? p??? ?????? ???.???  ??? p??? ??????)
  ... | bool = does (??? p??? ?????? ????.???  ??? p??? ??????)
  ??? num x ??????      = x
  ??? var ptr ??????    = follow ptr into ??
  ??? if p??? then p??? else p??? ?????? with ??? p??? ??????
  ... | ????.true  = ??? p??? ??????
  ... | ????.false = ??? p??? ??????
```

: Denotational semantics for VC predicates {#lst:vc-pred-denot-sem}

The problem is that `???_??????` produces expressions containing function calls, which block unification when placed in types, making predicate-value proofs difficult to split up^[e.g. `pf : ????.true ??? does (x ???.??? y) ????.??? does (y ???.??? num 4)` can't be matched (as `refl`) since Agda can't unify the LHS and RHS of the equation] or combine.

In contrast, big-step derivations can be split up by pattern-matching constructors. The constructors also make combining derivations easy.
This helps keep VC-validity proofs short & structured.


## Capture-avoiding ??-renaming

The typing rules use *capture-avoiding substitution*, a notoriously fickle algorithm (see [@sec:bugs-found]).

Fortunately, we don't actually need the full *substitution* algorithm -- the special case of *??-renaming* is sufficient (and easier to implement). This is possible since Lang-???? is an *Administrative Normal Form* language^[i.e. a language where functions can only be applied to variables].

This formalization implements (capture-avoiding) ??-renaming using a slightly unusual algorithm. Let's derive it now.

### The new algorithm

:::: hidden ::::
```agda
module ??-renaming-algorithm
    (String : Set)
    (_==_ : String ??? String ??? ????)
  where
  infixr 25 ????_???_
  infixl 24 _[_???_] _[_???_] 

  infixr 10 _if_???_
  infix 11 _otherwise
  _otherwise : ???{???a}{A : Set ???a} ??? A ??? A
  _otherwise = id
  _if_???_ : ???{???a}{A : Set ???a} ??? A ??? ???? ??? A ??? A
  a if ????.true ??? _ = a
  _ if ????.false ??? a = a

  _[_???_]' : String ??? String ??? String ??? String
```
::::::::::::::::

For simplicity, we'll work with the untyped lambda calculus, which has only two constructors:

```agda
  data Exp : Set where
    var : String ??? Exp
    ????_???_ : String ??? Exp ??? Exp 
```

We are going to implement an ??-renaming function

```agda
  _[_???_] : Exp ??? String ??? String ??? Exp
```

such that `e [ old ??? new ]` replaces all free occurrences of `old` with `new` in `e`, without changing `e`'s binding structure.

The case for variables is easy

```agda
  var x [ old ??? new ]
    = var new     if x == old
    ??? var x       otherwise
```

the case for ??-bindings is recursive, but straightforward enough except for the capture-avoiding case

```agda
  ???? x ??? e [ old ??? new ]
    = ???? x ??? e                         if x == old
    ??? {! must not capture old here !} if x == new
    ??? ???? x ??? (e [ old ??? new ])         otherwise
```

It is *not* correct to fill the hole with `???? x ??? (e [ old ??? new ])`, since this will capture all free occurrences of `old` in `e` (they will become bound by `???? x`, but we want them kept free).

The usual solution is to generate a "fresh" variable `tmp` (i.e. a variable that is not free in `e`), and then return `???? tmp ??? (e [ new ??? tmp ] [ old ??? new ])`. Unfortunately, generating "fresh" variables is quite intricate, requiring an extra traversal of `e`.

Let's derive an equivalent but simpler algorithm, by equational reasoning:

~~~eq
???? tmp ???
  (e [new ??? tmp][old ??? new])
      ==??==
???? old ???
  (e [new ??? tmp][old ??? new][tmp ??? old])
      ==??==
???? old ???
  (e [ new ??? old ])
~~~

The first equation is justified by the fact that `old` is fresh in `e [ new ??? tmp ] [ old ??? new ]` (thanks to the last renaming). 
The second equation is justified by observing that `[new ??? tmp][old ??? new][tmp ??? old]` just swaps `new` and `old`.

So overall, we have just reduced the tricky case of ??-renaming to ??-swapping, which can be implemented recursively:

```agda
  _[_???_] : Exp ??? String ??? String ??? Exp
  var x [ v1 ??? v2 ]
    = var (x [ v1 ??? v2 ]')
  ???? x ??? e [ v1 ??? v2 ]
    = ???? (x [ v1 ??? v2 ]') ??? (e [ v1 ??? v2 ])
```

where `_[_???_]'` is (non-recursive) ??-swapping on strings:

```agda
  s [ v1 ??? v2 ]'
    = v2        if s == v1
    ??? v1        if s == v2
    ??? s         otherwise
```

### Correctness

I have not proved the correctness of the algorithm formally. Some unit tests can be found in `Lang-??.Type.agda`.

Note that this algorithm is not new -- see e.g. [@Pitts2001NominalLA], page 4.

# Bugs found

The formalization also unearthed several mistakes in the paper.

Most of these involve the translation of subtyping constraints into SMT-ready verification conditions ([@fig:rules-ent-subty]).

![The rules for subtyping](images/rules-ent-subty.png){#fig:rules-ent-subty}

## Missing rule

The paper's $???$ relation ([@fig:rules-ent-subty]) is missing a rule.

There are rules for when ?? is empty ([Ent-Emp]{.smallcaps}), or when the last type in ?? is a base type ([Ent-Ext]{.smallcaps}), but no rule for when ?? contains a function type.

As a consequence, higher-order functions such as `flip` do not type-check:

::: hidden :::
```agda
module Example-Broken-HOF where
  open import Common.Example-Solver
  open import Lang-????.Type
  open import Lang-????.Term
  open import Lang-????.Typing
```
::::::::::::::

```agda
  flip =
    ???? "f" ??? ???? "x" ??? ???? "y" ???
    var "f" ["y"] ["x"]
```

To fix this bug, I added a rule that ignores function types in the context:

::: hidden :::
```agda
  data _???_ : Context ??? Untyped-Constraint ??? Set where
```
::::::::::::::

```agda
    ent-fun
      : ???{?? c x y s t}
      ??? ?? ??? c
      ---------------------------
      ??? (x ??? (y ??? s ???' t) ??? ??) ??? c
```

This rule is based on the subtyping algorithm presented in the paper, which also ignores function types.

## Non-capture-avoiding ??-renaming

The ??-renaming defined in the paper ([@fig:subst-defn]) is not capture-avoiding.

In the last case, if $x = z$, then all free occurrences of $y$ in $t$ are translated to bound $x$.

This is fixed by the new algorithm in [@sec:the-new-algorithm].

## Missing ??-renaming

The type systems in the paper are over-reliant on variable name equality.

For example, programs won't type-check if they contain types like:

::: hidden :::
```agda
module Example-Needs-CA??R where
  open import Lang-????.Type
  open import Lang-????.Typing
  open import Lang-????.Refinement
  _???_ = _:=_
  infixl 50 _???_
  int2int : Type
  int2int =
```
::::::::::::::
```agda
    "x"??? int ???"y"??? true ??? ???' int ???"z"??? true ???
```

This is because the [Ent-Ext]{.smallcaps} rule ([@fig:rules-ent-subty], yellow) requires that the name bound *inside* the refinement ("y") be the same as the one *outside* the refinement ("x").

This is easily fixed by adding ??-renaming to the [Ent-Ext]{.smallcaps} rule:

::: hidden :::
```agda
  data _???_ : Context ??? Untyped-Constraint ??? Set where
```
::::::::::::::
```agda
    ent-ext
      : ???{?? c x v b p}
      ??? ?? ??? (?????? x ??? b2p b ??? (p [ v ??? x ]??? ??? c))
      ----------------------------------------
      ??? (x ??? b ??? v ??? p ??? ??? ??) ??? c
```

## Non-unique typing derivations

The type-checking rule for `if` statements ([@fig:rule-if]) contains an alarming "y is fresh" side-condition.

![The "y is fresh" side condition](images/rule-if.png){#fig:rule-if}

This is very awkward side condition, for both implementations and meta-theory, since:

1. Free variables must be explicitly calculated
2. The (very loose) side condition acts as a *choice point*: any typing judgement involving an `if` statement may have an *infinite* number of typing derivations (rather than at most one), which makes writing decision procedures more difficult.

I avoided this can of worms by allowing contexts to contain raw refinements (alongside ordinary variable-type bindings).

This allows the type-checking rule for "if" to add its constraints to contexts without needing to invent a dummy variable:

::: hidden :::
```agda
module Raw-Refs where
  open import Lang-????.Refinement
  open import Lang-????.Type
  open import Lang-????.Term
  open import Lang-????.Typing
  data _???_??????_ (?? : Context) : Term ??? Type ??? Set where
```
::::::::::::::

```agda
    chk-if
      : ??? {x e??? e??? t}
      ??? ?? ??? var x ?????? (bool ??????)
      ??? (raw (var x ??? == ??? true ) ??? ??) ??? e??? ?????? t
      ??? (raw (var x ??? == ??? false) ??? ??) ??? e??? ?????? t
      ------------------------------------------
      ??? ?? ??? if x then e??? else e??? ?????? t
```

# Conclusion, Future Work

In this report, I've shown off the highlights of an Agda formalization of refinement typing, including a list of bugs and a bag of tricks such as mocking SMT and pure capture-avoiding ??-renaming.

However, I didn't try:

The final 6 languages

: in the paper, which include advanced features such as ML-style polymorphism, user-defined data types, and a richer refinement language.

Connecting a real SMT solver

: to replace the mock, which needs to be expanded for each new example.

Tidying up my implementation

: of algorithmic typing, which is currently an ad-hoc jumble of `with` syntax, the `id` monad, and helper functions. An advanced EDSL for writing decision procedures could really shine here.

# Bibliography

::: {#refs}
:::
