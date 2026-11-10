# Step 1 nodes: what vau calculus is. Start is a concept node; VauE.Env and VauE.vau_call are Lean
# declarations (Step 4). Term,
# IsValue, inst and Top are Lean declarations in Vau/ (Step 3); their text explains the Lean. Notation is ASCII: [eval T], [combine T1 T2], <T> (applicative), <vau x.T>, <vau0.T>,
# <vau2.T> (compound operatives), T[x <- V] (substitution). "%T" below expands to the thesis PDF URL,
# "%N" to the NEPLS talk, "%D1" to Schumacher's "Fexpr the Ultimate Lambda".
from _common import THESIS, NEPLS, DALE_FEXPR, make, q

NODES = []
node = make(NODES)


def L(s):
    return s.replace("%T", THESIS).replace("%N", NEPLS).replace("%D1", DALE_FEXPR)


# ---------------------------------------------------------------- 1. Start
node("Start",
     "Start: why vau calculus makes evaluation explicit",
     "Wand (1998) showed that in his calculus, where evaluation is implicit and fexprs are fully reflective, contextual equivalence is trivial. "
     "Vau calculus keeps source code as passive data and asks for evaluation with an explicit `[eval T]` term, "
     "so evaluation becomes one kind of reduction among others.",
     L("""
## Plain English

**Operatives and applicatives.** In Lisp, a *combination* is a pair that is to be evaluated: its first
element is the *operator* and the rest are the *operands*. Shutt calls the thing an operator designates a
*combiner*. A combiner is **applicative** if it acts on its *arguments* (the results of evaluating the
operands), like an ordinary Scheme procedure. It is **operative** if it acts on the *operands themselves*,
unevaluated, like `if` or `define`. A **fexpr** is a first-class operative that does its job by evaluating
a body, as a procedure does. Lisp had fexprs until about 1980, and then dropped them for macros.

**The problem: implicit evaluation.** In the lambda calculus, *reduction is evaluation*. The term
`((lambda x. x) y)` is at the same time the program text and the running computation, and one step turns
it into `y`. Now add a fexpr that can look at the *structure* of its operand. It can tell the operand
`((lambda x. x) y)` from the operand `y`, because one is a combination and the other is not. But a
calculus wants its equations to hold *in every context* (this is called compatibility). So the two terms
cannot be equal, even though one reduces to the other. Carried through, no two different terms are equal.
Mitchell Wand made this precise in *The Theory of Fexprs is Trivial* (Lisp and Symbolic Computation,
1998): in his reflective calculus, two terms are contextually equivalent only when they are the same up to
renaming of bound variables. A theory with only those equations tells you nothing.

**Shutt's diagnosis.** In his thesis
([section 8.4.1](%T#page=186) and [chapter 15](%T#page=354)), John N. Shutt argues that the cause is
*implicit evaluation*, not fexprs as such. Two things differ in his calculi:

1. **Evaluation is explicit.** A pair `(T1 . T2)` is only data. It is a combination only when it is
   inside a request to evaluate it: `[eval (T1 . T2)]`. Source code that a programmer writes contains no
   such requests, so it contains nothing to reduce, and a fexpr that receives it receives it exactly as
   written. Computation happens only in the *active terms* `[eval T]` and `[combine T1 T2]`.
2. **Not everything can be taken apart.** Fexprs in Wand's calculus can take apart every term. In Shutt's
   calculi, a fexpr can take apart pairs and atoms, but not environments, compound operatives, or active
   terms.

In his 2007 NEPLS talk, Shutt sums it up: explicit evaluation "makes term evaluation a special case of
term reduction" ([talk script](%N)). So an operand can be reduced *without being evaluated*, and reduction
still gives true equations, for example `[eval 5] = 5`.

**What this site explains.** The smallest of Shutt's calculi with this design is the pure
**vau-x calculus** ([thesis section 9.3](%T#page=203)). It has no symbols and no environments. Read, in
order:

1. [Term](#/node/Term): the terms.
2. [IsValue](#/node/IsValue): which terms are finished data.
3. [inst](#/node/inst): how a parameter gets its value (substitution).
4. [Top](#/node/Top): the seven general rules eval-self, eval-pair,
   eval-wrap, combine-wrap, beta-vau, parse-nil and parse-pair.

Real Kernel code uses `$vau` with symbols and environments. To make `$vau` understandable, two more nodes
explain environments informally, from Shutt's vau-e calculus:
[VauE.Env](#/node/VauE.Env) and [VauE.vau_call](#/node/VauE.vau_call).

## What the Lean proves

This repository has a Lean 4 formalization of the pure vau-x rules (folder `Vau/`, no Mathlib, no
`sorry`). On top of the [terms](#/node/Term), [substitution](#/node/inst), the
[rules](#/node/Top) and their [compatible closure](#/node/Step), it proves four headlines:

- [eval_is_reduction](#/node/eval_is_reduction): every run of an evaluator is a reduction sequence;
- [conservative_extension](#/node/conservative_extension): through the
  [lambda embedding](#/node/embed), vau-x keeps exactly the equations of the call-by-value lambda
  calculus;
- [confluence](#/node/confluence) of the concrete vau-x rules;
- [nontrivial](#/node/nontrivial): contextual equivalence in vau-x is not trivial.

A fifth headline is about Kernel-style code with symbols and environments. A separate Lean model of
Shutt's vau-e calculus ([environments](#/node/VauE.Env), [`$vau`](#/node/VauE.vau_call),
[wrap and unwrap](#/node/VauE.unwrap_wrap)) proves
[derived_lambda](#/node/VauE.derived_lambda): Shutt's `$lambda`, defined from `$vau`, `wrap` and
`eval`, evaluates its body with the parameters bound to the evaluated arguments, and
`lambda_static_scope` shows that the body runs in the environment of the `$lambda` expression, not the
caller's. Still **PLAN**:
[EnvironmentOpacity](#/node/EnvironmentOpacity), [EncapsulationTypes](#/node/EncapsulationTypes) and
the [ActorLayer](#/node/ActorLayer).

The Lean does **not** formalize Shutt's general framework of regular substitutive reduction systems
(thesis chapter 13). [Confluence of vau-e](#/node/VauE.confluence) is proved directly too. Each vau-x result is about the concrete
vau-x rules with no delta-rules.
"""),
     [q("In the lambda calculus with implicit evaluation, why does adding a fexpr that inspects its operand make the theory trivial?",
        ["Because fexprs cannot be typed",
         "Because the fexpr can tell a term from its reduct, and equations must hold in every context, so no two different terms can be equal",
         "Because beta-reduction stops working",
         "Because environments become mutable"],
        1, "A fexpr can see the difference between `((lambda x. x) y)` and `y`. Compatibility makes an equation hold inside every context, including the fexpr's operand, so the two cannot be equal. Wand (1998) shows only alpha-equivalent terms are contextually equivalent."),
      q("In vau calculus, what makes a pair `(T1 . T2)` act as a function call?",
        ["Nothing: it is always a call",
         "Being inside an active term such as `[eval (T1 . T2)]`",
         "Having a variable as its first element",
         "Being a value"],
        1, "A pair is passive data. The rule eval-pair applies only to `[eval (T1 . T2)]`. Explicit evaluation is the whole point."),
      q("Which statement is Shutt's summary of explicit evaluation in his 2007 NEPLS talk?",
        ["It makes reduction a special case of evaluation",
         "It makes term evaluation a special case of term reduction",
         "It removes the need for reduction",
         "It makes all terms values"],
        1, "The talk says explicit evaluation \"makes term evaluation a special case of term reduction\". Evaluation steps are reduction steps of `[eval ...]` terms; not every reduction step is an evaluation."),
      q("What does this repository's Lean prove about confluence?",
        ["Shutt's general Church-Rosser theorem for regular SRSs",
         "Confluence of the concrete vau-x rules (seven general schemata, no delta-rules), by a direct proof",
         "Nothing: confluence is only planned",
         "Confluence of the full Kernel language"],
        1, "`Vau.confluence` is about the concrete vau-x rules. The Lean does not formalize Shutt's SRS framework.")],
     caveats=[
         "Wand's result is summarized in our own words, not quoted. His calculus and his notion of fexpr differ from Shutt's; Shutt discusses the difference in thesis chapter 15.",
         "The example `((lambda x. x) y)` versus `y` is our illustration of the argument, not taken from Wand's paper.",
         "Shutt's thesis obtains Church-Rosser (confluence) for vau-x through a general theorem on regular substitutive reduction systems (sections 13.4 and 14.1.4). This site does not check that proof. The Lean here proves confluence only for the concrete vau-x rules, by a different route.",
     ])

# ---------------------------------------------------------------- 2. Syntax
node("Term",
     "The syntax of pure vau-x calculus",
     "A vau-x term is a self-evaluating term, a variable `x`, a pair `(T1 . T2)`, an applicative `<T>`, "
     "or an active term `[eval T]` or `[combine T1 T2]`.",
     L("""
## Plain English

This is Shutt's grammar for vau-x ([thesis (9.25)](%T#page=206)), written in ASCII:

```
d in PrimitiveData        o in PrimitiveOperatives        x in Variables

S ::= d | o | #ignore | () | <vau2.T> | <vau0.T> | <vau x.T>      self-evaluating terms
A ::= [eval T] | [combine T T]                                  active terms
T ::= S | x | (T . T) | <T> | A                                 terms
```

The pieces:

- **Passive data.** Primitive data `d` (numbers, say), the empty list `()`, the special atom `#ignore`,
  and pairs `(T1 . T2)`. A pair is *only data*: it is not a function call. As in Lisp, `(T1 T2 T3)` is
  short for `(T1 . (T2 . (T3 . ())))`.
- **Variables** `x`. These are substitutable variables, as in the lambda calculus. vau-x has **no symbols
  and no environments**. Shutt removes them on purpose: without environments, a symbol could not get an
  evaluation rule that agrees with the larger calculi ([thesis section 9.3](%T#page=203)).
- **Combiners.** Primitive operatives `o`, and three kinds of **compound operative**:
  - `<vau x.T>` takes its whole operand tree, binds it to `x`, and continues as `T`. It is the vau-x
    version of `lambda x. T`. Only this form binds a variable.
  - `<vau0.T>` accepts only the empty operand list `()`, and then continues as `T`.
  - `<vau2.T>` takes a pair of operands apart, one piece at a time (currying).
- **Applicatives** `<T>`. An applicative wraps an underlying combiner `T`. Calling it first evaluates the
  operands, then passes the results to `T`.
- **Active terms.** `[eval T]` means "evaluate `T`". `[combine T1 T2]` means "call combiner `T1` with
  operand tree `T2`". These are the only places where computation happens. They are computation states,
  not source text.

## Why it matters

The lambda calculus has one form, `(T1 T2)`, that is both data and a call. vau-x splits it into three:
the pair `(T1 . T2)` (data), `[eval ...]` (a request to evaluate), and `[combine ...]` (a call). This split
is what lets fexprs and a useful equational theory live together. See [Start](#/node/Start).

## In the Lean

`Vau.Term` has one constructor per form: `var n`, `dat n` (primitive data `d`), `prim n` (primitive
operative `o`), `ign` (`#ignore`), `nil` (`()`), `vau t`, `vau0 t`, `vau2 t`, `pair a b`, `wrap t`
(the applicative `<t>`), `eval t` and `comb a b` (`[combine a b]`).

Two choices are this project's:

- **De Bruijn indices.** A variable is a number: `var 0` is the variable bound by the nearest enclosing
  `vau`, `var 1` the next one out, and so on. So `<vau x.<vau y.x>>` is `vau (vau (var 1))`. Terms that
  differ only in the names of bound variables are the same Lean term.
- **Primitives are numbered, with no delta-rules.** `dat n` and `prim n` are indexed by natural
  numbers. A primitive operative has no rule of its own in this formalization.
"""),
     [q("Which of these is an active term?",
        ["`(T1 . T2)`", "`[combine T1 T2]`", "`<vau x.T>`", "`#ignore`"],
        1, "Active terms are `[eval T]` and `[combine T1 T2]`. A pair is passive data; `<vau x.T>` is a self-evaluating compound operative; `#ignore` is an atom."),
      q("Does pure vau-x calculus have symbols and environments?",
        ["Yes, both", "No: it has substitutable variables instead", "Only environments", "Only symbols"],
        1, "Shutt removes environments and symbols in vau-x (thesis (9.16) and (9.17)) and uses substitutable variables `x` as in the lambda calculus."),
      q("What does `<T>` denote in vau-x?",
        ["A quoted term", "An applicative whose underlying combiner is `T`", "A pair", "A primitive operative"],
        1, "`<T>` wraps combiner `T` as an applicative: calling it evaluates the operands first (rule combine-wrap)."),
      q("Which compound operative binds a variable?",
        ["`<vau0.T>`", "`<vau2.T>`", "`<vau x.T>`", "`<T>`"],
        2, "Only `<vau x.T>` binds `x` in `T`. `<vau0.T>` and `<vau2.T>` bind nothing; they take the operand tree apart."),
      q("Is the list `(T1 T2)` a function call in vau-x?",
        ["Yes, always", "No: it is the pair `(T1 . (T2 . ()))`, which is data until it is inside `[eval ...]`", "Only if `T1` is a variable", "Only if `T2` is a value"],
        1, "Lists are abbreviations for nested pairs, and pairs are passive. The rule eval-pair turns `[eval (T1 . T2)]` into a combination.")],
     caveats=[
         "The ASCII notation is this site's. Shutt uses the Greek letter vau and angle brackets.",
         "Primitive data and primitive operatives are parameters of the calculus: Shutt does not fix them. The Lean indexes both by natural numbers and gives primitive operatives no delta-rules.",
         "Terms are compared up to renaming of bound variables (alpha-equivalence), as Shutt states for vau-x. The Lean gets this for free from de Bruijn indices.",
     ])

# ---------------------------------------------------------------- 3. Values
node("IsValue",
     "Self-evaluating terms and values",
     "Self-evaluating terms `S` are the atoms and the three compound operatives. A value `V` is any term whose "
     "active subterms all sit inside an operative.",
     L("""
## Plain English

Two sets of terms matter for the reduction rules ([thesis (9.25)](%T#page=206)).

**Self-evaluating terms `S`.** These evaluate to themselves (rule eval-self):

- primitive data `d`, primitive operatives `o`, `#ignore`, and `()`;
- the compound operatives `<vau x.T>`, `<vau0.T>` and `<vau2.T>`, whatever their body `T` is.

Not in `S`: variables `x`, pairs `(T1 . T2)`, applicatives `<T>`, and active terms. Each of these has its
own rule, or no rule at all (a variable just waits to be substituted).

**Values `V`.** Shutt defines a value as a term in which every active subterm is within an operative.
In words: a value has no computation left to do *now*. Any `[eval ...]` or `[combine ...]` in it is inside
the body of an operative, where it waits until the operative is called.

| term | value? | why |
|---|---|---|
| `5`, `()`, `#ignore`, `x` | yes | no active subterm at all |
| `(1 . (2 . ()))` | yes | a pair of values |
| `<vau x.[eval x]>` | yes | the active subterm is inside the operative's body |
| `([eval 1] . 2)` | no | `[eval 1]` is not inside an operative |
| `<[eval 1]>` | no | the body of an applicative is not protected: it must be a value too |

**Why values matter.** The rule beta-vau substitutes the operand into the body only when the operand is a
value. Together with combine-wrap, this gives *eager* argument evaluation: each argument is reduced to a
value before the call goes on. Variables count as values, so substitution must only put values where
variables were; then every value stays a value after substitution.

A value is not the same as a normal form. `<vau x.[eval 5]>` is a value, but it still contains a redex
inside its body, and the calculus may reduce it there.

## In the Lean

`Vau.IsValue` is an inductive predicate. Its constructors say: variables, atoms and the three compound
operatives are values whatever their bodies are; a pair is a value if both parts are; `wrap t` is a value
if `t` is. There is no constructor for `eval` or `comb`. `Vau.SelfEval` is the set `S`; the lemma
`SelfEval.isValue` says every self-evaluating term is a value.
"""),
     [q("Is the variable `x` self-evaluating?",
        ["Yes", "No, but it is a value", "No, and it is not a value", "Only after substitution"],
        1, "`S` does not contain variables, so `[eval x]` has no rule. But `x` has no active subterm, so it is a value."),
      q("Is `<vau x.[eval x]>` a value?",
        ["Yes: its active subterm is inside an operative", "No: it contains `[eval x]`", "Only if `x` is bound", "Only after one reduction step"],
        0, "A value may contain active subterms, if they are inside an operative's body."),
      q("Is `([eval 1] . 2)` a value?",
        ["Yes", "No: `[eval 1]` is an active subterm that is not inside an operative", "Yes, because pairs are data", "Only if 2 is a value"],
        1, "Pairs are not operatives, so they do not protect their active subterms."),
      q("Why does beta-vau require its operand to be a value?",
        ["To make terms shorter", "So that arguments are evaluated eagerly and substitution keeps values as values", "Because variables are not values", "Because pairs cannot be substituted"],
        1, "Shutt substitutes only values. Variables are values, so putting a non-value in place of a variable could turn a value into a non-value.")],
     caveats=[
         "\"Within an operative\" is read here as: inside the body of one of the three compound operatives. Primitive operatives are atoms and have no subterms.",
         "For vau-e, Shutt notes that a lazy variant (substituting any term) is also possible. For vau-x he substitutes only values, so that substitution keeps values as values (thesis p. 203). The Lean follows vau-x.",
     ])

# ---------------------------------------------------------------- 4. Substitution
node("inst",
     "Free variables and substitution of values",
     "`T[x <- V]` replaces each free occurrence of the variable `x` in `T` by the value `V`, renaming bound "
     "variables so that nothing is captured. Only `<vau x.T>` binds a variable.",
     L("""
## Plain English

**Free variables.** As in the lambda calculus, `FV(T)` is the set of variables of `T` that are not bound.
The only binder is `<vau x.T>`: it binds `x` in `T`.

**Substitution** ([thesis (9.19)](%T#page=204)), in ASCII:

```
x1[x2 <- V]           =  V                                if x1 = x2
                      =  x1                               otherwise
<vau x1.T>[x2 <- V]   =  <vau x3.((T[x1 <- x3])[x2 <- V])>
                         where x3 is not x2, and x3 is not free in T or in V
any other form        =  the same form, with [x2 <- V] applied to each immediate subterm
```

"Any other form" covers everything that does not bind: atoms, pairs, applicatives, `<vau0.T>`,
`<vau2.T>`, `[eval T]` and `[combine T1 T2]`.

The renaming step is the usual guard against *capture*. Example: in `<vau x.[combine x y]>[y <- x]`, the
`x` that comes in must not be caught by the binder. The result is `<vau z.[combine z x]>` for a fresh
`z`. Shutt's rule always renames to a fresh `x3`; since terms are compared up to renaming of bound
variables, this changes nothing.

**Only values are substituted.** Shutt defines `T[x <- V]` only for values `V`
(see [Values](#/node/IsValue)). The rule beta-vau is the only rule that substitutes.

## In the Lean

With de Bruijn indices there are no names to rename. `Vau.inst t v` is `t[0 <- v]`: it replaces the
variable `var 0` (the one bound by the `vau` whose body is `t`) by `v`, and lowers the other free
indices by one. It is defined as `subst (scons v var) t`, where [subst](#/node/subst) substitutes for
every free variable at once, and [scons](#/node/scons) builds the substitution "0 goes to `v`, `n + 1`
goes to `var n`". Under a binder, [up](#/node/up) shifts the substituted terms with
[rename](#/node/rename) so that nothing is captured.

`inst` is defined for every `v`. The rule beta-vau in [Top](#/node/Top) uses it only when `v` is a
value, as in the thesis. `Vau.FreeIn n t` says that index `n` is free in `t`.
"""),
     [q("Which construct binds a variable?",
        ["`[eval T]`", "`<vau x.T>`", "`<vau2.T>`", "`(T1 . T2)`"],
        1, "Only `<vau x.T>` binds a variable."),
      q("What is `[combine x x][x <- 5]`?",
        ["`[combine x x]`", "`[combine 5 x]`", "`[combine 5 5]`", "`5`"],
        2, "Substitution goes into both subterms of `[combine ...]` and replaces each free `x`."),
      q("What is `<vau x.[combine x y]>[y <- x]`, up to renaming?",
        ["`<vau x.[combine x x]>`", "`<vau z.[combine z x]>`", "`<vau x.[combine x y]>`", "`[combine x x]`"],
        1, "The bound `x` is renamed to a fresh `z` first, so the incoming free `x` is not captured."),
      q("What may be substituted for a variable in vau-x?",
        ["Any term", "Only values", "Only variables", "Only active terms"],
        1, "Shutt defines substitution only of values, so that values stay values.")],
     caveats=[
         "The Lean uses de Bruijn indices, so renaming disappears from the definitions. The Lean does not prove that its `inst` agrees with Shutt's named substitution (9.19); that correspondence is the usual one between named terms up to alpha-equivalence and de Bruijn terms, and is not checked here.",
     ])

# ---------------------------------------------------------------- 5. ReductionSchemata
node("Top",
     "The reduction rules of vau-x",
     "Seven general rules (eval-self, eval-pair, eval-wrap, combine-wrap, beta-vau, parse-nil, parse-pair) "
     "say how an `[eval ...]` or `[combine ...]` term takes one step. Shutt also allows delta-rules; the Lean has none.",
     L("""
## Plain English

These are Shutt's schemata for vau-x ([thesis (9.25)](%T#page=206)). The names on the left are this
project's names.

| rule | one step | thesis |
|---|---|---|
| eval-self | `[eval S]  ->  S` | (9.25S) |
| eval-pair | `[eval (T1 . T2)]  ->  [combine [eval T1] T2]` | (9.25p) |
| eval-wrap | `[eval <T>]  ->  <[eval T]>` | (9.25a) |
| combine-wrap | `[combine <T0> (T1 ... Tm)]  ->  [combine T0 ([eval T1] ... [eval Tm])]` | (9.25gamma) |
| beta-vau | `[combine <vau x.T> V]  ->  T[x <- V]` | (9.25beta) |
| parse-nil | `[combine <vau0.T> ()]  ->  T` | (9.25vau0) |
| parse-pair | `[combine <vau2.T0> (T1 . T2)]  ->  [combine [combine T0 T1] T2]` | (9.25vau2) |

Shutt also allows **delta-rules** for primitive operatives, `[combine o P1] -> P3`, under conditions
that keep the calculus confluent (thesis Definition 9.22). They are not part of the seven general rules.

**Evaluation rules.**

- *eval-self*: atoms and compound operatives evaluate to themselves. There is **no rule for
  `[eval x]`**: a variable waits until substitution replaces it.
- *eval-pair*: to evaluate a pair, evaluate its first element (the operator), then combine the result with
  the rest **unevaluated**. The combiner decides what happens to the operands. This one rule is where
  fexprs come from.
- *eval-wrap*: to evaluate an applicative, evaluate the combiner inside it.

**Combination rules.**

- *combine-wrap*: calling an applicative on a proper list of operands `(T1 ... Tm)` (here `m` may be 0)
  puts an `[eval ...]` around each operand and passes the list to the underlying combiner.
- *beta-vau*: calling `<vau x.T>` substitutes the operand tree for `x` in the body. The operand must be a
  [value](#/node/IsValue), so any `[eval Ti]` from combine-wrap must finish first.
- *parse-nil*: `<vau0.T>` accepts the empty list and continues as `T`.
- *parse-pair*: `<vau2.T0>` takes a pair of operands apart: `T0` gets `T1`, and the combiner that comes
  out gets `T2`. This is currying. `T1` and `T2` do not have to be values.

A rule may be used on any subterm, not only at the top. That is the [compatible closure](#/node/Step).
Several redexes can be present at once, so reduction is not deterministic. Shutt's thesis shows that the
any two reduction paths can be joined again (Church-Rosser), and the Lean proves this for these rules:
[confluence](#/node/confluence).

In the Lean, `Vau.Top` has one constructor per rule: `evalSelf`, `evalPair`, `evalWrap`, `beta`,
`combWrap`, `parsePair` and `parseNil`. combine-wrap uses [IsList](#/node/IsList) and
[evalList](#/node/evalList); beta-vau uses [inst](#/node/inst) and [IsValue](#/node/IsValue).

## A worked example

Let `F = <vau2.<vau x.<vau0.x>>>`. It is an operative that takes exactly one operand and returns it.

As an **operative** (a fexpr), `F` returns its operand unevaluated:

```
[eval (F (F 7))]
-> [combine [eval F] ((F 7))]                 eval-pair
-> [combine F ((F 7))]                        eval-self
-> [combine [combine <vau x.<vau0.x>> (F 7)] ()]   parse-pair
-> [combine <vau0.(F 7)> ()]                  beta-vau   ((F 7) is a value)
-> (F 7)                                      parse-nil
```

As an **applicative** `<F>`, the operand is evaluated first:

```
[eval (<F> (F 7))]
-> [combine [eval <F>] ((F 7))]               eval-pair
-> [combine <[eval F]> ((F 7))]               eval-wrap
-> [combine <F> ((F 7))]                      eval-self (inside)
-> [combine F ([eval (F 7)])]                 combine-wrap
-> ... [eval (F 7)] reduces to 7 ...          (as above, inside the term)
-> [combine F (7)]
-> [combine [combine <vau x.<vau0.x>> 7] ()]  parse-pair
-> [combine <vau0.7> ()]                      beta-vau
-> 7                                          parse-nil
```

The same operative gives `(F 7)` or `7`, depending only on whether it is wrapped. In Shutt's words from
the NEPLS talk, Lisp `lambda` "constructs fexprs with applicative wrappers around them"
([talk script](%N)).
"""),
     [q("Which rule turns `[eval (T1 . T2)]` into `[combine [eval T1] T2]`?",
        ["eval-self", "eval-pair", "combine-wrap", "parse-pair"],
        1, "eval-pair evaluates the operator and passes the operand tree `T2` on, unevaluated."),
      q("Under eval-pair, is the operand tree `T2` evaluated?",
        ["Yes, always", "No: it is passed unevaluated, and the combiner decides", "Only if it is a value", "Only if `T1` is a variable"],
        1, "Operands are evaluated only if the combiner is an applicative (combine-wrap) or if an operative's body asks for it."),
      q("What must the operand be for beta-vau to fire?",
        ["Any term", "A value", "A variable", "The empty list"],
        1, "`[combine <vau x.T> V] -> T[x <- V]` requires a value `V`. This gives eager argument evaluation."),
      q("What does `[combine <vau0.T> ()]` reduce to?",
        ["`()`", "`T`", "`[eval T]`", "Nothing: it is stuck"],
        1, "parse-nil: `<vau0.T>` accepts the empty list and continues as `T`."),
      q("Which of these terms has no rule at its top?",
        ["`[eval 5]`", "`[eval x]`", "`[eval <vau0.T>]`", "`[eval (T1 . T2)]`"],
        1, "Variables are not self-evaluating, and vau-x has no symbol lookup. `[eval x]` waits until `x` is substituted."),
      q("In the worked example, what does `[eval (F (F 7))]` reduce to when `F` is not wrapped?",
        ["`7`", "`(F 7)`", "`F`", "`()`"],
        1, "An unwrapped operative gets its operand unevaluated, so it returns the data `(F 7)`.")],
     caveats=[
         "The rule names are this project's. Shutt numbers the schemata (9.25S), (9.25p), (9.25a), (9.25gamma), (9.25beta), (9.25vau0), (9.25vau2) and (9.25delta).",
         "combine-wrap needs a proper list of operands `(T1 ... Tm)`. An applicative called on an improper operand tree has no rule.",
         "The worked example is ours, built in the style of the NEPLS talk's traced reduction. It uses only the seven general rules. The Lean checks both results with the evaluator of eval_is_reduction: `Vau.run_F_F7` (unwrapped, result `(F 7)`) and `Vau.run_wrapF_F7` (wrapped, result `7`), in `Vau/Eval.lean`.",
         "The Lean has the seven general rules and no delta-rules. Every result on this site is about that calculus.",
     ])

# ---------------------------------------------------------------- 11 (informal). Environments
node("VauE.Env",
     "Environments (vau-e)",
     "In Shutt's vau-e calculus an environment is a finite list of bindings of symbols to terms, and "
     "`[eval s e]` looks up the symbol `s` in `e`. Pure vau-x has no environments; the Lean models vau-e separately.",
     L("""
## Plain English

Pure vau-x has **no environments**. But real Kernel code, and Shutt's larger calculi vau-e and vau-p, do.
This node gives what is needed to read [`$vau`](#/node/VauE.vau_call). It follows Shutt's pure
**vau-e calculus** ([thesis section 9.1](%T#page=195)).

**What an environment is.** A list of bindings `s <- T` of symbols to terms. We write it
`{{s1 <- T1, ..., sn <- Tn}}`. The bindings are kept in order by symbol, and no symbol is bound twice.
Shutt puts these rules in the grammar, so that two environments with the same bindings are the same term.

**Where environments go.** In vau-e, the active terms carry an environment:
`[eval T e]` (evaluate `T` in `e`) and `[combine T1 T2 e]` (call `T1` on `T2`, from the caller's
environment `e`). Two evaluation rules use it ([thesis (9.7)](%T#page=199)):

```
[eval s e]          ->  lookup(s, e)              if s is bound in e
[eval (T1 . T2) e]  ->  [combine [eval T1 e] T2 e]
```

The second rule is eval-pair with an environment: the caller's environment travels with the
combination, so the combiner can use it.

**Joining environments.** `e1 . e2` puts the bindings of `e1` in front of those of `e2`. If both bind the
same symbol, the binding from `e1` wins. This is how a local environment shadows an outer one.

**Environments are encapsulated.** An environment is a value and evaluates to itself, but a fexpr cannot
take it apart. Shutt points out (thesis chapter 15) that this is one reason why his fexprs, unlike Wand's,
leave a nontrivial theory. Dale Schumacher's actor implementation of Kernel shows the same idea in
another way: an environment is an actor that answers `#lookup` messages, and passes a lookup it cannot
answer to its parent ([Fexpr the Ultimate Lambda](%D1)).

## In the Lean

The file `Vau/Env/Syntax.lean` (namespace `VauE`) defines vau-e terms and environments together:
`VauE.Term` has constructors for primitive data, primitive operatives (`$vau`, `$wrap`, `$unwrap`,
`$eval`, `$list*`), symbols, `#ignore`, `()`, environments (`env e`), compound operatives
`oper ptree eparm body senv`, pairs, applicatives, `eval t e` and `comb t1 t2 e`. `VauE.Env` is
`List (Prod Nat Term)`: a list of bindings `(s, t)`.

- `Env.lookup s e`: the term bound to `s` by the **first** binding of `s` in `e`.
- `Env.join e1 e2`: the bindings of `e1`, then those of `e2`. `Env.lookup_join` proves that a lookup
  in `e1 . e2` tries `e1` first, then `e2`, which is Shutt's "left wins".
- `ematch ptree t`: Shutt's `match` (9.6), with the check that the two halves of a pair parameter
  tree share no symbol.

**One difference from Shutt.** Shutt keeps the bindings sorted, with no symbol bound twice, so two
environments with the same bindings are the same term. The Lean uses plain lists. Every lookup gives
the same answer as Shutt's, but two lists of the same bindings in a different order are different
terms, so the Lean's equational theory of vau-e is weaker than Shutt's. Symbols are numbers.
"""),
     [q("Does pure vau-x have environments?",
        ["Yes", "No: environments come from vau-e and vau-p", "Only the empty environment", "Only for primitive operatives"],
        1, "Shutt removes environments in vau-x. The Lean models vau-e in a separate namespace, `VauE`."),
      q("What does `[eval s e]` reduce to in vau-e?",
        ["`s`", "`lookup(s, e)`, if `s` is bound in `e`", "`e`", "`[combine s e]`"],
        1, "Symbol evaluation is lookup in the environment of the eval."),
      q("If `e1` and `e2` both bind `s`, which binding does `e1 . e2` keep?",
        ["The one from `e2`", "The one from `e1`", "Both", "Neither"],
        1, "In Shutt's definition the left environment wins, which gives shadowing."),
      q("Can a fexpr take an environment apart in Shutt's calculi?",
        ["Yes", "No: environments are encapsulated", "Only the static environment", "Only in vau-x"],
        1, "Environments and compound operatives are encapsulated objects. Fexprs can take apart pairs and atoms only.")],
     caveats=[
         "The Lean environments are unsorted lists with first-binding lookup, not Shutt's normalized environments. Lookups agree; equality of environment terms does not.",
         "This node follows the pure vau-e calculus. Kernel's environments are mutable and have parents (`$define!`); mutation is not covered here (Shutt treats it in thesis chapter 12).",
         "The `{{...}}` notation is this site's ASCII for Shutt's double angle brackets.",
     ])

# ---------------------------------------------------------------- 12 (informal). $vau static and dynamic environment
node("VauE.vau_call",
     "$vau: the static and the dynamic environment",
     "Evaluating `($vau ptree eparm body)` builds a compound operative that keeps the environment it was built in "
     "(the static environment). When it is called, it can bind the caller's environment (the dynamic environment) "
     "to `eparm`, or refuse it with `#ignore`.",
     L("""
## Plain English

In Kernel, `$vau` builds fexprs. A call has the form `($vau ptree eparm body)`:

- `ptree` is a *parameter tree*: a symbol, `()`, `#ignore`, or a pair of parameter trees. No symbol may
  appear twice.
- `eparm` is usually a symbol or `#ignore`; it names the caller's environment. (In the calculus it
  may be any parameter tree, matched against the environment.)
- `body` is the expression to evaluate when the operative is called.

**Building the operative.** In Shutt's vau-e calculus, `$vau` is a primitive operative with this
delta-rule ([thesis (9.12)](%T#page=201)):

```
[combine $vau (V1 V2 V3) V4]  ->  <operative V1 V2 V3 V4>
```

`V4` is the environment in which the `$vau` combination was evaluated. The new operative keeps it: it is
the operative's **static environment**. The operands `V1 V2 V3` (parameter tree, environment parameter,
body) are taken as they are, unevaluated.

**Calling the operative** ([thesis (9.7beta)](%T#page=199)):

```
[combine <operative V1 V2 T e1> V3 e2]
  ->  [eval T match((V1 . V2), (V3 . e2)) . e1]       if the match is defined
```

In words: match the parameter tree `V1` against the operands `V3` (still unevaluated), and match the
environment parameter `V2` against `e2`, the caller's **dynamic environment**. Put the resulting
bindings in front of the static environment `e1`. Evaluate the body `T` there.

Matching is simple: a symbol binds whatever it meets; `#ignore` matches anything and binds nothing; `()`
matches only `()`; a pair matches a pair, part by part.

**Static versus dynamic.** Using the static environment for the body gives static (lexical) scope, as in
Scheme. Old Lisps used the dynamic environment and got dynamic scope. `$vau` uses the static environment,
and gives the dynamic one only on request, through `eparm`. Schumacher puts it this way: Shutt's `$vau`
"provides controlled access to both environments" ([Fexpr the Ultimate Lambda](%D1)). With `#ignore` as
`eparm`, the body cannot reach the caller's environment at all. Shutt notes that ignoring the dynamic
environment helps hygiene and proper tail recursion (thesis section 4.2).

**Small examples** from Shutt's thesis (section 4.2):

- `($vau (x) #ignore x)` returns its one operand unevaluated: a quote operative.
- `(wrap ($vau () e e))` returns the caller's environment (`get-current-environment`).
- `(wrap ($vau x #ignore x))` returns the list of its evaluated operands (`list`).

**wrap.** The delta-rule `[combine $wrap (V1) V2] -> <applicative V1>` wraps a combiner. Calling the
applicative evaluates each operand in the caller's environment `e`, then calls the underlying combiner:
`[combine <applicative T> (T1 ... Tm) e] -> [combine T ([eval T1 e] ... [eval Tm e]) e]`.
This is combine-wrap with environments.

**Back to vau-x.** vau-x has no rule for `$vau`: `$vau` needs symbols for its parameter tree, and vau-x
has none. In vau-x one writes the compound operatives `<vau x.T>`, `<vau0.T>` and `<vau2.T>` directly.
Shutt's vau-p calculus joins the two worlds: `$vau` binds parameters to substitutable variables when it
builds the operative, and the operands are substituted when it is called.

## The Lean statement

```
theorem vau_call {p b v : Term} {d : Nat} {e1 e2 m : Env} (hp : IsValue p) (hv : IsValue v)
    (hd : disjoint (syms p) [d] = true) (hm : ematch p v = some m) :
    Steps (comb (oper p (sym d) b (env e1)) v (env e2))
      (eval b (env (Env.join (Env.join m [(d, env e2)]) e1)))
```

In words: call the operative `<operative p d b e1>` on the operand tree `v` from the dynamic
environment `e2`. If `p` matches `v` with bindings `m`, and `d` is not also in `p`, the body `b` is
evaluated in `m`, then `d <- e2`, then the static environment `e1`. `vau_call_lookup` spells out
lookups in that environment: a symbol not bound by `p` is `e2` if it is `d`, and otherwise is
looked up in `e1`. The rules themselves are in `VauE.Top` (`beta` and `deltaVau`).
"""),
     [q("Which environment becomes the static environment of the operative built by `($vau (x) e body)`?",
        ["The caller's environment at each later call", "The environment in which the `$vau` combination is evaluated", "The empty environment", "The global environment"],
        1, "In `[combine $vau (V1 V2 V3) V4] -> <operative V1 V2 V3 V4>`, `V4` is the environment of the `$vau` call."),
      q("Where is the body of a compound operative evaluated?",
        ["In the caller's environment", "In the static environment, with the parameter bindings in front", "In the empty environment", "Nowhere: it is returned as data"],
        1, "`[eval T match(...) . e1]`: the match bindings come first, then the static environment `e1`."),
      q("What happens when the environment parameter is `#ignore`?",
        ["The body is not evaluated", "The caller's environment is not bound, so the body cannot reach it", "The operands are evaluated", "The static environment is dropped"],
        1, "`#ignore` matches anything and binds nothing."),
      q("Are the operands evaluated before a compound operative is called?",
        ["Yes", "No: they are matched against the parameter tree unevaluated", "Only the first one", "Only if they are symbols"],
        1, "That is what makes it an operative. To evaluate them first, wrap it."),
      q("Does pure vau-x have a reduction rule for `$vau`?",
        ["Yes, a delta-rule", "No: `$vau` needs symbols, which vau-x does not have", "Yes, beta-vau", "Only for `#ignore`"],
        1, "Shutt says no natural vau-x schema can be built for `$vau`.")],
     caveats=[
         "The Lean models Shutt's pure vau-e calculus in namespace `VauE`, with unsorted environments (see VauE.Env). It proves this one-step call rule, and separately confluence of vau-e (VauE.confluence).",
         "In vau-e the body of a compound operative is one expression; Kernel allows a sequence. Shutt explains that without side effects one expression is enough.",
         "Kernel creates a fresh child environment for each call, which matters once environments can be mutated. Pure vau-e uses the join `match(...) . e1` instead.",
     ])
