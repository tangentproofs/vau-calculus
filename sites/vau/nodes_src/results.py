# Step 3 nodes: the formalized results. Each node id is a Lean declaration in Vau/, and each text explains
# what that declaration says. Nothing here goes beyond the Lean statement; where the English is looser, a
# caveat says so. "%T" expands to the thesis PDF URL, "%N" to the NEPLS talk.
from _common import THESIS, NEPLS, make, q

NODES = []
node = make(NODES)

SCOPE = ("The Lean is about the concrete vau-x calculus with the seven general schemata and no delta-rules. "
         "It does not formalize Shutt's regular substitutive reduction systems (thesis chapter 13).")


def L(s):
    return s.replace("%T", THESIS).replace("%N", NEPLS)


# ---------------------------------------------------------------- Step (compatible closure)
node("Step",
     "One step: a rule may fire anywhere inside a term",
     "`Step t t'` holds when one of the seven rules fires at one position inside `t`, top or deep inside, "
     "and gives `t'`. It is the compatible closure of the rules.",
     L("""
## Plain English

Each rule in [Top](#/node/Top) is written for the top of a term, for example `[eval 5] -> 5`. But
`[eval 5]` can also sit deep inside a bigger term: in an operand list, or in the body of an operative.
A **context** `C[ ]` is a term with one hole. A relation is **compatible** if, whenever `M -> N`, also
`C[M] -> C[N]` for every context `C`. The **compatible closure** of a set of rules is the smallest
compatible relation that contains them ([thesis section 2.3](%T#page=53)).

So one step means: pick one subterm that matches the left side of one rule, and replace it by the right
side. Everything else stays as it is.

Two points are special to vau-x:

- **Steps inside operands are allowed.** Because evaluation is explicit, a step inside an operand is not
  an evaluation of that operand. `(5 . [eval 6]) -> (5 . 6)` is a step.
- **Steps inside an operative body are allowed.** `<vau x.[eval 5]> -> <vau x.5>`, like reducing under
  a lambda.

## In the Lean

`Vau.Step` has a constructor `top` (a rule of `Top` at the top) and one congruence constructor per place
where a subterm can sit: `vau`, `vau0`, `vau2`, `wrap`, `eval`, `pairL`, `pairR`, `combL`, `combR`.

Two lemmas check that this is the compatible closure:

- `Step.plug`: a step inside any one-hole context [Ctx](#/node/Ctx) is a step of the whole term;
- `Step.exists_ctx`: every step is one rule of `Top` inside some one-hole context.

[Steps](#/node/Steps) is zero or more steps, and [Conv](#/node/Conv) is the equational theory.
"""),
     [q("What does it mean that the step relation is compatible?",
        ["Every term has a step", "If `M -> N`, then `C[M] -> C[N]` for every context `C`", "Steps never change the size of a term", "Two different steps always give the same result"],
        1, "Compatibility lets a rule fire at any position. It is not determinism, and it is not confluence."),
      q("Is `(5 . [eval 6]) -> (5 . 6)` a step of vau-x?",
        ["No: operands are never reduced", "Yes: eval-self fires inside the pair (constructor `pairR` around `top`)", "Only if the pair is evaluated first", "Only in vau-e"],
        1, "In Lean: `Step.pairR _ (Step.top (Top.evalSelf (SelfEval.dat 6)))`."),
      q("Which lemma says that every step is a rule inside a one-hole context?",
        ["`Step.plug`", "`Step.exists_ctx`", "`confluence`", "`Run.toSteps`"],
        1, "`Step.exists_ctx` gives the context, the rule instance, and the two equations. `Step.plug` is the other direction.")],
     caveats=[SCOPE])

# ---------------------------------------------------------------- eval_is_reduction (headline)
node("eval_is_reduction",
     "Evaluation is a special case of reduction",
     "If an evaluator, defined on its own like a Lisp interpreter, runs `[eval t]` to `v`, then "
     "`[eval t] ->* v` by the vau-x rules, and `v` is a value.",
     L("""
## Plain English

Shutt's 2007 NEPLS talk says that explicit evaluation "makes term evaluation a special case of term
reduction" ([talk script](%N)). To make that sentence checkable, we need two things to compare:

1. **An evaluator.** [Run](#/node/Run) is a big-step evaluator for vau-x, written like a Lisp
   interpreter: to evaluate a pair, evaluate the operator and call the combiner on the operand tree; an
   applicative evaluates each operand first; an operative substitutes its operand into its body. It is
   defined by its own rules, not from the reduction relation. Its cases mirror the seven rules one for
   one, as big-step rules.
2. **Reduction.** [Steps](#/node/Steps): zero or more steps of the [compatible closure](#/node/Step)
   of the seven rules.

The theorem says that the evaluator is a special case of reduction: **every evaluation is a reduction
sequence**, and it ends in a value.

## The Lean statement

```
theorem eval_is_reduction {t v : Term} (h : Run (eval t) v) : Steps (eval t) v /\\ IsValue v
```

It follows from `Run.toSteps` (every run, of any term, is a reduction sequence) and `Run.isValue` (every
result is a value), both proved by induction on the run.

## What it does not say

- It is **one direction**. Reduction has many steps that `Run` never takes (for example, steps inside an
  operative body), so the converse is false and is not claimed.
- It does not say that `Run` is Shutt's evaluator. The thesis gives no operational semantics for vau-x;
  `Run` is this project's.
- It does not say that `Run` terminates or is deterministic.

## A check that it is not empty

`Vau/Eval.lean` runs the worked example of [Top](#/node/Top) with `Run`. With
`F = <vau2.<vau x.<vau0.x>>>`: `run_F_F7` shows `[eval (F (F 7))]` runs to the data `(F 7)`, and
`run_wrapF_F7` shows `[eval (<F> (F 7))]` runs to `7`.
"""),
     [q("Which direction does `eval_is_reduction` prove?",
        ["Every reduction is an evaluation", "Every evaluation by `Run` is a reduction sequence", "Evaluation and reduction are the same relation", "Reduction never terminates"],
        1, "The hypothesis is `Run (eval t) v`; the conclusion is `Steps (eval t) v`."),
      q("Where does the evaluator `Run` come from?",
        ["From thesis section 9.3", "It is this project's definition, made independently of the rules", "From Wand's paper", "From Schumacher's Humus code"],
        1, "Shutt gives no operational semantics for vau-x. `Run` is ours, and the node says so."),
      q("Besides the reduction sequence, what else does the theorem give about `v`?",
        ["That it is a normal form", "That it is a value (`IsValue v`)", "That it is primitive data", "That it is unique"],
        1, "The second conjunct is `IsValue v`. A value may still contain redexes inside an operative body, so it need not be a normal form."),
      q("What axioms does `#print axioms Vau.eval_is_reduction` report?",
        ["`propext` and `Quot.sound`", "None", "`Classical.choice`", "`sorryAx`"],
        1, "The proof is a plain induction; Lean reports that it does not depend on any axioms.")],
     caveats=[
         "The cases of `Run` mirror the seven rules one for one, as big-step rules. So the theorem checks that this big-step evaluator agrees with small-step reduction, in one direction. It is not independent evidence about any evaluator of Shutt's.",
         "The quoted phrase is from Shutt's NEPLS talk script. The talk speaks informally; this theorem is one precise version chosen by this project, not by Shutt.",
         SCOPE,
     ])

# ---------------------------------------------------------------- embed (lambda embedding)
node("embed",
     "The lambda calculus inside vau-x",
     "Shutt's map sends `lambda x.M` to the operative `<vau x.M'>` and an application to `[combine M' N']`. "
     "The Lean proves that it turns call-by-value lambda steps into vau-x steps, and makes no new ones.",
     L("""
## Plain English

In [thesis section 15.4](%T#page=365), Shutt points out that inside a vau calculus there is a corner
that he describes as isomorphic to the lambda calculus: terms built only from variables, compound operatives
`<vau x.T>` and `[combine ...]` terms. His map (15.28), written here for vau-x:

| lambda term | vau-x term |
|---|---|
| `x` | `x` |
| a constant `c` | primitive data `c` (this project's choice) |
| `(M N)` | `[combine M' N']` |
| `lambda x.M` | `<vau x.M'>` |

A lambda abstraction becomes an **operative**, not an applicative. In Shutt's words, the combiners of
the lambda calculus "always were, essentially, fexprs".

beta-vau fires only when the operand is a **value**. The image of a variable, a constant or an
abstraction is a value; the image of an application is not. So the image reduces like the
**call-by-value** lambda calculus (Plotkin's lambda-v), where beta fires only on a value argument.

## In the Lean

- [LTerm](#/node/LTerm): lambda terms with constants, de Bruijn indices.
- [LStep](#/node/LStep): one call-by-value beta step, at any position (including under a lambda).
- `Vau.embed : LTerm -> Term`, by the table above.

Proved:

- `embed_step`: if `LStep M N`, then `Step (embed M) (embed N)` (**simulation**);
- `step_embed`: if `Step (embed M) T`, then `T = embed N` for some `N` with `LStep M N` (**no new
  steps**);
- `embed_injective`, `embed_inst` (embedding commutes with substitution), and `steps_embed` (the
  many-step version of `step_embed`).
"""),
     [q("What does Shutt's map send `lambda x.M` to?",
        ["The applicative `<<vau x.M'>>`", "The operative `<vau x.M'>`", "`[eval M']`", "The pair `(x . M')`"],
        1, "`embed (.lam t) = vau (embed t)`."),
      q("Why does the image behave call-by-value?",
        ["Because vau-x has no variables", "Because beta-vau needs a value operand, and the image of an application is not a value", "Because combine-wrap evaluates every operand", "Because the Lean says so without proof"],
        1, "`isValue_of_embed` and `embed_isValue` connect the two notions of value; `step_embed` shows no other steps exist."),
      q("What does `step_embed` say?",
        ["Every lambda step is a vau-x step", "Every vau-x step from `embed M` is the image of a lambda-v step from `M`", "`embed` is surjective", "vau-x is confluent"],
        1, "That is the 'no new steps' half. The 'simulation' half is `embed_step`.")],
     caveats=[
         "Map (15.28) in the thesis is written for vau-p, with an extra environment argument. Shutt says the point is clearer in vau-x, which has no environments; this vau-x version is our adaptation.",
         "Shutt says the image has the beta-rule and the same equational theory as the lambda calculus. Because beta-vau needs a value operand, the Lean shows that for vau-x the image has exactly the theory of call-by-value lambda (lambda-v), which is strictly weaker than full beta: for example `(lambda x.c) Omega = c` holds with full beta but not in lambda-v.",
         "In thesis (15.27) the constants are combiners such as `*` and `+`. Mapping constants to primitive data is this project's choice; with no delta-rules it changes no result.",
     ])

# ---------------------------------------------------------------- conservative_extension (headline)
node("conservative_extension",
     "vau-x conservatively extends the call-by-value lambda calculus",
     "Two lambda terms are equal in the call-by-value lambda calculus if and only if their images are equal "
     "in vau-x. Adding fexprs loses no lambda-v equation and adds none.",
     L("""
## Plain English

A calculus `B` **conservatively extends** a calculus `A` (through a map from `A` to `B`) if `B` proves an
equation between images of `A` terms exactly when `A` proves it.

This is the opposite of Wand's triviality result, where adding fexprs destroys the lambda calculus
equations. Shutt writes that his calculus "conservatively extends" its lambda-isomorphic subcalculus
([thesis section 15.4](%T#page=366)).

## The Lean statement

```
theorem conservative_extension (M N : LTerm) : LConv M N <-> Conv (embed M) (embed N)
```

- [LConv](#/node/LConv) is the equational theory of the call-by-value lambda calculus: the equivalence
  closure of [LStep](#/node/LStep).
- [Conv](#/node/Conv) is the equational theory of vau-x: the equivalence closure of
  [Step](#/node/Step).
- [embed](#/node/embed) is Shutt's map.

**How it is proved.** Left to right: each lambda-v step is a vau-x step (`embed_step`). Right to left: a
chain of vau-x equalities between `embed M` and `embed N` may pass through terms that are not images.
[confluence](#/node/confluence) gives a common reduct `u` of `embed M` and `embed N`. Every reduct of an
image is an image (`steps_embed`), so `u = embed P` and `u = embed Q` with `M ->* P` and `N ->* Q`. Since
`embed` is injective, `P = Q`, so `M` and `N` are equal in lambda-v.
"""),
     [q("What does conservative extension mean here?",
        ["vau-x has more terms than the lambda calculus", "Two lambda terms are equal in lambda-v iff their images are equal in vau-x", "vau-x has no new rules", "Every vau-x term is the image of a lambda term"],
        1, "That is exactly the `<->` in the statement."),
      q("Which half of the proof needs confluence of vau-x?",
        ["Left to right (lambda to vau-x)", "Right to left (vau-x to lambda)", "Neither", "Both equally"],
        1, "A vau-x equality chain may leave the image. Confluence gives a common reduct, which `steps_embed` pulls back."),
      q("Which lambda calculus is this about?",
        ["Call-by-name lambda calculus with full beta", "Call-by-value lambda calculus (beta only on value arguments)", "Simply typed lambda calculus", "Lambda calculus with eta"],
        1, "`LStep.beta` requires `v.IsValue`, as beta-vau does.")],
     caveats=[
         "Shutt states conservativity informally in section 15.4 about vau-p. This precise statement, for vau-x and call-by-value lambda, is this project's choice.",
         "`#print axioms Vau.conservative_extension` reports `propext` and `Quot.sound` (the second comes from function extensionality in the substitution lemmas).",
         SCOPE,
     ])

# ---------------------------------------------------------------- confluence (headline)
node("confluence",
     "Confluence of the vau-x rules",
     "If `t ->* s1` and `t ->* s2`, then `s1 ->* u` and `s2 ->* u` for some `u`. Proved directly for the "
     "concrete vau-x rules by parallel reduction, not through Shutt's general framework.",
     L("""
## Plain English

A relation is **confluent** (or Church-Rosser) if two different reduction paths from one term can always
be joined again: from `t` you go to `s1` one way and to `s2` another way; then both can reach one common
`u`.

Confluence is what makes the equational theory useful. If two terms are equal, they have a common reduct.
In particular two different normal forms are never equal, so the theory does not collapse.

Shutt obtains confluence for vau-x from a general result: in [thesis chapter 13](%T#page=254) he proves
that every regular substitutive reduction system (SRS) is Church-Rosser (Theorem 13.104), and in section
14.1.4 he shows that vau-x is one.

## The Lean statement

```
theorem confluence {t s1 s2 : Term} (h1 : Steps t s1) (h2 : Steps t s2) :
    exists u, Steps s1 u /\\ Steps s2 u
```

Also proved: `church_rosser` (if `Conv a b` then `a` and `b` have a common reduct) and `Conv.normal_eq`
(two normal forms that are equal in the theory are the same term).

## How it is proved

By parallel reduction and complete developments (Tait, Martin-Lof, Takahashi), in
`Vau/Confluence.lean`:

1. `Par` fires any set of redexes that are already present in a term, all at once.
2. `cd t`, the complete development, fires all of them.
3. `Par.to_cd`: every parallel step from `t` can be continued to `cd t` in one more parallel step. The
   hard cases are beta-vau (it needs `Par.inst`: parallel steps commute with substitution of values) and
   combine-wrap (it needs proper lists to stay proper lists).
4. So `Par` has the diamond property, and so does its closure, which equals [Steps](#/node/Steps).

**This does not formalize Shutt's SRS framework.** It checks the conclusion for vau-x only, by a
different route.
"""),
     [q("What does confluence say?",
        ["Every term has a normal form", "Two reduction paths from one term can always be joined", "Reduction is deterministic", "Every step is an evaluation"],
        1, "Confluence is about joining paths. It does not say that reduction terminates or is deterministic."),
      q("How does this repository prove confluence?",
        ["By formalizing Shutt's Theorem 13.104 for regular SRSs", "By a direct parallel-reduction proof for the concrete vau-x rules", "By citing the thesis", "By testing many terms"],
        1, "The Lean proof uses `Par`, `cd` and `Par.to_cd`. It does not formalize chapter 13."),
      q("Which lemma about parallel steps is needed for the beta-vau case?",
        ["`Par.inst`: parallel steps commute with substitution of a value", "`Step.plug`", "`embed_step`", "`Run.isValue`"],
        0, "When the redex `[combine <vau x.T> V]` fires, the steps inside `T` and `V` must carry over into `T[x <- V]`."),
      q("Are delta-rules covered?",
        ["Yes, all of Shutt's delta-rules", "No: the Lean calculus has no delta-rules", "Only for `$vau`", "Only for `$wrap`"],
        1, "Primitive operatives have no rules in this formalization. Shutt's conditions on delta-rules (Definition 9.22) are not formalized.")],
     caveats=[
         "This site does not check Shutt's proof of Theorem 13.104 or his section 14.1.4 argument. It reports what the thesis says, and proves the vau-x conclusion separately.",
         "`#print axioms Vau.confluence` reports `propext` and `Quot.sound`.",
         SCOPE,
     ])

# ---------------------------------------------------------------- nontrivial (headline)
node("nontrivial",
     "Contextual equivalence in vau-x is nontrivial",
     "`[eval 5]` and `5` are different terms that no context can tell apart, while `5` and `6` can be told "
     "apart. Wand's triviality does not happen in vau-x.",
     L("""
## Plain English

Two terms are **contextually equivalent** if no program can tell them apart: put either one into any
context, run it, and you see the same results.

Wand's result ([Start](#/node/Start)) says that in a calculus with implicit evaluation and fully
reflective fexprs, contextual equivalence is **trivial**: only terms that are the same up to renaming of
bound variables are equivalent. In vau-x, a fexpr cannot take apart an active term such as `[eval 5]`,
and confluence makes reduction steps invisible to every context. So the equation `[eval 5] = 5` holds
contextually, and the theory is not trivial.

## The Lean statement

```
theorem nontrivial :
    Not (eval (dat 5) = dat 5) /\\ CtxEquiv (eval (dat 5)) (dat 5) /\\ Not (CtxEquiv (dat 5) (dat 6))
```

[CtxEquiv](#/node/CtxEquiv) `t1 t2` means: for every one-hole context `c` and every normal form `N`,
`c[t1] ->* N` iff `c[t2] ->* N`.

The middle part comes from a general theorem, `conv_ctxEquiv`: **any two terms that are equal in the
equational theory [Conv](#/node/Conv) are contextually equivalent.** Its proof uses
[confluence](#/node/confluence). The last part uses the empty context: `5` reaches the normal form `5`,
and `6` does not.
"""),
     [q("What would trivial contextual equivalence mean, in Wand's sense?",
        ["Every pair of terms is equivalent", "Only terms equal up to renaming of bound variables are equivalent", "No term is equivalent to itself", "Only values are equivalent"],
        1, "Wand's result is that the equivalence collapses to alpha-equivalence. With de Bruijn indices that is plain equality."),
      q("Why are `[eval 5]` and `5` contextually equivalent in the Lean?",
        ["Because they are the same term", "Because `[eval 5] -> 5`, so they are equal in `Conv`, and `conv_ctxEquiv` turns that into `CtxEquiv`", "Because vau-x has no constants", "Because it is assumed"],
        1, "`conv_ctxEquiv` is proved from confluence and the compatibility of `Conv` with contexts."),
      q("Why is the third conjunct (`5` and `6` not equivalent) needed?",
        ["It is not needed", "To show the relation is not 'everything is equal', which would also be trivial", "To show confluence", "To show `5` is a value"],
        1, "A useful theory must relate some different terms, and must not relate all of them."),
      q("What does `CtxEquiv` observe?",
        ["Only termination", "Which normal forms the program reaches, under full reduction", "Types", "Only the first step"],
        1, "`CtxEquiv t1 t2 := forall c N, Normal N -> (Steps (c.plug t1) N <-> Steps (c.plug t2) N)`.")],
     caveats=[
         "The notion of observation is this project's. Shutt's Definition 13.90 observes, along a fixed evaluation order, normalization and minimal observable normal forms; it is defined for calculi with an operational semantics, which vau-x lacks. `CtxEquiv` uses full reduction and any normal form.",
         "Contexts may capture free variables and need not be closed. Shutt's definition only quantifies over contexts that make both terms closed.",
         "`#print axioms Vau.nontrivial` reports `propext` and `Quot.sound`.",
         "The separation of `5` from `6` uses which normal form is reached. With no delta-rules, no context can branch on which atom it holds, so an observation of termination only would not separate them.",
         SCOPE,
     ])
