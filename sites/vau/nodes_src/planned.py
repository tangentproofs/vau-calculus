# Step 2: the planned proof graph. These nodes describe results that the Lean formalization is PLANNED to
# state and prove. No Lean exists yet: every node here is "formal": "planned" in site.json, and nothing
# here may be read as a proved theorem. "Planned statement" means "what we intend to state in Lean".
# Notation as in definitions.py. "%T" expands to the thesis PDF URL, "%N" to the NEPLS talk, "%D1", "%D2"
# and "%D3" to Schumacher's three posts.
from _common import THESIS, NEPLS, DALE_FEXPR, DALE_EXT, DALE_ACTORS, make, q

NODES = []
node = make(NODES)

PLAN_NOTE = ("Nothing on this node is proved. It describes a result that the planned Lean is meant to state "
             "and prove. The exact Lean statement may differ; when the Lean lands, this node will quote it.")


def L(s):
    return (s.replace("%T", THESIS).replace("%N", NEPLS).replace("%D1", DALE_FEXPR)
            .replace("%D2", DALE_EXT).replace("%D3", DALE_ACTORS))


# ---------------------------------------------------------------- 6. Compatible closure
node("CompatibleClosure",
     "Compatible closure: a rule may fire anywhere inside a term",
     "The seven rules say what happens at the top of a term. The step relation of vau-x lets a rule fire at "
     "any position inside a term. That relation is the compatible closure of the rules.",
     L("""
## Plain English

Each rule on [ReductionSchemata](#/node/ReductionSchemata) is written for the top of a term, for example
`[eval 5] -> 5`. But `[eval 5]` can also sit deep inside a bigger term, for example in the operand list of
a combination, or in the body of an operative. A **context** `C[ ]` is a term with one hole. A relation
is **compatible** if, whenever `M -> N`, also `C[M] -> C[N]` for every context `C`. The **compatible
closure** of a set of rules is the smallest compatible relation that contains every rule. Shutt defines
the step relation of a calculus this way ([thesis section 2.3](%T#page=53)).

So in vau-x one step means: pick one subterm that matches the left side of one rule, and replace it by
the right side. Everything else stays as it is. Zero or more steps is written `->*`.

Two points are special to vau-x:

- **Reduction inside operands is allowed.** Because evaluation is explicit, a step inside an operand is
  not an evaluation of that operand. `(5 . [eval 6]) -> (5 . 6)` is a true step, and a fexpr that later
  receives the operand cannot tell the difference, because a fexpr cannot take apart an active term.
- **Reduction inside an operative body is allowed.** `<vau x.[eval 5]> -> <vau x.5>`. This is like
  reducing under a lambda.

## What is planned

- A Lean inductive relation `Step : Term -> Term -> Prop` with one constructor for each rule at the top,
  and one "congruence" constructor for each place where a subterm can sit.
- Its reflexive-transitive closure `Steps` (written `->*` here).
- A small check that `Step` really is compatible: a step inside any one-hole context is a step of the
  whole term.
"""),
     [q("What does it mean that the step relation is compatible?",
        ["Every term has a step", "If `M -> N`, then `C[M] -> C[N]` for every context `C`", "Steps never change the size of a term", "Two different steps always give the same result"],
        1, "Compatibility lets a rule fire at any position. It is not determinism (that is the last option) and it is not confluence."),
      q("Is `(5 . [eval 6]) -> (5 . 6)` a step of vau-x?",
        ["No: operands are never reduced", "Yes: eval-self fires inside the pair, by compatible closure", "Only if the pair is evaluated first", "Only in vau-e"],
        1, "The compatible closure allows a step at any position. With explicit evaluation this is safe: it is not an evaluation of the operand."),
      q("Is anything on this node proved in Lean?",
        ["Yes", "No: it is a PLAN", "Only the definition", "Only for eval-self"],
        1, PLAN_NOTE)],
     caveats=[
         PLAN_NOTE,
         "The thesis page link points to Shutt's general definition of compatibility (section 2.3). His formal definition of the vau-x step relation goes through the SRS framework of chapter 13, which the planned Lean does not formalize.",
     ])

# ---------------------------------------------------------------- 7. Evaluation is reduction (headline)
node("EvalIsReduction",
     "Planned headline: evaluation is a special case of reduction",
     "Planned statement: define an evaluator for vau-x separately from the rules, and show that every "
     "evaluation of `T` to `V` is a reduction sequence `[eval T] ->* V`.",
     L("""
## Plain English

Shutt's 2007 NEPLS talk says that explicit evaluation "makes term evaluation a special case of term
reduction" ([talk script](%N)). In the vau calculi this is almost true by design: evaluation is not a
separate machine; it is what happens to an `[eval ...]` term under the rules.

To make the sentence into something that can be checked, we need **two** things to compare:

1. **An evaluator.** A definition, made independently of the compatible closure, of "`T` evaluates to
   `V`". For example, a big-step relation in the style of a Lisp interpreter: a self-evaluating term
   evaluates to itself; to evaluate a pair, evaluate the operator, then call the combiner on the operand
   tree; an applicative first evaluates each operand; an operative substitutes its operand into its body.
2. **Reduction.** The step relation of [CompatibleClosure](#/node/CompatibleClosure).

The planned headline says that the evaluator is a special case of reduction: **every evaluation is a
reduction sequence.**

## What is planned

Planned statement, in English:

> For all terms `T` and `V`: if `T` evaluates to `V` under the evaluator, then `[eval T] ->* V` in the
> compatible closure of the seven general rules.

Notes on scope, to keep the claim honest:

- The evaluator is our definition. It is not in the thesis. Shutt's thesis gives evaluation orders and
  operational semantics for other vau calculi (chapter 14); it does not give one for vau-x.
- The planned statement is one direction only (evaluation implies reduction). The other direction is
  false in general: many reduction steps, such as steps inside an operative body, are not evaluation
  steps.
- If the evaluator needs a side condition (for example, closed terms, or no delta-rules), the Lean will
  state it in the theorem, not hide it.
"""),
     [q("Which direction does the planned headline state?",
        ["Every reduction is an evaluation", "Every evaluation is a reduction sequence", "Evaluation and reduction are the same relation", "Reduction never terminates"],
        1, "The plan is one direction: if `T` evaluates to `V`, then `[eval T] ->* V`. Not every reduction step is an evaluation step."),
      q("Where does the evaluator in the planned statement come from?",
        ["From thesis section 9.3", "It is this project's own definition, made independently of the rules", "From Wand's paper", "From Schumacher's Humus code"],
        1, "Shutt does not give an operational semantics for vau-x. The planned evaluator is ours, and the Lean will say so."),
      q("Is this headline proved?",
        ["Yes", "No: it is a PLAN; no Lean exists yet", "Yes, by Shutt in the thesis", "Only for closed terms"],
        1, PLAN_NOTE)],
     caveats=[
         PLAN_NOTE,
         "The quoted phrase is from Shutt's NEPLS talk script. The talk speaks informally; the planned Lean statement is a precise version chosen by this project, not by Shutt.",
     ])

# ---------------------------------------------------------------- 8. Lambda embedding
node("LambdaEmbedding",
     "Planned: the lambda calculus embeds into vau-x",
     "Shutt maps lambda terms into fexpr terms: `lambda x.T` becomes the operative `<vau x.T'>`, and "
     "application becomes `[combine T1' T2']`. The plan is to define this map in Lean and show that it "
     "turns lambda steps into vau-x steps.",
     L("""
## Plain English

In [thesis section 15.4](%T#page=365), Shutt points out a surprising fact. Inside a vau calculus there
is a corner that behaves exactly like the lambda calculus: terms built only from variables, compound
operatives and `[combine ...]` terms, with no `[eval ...]` and no pairs. He gives the map (15.28),
written here for vau-x (which has no environments):

| lambda term | vau-x term |
|---|---|
| `x` | `x` |
| a constant `c` | `c` |
| `(T1 T2)` | `[combine T1' T2']` |
| `lambda x.T` | `<vau x.T'>` |

Here `T'` is the image of `T`. So a lambda abstraction becomes an **operative**, not an applicative. In
Shutt's words, the combiners of the lambda calculus "always were, essentially, fexprs": they do nothing
special to evaluate their operands.

There is a detail to watch. In vau-x, beta-vau fires only when the operand is a **value**
(`[combine <vau x.T> V] -> T[x <- V]`). The image of a variable or of an abstraction is a value; the
image of an application is not. So the image of the lambda calculus reduces like the **call-by-value**
lambda calculus (Plotkin's lambda-v), where beta fires only on a value argument. This is our reading of
the rules; the planned Lean will make it exact.

## What is planned

- A Lean type of lambda terms (with the same variable names as vau-x terms) and the map `embed`.
- Planned statement (simulation): if `M -> N` by one call-by-value beta step, then
  `embed M -> embed N` by one beta-vau step.
- Planned statement (no new steps): every vau-x step from `embed M` lands on `embed N` for some lambda
  term `N` with `M -> N`.
- Both statements are about the call-by-value calculus. If the Lean shows that the full (call-by-name)
  beta rule is needed for some claim, that will be stated, not hidden.
"""),
     [q("What does Shutt's map send `lambda x.T` to?",
        ["The applicative `<<vau x.T'>>`", "The operative `<vau x.T'>`", "`[eval T']`", "The pair `(x . T')`"],
        1, "Map (15.28) sends an abstraction to an operative. Lambda calculus combiners do not evaluate their operands, so they act like fexprs."),
      q("Why does the image of the lambda calculus behave call-by-value in vau-x?",
        ["Because vau-x has no variables", "Because beta-vau fires only on a value operand, and the image of an application is not a value", "Because combine-wrap evaluates every operand", "Because Shutt says so in section 9.3"],
        1, "beta-vau needs `V`. An application maps to a `[combine ...]` term, which is active and so not a value. This is our reading, to be checked in Lean."),
      q("Is the embedding proved?",
        ["Yes", "No: it is a PLAN", "Only the simulation half", "Only for closed terms"],
        1, PLAN_NOTE)],
     caveats=[
         PLAN_NOTE,
         "Map (15.28) in the thesis is written for the environment calculus vau-p, with an extra environment argument. Shutt notes that the point is clearer in vau-x, which has no environments. The vau-x table here drops that argument; that adaptation is ours.",
         "The call-by-value reading is this project's, from the side condition on beta-vau. Shutt's text speaks of 'the beta-rule'.",
     ])

# ---------------------------------------------------------------- 9. Conservative extension (headline)
node("ConservativeExtension",
     "Planned headline: vau-x conservatively extends the lambda calculus",
     "Planned statement: two lambda terms are equal in the call-by-value lambda calculus exactly when "
     "their images are equal in vau-x. Adding fexprs then loses none of the lambda calculus equations.",
     L("""
## Plain English

A calculus `B` **conservatively extends** a calculus `A` (through a map from `A` to `B`) if `B` proves an
equation between images of `A` terms exactly when `A` proves it. Nothing true in `A` is lost, and `B`
adds no new equations between `A` terms.

This is the opposite of Wand's triviality result. In Wand's setting, adding fexprs **destroys** the
lambda calculus equations. Shutt writes that his calculus "conservatively extends" its
lambda-isomorphic subcalculus ([thesis section 15.4](%T#page=366)), so all the equational strength of
the lambda calculus is still there, to be used where it is safe.

## What is planned

Planned statement, in English, with `embed` from [LambdaEmbedding](#/node/LambdaEmbedding) and `=` the
equivalence (reflexive, symmetric and transitive closure) generated by the steps:

> For all lambda terms `M` and `N`: `M = N` in the call-by-value lambda calculus if and only if
> `embed M = embed N` in vau-x.

- The "only if" half follows from the simulation half of the embedding.
- The "if" half is harder. A chain of vau-x equalities between `embed M` and `embed N` may pass through
  terms that are not images. The planned route is to use [Confluence](#/node/Confluence) of vau-x to get
  a common reduct, then the "no new steps" half of the embedding to pull it back.
- If the Lean can only prove one half, the node will be marked **partial**, and the missing half will be
  named.
"""),
     [q("What does 'conservative extension' mean here?",
        ["vau-x has more terms than the lambda calculus", "Two lambda terms are equal in lambda iff their images are equal in vau-x", "vau-x has no new rules", "Every vau-x term is the image of a lambda term"],
        1, "Conservative means no equations are lost and none are added between images of lambda terms."),
      q("Which half of the planned statement is expected to need confluence?",
        ["The 'only if' half (lambda to vau-x)", "The 'if' half (vau-x to lambda)", "Neither", "Both equally"],
        1, "A vau-x equality chain may leave the image of the embedding. Confluence gives a common reduct that stays inside it."),
      q("Is this headline proved?",
        ["Yes", "No: it is a PLAN", "Yes, by Wand", "Only the 'if' half"],
        1, PLAN_NOTE)],
     caveats=[
         PLAN_NOTE,
         "Shutt states conservativity informally in section 15.4 about vau-p, and he says the point is clearer for vau-x. The precise statement above is this project's choice.",
         "If only one half is proved in Lean, this node will be marked partial, not proved.",
     ])

# ---------------------------------------------------------------- 10. Confluence (headline)
node("Confluence",
     "Planned headline: confluence of the vau-x rules",
     "Planned statement: if `T ->* T1` and `T ->* T2`, then `T1 ->* T3` and `T2 ->* T3` for some `T3`. "
     "The plan proves this directly for the concrete vau-x rules, not through Shutt's general framework.",
     L("""
## Plain English

A relation is **confluent** (or Church-Rosser) if two different reduction paths from one term can
always be joined again. Picture a diamond: from `T` you go to `T1` one way and to `T2` another way; then
both `T1` and `T2` can reach one common `T3`.

Confluence is what makes the equational theory useful. If `T1 = T2`, then they have a common reduct. In
particular, two different normal forms are never equal, so the theory does not collapse. That is the
thing Wand's result showed to fail in his reflective calculus.

Shutt obtains confluence for vau-x from a general result. In [thesis chapter 13](%T#page=254) he
defines **regular substitutive reduction systems** (SRSs) and proves that every regular SRS is
Church-Rosser (Theorem 13.104). In section 14.1.4 he shows that vau-x, and six other of his nine vau
calculi, are regular SRSs.

## What is planned

- Planned statement: the reflexive-transitive closure of the vau-x step relation (seven general rules,
  compatible closure) is confluent.
- Planned method: a direct proof for the concrete rules, by parallel reduction (the Tait and Martin-Lof
  method). Define a parallel step that can fire many redexes at once, show it has the diamond property,
  and show that its closure is the same as the closure of the single step.
- **This does not formalize Shutt's SRS framework.** It checks the conclusion for vau-x only, by a
  different route.
- Delta-rules: the first version uses the seven general rules only. Delta-rules, if added, will be
  stated as a hypothesis or as a fixed concrete set, and the theorem will say which.
"""),
     [q("What does confluence say?",
        ["Every term has a normal form", "Two reduction paths from one term can always be joined", "Reduction is deterministic", "Every step is an evaluation"],
        1, "Confluence is about joining paths. It does not say that reduction terminates or is deterministic."),
      q("How does Shutt obtain confluence of vau-x in the thesis?",
        ["By a direct parallel-reduction proof for vau-x", "Through a general theorem on regular SRSs (13.104) and section 14.1.4", "He does not; it is an open problem", "Through Wand's paper"],
        1, "Shutt proves a general theorem and then shows that vau-x is a regular SRS. The planned Lean takes a different, direct route."),
      q("Will the planned Lean formalize the regular SRS framework?",
        ["Yes", "No: only the conclusion for the concrete vau-x rules", "Only Theorem 13.104", "Only for vau-e"],
        1, "The plan is explicit: a direct proof for vau-x, not a formalization of chapter 13."),
      q("Is confluence proved in this repository?",
        ["Yes", "No: it is a PLAN", "Yes, for vau-e", "Only the diamond lemma"],
        1, PLAN_NOTE)],
     caveats=[
         PLAN_NOTE,
         "This site does not check Shutt's proof of Theorem 13.104 or his section 14.1.4 argument. It only reports what the thesis says.",
     ])

# ---------------------------------------------------------------- 13. wrap / unwrap
node("WrapUnwrap",
     "wrap and unwrap: making and taking apart applicatives",
     "`wrap` turns a combiner into an applicative that evaluates its operands first. `unwrap` takes the "
     "wrapper off again. In vau-e the primitive operatives `$wrap` and `$unwrap` have their own delta-rules.",
     L("""
## Plain English

In vau-x, an applicative is written `<T>`: the combiner `T` in a **wrapper**. combine-wrap says what a
wrapper does: evaluate each operand, then pass the results to `T`. See
[ReductionSchemata](#/node/ReductionSchemata).

Kernel gives the programmer two applicatives, `wrap` and `unwrap`, to work with wrappers
([thesis section 4.2](%T#page=92)). The calculus vau-e models the underlying primitive **operatives**
`$wrap` and `$unwrap` with delta-rules ([thesis (9.12)](%T#page=201)). In this site's ASCII notation,
with `e` the dynamic environment (which these two rules ignore):

- `[combine $wrap (V) e] -> <V>`: build the applicative whose underlying combiner is `V`;
- `[combine $unwrap (<V>) e] -> V`: take the wrapper off.

Kernel's applicatives `wrap` and `unwrap` are these two operatives in a wrapper, so their operand is
evaluated first.

So `(unwrap (wrap c))` gives back `c`. And `(wrap c)` where `c` is already applicative gives a combiner
that evaluates its operands **twice**. That is legal and sometimes useful.

The key design point: in Kernel, applicatives are not a separate kind of thing. Every applicative is a
wrapper around some combiner, often an operative. `$lambda` is defined this way
([DerivedLambda](#/node/DerivedLambda)).

## What is planned

- vau-x already has wrappers `<T>` in its syntax, so the planned Lean covers the wrapper and
  combine-wrap as part of the core rules.
- The primitive applicatives `wrap` and `unwrap` belong to vau-e (with delta-rules). A Lean model of
  them is planned after the core vau-x results, and may stay planned.
"""),
     [q("What does `(unwrap (wrap c))` give?",
        ["An error", "`c`", "`(wrap c)`", "The operands of `c`"],
        1, "unwrap removes the wrapper that wrap added."),
      q("What does wrapping an applicative a second time do?",
        ["It is an error", "Its operands are evaluated twice", "Nothing: wrap is idempotent", "It turns it into an operative"],
        1, "Each wrapper evaluates the operands once before passing them on."),
      q("Is a Lean model of wrap and unwrap available?",
        ["Yes", "No: it is a PLAN", "Only unwrap", "Only in Humus"],
        1, PLAN_NOTE)],
     caveats=[
         PLAN_NOTE,
         "The two delta-rules are written in this site's ASCII notation. In the thesis the applicative is written as a tagged term, `<applicative V>`. See thesis (9.12) for the exact rules.",
     ])

# ---------------------------------------------------------------- 14. Derived $lambda (headline)
node("DerivedLambda",
     "Planned headline: $lambda is derived from $vau and wrap",
     "Kernel has no primitive `$lambda`. Shutt defines it from `$vau`, `wrap` and `eval`. The planned "
     "statement is that this definition behaves like an ordinary lambda.",
     L("""
## Plain English

In Scheme, `lambda` is primitive. In Kernel it is not. Shutt defines it in a few lines
([thesis (4.10)](%T#page=94)), written here with ASCII names:

```
($define! $lambda
   ($vau (ptree . body) static-env
      (wrap (eval (list* $vau ptree #ignore body)
                  static-env))))
```

Read it from the inside out:

1. `$lambda` is itself an operative. Its operands `(ptree . body)` are **not** evaluated, and it
   receives the environment where it is called as `static-env`.
2. It builds the list `($vau ptree #ignore . body)`: a `$vau` expression that ignores the dynamic
   environment.
3. It evaluates that list in `static-env`, which gives a compound operative whose body runs in the
   environment where the `$lambda` expression was written (static scope).
4. It wraps the result with `wrap`, so the operands are evaluated before the body runs.

So a `$lambda` is an applicative wrapper around a statically scoped fexpr that ignores its caller's
environment. This is the same idea as in [LambdaEmbedding](#/node/LambdaEmbedding), seen from the
programming side.

## What is planned

- Planned statement, in English: in a Lean model of vau-e (environments, symbols, `$vau`, `wrap`,
  `eval`), for a simple parameter tree and body, `(($lambda ptree body) args)` called in an environment
  `e` reduces to the result of evaluating `body` in the static environment extended with the parameters
  bound to the **evaluated** arguments.
- This needs [Environments](#/node/Environments), [VauEnvironments](#/node/VauEnvironments) and
  [WrapUnwrap](#/node/WrapUnwrap) in Lean first. It comes after the vau-x results and may stay planned.
"""),
     [q("Why does the derived `$lambda` use `#ignore` for the environment parameter of the inner `$vau`?",
        ["To save memory", "So the resulting combiner cannot see its caller's environment, as an ordinary lambda", "Because `$vau` needs it", "To evaluate operands twice"],
        1, "An ordinary procedure should not see the dynamic environment. `#ignore` makes sure the body cannot."),
      q("What makes the derived `$lambda` evaluate its arguments?",
        ["`eval`", "`wrap`", "`list*`", "`$define!`"],
        1, "The final `wrap` turns the operative into an applicative."),
      q("Is this headline proved?",
        ["Yes", "No: it is a PLAN", "Yes, in Kernel's test suite", "Only for one parameter"],
        1, PLAN_NOTE)],
     caveats=[
         PLAN_NOTE,
         "The definition is quoted from the thesis (4.10) because it is short and central. The step-by-step reading is ours.",
     ])

# ---------------------------------------------------------------- 15. Nontrivial equivalence (headline)
node("NontrivialEquivalence",
     "Planned headline: contextual equivalence in vau-x is nontrivial",
     "Planned statement: some pairs of different terms are contextually equivalent in vau-x (for example "
     "`[eval 5]` and `5`), and some pairs are not. Wand's triviality does not happen here.",
     L("""
## Plain English

Two terms are **contextually equivalent** (Shutt says operationally equivalent) if no program can tell
them apart: put either one into any context, run it, and you see the same result. Shutt's definition
([thesis Definition 13.90](%T#page=295)) compares whether the program finishes and which observable
answer it gives.

Wand's result ([Start](#/node/Start)) says that in a calculus with implicit evaluation and fully
reflective fexprs, contextual equivalence is **trivial**: only terms that are the same up to renaming of
bound variables are equivalent.

In vau-x, an operand that a fexpr receives is never reduced as part of being received, and a fexpr
cannot take apart an active term such as `[eval 5]`. So the step `[eval 5] -> 5` should be invisible to
every context. A theory with that equation is not trivial.

## What is planned

- A definition of observation for vau-x: for example, "the program reduces to this constant". Shutt's
  Definition 13.90 is the model. vau-x has no operational semantics in the thesis, so the choice will be
  stated.
- Planned statement (nontrivial, below): `[eval 5]` and `5`, two different terms, are contextually
  equivalent. The planned route is through [Confluence](#/node/Confluence): equal terms have a common
  reduct, so no context can separate them.
- Planned statement (nontrivial, above): two different constants are **not** contextually equivalent.
  So the relation is not "everything is equal" either.
"""),
     [q("What would 'trivial' contextual equivalence mean, in Wand's sense?",
        ["Every pair of terms is equivalent", "Only terms equal up to renaming of bound variables are equivalent", "No term is equivalent to itself", "Only values are equivalent"],
        1, "Wand's result is that the equivalence collapses to alpha-equivalence, so the theory has no useful equations."),
      q("Why should `[eval 5]` and `5` be indistinguishable in vau-x?",
        ["Because they are the same term", "Because `[eval 5] -> 5`, and with confluence no context can tell a term from its reduct", "Because vau-x has no constants", "Because fexprs evaluate their operands"],
        1, "This is the planned route. A fexpr cannot take apart `[eval 5]`, and confluence makes reduction steps sound for equivalence."),
      q("Is this headline proved?",
        ["Yes", "No: it is a PLAN", "Yes, by Wand", "Only the 'above' half"],
        1, PLAN_NOTE)],
     caveats=[
         PLAN_NOTE,
         "Shutt's operational-equivalence results in chapter 14 are for vau calculi that have an operational semantics (vau-i, vau-C, vau-S). The planned vau-x statement uses this project's own choice of observation.",
     ])

# ---------------------------------------------------------------- 16. Environment opacity / hygiene
node("EnvironmentOpacity",
     "Planned: environments are opaque, and that supports hygiene",
     "A Kernel program cannot list or take apart an environment. It can only look up symbols in it, or "
     "change it if it holds a direct reference. Shutt's hygiene argument rests on this.",
     L("""
## Plain English

**Hygiene** means that a variable binding affects only the part of the source code where the binding is
written. Macros and fexprs both threaten hygiene: they can capture or expose names by accident. Shutt
spends [thesis chapter 5](%T#page=101) on how Kernel keeps fexprs well-behaved.

Two of his tactics matter here:

- **Environments are encapsulated.** A program cannot ask an environment for a list of its bindings, and
  cannot take an environment apart. A fexpr that receives its caller's environment as `e` can evaluate
  things in `e` and look up symbols, but cannot find out what else `e` holds. In vau calculus terms, an
  environment is not something a fexpr can deconstruct ([Start](#/node/Start)).
- **Mutation is local.** A combiner can change only environments it holds a direct reference to, and
  Kernel's `$define!` changes only the local environment. A callee that does not receive its caller's
  environment cannot change it.

## What is planned

- An informal node for now. A planned Lean statement would be in a Lean model of vau-e, for example: a
  combiner whose environment parameter is `#ignore` gives the same result in every calling environment.
- This node may stay planned in this project.
"""),
     [q("What is hygiene, in Shutt's sense?",
        ["Garbage collection of unused environments", "A variable binding affects only the part of the source code where it is written", "Type safety", "Evaluating every operand exactly once"],
        1, "Hygiene is about keeping bindings local to the region of code where they are written."),
      q("What does 'environments are encapsulated' mean in Kernel?",
        ["They are immutable", "A program cannot list or take apart an environment's bindings", "They are garbage-collected", "They cannot be passed to fexprs"],
        1, "A program can look up symbols in an environment but cannot inspect its whole contents."),
      q("Is the planned Lean statement proved?",
        ["Yes", "No: it is a PLAN", "Only for vau-x", "Only for $lambda"],
        1, PLAN_NOTE)],
     caveats=[
         PLAN_NOTE,
         "The summary of chapter 5 is ours and short. See the thesis for Shutt's full treatment of hygiene, including stable bindings.",
     ])

# ---------------------------------------------------------------- 17. Encapsulation types (later)
node("EncapsulationTypes",
     "Later: encapsulation types",
     "Kernel's `make-encapsulation-type` returns three applicatives: an encapsulator, a type predicate and "
     "a decapsulator. Only code that holds the decapsulator can read the content. This node is planned for later.",
     L("""
## Plain English

Kernel lets a program create a new abstract data type at run time
([thesis section 7.2](%T#page=146)). One call, `(make-encapsulation-type)`, returns three applicatives:

- an **encapsulator** `e`: it takes one value and returns a new encapsulated object that holds it;
- a **type predicate** `p?`: it returns true iff all its arguments were made by `e`;
- a **decapsulator** `d`: it takes an object made by `e` and returns its content.

The content can be read **only** through `d`. So if a module keeps `d` private and exports only safe
operations, nobody else can read or forge the content. The thesis uses this idiom often, inside a
`$provide!` block.

This is the same principle as [EnvironmentOpacity](#/node/EnvironmentOpacity): the language keeps some
objects opaque, and that gives programmers abstraction barriers that fexprs cannot break.

## What is planned

Nothing for now. This node is **later**: it records the idea and where to read about it. No Lean model
of encapsulation types is planned in the current step.
"""),
     [q("What does `(make-encapsulation-type)` return?",
        ["One new object", "Three applicatives: encapsulator, type predicate, decapsulator", "A new environment", "An operative"],
        1, "It returns a matched set of three applicatives for a new type."),
      q("Which of the three applicatives can read an encapsulated object's content?",
        ["The encapsulator", "The type predicate", "The decapsulator", "Any of them"],
        2, "Only the matching decapsulator returns the content."),
      q("Is there Lean for encapsulation types?",
        ["Yes", "No: this node is planned for later", "Only the predicate", "Only in Humus"],
        1, PLAN_NOTE)],
     caveats=[PLAN_NOTE])

# ---------------------------------------------------------------- 18. Actor layer (later)
node("ActorLayer",
     "Later: an actor view of vau evaluation",
     "Dale Schumacher implements Kernel as a system of actors in his language Humus: evaluation and "
     "combination are messages, and operands may be evaluated concurrently. There is no published "
     "confluence proof for such a layer. This node is planned for later.",
     L("""
## Plain English

Dale Schumacher's posts describe an evaluator for a Kernel-like language built from **actors**: objects
that react to messages ([Fexpr the Ultimate Lambda](%D1), [Semantic Extensibility with Vau](%D2),
[Implementing Actors in Kernel](%D3)). In his Humus code:

- an expression is an actor that answers an `#eval` message with an environment, sending the result to
  a customer;
- a combiner is an actor that answers a `#comb` message with the operand tree and the environment;
- an environment is an actor that answers `#lookup`, and forwards the request to its parent if it does
  not have the symbol;
- the `$` prefix of Kernel names is written `&`, for example `&vau`.

Because each request is a message, an applicative can send `#eval` to all its operands at once, so the
operands may be evaluated **concurrently**. The order of operand evaluation is then not fixed.

This raises a confluence question. The vau-x rules already allow reduction anywhere
([CompatibleClosure](#/node/CompatibleClosure)), and [Confluence](#/node/Confluence) is planned for
them. But an actor system has its own semantics (message order, state in environment actors). Whether a
concurrent actor implementation gives the same answers as the calculus is a separate question.
**We know of no published confluence proof for such an actor layer.**

## What is planned

Nothing for now. This node is **later**. A possible future direction: model `#eval` and `#comb`
messages, and relate the actor runs to vau-x reduction sequences.
"""),
     [q("In Schumacher's actor evaluator, which message asks a combiner to act on an operand tree?",
        ["`#eval`", "`#comb`", "`#lookup`", "`#wrap`"],
        1, "`#eval` goes to expressions, `#comb` to combiners, `#lookup` to environments."),
      q("Is there a published confluence proof for an actor implementation of Kernel?",
        ["Yes, in Shutt's thesis", "Not that we know of", "Yes, in Schumacher's posts", "Yes, in Wand's paper"],
        1, "We found none. Shutt's confluence results are for the calculi, not for an actor implementation."),
      q("Is there Lean for the actor layer?",
        ["Yes", "No: this node is planned for later", "Only for `#eval`", "Only for `#lookup`"],
        1, PLAN_NOTE)],
     caveats=[
         PLAN_NOTE,
         "The description of Schumacher's design is our summary of his three posts. His code may differ in detail.",
         "'No published confluence proof' means that we searched and found none, not that none can exist.",
     ])
