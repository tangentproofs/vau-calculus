# Step 3 nodes: the supporting Lean definitions that the headline statements mention. Each node id is a
# Lean declaration in Vau/. These are short; each says what the Lean definition is and why it is there.
from _common import make, q

NODES = []
node = make(NODES)

DB = ("De Bruijn indices are this project's representation. Shutt uses named variables with renaming; "
      "the two are the usual two views of terms up to renaming of bound variables.")

# ---------------------------------------------------------------- SelfEval, IsList, evalList
node("SelfEval",
     "Self-evaluating terms S",
     "`SelfEval s` holds for primitive data, primitive operatives, `#ignore`, `()` and the three compound "
     "operatives. These are the terms that eval-self returns unchanged.",
     """
## Plain English

This is Shutt's set `S` from (9.25). The rule eval-self says `[eval S] -> S`. Variables, pairs,
applicatives and active terms are **not** self-evaluating: pairs and applicatives have their own
evaluation rules, and a variable has no rule (it waits to be substituted).

## In the Lean

`Vau.SelfEval` has seven constructors: `dat n`, `prim n`, `ign`, `nil`, `vau t`, `vau0 t`, `vau2 t`.
The lemma `SelfEval.isValue` says that each self-evaluating term is a [value](#/node/IsValue).
""",
     [q("Is a pair `(1 . 2)` self-evaluating?",
        ["Yes", "No: a pair evaluates by eval-pair, as a combination", "Only if both parts are numbers", "Only inside an operative"],
        1, "There is no `SelfEval.pair` constructor. `[eval (1 . 2)]` steps by eval-pair."),
      q("Is `<vau x.[eval x]>` self-evaluating?",
        ["Yes: every compound operative is, whatever its body", "No: its body is active", "Only after its body is reduced", "No: only atoms are"],
        0, "`SelfEval.vau t` has no condition on `t`."),
      q("Is a variable self-evaluating?",
        ["Yes", "No", "Only `var 0`", "Only free variables"],
        1, "There is no `SelfEval.var`. `[eval x]` has no rule in vau-x.")])

node("IsList",
     "Proper lists",
     "`IsList t` holds when `t` is `()` or a pair whose second part is a proper list: `(T1 ... Tm)`. "
     "combine-wrap needs its operand tree to be a proper list.",
     """
## Plain English

As in Lisp, `(T1 T2 T3)` is short for `(T1 . (T2 . (T3 . ())))`. A **proper list** is a chain of pairs
that ends in `()`. The elements `Ti` can be any terms.

combine-wrap, `[combine <T0> (T1 ... Tm)] -> [combine T0 ([eval T1] ... [eval Tm])]`, needs a proper
list: an applicative evaluates each operand, and it must know where the operands end.

## In the Lean

`Vau.IsList` has two constructors: `nil` and `cons a h` (from `IsList b`, get `IsList (pair a b)`).
`isListB` is a Boolean test with `isListB_iff`.
""",
     [q("Is `(1 . 2)` a proper list?",
        ["Yes", "No: it ends in `2`, not `()`", "Only if 2 is a value", "Yes, of length 2"],
        1, "The last `cdr` must be `()`. `IsList (dat 2)` does not hold."),
      q("Must the elements of a proper list be values?",
        ["Yes", "No: any terms", "Only the first", "Only the last"],
        1, "`IsList.cons a h` puts no condition on `a`."),
      q("Which rule needs `IsList`?",
        ["eval-pair", "combine-wrap", "parse-pair", "beta-vau"],
        1, "`Top.combWrap` has the hypothesis `IsList ts`.")])

node("evalList",
     "Wrap each operand in eval",
     "`evalList (T1 ... Tm)` is `([eval T1] ... [eval Tm])`. It builds the right side of combine-wrap.",
     """
## Plain English

When an applicative is called, each operand is to be evaluated. combine-wrap does not evaluate them
itself; it puts an `[eval ...]` around each one, and later steps do the work.

## In the Lean

`Vau.evalList (pair a b) = pair (eval a) (evalList b)`, and `evalList t = t` for every other form. It is
only used on [proper lists](#/node/IsList). Lemmas: `IsList.evalList`, `rename_evalList`,
`subst_evalList` (the last two need `IsList`).
""",
     [q("What is `evalList (1 2)`?",
        ["`(1 2)`", "`([eval 1] [eval 2])`", "`[eval (1 2)]`", "`(1 . [eval 2])`"],
        1, "Each element gets its own `eval`; the list structure stays."),
      q("What is `evalList ()`?",
        ["`[eval ()]`", "`()`", "`nil . nil`", "Undefined"],
        1, "The empty list has no elements, so nothing changes."),
      q("Does `evalList` itself evaluate anything?",
        ["Yes, it runs each operand", "No: it only adds `[eval ...]` around each operand", "Only values", "Only the first operand"],
        1, "It is a syntactic function. The evaluation happens in later steps.")])

# ---------------------------------------------------------------- substitution machinery
node("lift",
     "Lift a renaming under a binder",
     "`lift rn` keeps index 0 (the newly bound variable) and sends `n + 1` to `rn n + 1`. It is how a renaming "
     "goes under a `vau`.",
     """
## Plain English

With de Bruijn indices, going under a binder adds one new variable at index 0 and shifts the others up
by one. A renaming `rn` of the outer variables must leave the new variable alone and act on the others,
shifted. That is `lift rn`.

## In the Lean

`Vau.lift rn 0 = 0` and `Vau.lift rn (n + 1) = rn n + 1`. Lemmas: `lift_comp`, `lift_comp_succ`.
""",
     [q("What is `lift rn 0`?",
        ["`rn 0`", "`0`", "`1`", "`rn 0 + 1`"],
        1, "Index 0 is the variable bound by the binder we just entered; it is not renamed."),
      q("What is `lift rn 3`?",
        ["`rn 3`", "`rn 2 + 1`", "`3`", "`rn 4`"],
        1, "`lift rn (n + 1) = rn n + 1` with `n = 2`."),
      q("Where is `lift` used?",
        ["In `rename`, under `vau`", "In `evalList`", "In `Run`", "In `CtxEquiv`"],
        0, "`rename rn (vau t) = vau (rename (lift rn) t)`.")],
     caveats=[DB])

node("rename",
     "Renaming free variables",
     "`rename rn t` changes each free variable `var n` of `t` to `var (rn n)`. It is used to shift terms when "
     "they move under a binder.",
     """
## Plain English

A renaming is a function `rn` from indices to indices. `rename rn t` applies it to every free variable of
`t`, and goes under each `vau` with [lift](#/node/lift). The most common use is `rename Nat.succ`, which
shifts every free variable up by one, so that a term can be put under one more binder without capture.

## In the Lean

`Vau.rename` is defined by recursion on [Term](#/node/Term). Lemmas: `rename_rename`,
`rename_eq_subst` (renaming is a special case of [subst](#/node/subst)), `rename_inst`, and that
renaming keeps values, self-evaluating terms and proper lists.
""",
     [q("What is `rename Nat.succ (var 0)`?",
        ["`var 0`", "`var 1`", "`vau (var 0)`", "`var 2`"],
        1, "`rename rn (var n) = var (rn n)`."),
      q("What is `rename rn (vau (var 0))`?",
        ["`vau (var (rn 0))`", "`vau (var 0)`", "`var (rn 0)`", "`vau (var 1)`"],
        1, "Under `vau` the renaming is `lift rn`, which keeps 0. The bound variable is not renamed."),
      q("Does renaming change a constant `dat 7`?",
        ["Yes", "No", "Only under a binder", "Only if `rn 7` differs from 7"],
        1, "`rename rn (dat n) = dat n`: constants are not variables.")],
     caveats=[DB])

node("up",
     "Lift a substitution under a binder",
     "`up sg` keeps index 0 and sends `n + 1` to `sg n` shifted up by one. It is how a substitution goes under "
     "a `vau` without capturing anything.",
     """
## Plain English

A substitution `sg` gives a term for each free variable. Under a binder, index 0 is the new bound
variable, which must stay itself; index `n + 1` is the old variable `n`, which gets `sg n`. But `sg n` now
sits under one more binder, so its own free variables must be shifted up by one. That is what makes the
substitution capture-free.

## In the Lean

`Vau.up sg 0 = var 0` and `Vau.up sg (n + 1) = rename Nat.succ (sg n)`. Lemmas: `up_comp_lift`,
`rename_comp_up`, `subst_comp_up`, `up_var`, `IsValue.up` (if every `sg n` is a value, so is every
`up sg n`).
""",
     [q("What is `up sg 0`?",
        ["`sg 0`", "`var 0`", "`rename Nat.succ (sg 0)`", "`var 1`"],
        1, "The newly bound variable stays itself."),
      q("Why is `sg n` shifted by `rename Nat.succ` in `up sg (n + 1)`?",
        ["To make it shorter", "Because it now sits under one more binder, and its free variables must not be captured", "Because `sg` is a renaming", "It is not shifted"],
        1, "This is the de Bruijn form of capture avoidance."),
      q("If every `sg n` is a value, is every `up sg n` a value?",
        ["Yes: `IsValue.up`", "No", "Only for `n = 0`", "Only if `sg` is a renaming"],
        0, "`var 0` is a value, and renaming keeps values.")],
     caveats=[DB])

node("subst",
     "Parallel substitution",
     "`subst sg t` replaces every free variable `var n` of `t` by the term `sg n`, all at once, and goes under "
     "each `vau` with `up sg`.",
     """
## Plain English

This is substitution for all free variables at the same time. Single substitution
[inst](#/node/inst) is the special case where index 0 gets one term and the other indices move down by
one.

Working with parallel substitutions makes the algebra simple. The key fact is that substitutions
compose: doing `sg` and then `tg` is the same as doing one substitution, `Function.comp (subst tg) sg`.

## In the Lean

`Vau.subst` is defined by recursion on [Term](#/node/Term), with [up](#/node/up) under `vau`. Lemmas:
`subst_rename`, `rename_subst`, `subst_subst` (composition), `subst_var` (the identity substitution),
`subst_inst` (substitution commutes with single substitution), and that substitution of values keeps
values (`IsValue.subst`).
""",
     [q("What is `subst sg (var 3)`?",
        ["`var 3`", "`sg 3`", "`var (sg 3)`", "`sg 0`"],
        1, "A free variable is replaced by its term."),
      q("What does `subst_subst` say?",
        ["Substitution is idempotent", "Doing `sg` then `tg` equals the single substitution `Function.comp (subst tg) sg`", "Substitution commutes with renaming", "Every term is a substitution instance"],
        1, "`subst tg (subst sg t) = subst (Function.comp (subst tg) sg) t`."),
      q("Under which condition does `subst sg v` stay a value?",
        ["Always", "When `v` is a value and every `sg n` is a value", "When `sg` is a renaming", "Never"],
        1, "`IsValue.subst` needs both, because variables are values and get replaced.")],
     caveats=[DB])

node("scons",
     "Extend a substitution at index 0",
     "`scons v sg` sends index 0 to `v` and `n + 1` to `sg n`. With `sg = var`, it is the substitution behind "
     "`inst t v`.",
     """
## Plain English

`scons` is "cons" for substitutions. `scons v var` maps `0` to `v` and `n + 1` to `var n`: it fills in
the variable bound by the outermost `vau` with `v`, and moves every other free variable down by one,
because that binder is gone after the call.

## In the Lean

`Vau.scons v sg 0 = v` and `Vau.scons v sg (n + 1) = sg n`. `inst t v = subst (scons v var) t`.
`IsValue.scons`: if `v` is a value, every `scons v var n` is a value.
""",
     [q("What is `scons v var 0`?",
        ["`var 0`", "`v`", "`var 1`", "`sg 0`"],
        1, "Index 0 gets `v`."),
      q("What is `scons v var 4`?",
        ["`var 4`", "`var 3`", "`v`", "`var 5`"],
        1, "`scons v sg (n + 1) = sg n`, so index 4 goes to `var 3`."),
      q("Why do the other indices move down by one?",
        ["They do not", "Because the binder of index 0 is removed when the operative is called", "To avoid capture", "Because `v` is a value"],
        1, "After beta-vau, the `vau` around the body is gone.")],
     caveats=[DB])

# ---------------------------------------------------------------- closures
node("Star",
     "Zero or more steps of a relation",
     "`Star r a b` holds when `b` can be reached from `a` by zero or more `r`-steps. It is the "
     "reflexive-transitive closure, defined here to avoid a Mathlib dependency.",
     """
## Plain English

Given a one-step relation `r`, `Star r` allows any finite number of steps, including none.

## In the Lean

`Vau.Star` has `refl t` (zero steps) and `tail` (a path to `b`, then one more step to `c`). It works for
any type, so it is used for vau-x terms and for lambda terms. Lemmas: `Star.single`, `Star.trans`,
`Star.head`, `Star.map` (a map that keeps single steps keeps paths), `Star.mono`, `Star.toEqvGen`.
""",
     [q("Does `Star r a a` hold for every `a`?",
        ["Yes: `Star.refl`", "Only if `r a a`", "No", "Only for values"],
        0, "Zero steps are allowed."),
      q("Why is `Star` defined in this repository and not imported?",
        ["It is not defined here", "To avoid depending on Mathlib", "Because Lean core forbids it", "To change its meaning"],
        1, "The project has no dependencies. Mathlib's `Relation.ReflTransGen` is the same idea."),
      q("If `r a b` and `Star r b c`, does `Star r a c` hold?",
        ["Yes: `Star.head`", "No", "Only if `a = c`", "Only for confluent `r`"],
        0, "Paths compose.")])

node("Steps",
     "Reduction: zero or more steps, ->*",
     "`Steps t t'` (written `t ->* t'`) holds when `t'` can be reached from `t` by zero or more vau-x steps.",
     """
## Plain English

This is the many-step reduction relation of vau-x: [Star](#/node/Star) applied to
[Step](#/node/Step). It is what "`t` reduces to `t'`" means on this site.

## In the Lean

`abbrev Steps := Star Step`. Lemmas: congruences `Steps.vau`, `Steps.pair`, `Steps.comb` and the
others; `Steps.top` (one rule at the top); `Steps.plug` (reduction inside any context);
`Steps.normal_eq` (a normal form reduces only to itself).
""",
     [q("Does `Steps t t` hold?",
        ["Yes, by zero steps", "Only if `t` is a value", "Only if `t` is normal", "No"],
        0, "`Star.refl`."),
      q("If `a ->* a'` and `b ->* b'`, does `[combine a b] ->* [combine a' b']` hold?",
        ["Yes: `Steps.comb`", "No", "Only if `a` is an operative", "Only if `b` is a value"],
        0, "Reduction is allowed in both parts, one after the other."),
      q("If `t` is a normal form and `t ->* t'`, what is `t'`?",
        ["Anything", "`t` itself", "A value", "`()`"],
        1, "`Steps.normal_eq`: a normal form has no step, so the path has length 0.")])

node("EqvGen",
     "Equivalence closure of a relation",
     "`EqvGen r a b` holds when `a` and `b` are joined by a finite zigzag of `r`-steps, forwards and "
     "backwards. It is the smallest equivalence relation that contains `r`.",
     """
## Plain English

An equational theory lets you use a rule in both directions. `EqvGen r` is the closure of `r` under
reflexivity, symmetry and transitivity.

## In the Lean

`Vau.EqvGen` has four constructors: `rel`, `refl`, `symm`, `trans`. It works for any type. Mathlib has
the same notion as `Relation.EqvGen`; it is defined here to avoid the dependency.
""",
     [q("Is `EqvGen r` symmetric?",
        ["Yes, by the `symm` constructor", "Only if `r` is symmetric", "No", "Only for terms"],
        0, "Symmetry is built in."),
      q("If `r a b`, does `EqvGen r b a` hold?",
        ["Yes: `symm (rel h)`", "No", "Only if `r b a`", "Only if `a = b`"],
        0, "Use the step backwards."),
      q("Which two equational theories on this site are `EqvGen`s?",
        ["`Conv` and `LConv`", "`Steps` and `LSteps`", "`Run` and `Par`", "`Top` and `Step`"],
        0, "`Conv := EqvGen Step` and `LConv := EqvGen LStep`.")])

node("Conv",
     "The equational theory of vau-x",
     "`Conv a b` holds when `a` and `b` are joined by a zigzag of vau-x steps. It is the equational theory "
     "generated by the seven rules in every context.",
     """
## Plain English

Two terms are **equal in the theory** if you can get from one to the other by steps used forwards or
backwards. For example `[eval 5]` and `5` are equal, because `[eval 5] -> 5`.

By [confluence](#/node/confluence), equal terms always have a common reduct (`church_rosser`). So
two different normal forms are never equal: the theory does not collapse.

## In the Lean

`abbrev Conv := EqvGen Step`. Lemmas: `Conv.plug` (equal terms stay equal in every context),
`church_rosser`, `Conv.normal_eq`, `Conv.steps_normal`.
""",
     [q("Is `Conv (eval (dat 5)) (dat 5)` true?",
        ["Yes: `EqvGen.rel` of the eval-self step", "No", "Only after evaluation", "Only in vau-e"],
        0, "One step is enough."),
      q("What does `church_rosser` say about `Conv a b`?",
        ["`a = b`", "`a` and `b` have a common reduct", "`a` and `b` are values", "`a ->* b`"],
        1, "This is where confluence is used."),
      q("Can two different normal forms be equal in `Conv`?",
        ["Yes", "No: `Conv.normal_eq`", "Only constants", "Only if they are values"],
        1, "They would have a common reduct, but a normal form only reduces to itself.")])

# ---------------------------------------------------------------- evaluator
node("Run",
     "A big-step evaluator for vau-x",
     "`Run t r` says that a Lisp-style interpreter, defined by its own rules, takes `t` to the value `r`. It "
     "is this project's definition; the thesis gives no evaluator for vau-x.",
     """
## Plain English

`Run` is written the way one would write an interpreter, one rule per case:

- **Data** (atoms, operatives, pairs, applicatives) runs part by part. An operative body is not entered.
- **`[eval t]`**: run `t` to a value. A self-evaluating result is the answer. A pair `(a . b)` continues
  as `[combine [eval a] b]`. An applicative `<u>` gives `<f>`, where `[eval u]` runs to `f`.
- **`[combine f x]`**: run `f` and `x` to values, then call the combiner:
  - `<vau x.T>` with value `v`: run `T[x <- v]`;
  - a wrapper `<c>` with a proper list `xs`: run `[combine c ([eval x1] ...)]`;
  - `<vau2.T>` with a pair `(a . b)`: run `[combine [combine T a] b]`;
  - `<vau0.T>` with `()`: run `T`.

It is defined on its own, without the reduction relation. Its cases mirror the seven rules one for one,
so [eval_is_reduction](#/node/eval_is_reduction) checks that big-step and small-step agree in one
direction.

## In the Lean

`Vau.Run` is an inductive relation with 17 constructors. `Run.isValue`: every result is a value.
`Run.toSteps`: every run is a reduction sequence. Examples: `run_F7`, `run_F_F7`, `run_wrapF_F7`.
""",
     [q("Does `Run` reduce inside the body of an operative?",
        ["Yes", "No: `Run (vau t) (vau t)` leaves the body alone", "Only for `vau0`", "Only if the body is a value"],
        1, "Like a real interpreter, `Run` does not look inside closures."),
      q("How does `Run` handle a call of an applicative `<c>`?",
        ["It ignores the wrapper", "It runs `[combine c ([eval x1] ...)]`, so each operand is evaluated", "It evaluates the combiner twice", "It fails"],
        1, "That is the constructor `combWrap`, mirroring combine-wrap."),
      q("Is every result of `Run` a value?",
        ["Yes: `Run.isValue`", "No", "Only for closed terms", "Only for `eval` terms"],
        0, "Proved by induction on the run.")],
     caveats=["`Run` is a relation and fixes no evaluation order. Any order of its premises gives a reduction sequence."])

# ---------------------------------------------------------------- lambda side
node("LTerm",
     "Lambda terms",
     "`LTerm` is the lambda calculus with constants: variables (de Bruijn indices), constants, applications "
     "`(M N)` and abstractions `lambda.M`.",
     """
## Plain English

These are the terms of the lambda calculus that [embed](#/node/embed) maps into vau-x. Constants
are numbered and map to primitive data.

## In the Lean

`Vau.LTerm` has constructors `var n`, `con n`, `app a b`, `lam t`. It has its own renaming,
substitution and single substitution: [LTerm.rename](#/node/LTerm.rename), [LTerm.up](#/node/LTerm.up),
[LTerm.subst](#/node/LTerm.subst), [LTerm.scons](#/node/LTerm.scons), [LTerm.inst](#/node/LTerm.inst),
built the same way as for vau-x terms.
""",
     [q("Which constructor binds a variable?",
        ["`app`", "`lam`", "`con`", "`var`"],
        1, "`lam t` binds index 0 in `t`."),
      q("What does `embed (con 3)` give?",
        ["`var 3`", "`dat 3`", "`prim 3`", "`vau (dat 3)`"],
        1, "Constants become primitive data."),
      q("Does `LTerm` have pairs or `eval`?",
        ["Yes", "No: only variables, constants, application and abstraction", "Only pairs", "Only eval"],
        1, "It is the plain lambda calculus with constants.")],
     caveats=[DB])

node("LTerm.IsValue",
     "Values of the call-by-value lambda calculus",
     "A lambda value is a variable, a constant or an abstraction. An application is not a value.",
     """
## Plain English

In Plotkin's call-by-value lambda calculus, beta fires only when the argument is a value. Values are the
terms with nothing left to compute at the top: variables, constants and abstractions.

## In the Lean

`Vau.LTerm.IsValue` has constructors `var`, `con`, `lam`. `embed_isValue` and `isValue_of_embed` show
that `v` is a lambda value iff `embed v` is a vau-x [value](#/node/IsValue).
""",
     [q("Is `(lambda.x) y` a value?",
        ["Yes", "No: it is an application", "Only if `y` is a value", "Only after one step"],
        1, "There is no `IsValue.app`."),
      q("Is `lambda.((x x) y)` a value?",
        ["Yes: every abstraction is", "No: its body is an application", "Only if closed", "Only after reduction"],
        0, "`IsValue.lam t` has no condition on the body."),
      q("What links lambda values and vau-x values?",
        ["Nothing", "`v.IsValue <-> IsValue (embed v)` (two lemmas)", "Only for constants", "`confluence`"],
        1, "`embed_isValue` and `isValue_of_embed`.")])

node("LTerm.rename",
     "Renaming lambda variables",
     "`LTerm.rename rn t` changes each free variable `var n` of a lambda term to `var (rn n)`, using `lift rn` "
     "under each `lam`.",
     """
## Plain English

The same operation as [rename](#/node/rename), on lambda terms. It is used to shift a term under one
more binder.

## In the Lean

`Vau.LTerm.rename`. The lemma `embed_rename` says `embed (t.rename rn) = rename rn (embed t)`: the
embedding commutes with renaming.
""",
     [q("Which function does `LTerm.rename` use under `lam`?",
        ["`up`", "`lift`", "`scons`", "`inst`"],
        1, "`rename rn (lam t) = lam (rename (lift rn) t)`."),
      q("Does `embed` commute with renaming?",
        ["Yes: `embed_rename`", "No", "Only for closed terms", "Only for values"],
        0, "Both are defined by the same recursion."),
      q("What is `(con 4).rename rn`?",
        ["`con (rn 4)`", "`con 4`", "`var 4`", "`var (rn 4)`"],
        1, "Constants are not variables.")],
     caveats=[DB])

node("LTerm.up",
     "Lift a lambda substitution under a binder",
     "`LTerm.up sg` keeps index 0 and sends `n + 1` to `sg n` shifted up by one, so that substitution under "
     "`lam` captures nothing.",
     """
## Plain English

The same operation as [up](#/node/up), on lambda terms.

## In the Lean

`Vau.LTerm.up sg 0 = var 0`, `Vau.LTerm.up sg (n + 1) = (sg n).rename Nat.succ`. It is used in the proof
of `embed_subst`.
""",
     [q("What is `LTerm.up sg 0`?",
        ["`sg 0`", "`var 0`", "`lam (var 0)`", "`var 1`"],
        1, "The new bound variable stays itself."),
      q("Why is there a separate `LTerm.up` and not just `up`?",
        ["There is not", "Because it acts on lambda terms, not vau-x terms", "Because it is call-by-name", "Because it binds two variables"],
        1, "The two term types are different; the definitions have the same shape."),
      q("Which lemma uses `LTerm.up` together with `up`?",
        ["`embed_subst`", "`confluence`", "`Run.toSteps`", "`nontrivial`"],
        0, "Under `lam`, the proof checks that `Function.comp embed (LTerm.up sg) = up (Function.comp embed sg)`.")],
     caveats=[DB])

node("LTerm.subst",
     "Parallel substitution on lambda terms",
     "`LTerm.subst sg t` replaces each free variable `var n` of a lambda term by `sg n`, using `LTerm.up sg` "
     "under each `lam`.",
     """
## Plain English

The same operation as [subst](#/node/subst), on lambda terms.

## In the Lean

`Vau.LTerm.subst`. The lemma `embed_subst` says `embed (t.subst sg) = subst (Function.comp embed sg) (embed t)`:
the embedding commutes with substitution. This is what makes beta-v steps map to beta-vau steps.
""",
     [q("What is `(var 2).subst sg`?",
        ["`var 2`", "`sg 2`", "`sg 0`", "`lam (sg 2)`"],
        1, "A free variable is replaced by its term."),
      q("What does `embed_subst` say?",
        ["`embed` is injective", "`embed` commutes with substitution", "Substitution keeps values", "Lambda-v is confluent"],
        1, "`embed (t.subst sg) = subst (Function.comp embed sg) (embed t)`."),
      q("Why is `embed_subst` needed?",
        ["To show beta-v steps become beta-vau steps", "To define `embed`", "For `Run`", "It is not used"],
        0, "`embed_inst` follows from it, and `embed_step` uses `embed_inst`.")],
     caveats=[DB])

node("LTerm.scons",
     "Extend a lambda substitution at index 0",
     "`LTerm.scons v sg` sends index 0 to `v` and `n + 1` to `sg n`.",
     """
## Plain English

The same operation as [scons](#/node/scons), on lambda terms. `LTerm.scons v var` fills in the
variable bound by the outer `lam` with `v` and moves the other free variables down by one.

## In the Lean

`Vau.LTerm.scons v sg 0 = v`, `Vau.LTerm.scons v sg (n + 1) = sg n`.
""",
     [q("What is `LTerm.scons v var 0`?",
        ["`var 0`", "`v`", "`var 1`", "`lam v`"],
        1, "Index 0 gets `v`."),
      q("What is `LTerm.scons v var 2`?",
        ["`var 2`", "`var 1`", "`v`", "`var 3`"],
        1, "`scons v sg (n + 1) = sg n` with `n = 1`."),
      q("Which definition uses `LTerm.scons`?",
        ["`LTerm.inst`", "`embed`", "`LTerm.IsValue`", "`LStep.lam`"],
        0, "`t.inst v = t.subst (scons v var)`.")],
     caveats=[DB])

node("LTerm.inst",
     "Single substitution on lambda terms",
     "`t.inst v` is `t[0 <- v]`: the body `t` of `lambda.t` with `v` for the bound variable. It is the right "
     "side of beta-v.",
     """
## Plain English

The same operation as [inst](#/node/inst), on lambda terms: `t.inst v = t.subst (scons v var)`.

## In the Lean

`Vau.LTerm.inst`. The lemma `embed_inst` says `embed (t.inst v) = inst (embed t) (embed v)`.
""",
     [q("What is `(var 0).inst v`?",
        ["`var 0`", "`v`", "`lam v`", "`var 1`"],
        1, "Index 0 is the bound variable; it gets `v`."),
      q("What is `(var 1).inst v`?",
        ["`v`", "`var 0`", "`var 1`", "`var 2`"],
        1, "The other free variables move down by one, because the binder is gone."),
      q("Which lemma connects `LTerm.inst` and `inst`?",
        ["`embed_inst`", "`subst_inst`", "`rename_inst`", "`Par.inst`"],
        0, "`embed (t.inst v) = inst (embed t) (embed v)`.")],
     caveats=[DB])

node("LStep",
     "One step of the call-by-value lambda calculus",
     "`LStep M N` holds when one beta-v step, `(lambda.t) v -> t[0 <- v]` with `v` a value, fires at one "
     "position inside `M` and gives `N`.",
     """
## Plain English

This is Plotkin's call-by-value lambda calculus (lambda-v) as a reduction relation: the beta rule fires
only when the argument is a [value](#/node/LTerm.IsValue), and it may fire at any position, including
under a lambda.

## In the Lean

`Vau.LStep` has constructors `beta` (needs `v.IsValue`), `lam`, `appL` and `appR`. `LSteps` is
`Star LStep`.
""",
     [q("Can `(lambda.x) ((lambda.y) z)` take a beta step at the top?",
        ["Yes", "No: the argument is an application, not a value", "Only under call-by-name", "Only if `z` is a constant"],
        1, "`LStep.beta` needs `v.IsValue`. The inner application can step first (`appR`)."),
      q("Can a step happen under a lambda?",
        ["No", "Yes: `LStep.lam`", "Only for closed terms", "Only at the top"],
        1, "The relation is the compatible closure, like vau-x `Step`."),
      q("What does `embed_step` say about `LStep`?",
        ["Each `LStep` is a vau-x `Step` between the images", "It is confluent", "It is deterministic", "Nothing"],
        0, "Simulation.")])

node("LConv",
     "The equational theory of call-by-value lambda",
     "`LConv M N` holds when `M` and `N` are joined by a zigzag of call-by-value beta steps.",
     """
## Plain English

The equational theory of lambda-v: [EqvGen](#/node/EqvGen) of [LStep](#/node/LStep). It is the
left side of [conservative_extension](#/node/conservative_extension).

## In the Lean

`abbrev LConv := EqvGen LStep`.
""",
     [q("Is `LConv ((lambda.x) c) c` true for a constant `c`?",
        ["Yes: one beta-v step", "No", "Only if `c` is a variable", "Only in vau-x"],
        0, "`c` is a value, so beta-v fires: `(lambda.x) c -> c`."),
      q("Is `LConv` symmetric?",
        ["Yes", "No", "Only for values", "Only for closed terms"],
        0, "It is an equivalence closure."),
      q("Where is `LConv` used?",
        ["In `conservative_extension`", "In `Run`", "In `CtxEquiv`", "In `confluence`"],
        0, "`LConv M N <-> Conv (embed M) (embed N)`.")])

node("Normal",
     "Normal forms",
     "`Normal t` holds when no vau-x step applies anywhere in `t`. Primitive data such as `5` is normal.",
     """
## Plain English

A normal form is a term where computation has stopped: there is no redex at any position. Normal forms
are what a context can observe in [CtxEquiv](#/node/CtxEquiv).

A value need not be normal: `<vau x.[eval 5]>` is a value but has a redex inside its body.

## In the Lean

`def Normal (t : Term) : Prop := forall t', Not (Step t t')`. Lemmas: `normal_dat` (`dat n` is normal),
`Steps.normal_eq` (a normal form reduces only to itself), and `Conv.normal_eq` (two normal forms that
are equal in the theory are the same term).
""",
     [q("Is `dat 5` a normal form?",
        ["Yes: `normal_dat`", "No", "Only if it is a value", "Only in a context"],
        0, "No rule has a constant at the top, and a constant has no subterms."),
      q("Is `<vau x.[eval 5]>` a normal form?",
        ["Yes, it is a value", "No: `[eval 5] -> 5` fires inside the body", "Only after a call", "Yes, operatives are always normal"],
        1, "Steps inside operative bodies are allowed."),
      q("Can two different normal forms be equal in `Conv`?",
        ["Yes", "No: `Conv.normal_eq`", "Only constants", "Only values"],
        1, "This uses confluence.")])

# ---------------------------------------------------------------- contexts
node("Ctx",
     "One-hole contexts",
     "A context is a vau-x term with one hole in it. `Ctx.plug c t` puts `t` into the hole of `c`.",
     """
## Plain English

To say "no program can tell `t1` from `t2`", we quantify over all ways of putting a term into a bigger
program. A one-hole context is such a bigger program with a hole. The hole may be anywhere: in an
operand, under a `vau`, inside an `eval`.

## In the Lean

`Vau.Ctx` has a constructor `hole`, and one constructor per place where a subterm can sit (`vau`,
`vau0`, `vau2`, `wrap`, `eval`, `pairL`, `pairR`, `combL`, `combR`). [Ctx.plug](#/node/Ctx.plug) fills
the hole.
""",
     [q("Can the hole be under a `vau`?",
        ["Yes: `Ctx.vau`", "No", "Only at the top", "Only in an operand"],
        0, "Contexts may reach into operative bodies."),
      q("How many holes does a `Ctx` have?",
        ["None", "Exactly one", "Any number", "Two"],
        1, "Every constructor except `hole` has exactly one sub-context."),
      q("What is the simplest context?",
        ["`Ctx.hole`, which is just the hole", "`Ctx.eval Ctx.hole`", "`Ctx.vau Ctx.hole`", "There is none"],
        0, "Plugging into `hole` gives the term itself.")])

node("Ctx.plug",
     "Put a term into a context",
     "`c.plug t` replaces the hole of the context `c` by `t`. It does not rename: a context may capture "
     "free variables of `t`.",
     """
## Plain English

Plugging is plain replacement. If the hole is under a `vau`, the free variable `var 0` of `t` becomes
bound by that `vau`. That is how contexts work in the thesis too: capture is the point of a context.

## In the Lean

`Vau.Ctx.plug` is defined by recursion on the context. `Step.plug`, `Steps.plug` and `Conv.plug`: steps
and equalities carry over into every context.
""",
     [q("What is `Ctx.hole.plug t`?",
        ["`t`", "`eval t`", "`()`", "Undefined"],
        0, "The hole is replaced by `t`."),
      q("Does plugging rename variables to avoid capture?",
        ["Yes", "No: a context may capture free variables", "Only under `vau0`", "Only for values"],
        1, "Capture is intended."),
      q("If `Step t t'`, does `Step (c.plug t) (c.plug t')` hold?",
        ["Yes: `Step.plug`", "No", "Only for `hole`", "Only if `t` is a value"],
        0, "This is compatibility.")])

node("CtxEquiv",
     "Contextual equivalence",
     "`CtxEquiv t1 t2`: in every one-hole context, `t1` and `t2` reach exactly the same normal forms. No "
     "program can tell them apart by its results.",
     """
## Plain English

Two terms are contextually equivalent if every program that contains one of them behaves the same way
when it contains the other instead. Here "behaves the same" means: for every normal form `N`, the
program reduces to `N` with one term iff it does with the other. In particular, one version reaches a
normal form iff the other does.

## In the Lean

```
def CtxEquiv (t1 t2 : Term) : Prop :=
  forall (c : Ctx) (N : Term), Normal N -> (Steps (c.plug t1) N <-> Steps (c.plug t2) N)
```

`Normal N` means `N` has no step. `conv_ctxEquiv`: if `Conv t1 t2` then `CtxEquiv t1 t2`.
""",
     [q("What does a context observe in `CtxEquiv`?",
        ["The number of steps", "Which normal forms the program reaches", "Only whether the first step exists", "Types"],
        1, "The definition compares `Steps (c.plug t) N` for every normal `N`."),
      q("Does `CtxEquiv` follow from `Conv`?",
        ["Yes: `conv_ctxEquiv`, which uses confluence", "No", "Only for values", "Only for closed terms"],
        0, "Equal terms have a common reduct in every context; a normal form only reduces to itself."),
      q("Is `CtxEquiv (dat 5) (dat 6)` true?",
        ["Yes", "No: the empty context reaches `5` from one and not the other", "Only in vau-e", "Unknown"],
        1, "Part three of `nontrivial`.")],
     caveats=["This notion of observation is this project's choice. Shutt's Definition 13.90 uses a fixed evaluation order and closed contexts, for calculi with an operational semantics."])
