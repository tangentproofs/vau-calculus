# Step 4 nodes: vau-e with environments in Lean (namespace VauE, files Vau/Env/*.lean): derived $lambda,
# wrap/unwrap, and the definitions their statements use. Node ids are Lean declarations.
from _common import THESIS, make, q

NODES = []
node = make(NODES)

ENV = ("The Lean environments are unsorted lists with first-binding lookup. Shutt's are sorted with no "
       "symbol bound twice. Lookup agrees with Shutt's lookup on the normalized environment, but Lean environments may hold "
       "shadowed duplicate bindings, which Shutt's grammar forbids, and equality of environment terms is weaker (see VauE.Env). "
       "`VauE.env_opacity` shows that no program can observe the order or the shadowed bindings (observing reduction to primitive data).")
OURS = ("`$eval` and `$list*` have delta-rules written by this project. Shutt uses them in thesis "
        "(4.20)-(4.22) and calls their rules self-evident; he gives rules (9.12) only for `$vau`, `$wrap` "
        "and `$unwrap`.")


def L(s):
    return s.replace("%T", THESIS)


# ---------------------------------------------------------------- derived_lambda (headline)
node("VauE.derived_lambda",
     "$lambda is derived from $vau, wrap and eval",
     "In vau-e, with Shutt's definition of `$lambda`, `(($lambda p b) . args)` evaluated in `e` reduces to `b` "
     "evaluated in `e` with `p` bound to the evaluated arguments; `lambda_static_scope` adds static scope.",
     L("""
## Plain English

In Scheme, `lambda` is primitive. In Kernel it is not. Shutt defines it in a few lines
([thesis (4.10)](%T#page=94)):

```
($define! $lambda
   ($vau (ptree . body) static-env
      (wrap (eval (list* $vau ptree #ignore body)
                  static-env))))
```

Read it from the inside out:

1. `$lambda` is itself an operative. Its operands `(ptree . body)` are **not** evaluated, and it
   receives the environment where it is called as `static-env`.
2. `list*` builds the list `($vau ptree #ignore . body)`, with the primitive `$vau` in front.
3. `eval` evaluates that list in `static-env`, which gives a compound operative whose body runs in the
   environment where the `$lambda` expression was written (static scope), and which ignores its
   caller's environment.
4. `wrap` makes it an applicative, so the operands are evaluated before the body runs.

Shutt states the intended behavior as (4.9): `($lambda ptree x)` is equivalent to
`(wrap ($vau ptree #ignore x))`.

## The Lean statement

```
theorem derived_lambda {p b args vs : Term} {e0 e m : Env} (h0 : Ground e0)
    (h1 : Env.lookup sLambda e = some (lambdaOp e0)) (hp : IsValue p) (hb : IsValue b)
    (hargs : IsList args) (hev : Steps (evalList (env e) args) vs) (hvs : IsValue vs)
    (hm : ematch p vs = some m) :
    Steps (eval (pair (list3 (sym sLambda) p b) args) (env e)) (eval b (env (Env.join m e)))
```

The hypotheses, in words:

- `e0` has the standard bindings of `$vau`, `wrap`, `eval` and `list*` ([Ground](#/node/VauE.Ground)),
  and in `e` the symbol `$lambda` is bound to the operative that (4.10) makes in `e0`
  ([lambdaOp](#/node/VauE.lambdaOp));
- the parameter tree `p` and the body `b` are values (any source code is a value: it has no active
  subterm);
- the operands `args` form a proper list, and evaluating each in `e` gives the values `vs`;
- `p` matches `vs`, with bindings `m`.

The conclusion: the combination reduces to `[eval b (m . e)]`. The body runs in the environment where
the `$lambda` expression was evaluated, extended by the parameters.

## The parts

`Vau/Env/Lambda.lean` proves the steps one by one, following Shutt's traces:

- `lambda_def`: the `$vau` expression of (4.10), evaluated in `e0`, gives `lambdaOp e0` (thesis (4.18));
- `lambda_expr`: `($lambda p b)` evaluated in `e1` gives `<applicative <operative p #ignore b e1>>`
  (thesis (4.20)-(4.22)), and `e1` needs no binding other than `$lambda`;
- `lambda_call`: calling that applicative from **any** environment `e2` evaluates the operands in `e2`
  and then runs `b` in `m . e1`, so `e2` is ignored;
- `lambda_static_scope`: **static scope.** Evaluate `($lambda p b)` in `e1`, bind the result to a
  symbol `f` in another environment `e2`, and call `(f . args)` from `e2`: the arguments are evaluated
  in `e2`, but the body runs in `m . e1`, not in `e2`. (In `derived_lambda` alone the two environments
  are the same `e`, so it cannot tell static from dynamic scope; this theorem can.)
- `lambda_eq_wrap_vau`: thesis (4.9). `($lambda p b)` and `(wrap ($vau p #ignore b))` reduce to the
  same applicative, so they are equal in the equational theory.
- `lambda_id_seven`: a concrete check that the hypotheses can be met: `(($lambda (x) x) 7)` reduces to
  `7` in a real environment.
"""),
     [q("In `lambda_static_scope`, the applicative is made in `e1` and called from `e2`. Where does the body run?",
        ["In `e2`, the caller's environment", "In `e1`, extended by the parameters", "In the empty environment", "In `e0`, where `$lambda` was defined"],
        1, "The conclusion is `eval b (env (Env.join m e1))`. The arguments are evaluated in `e2`, but `e2` is not where the body runs."),
      q("Why must `e0` (not `e`) bind `$vau`, `wrap`, `eval` and `list*`?",
        ["It must not", "Because the body of `$lambda` looks them up in its own local environment, which extends `e0`", "Because `e` is empty", "Because of hygiene rules in Lean"],
        1, "That is the point of the thesis trace: `$vau` is looked up where `$lambda` was defined, and the primitive itself is put into the constructed list."),
      q("What does `lambda_eq_wrap_vau` prove?",
        ["`$lambda` is primitive", "Thesis (4.9): `($lambda p b)` and `(wrap ($vau p #ignore b))` are equal in the equational theory", "`$lambda` is confluent", "`wrap` is the identity"],
        1, "Both sides reduce to `<applicative <operative p #ignore b e>>`."),
      q("Does this theorem assume anything about the arguments?",
        ["No", "Yes: they form a proper list, evaluate to the values `vs`, and `p` matches `vs`; all are stated as hypotheses", "Only that they are numbers", "Only that there is one"],
        1, "Nothing is hidden: every assumption is a named hypothesis.")],
     caveats=[
         "The Lean models Shutt's pure vau-e (section 9.1): no `$define!`, no mutation. So `$lambda` is bound in `e` by hypothesis, not by running `$define!`.",
         "vau-e operatives have one body expression, so the theorem is about `($lambda p b)` with one body expression `b`.",
         OURS,
         ENV,
         "`#print axioms VauE.derived_lambda` reports `propext` and `Quot.sound`.",
         "The theorem gives one reduction sequence. `VauE.confluence` (proved separately) says that any other reduction of the same term can be joined with it again.",
     ])

# ---------------------------------------------------------------- unwrap_wrap
node("VauE.unwrap_wrap",
     "wrap and unwrap",
     "`(wrap c)` makes an applicative from a combiner, and `(unwrap a)` takes the wrapper off. The Lean proves "
     "that if `c` reduces to a value `v`, then `(unwrap (wrap c))` reduces to `v`.",
     L("""
## Plain English

In vau-x and vau-e, an applicative is a combiner in a **wrapper**: `<applicative T>`. Calling it
evaluates each operand first, then passes the results to `T` (rule combine-app).

Kernel's applicatives `wrap` and `unwrap` make and take apart wrappers. vau-e models their underlying
primitive operatives with delta-rules ([thesis (9.12)](%T#page=201)):

```
[combine $wrap (V) e]                    ->  <applicative V>
[combine $unwrap (<applicative V>) e]    ->  V
```

`wrap = <applicative $wrap>`, so its operand is evaluated first.

Every applicative in Kernel is a wrapper around some combiner, often an operative. `$lambda` is defined
this way ([derived_lambda](#/node/VauE.derived_lambda)).

## The Lean statement

```
theorem unwrap_wrap {c v : Term} {e : Env} (hw : Env.lookup sWrap e = some wrapA)
    (hu : Env.lookup sUnwrap e = some unwrapA) (hc : Steps (eval c (env e)) v) (hv : IsValue v) :
    Steps (eval (list2 (sym sUnwrap) (list2 (sym sWrap) c)) (env e)) v
```

If `wrap` and `unwrap` have their standard bindings in `e`, and `c` reduces to a value `v`, then
`(unwrap (wrap c))` reduces to `v`. A value need not be a normal form, so this does not say that `v`
is the only possible result; [confluence](#/node/VauE.confluence) says that any two results can be
joined again.
"""),
     [q("What does `(unwrap (wrap c))` evaluate to?",
        ["An error", "The value of `c`", "`(wrap c)`", "The operands of `c`"],
        1, "`unwrap` removes the wrapper that `wrap` added."),
      q("Is the operand of `wrap` evaluated?",
        ["No", "Yes: `wrap` is an applicative, `<applicative $wrap>`", "Only if it is a symbol", "Only in vau-x"],
        1, "The proof steps through combine-app, which evaluates the operand."),
      q("Which delta-rules does this use?",
        ["Shutt's (9.12) for `$wrap` and `$unwrap`", "This project's `$eval` rule", "beta-vau", "None"],
        0, "`Top.deltaWrap` and `Top.deltaUnwrap` are Shutt's rules.")],
     caveats=[ENV])

# ---------------------------------------------------------------- definitions
node("VauE.Term",
     "Terms of vau-e",
     "A vau-e term is primitive data, a primitive operative, a symbol, `#ignore`, `()`, an environment, a "
     "compound operative, a pair, an applicative, `[eval T e]`, `[combine T1 T2 e]`, or (this project's addition) a capsule.",
     L("""
## Plain English

This is Shutt's grammar (9.1) ([thesis section 9.1](%T#page=195)). Compared with vau-x it adds
**symbols** and **environments**, and drops substitutable variables:

- `[eval T e]` evaluates `T` in the environment `e`;
- `[combine T1 T2 e]` calls the combiner `T1` on the operand tree `T2`, from the environment `e`;
- `<operative ptree eparm body senv>` is a compound operative: it remembers its parameter tree, its
  environment parameter, its body and its static environment;
- `<applicative T>` wraps a combiner.

## In the Lean

`VauE.Term` has one constructor per form: `dat`, `prim` (one of the [primitives](#/node/VauE.Prim)),
`sym`, `ign`, `nil`, `env` (a list of bindings, see [Env](#/node/VauE.Env)), `oper`, `pair`, `app`,
`eval`, `comb`, and `capsule k v` (an encapsulated object of type `k`; this project's addition for
[encapsulation types](#/node/VauE.capsule_opacity)). Symbols are numbers; the `$lambda` file names the
ones it uses with notations such as `sLambda` (the number 4).
"""),
     [q("Which of these is new in vau-e compared with vau-x?",
        ["Pairs", "Symbols and environments", "Applicatives", "`[eval T]`"],
        1, "vau-x has neither symbols nor environments."),
      q("How many parts does a compound operative have?",
        ["One: the body", "Four: parameter tree, environment parameter, body, static environment", "Two", "Three"],
        1, "`oper ptree eparm body senv`."),
      q("What is `[combine T1 T2 e]`?",
        ["A pair", "A call of combiner `T1` on operands `T2`, from environment `e`", "An environment", "A symbol lookup"],
        1, "The third part is the caller's (dynamic) environment.")],
     caveats=["Symbols and primitive data are numbers in the Lean. Primitive operatives are the ones in `Prim`. The `capsule` term is not in Shutt's grammar; it models Kernel's encapsulated objects."])

node("VauE.Prim",
     "Primitive operatives of the Lean vau-e",
     "`$vau`, `$wrap`, `$unwrap`, `$eval`, `$list*`, and for each encapsulation type `k`: `$encap k`, `$isEncap k`, `$decap k`. For a standard applicative "
     "`foo`, `$foo` is its underlying operative: `foo = <applicative $foo>`.",
     """
## Plain English

Shutt gives delta-rules for `$vau`, `$wrap` and `$unwrap` (9.12). The definition of `$lambda` also uses
the applicatives `eval` and `list*`, so the Lean adds their underlying operatives `$eval` and `$list*`.

## In the Lean

`VauE.Prim` has constructors `vau`, `wrap`, `unwrap`, `eval`, `listStar`, and `encap k`, `isEncap k`,
`decap k` for encapsulation types (see [capsule_opacity](#/node/VauE.capsule_opacity)). Their rules are
in [Top](#/node/VauE.Top).
""",
     [q("What is the applicative `wrap` in the Lean?",
        ["A primitive", "`app (prim .wrap)`, the wrapped operative `$wrap`", "A compound operative", "A symbol"],
        1, "See `wrapA`."),
      q("Which of these primitives have rules written by this project, not Shutt?",
        ["`$vau` and `$wrap`", "`$eval` and `$list*`", "`$unwrap`", "None"],
        1, "Shutt uses them in his trace but leaves their rules out as self-evident. The encapsulation primitives are also this project's."),
      q("Does the Lean have `$define!`?",
        ["Yes", "No: pure vau-e has no mutation", "Only for `$lambda`", "Only at top level"],
        1, "`$lambda` is bound in an environment by hypothesis instead.")],
     caveats=[OURS])

node("VauE.Env.lookup",
     "Looking up a symbol",
     "`Env.lookup s e` is the term bound to the symbol `s` by the first binding of `s` in `e`, or nothing if "
     "`s` is not bound.",
     """
## Plain English

This is Shutt's `lookup(s, e)` (9.6). The rule eval-sym, `[eval s e] -> lookup(s, e)`, uses it.

## In the Lean

`Env.lookup s [] = none`, and `Env.lookup s ((s', t) :: r)` is `some t` if `s = s'`, else
`Env.lookup s r`. `Env.lookup_join`: a lookup in `e1 . e2` tries `e1` first.
""",
     [q("What is `Env.lookup 3 [(3, a), (3, b)]`?",
        ["`some b`", "`some a`", "`none`", "Both"],
        1, "The first binding wins."),
      q("What is `Env.lookup 5 []`?",
        ["`some nil`", "`none`", "An error", "`some (sym 5)`"],
        1, "An empty environment binds nothing."),
      q("Which rule uses lookup?",
        ["eval-pair", "eval-sym", "beta-oper", "delta-wrap"],
        1, "`Top.evalSym`.")],
     caveats=[ENV])

node("VauE.Env.join",
     "Joining environments",
     "`Env.join e1 e2` is `e1` followed by `e2`, so a binding in `e1` wins over one in `e2`. This is how local "
     "bindings shadow outer ones.",
     """
## Plain English

Shutt's `e1 . e2` (9.6) merges two sorted environments, keeping the binding from `e1` when both bind a
symbol. The Lean appends the lists; lookup takes the first binding, which gives the same answers.

## In the Lean

`Env.join e1 e2 = e1 ++ e2`. Lemmas: `Env.join_emp`, `Env.lookup_join`.
""",
     [q("If `e1` and `e2` both bind `s`, which binding does a lookup in `Env.join e1 e2` see?",
        ["The one in `e2`", "The one in `e1`", "Neither", "Both"],
        1, "`Env.lookup_join`."),
      q("What is `Env.join e []`?",
        ["`[]`", "`e`", "`e ++ e`", "Undefined"],
        1, "`Env.join_emp`."),
      q("Where does beta-oper use join?",
        ["To put the call's bindings in front of the static environment", "To evaluate operands", "Never", "To build applicatives"],
        0, "`eval body (env (Env.join m e1))`.")],
     caveats=[ENV])

node("VauE.syms",
     "Symbols of a parameter tree",
     "`syms p` lists the symbols in a parameter tree `p`. It is used to check that the two halves of a pair "
     "parameter tree share no symbol.",
     """
## Plain English

Shutt's `match` on a pair parameter tree `(T1 . T2)` is defined only if `T1` and `T2` have no symbols in
common (9.6), so that no symbol is bound twice.

## In the Lean

`syms (sym s) = [s]`, `syms (pair a b) = syms a ++ syms b`, and `[]` for other terms.
""",
     [q("What is `syms (pair (sym 1) (pair (sym 2) nil))`?",
        ["`[]`", "`[1, 2]`", "`[1]`", "`[2]`"],
        1, "The symbols of both halves."),
      q("What is `syms ign`?",
        ["`[ign]`", "`[]`", "`[0]`", "Undefined"],
        1, "`#ignore` binds nothing."),
      q("Why is `syms` needed?",
        ["For lookup", "To check that a pair parameter tree binds no symbol twice", "For eval", "It is not"],
        1, "See `ematch`.")])

node("VauE.disjoint",
     "No common element",
     "`disjoint xs ys` is `true` when the two lists of symbols have no element in common.",
     """
## Plain English

A Boolean test used by [ematch](#/node/VauE.ematch) and in the hypothesis of
[vau_call](#/node/VauE.vau_call).

## In the Lean

`disjoint xs ys = xs.all (fun x => !(ys.contains x))`. Lemma: `disjoint_nil`.
""",
     [q("What is `disjoint [1, 2] [3]`?",
        ["`true`", "`false`", "Undefined", "`[1, 2, 3]`"],
        0, "No common element."),
      q("What is `disjoint [1, 2] [2]`?",
        ["`true`", "`false`", "`[2]`", "Undefined"],
        1, "2 is in both."),
      q("What is `disjoint xs []` for any `xs`?",
        ["`false`", "`true`", "Depends on `xs`", "Undefined"],
        1, "`disjoint_nil`.")])

node("VauE.ematch",
     "Matching a parameter tree",
     "`ematch p t` gives the bindings made by matching the parameter tree `p` against the operand tree `t`: a "
     "symbol binds anything, `#ignore` binds nothing, `()` matches `()`, a pair matches a pair part by part.",
     """
## Plain English

This is Shutt's `match` (9.6). It is how a compound operative binds its operands and the caller's
environment.

## In the Lean

`ematch ign _ = some []`, `ematch nil nil = some []`, `ematch (sym s) t = some [(s, t)]`, and for pairs
it joins the two halves' bindings if both match and the halves share no symbol
([syms](#/node/VauE.syms), [disjoint](#/node/VauE.disjoint)). Otherwise `none`.
""",
     [q("What does `ematch (sym 5) t` give?",
        ["`none`", "`some [(5, t)]`", "`some []`", "`t`"],
        1, "A symbol binds whatever it meets."),
      q("What does `ematch ign t` give?",
        ["`none`", "`some []`: it matches and binds nothing", "`some [(0, t)]`", "`t`"],
        1, "`#ignore` matches anything."),
      q("Does `ematch nil (dat 3)` match?",
        ["Yes", "No: `()` matches only `()`", "Only if 3 is a value", "It binds 3"],
        1, "It gives `none`.")])

node("VauE.SelfEval",
     "Self-evaluating terms in vau-e",
     "Primitive data, primitive operatives, environments, `#ignore`, `()`, compound operatives and capsules "
     "evaluate to themselves (rule eval-self).",
     """
## Plain English

Shutt's set `S` (9.1). Symbols are not self-evaluating (they are looked up), and neither are pairs
(combinations) or applicatives (rule eval-app).

## In the Lean

`VauE.SelfEval` has seven constructors: `dat`, `prim`, `env`, `ign`, `nil`, `oper`, `capsule`.
""",
     [q("Is a symbol self-evaluating?",
        ["Yes", "No: it is looked up (eval-sym)", "Only if bound", "Only `$vau`"],
        1, "There is no `SelfEval.sym`."),
      q("Is an environment self-evaluating?",
        ["Yes", "No", "Only the empty one", "Only in vau-x"],
        0, "`SelfEval.env`."),
      q("Is `$vau` (the primitive) self-evaluating?",
        ["Yes: `SelfEval.prim`", "No", "Only when wrapped", "Only in `e0`"],
        0, "This is why the `$vau` that `list*` puts in the list stays itself when evaluated in a new environment.")])

node("VauE.IsValue",
     "Values in vau-e",
     "A vau-e value is a term whose every active subterm is within an operative or an environment. Symbols, "
     "environments and compound operatives are values.",
     """
## Plain English

Shutt's `V` (9.1). Operands of a compound operative must be values (rule beta-oper), and so must the
operands of the delta-rules: this is eager argument evaluation. Any source code is a value, because it
has no active subterm.

## In the Lean

`VauE.IsValue` has constructors for `dat`, `prim`, `sym`, `ign`, `nil`, `env e` (any bindings),
`oper` (any parts), `capsule` (any content; this is this project's choice, like Shutt's choice for
environments), `pair` of values and `app` of a value.
""",
     [q("Is a symbol a value?",
        ["Yes", "No", "Only if bound", "Only in vau-x"],
        0, "`IsValue.sym`."),
      q("Is `[eval x e]` a value?",
        ["Yes", "No: it is active and not inside an operative or environment", "Only if `x` is a value", "Always"],
        1, "There is no `IsValue.eval`."),
      q("Must the bindings of an environment be values for the environment to be a value?",
        ["Yes", "No: `IsValue.env e` holds for any `e`", "Only the first", "Only in Kernel"],
        1, "Shutt treats environments as values even when they hold non-values.")])

node("VauE.IsList",
     "Proper lists in vau-e",
     "`IsList t` holds when `t` is `()` or a pair whose second part is a proper list. combine-app needs a "
     "proper list of operands.",
     """
## Plain English

The same idea as in vau-x ([IsList](#/node/IsList)): an applicative must know where its operands end.

## In the Lean

`VauE.IsList` has constructors `nil` and `cons`.
""",
     [q("Is `(1 2)` a proper list?",
        ["Yes", "No", "Only if 1 and 2 are values", "Only in vau-x"],
        0, "`(1 . (2 . ()))`."),
      q("Is `(1 . 2)` a proper list?",
        ["Yes", "No", "Yes, of length 2", "Only if evaluated"],
        1, "It does not end in `()`."),
      q("Which rule needs it?",
        ["eval-sym", "combine-app", "delta-vau", "eval-self"],
        1, "`Top.combApp`.")])

node("VauE.evalList",
     "Evaluate each operand, in an environment",
     "`evalList e (T1 ... Tm)` is `([eval T1 e] ... [eval Tm e])`. It is the right side of combine-app, and "
     "the arguments hypothesis of derived_lambda.",
     """
## Plain English

When an applicative is called from environment `e`, each operand is evaluated in `e`.

## In the Lean

`evalList e (pair a b) = pair (eval a e) (evalList e b)`, identity otherwise.
""",
     [q("What is `evalList e (1 2)`?",
        ["`(1 2)`", "`([eval 1 e] [eval 2 e])`", "`[eval (1 2) e]`", "`e`"],
        1, "Each element gets its own `eval`."),
      q("In which environment are the operands evaluated?",
        ["The static environment", "The caller's environment `e`", "The empty environment", "`e0`"],
        1, "That is why `lambda_call` evaluates the arguments in `e2`."),
      q("What does the hypothesis `Steps (evalList (env e) args) vs` say?",
        ["The arguments are values already", "Evaluating each argument in `e` gives the values `vs`", "`args` is empty", "Nothing"],
        1, "It is a reduction of the whole list.")])

node("VauE.buildListStar",
     "What list* builds",
     "`buildListStar (x1 ... xn)` is `(x1 ... xn-1 . xn)`: like `list`, but the last argument is the rest of "
     "the list. It is the result of this project's delta-rule for `$list*`.",
     """
## Plain English

`list*` is a standard Kernel applicative (from MacLisp and Common Lisp). In `$lambda`,
`(list* $vau ptree #ignore body)` with `body = (b)` builds `($vau ptree #ignore b)`.

## In the Lean

`buildListStar (pair x nil) = some x`, `buildListStar (pair x rest) = (buildListStar rest)` with `x`
consed in front, and `none` otherwise (no arguments, or an improper list).
""",
     [q("What is `list*` of `(1 2 (3))`?",
        ["`(1 2 (3))`", "`(1 2 3)`", "`(1 . 2)`", "`((3))`"],
        1, "`(1 2 . (3))` is `(1 2 3)`."),
      q("What is `list*` of `(5)`?",
        ["`(5)`", "`5`", "`()`", "Undefined"],
        1, "One argument is returned as it is."),
      q("Who wrote the rule for `$list*`?",
        ["Shutt, (9.12)", "This project", "Kernel's report", "Nobody"],
        1, "Shutt leaves it out as self-evident.")],
     caveats=[OURS])

node("VauE.Top",
     "The vau-e rules",
     "The general rules (9.7) of vau-e (eval-self, eval-sym, eval-pair, eval-app, beta-oper, combine-app) and "
     "delta-rules for `$vau`, `$wrap`, `$unwrap` (Shutt's (9.12)), and `$eval`, `$list*` and encapsulation types (this project's).",
     L("""
## Plain English

| rule | one step | thesis |
|---|---|---|
| eval-self | `[eval S e] -> S` | (9.7S) |
| eval-sym | `[eval s e] -> lookup(s, e)` | (9.7s) |
| eval-pair | `[eval (T1 . T2) e] -> [combine [eval T1 e] T2 e]` | (9.7p) |
| eval-app | `[eval <applicative T> e] -> <applicative [eval T e]>` | (9.7a) |
| beta-oper | `[combine <operative V1 V2 T e1> V3 e2] -> [eval T match((V1 . V2), (V3 . e2)) . e1]` | (9.7beta) |
| combine-app | `[combine <applicative T> (T1 ... Tm) e] -> [combine T ([eval T1 e] ... [eval Tm e]) e]` | (9.7gamma) |
| delta-vau | `[combine $vau (V1 V2 V3) e] -> <operative V1 V2 V3 e>` | (9.12) |
| delta-wrap | `[combine $wrap (V) e] -> <applicative V>` | (9.12) |
| delta-unwrap | `[combine $unwrap (<applicative V>) e] -> V` | (9.12) |
| delta-eval | `[combine $eval (V e1) e] -> [eval V e1]` | this project |
| delta-list* | `[combine $list* (V1 ... Vn) e] -> (V1 ... Vn-1 . Vn)` | this project |
| delta-encap | `[combine $encap_k (V) e] -> <capsule k V>` | this project |
| delta-isEncap | `[combine $isEncap_k (V1 ... Vn) e] -> #t` if all `Vi` are capsules of type `k`, else `#f` | this project |
| delta-decap | `[combine $decap_k (<capsule k V>) e] -> V` | this project |

See [thesis (9.7)](%T#page=199) and [(9.12)](%T#page=201).

## In the Lean

`VauE.Top` has one constructor per row. [Step](#/node/VauE.Step) is its compatible closure.
"""),
     [q("In beta-oper, which environment does the body run in?",
        ["`e2`, the caller's", "The match bindings in front of `e1`, the static environment", "The empty environment", "`e1` alone"],
        1, "`[eval T match(...) . e1]`."),
      q("Must the operands of a compound operative be values?",
        ["No", "Yes: `V3` in beta-oper", "Only symbols", "Only for applicatives"],
        1, "This is eager argument evaluation."),
      q("Which of these rules are this project's, not Shutt's?",
        ["delta-vau and delta-wrap", "delta-eval and delta-list*", "eval-sym", "beta-oper"],
        1, "Shutt gives (9.12) only for `$vau`, `$wrap`, `$unwrap`. The encapsulation rules are also this project's.")],
     caveats=[
         "Where (9.12) writes the dynamic-environment operand as a value `V`, the Lean requires a literal environment `env e`, following Definition 9.10(4). The Lean `$eval` rule requires a value and a literal environment operand, and `$list*` requires its whole operand list to be a value.",
         "Thesis (9.7a) is printed as `[eval <applicative T>] -> <applicative [eval T]>`, without the environment operand. The Lean reads it as `[eval <applicative T> e] -> <applicative [eval T e]>`.",
         OURS,
     ])

node("VauE.Step",
     "One step of vau-e",
     "`Step t t'` holds when one vau-e rule fires at one position inside `t`, including inside the bindings of "
     "an environment and inside every part of a compound operative.",
     """
## Plain English

The compatible closure of [Top](#/node/VauE.Top), as for vau-x ([Step](#/node/Step)). Shutt's
contexts (9.5) reach every subterm position, including bindings inside an environment; so does the Lean.

## In the Lean

`VauE.Step` has `top`, `envHere` and `envThere` (a step inside a binding), and congruences for every
part of `oper`, `pair`, `app`, `eval`, `comb` and `capsule`. [Steps](#/node/VauE.Steps) is zero or more steps.
""",
     [q("Can a step happen inside a binding of an environment?",
        ["No", "Yes: `envHere` and `envThere`", "Only the first binding", "Only in vau-x"],
        1, "Shutt's contexts include binding contexts."),
      q("Can a step happen inside the body of a compound operative?",
        ["No", "Yes: `oper3`", "Only after a call", "Only for `$vau`"],
        1, "As in vau-x."),
      q("Is confluence of `VauE.Steps` proved?",
        ["Yes: `VauE.confluence`", "No", "Only for `$lambda`", "Only for environments"],
        0, "By the same parallel-reduction method as for vau-x.")])

node("VauE.Steps",
     "Reduction in vau-e",
     "`Steps t t'` holds when `t'` can be reached from `t` by zero or more vau-e steps.",
     """
## Plain English

Zero or more steps of [Step](#/node/VauE.Step).

## In the Lean

`abbrev Steps := Vau.Star Step` (the same [Star](#/node/Star) as for vau-x). Congruences:
`Steps.pair`, `Steps.app`, `Steps.evalL`, `Steps.comb`. `VauE.Conv` is the equational theory.
""",
     [q("Does `Steps t t` hold?",
        ["Yes", "No", "Only for values", "Only for environments"],
        0, "Zero steps."),
      q("Which closure is `Steps` built from?",
        ["`Vau.Star`", "`Vau.EqvGen`", "`List`", "None"],
        0, "The same reflexive-transitive closure as for vau-x."),
      q("Which relation is the equational theory of vau-e?",
        ["`VauE.Steps`", "`VauE.Conv`", "`VauE.Top`", "`VauE.ematch`"],
        1, "`Conv := Vau.EqvGen Step`.")])

def _list(n):
    args = " ".join(f"a{i}" for i in range(1, n + 1))
    node(f"VauE.list{n}",
         f"The list of {n} element{'s' if n > 1 else ''}",
         f"`list{n} {args}` is the proper list `({args})`, written with pairs and `()`.",
         f"""
## Plain English

A short name for writing Kernel source code in the Lean: `list{n} {args}` is `({args})`, which is
`{" ".join(f"(a{i} ." for i in range(1, n + 1))} (){")" * n}`.

## In the Lean

An `abbrev`, so it unfolds to nested `pair` terms ending in `nil`.
""",
         [q(f"How many elements does `list{n} {args}` have?", [str(n), str(n + 1), "0", "Unknown"], 0, f"It lists exactly {n} terms."),
          q(f"Does `list{n}` end in `()`?", ["Yes", "No"], 0, "It is a proper list."),
          q(f"Is `list{n}` a new kind of term?", ["Yes", "No: it is an abbreviation for pairs"], 1, "It unfolds by definition.")])


for _n in (1, 2, 3, 4):
    _list(_n)


def _app(name, prim, word):
    node(f"VauE.{name}",
         f"The applicative {word}",
         f"`{name}` is `<applicative ${word}>`: the standard applicative `{word}`, whose underlying operative is "
         f"the primitive `${word}`.",
         f"""
## Plain English

In Kernel, `{word}` evaluates its operands and then acts on the results. In the calculus it is the
primitive operative `${word}` in a wrapper. A hypothesis such as `Env.lookup s e = some {name}` says that
the symbol `{word}` has its standard binding in `e`.

## In the Lean

`abbrev {name} : Term := app (prim .{prim})`.
""",
         [q(f"Is `{name}` an operative or an applicative?", ["Operative", "Applicative"], 1, "It is `app (prim ...)`."),
          q(f"Are the operands of `{word}` evaluated?", ["Yes", "No"], 0, "Rule combine-app evaluates them first."),
          q(f"What is the underlying combiner of `{name}`?", [f"`prim .{prim}`", "A compound operative", "`nil`"], 0, "Unwrapping gives the primitive.")])


_app("wrapA", "wrap", "wrap")
_app("unwrapA", "unwrap", "unwrap")
_app("evalA", "eval", "eval")
_app("listStarA", "listStar", "list*")

node("VauE.Ground",
     "An environment with the standard bindings for $lambda",
     "`Ground e` says that in `e` the symbols `$vau`, `wrap`, `eval` and `list*` have their standard "
     "bindings. It is the environment `e0` of thesis (4.18), where `$lambda` is defined.",
     """
## Plain English

The definition of `$lambda` uses four standard combiners. Shutt assumes them in the environment `e0`
where `$lambda` is defined. `Ground e0` states exactly that.

## In the Lean

A structure with four fields: `Env.lookup sVau e = some (prim .vau)`, `Env.lookup sWrap e = some wrapA`,
`Env.lookup sEval e = some evalA`, `Env.lookup sListStar e = some listStarA`. `ground_groundEnv` shows
an environment that satisfies it.
""",
     [q("Which symbols must `Ground e` bind?",
        ["`$lambda` only", "`$vau`, `wrap`, `eval`, `list*`", "All symbols", "None"],
        1, "The four combiners in the body of `$lambda`."),
      q("Must the calling environment satisfy `Ground`?",
        ["Yes", "No: only `e0`, where `$lambda` was made", "Only for `wrap`", "Only for `eval`"],
        1, "The body of `$lambda` looks them up in its own local environment, which extends `e0`."),
      q("Is `Ground` satisfiable?",
        ["Unknown", "Yes: `ground_groundEnv`", "No", "Only for empty environments"],
        1, "A concrete environment satisfies it.")])

node("VauE.lambdaOp",
     "The compound operative $lambda",
     "`lambdaOp e0` is `<operative (ptree . body) static-env (wrap ...) e0>`: what Shutt's definition (4.10) "
     "evaluates to in `e0`.",
     """
## Plain English

Evaluating `($vau (ptree . body) static-env (wrap ...))` in `e0` builds this compound operative
(thesis (4.18)). `lambda_def` proves it. Its parameter tree `(ptree . body)` binds the first operand to
`ptree` and the rest to `body`; its environment parameter `static-env` binds the caller's environment.

## In the Lean

`abbrev lambdaOp (e0 : Env) : Term := oper (pair (sym sPtree) (sym sBody)) (sym sStatic) lambdaBody (env e0)`.
The body is [lambdaBody](#/node/VauE.lambdaBody).
""",
     [q("What is the static environment of `lambdaOp e0`?",
        ["The caller's", "`e0`, where `$lambda` was defined", "Empty", "`static-env`"],
        1, "The last part of `oper`."),
      q("What does `static-env` bind when `$lambda` is called?",
        ["`e0`", "The environment of the call to `$lambda`", "Nothing", "The body"],
        1, "It is the environment parameter."),
      q("Which theorem shows that the source of (4.10) evaluates to `lambdaOp e0`?",
        ["`lambda_def`", "`lambda_call`", "`unwrap_wrap`", "`confluence`"],
        0, "Thesis (4.18).")])

node("VauE.lambdaBody",
     "The body of $lambda",
     "`lambdaBody` is the source `(wrap (eval (list* $vau ptree #ignore body) static-env))`.",
     """
## Plain English

The body of [lambdaOp](#/node/VauE.lambdaOp). It wraps the result of [srcEval](#/node/VauE.srcEval).

## In the Lean

`abbrev lambdaBody : Term := list2 (sym sWrap) srcEval`.
""",
     [q("What is the first element of `lambdaBody`?",
        ["The symbol `wrap`", "The primitive `$wrap`", "`eval`", "`$vau`"],
        0, "It is source code: the symbol, looked up when evaluated."),
      q("Is `lambdaBody` a value?",
        ["Yes: it is source code with no active subterm", "No", "Only after evaluation", "Only in `e0`"],
        0, "Only symbols and pairs."),
      q("What does evaluating it produce, in the trace?",
        ["A symbol", "An applicative around a compound operative", "A number", "An environment"],
        1, "`<applicative <operative p #ignore b e1>>`.")])

node("VauE.srcEval",
     "(eval (list* ...) static-env)",
     "`srcEval` is the source `(eval (list* $vau ptree #ignore body) static-env)`: it builds a `$vau` "
     "combination and evaluates it in the environment where `$lambda` was called.",
     """
## Plain English

Part of the body of `$lambda`. `eval_srcEval` proves (thesis (4.21)): in the local environment of the
call, it evaluates to `<operative p #ignore b e1>`.

## In the Lean

`abbrev srcEval : Term := list3 (sym sEval) srcListStar (sym sStatic)`.
""",
     [q("In which environment is the built `$vau` combination evaluated?",
        ["`e0`", "`static-env`, the environment of the call to `$lambda`", "The empty one", "The arguments' environment"],
        1, "That makes it the static environment of the new operative."),
      q("What does `srcEval` evaluate to?",
        ["`<operative p #ignore b e1>`", "`<applicative ...>`", "`b`", "`p`"],
        0, "The wrapping happens one level up."),
      q("Which lemma proves this?",
        ["`eval_srcEval`", "`lambda_def`", "`unwrap_wrap`", "`vau_call`"],
        0, "It follows thesis (4.21).")])

node("VauE.srcListStar",
     "(list* $vau ptree #ignore body)",
     "`srcListStar` is the source `(list* $vau ptree #ignore body)`. It builds the list `($vau p #ignore b)`, "
     "with the primitive `$vau` (not the symbol) in front.",
     """
## Plain English

Because `$vau` is looked up in the local environment of `$lambda` (which extends `e0`), the built list
holds the primitive itself. So when it is later evaluated in another environment, that environment need
not bind `$vau`: the primitive is self-evaluating. Shutt points this out after (4.21).

## In the Lean

`abbrev srcListStar : Term := pair (sym sListStar) (list4 (sym sVau) (sym sPtree) ign (sym sBody))`.
`eval_srcListStar` proves that it evaluates to `list4 (prim .vau) p ign b`.
""",
     [q("What is first in the built list?",
        ["The symbol `$vau`", "The primitive `$vau`", "`list*`", "`#ignore`"],
        1, "The symbol was evaluated in the local environment."),
      q("Why does that matter?",
        ["It does not", "The caller's environment need not bind `$vau`", "It makes the list shorter", "It is needed for confluence"],
        1, "`lambda_expr` needs no binding in `e1` other than `$lambda`."),
      q("What does `body` hold when `$lambda` is called as `($lambda p b)`?",
        ["`b`", "`(b)`", "`p`", "`(p b)`"],
        1, "The parameter tree `(ptree . body)` binds the rest of the operands.")])

# ---------------------------------------------------------------- confluence of vau-e (headline)
node("VauE.confluence",
     "Confluence of the vau-e rules",
     "If `t ->* s1` and `t ->* s2` in vau-e, then `s1 ->* u` and `s2 ->* u` for some `u`. Proved directly for "
     "this formalization's vau-e rules by parallel reduction, not through Shutt's general framework.",
     L("""
## Plain English

A relation is **confluent** if two different reduction paths from one term can always be joined again
(see [confluence](#/node/confluence) for vau-x). Shutt shows that vau-e, like vau-x, is Church-Rosser,
through his theorem on regular substitutive reduction systems (thesis chapter 13 and section 14.1.4).

## The Lean statement

```
theorem confluence {t s1 s2 : Term} (h1 : Steps t s1) (h2 : Steps t s2) :
    exists u, Steps s1 u /\\ Steps s2 u
```

in namespace `VauE`, about [VauE.Steps](#/node/VauE.Steps): the rules of [VauE.Top](#/node/VauE.Top)
(Shutt's (9.7), his delta-rules (9.12) for `$vau`, `$wrap`, `$unwrap`, and this project's delta-rules
for `$eval`, `$list*` and encapsulation types) in the compatible closure, including steps inside environment bindings.

Also proved: `VauE.church_rosser` (terms equal in the theory have a common reduct) and
`VauE.normal_unique` (a term reduces to at most one normal form).

## How it is proved

In `Vau/Env/Confluence.lean`, by parallel reduction and complete developments, as for vau-x. vau-e has
no substitution, so there is no substitution lemma. The new work is to show that parallel steps keep
what each rule looks at:

- `Par.lookup_some`: reducing inside the bindings of an environment keeps every lookup defined, with a
  reduced result;
- `Par.pattern` and `Par.ematch_some`: a parameter tree that matches cannot change, and a match stays
  defined when the operand tree and the dynamic environment are reduced;
- `Par.isList`, `Par.isValue`, `Par.buildListStar_some`: proper lists, values and `list*` arguments
  keep their shape.

`Par.to_cd` (every parallel step from `t` can be completed to `cd t`) then gives the diamond property.
"""),
     [q("Which rules does `VauE.confluence` cover?",
        ["All of Kernel", "This formalization's vau-e rules: (9.7), (9.12) and the project's `$eval`, `$list*` and encapsulation rules", "Only the general schemata (9.7)", "Only vau-x"],
        1, "Other delta-rules would need their own check."),
      q("What replaces the substitution lemma of the vau-x proof?",
        ["Nothing is needed", "Lemmas that parallel steps keep lookups, matches, lists and values", "A typing lemma", "Shutt's Theorem 13.104"],
        1, "vau-e has no substitution; its rules look up, match and take apart lists instead."),
      q("What does `VauE.normal_unique` add?",
        ["Every term has a normal form", "A term reduces to at most one normal form", "Reduction is deterministic", "Environments are sorted"],
        1, "It follows from confluence; it does not say that a normal form exists.")],
     caveats=[
         "This does not formalize Shutt's regular SRS framework; it checks the conclusion for this formalization's rules by a direct proof.",
         "Environments are unsorted lists here, so this is confluence of a calculus whose equational theory is weaker than Shutt's vau-e (see VauE.Env). Steps inside shadowed bindings are included.",
         "`#print axioms VauE.confluence` reports `propext` and `Quot.sound`.",
     ])
