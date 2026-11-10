# Planned nodes. These describe results that have NO Lean yet: every node here is "formal": "planned" in
# site.json, and nothing here may be read as a proved theorem. (The nodes that now have Lean moved to
# results.py in Step 3.) "Planned statement" means "what we intend to state in Lean".
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


# ---------------------------------------------------------------- 13. wrap / unwrap
node("WrapUnwrap",
     "wrap and unwrap: making and taking apart applicatives",
     "`wrap` turns a combiner into an applicative that evaluates its operands first. `unwrap` takes the "
     "wrapper off again. In vau-e the primitive operatives `$wrap` and `$unwrap` have their own delta-rules.",
     L("""
## Plain English

In vau-x, an applicative is written `<T>`: the combiner `T` in a **wrapper**. combine-wrap says what a
wrapper does: evaluate each operand, then pass the results to `T`. See
[Top](#/node/Top).

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

- vau-x already has wrappers `<T>` in its syntax, so the Lean already covers the wrapper and
  combine-wrap as part of the core rules ([Top](#/node/Top)).
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
environment. This is the same idea as in the [lambda embedding](#/node/embed), seen from the
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
([compatible closure](#/node/Step)), and [confluence](#/node/confluence) is proved in Lean
for them. But an actor system has its own semantics (message order, state in environment actors). Whether a
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
