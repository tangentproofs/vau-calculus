# Step 6 nodes: environment opacity and hygiene in vau-e (Vau/Env/Opacity.lean). Node ids are Lean
# declarations.
from _common import THESIS, make, q

NODES = []
node = make(NODES)


def L(s):
    return s.replace("%T", THESIS)


node("VauE.env_opacity",
     "Environments are opaque",
     "In vau-e, two environments that give the same answer to every lookup cannot be told apart by any "
     "program: in every context, one reduces to a number `n` exactly when the other does.",
     L("""
## Plain English

**Hygiene** means that a binding affects only the part of the program where it is written. Shutt spends
[thesis chapter 5](%T#page=101) on how Kernel keeps fexprs hygienic. One of his tactics is that
**environments are encapsulated**: a program can evaluate a symbol in an environment, but it cannot list
the bindings or take the environment apart. In chapter 15 he names this as one reason why his fexprs do
not make the theory trivial.

This theorem makes the claim precise for vau-e: the only thing a program can learn about an environment
is the answer to lookups.

## The Lean statement

```
theorem env_opacity {bs bs' : Env} (h : forall s, Env.lookup s bs = Env.lookup s bs') (c : Ctx)
    (n : Nat) : Steps (c.plug (env bs)) (dat n) <-> Steps (c.plug (env bs')) (dat n)
```

[Ctx](#/node/VauE.Ctx) is any one-hole context, so the environment can be put anywhere in any program.
The observation is: the program reduces to primitive data `n`.

Two corollaries:

- `shadow_invisible`: `{{s <- a, s <- b, ...}}` and `{{s <- a, ...}}` cannot be told apart: a binding
  hidden behind an earlier binding of the same symbol is invisible.
- `order_invisible`: the order of bindings of different symbols is invisible.

So the Lean's unsorted environments behave, for every program, like Shutt's sorted ones with no symbol
bound twice. (Their equational theory is still weaker: the theorem is about observations, not about
equality of terms.) And `lookup_observable` checks the other side: `{{x <- 5}}` and `{{x <- 6}}` **can**
be told apart, by the context `[eval x _]`.

Also in the file: `match_env_opaque`: a parameter tree can only bind an environment whole, or ignore
it; it cannot take it apart.

## How it is proved

`Sim` relates terms that are equal except that environments are compared only by their lookups.
`sim_step` shows that every step of one side is matched by zero or more steps of the other. The hard
case is a step inside a binding: if the binding is visible, the other side takes the same steps inside
its own visible binding of that symbol (`steps_update`); if it is hidden, the other side does nothing.
`Sim.plug` puts related terms into any context, and `Sim.steps` follows a whole reduction.
"""),
     [q("What can a program learn about an environment, by this theorem?",
        ["Its list of bindings", "Only the answers to lookups", "Nothing at all", "The order of its bindings"],
        1, "Environments with the same lookups give the same observations in every context."),
      q("Can a program tell `{{x <- 5}}` from `{{x <- 6}}`?",
        ["No, environments are fully opaque", "Yes: `lookup_observable` uses the context `[eval x _]`", "Only with mutation", "Only in vau-x"],
        1, "Opacity hides the representation, not the lookups."),
      q("What does `shadow_invisible` say?",
        ["Shadowed bindings are deleted", "A binding hidden behind an earlier binding of the same symbol cannot be observed", "Symbols cannot be rebound", "Environments are sorted"],
        1, "It is `env_opacity` for two environments with the same lookups."),
      q("What is observed in the theorem?",
        ["Termination", "Reduction to primitive data `n`", "Types", "The number of steps"],
        1, "This is the observation chosen here; the node says so.")],
     caveats=[
         "Encapsulated objects (VauE.capsule_opacity) follow the same idea for programmer-defined types.",
         "The observation is reduction to primitive data. A stronger notion (for example observing termination) is not proved here.",
         "This is opacity in pure vau-e: no mutation, no `$define!`, no first-class continuations. Kernel's other hygiene tactics (stable bindings, mutation only of local environments) are not formalized.",
         "`#print axioms VauE.env_opacity` reports `propext` and `Quot.sound`.",
     ])

node("VauE.ignore_hygiene",
     "Hygiene of #ignore",
     "A compound operative whose environment parameter is `#ignore` reduces to the same term when called "
     "from any two dynamic environments: the caller's environment cannot affect the call.",
     """
## Plain English

When `$vau` is given `#ignore` as its environment parameter, the operative it builds refuses its caller's
environment. Shutt notes that this helps hygiene (thesis section 4.2): the body cannot see or depend on
where it was called from. `$lambda` uses exactly this ([derived_lambda](#/node/VauE.derived_lambda)).

## The Lean statement

```
theorem ignore_hygiene {p v b : Term} {e1 e2 e3 m : Env} (hp : IsValue p) (hv : IsValue v)
    (hm : ematch p v = some m) :
    Steps (comb (oper p ign b (env e1)) v (env e2)) (eval b (env (Env.join m e1))) /\\
    Steps (comb (oper p ign b (env e1)) v (env e3)) (eval b (env (Env.join m e1)))
```

Calls from `e2` and from `e3` reach the same term, in which neither `e2` nor `e3` appears.
`ignore_hygiene_conv` states it as an equation of the theory.
""",
     [q("What does `#ignore` as environment parameter do?",
        ["It evaluates the operands", "It refuses the caller's environment: nothing is bound to it", "It deletes the static environment", "It makes the operative an applicative"],
        1, "`ematch ign _ = some []`."),
      q("Does the result of the call depend on the caller's environment `e2`?",
        ["Yes", "No: both calls reach `eval b (env (Env.join m e1))`", "Only through the operands", "Only if `b` is a symbol"],
        1, "The operands here are already values; in a full call they are evaluated in the caller's environment first (see lambda_call)."),
      q("Which definition uses `#ignore` this way?",
        ["`$lambda`", "`list*`", "`$unwrap`", "`eval`"],
        0, "`(list* $vau ptree #ignore body)`.")],
     caveats=["The operand tree `v` is a value here. In a call of an applicative, the operands are first evaluated in the caller's environment, so that environment does matter for the arguments (see VauE.derived_lambda)."])

node("VauE.Ctx",
     "One-hole contexts for vau-e",
     "A vau-e term with one hole. The hole may be anywhere, including inside one binding of an environment.",
     """
## Plain English

To say "no program can tell two terms apart", we put each into every possible surrounding program.
A one-hole context is such a program with a hole.

## In the Lean

`VauE.Ctx` has `hole`, `envAt pre s c post` (the environment `pre ++ (s <- c) :: post`, with the hole in
one binding), and one constructor for each other place a subterm can sit. [Ctx.plug](#/node/VauE.Ctx.plug)
fills the hole.
""",
     [q("Can the hole be inside a binding of an environment?",
        ["No", "Yes: `envAt`", "Only the first binding", "Only in vau-x"],
        1, "Contexts reach every position."),
      q("How many holes does a context have?",
        ["None", "Exactly one", "Two", "Any number"],
        1, "Each constructor except `hole` has one sub-context."),
      q("Is this the same `Ctx` as for vau-x?",
        ["Yes", "No: `VauE.Ctx` is for vau-e terms", "Only for pairs", "Only for eval"],
        1, "vau-x has `Vau.Ctx` for its own terms.")])

node("VauE.Ctx.plug",
     "Put a term into a vau-e context",
     "`c.plug t` replaces the hole of `c` by `t`. Nothing is renamed.",
     """
## Plain English

Plain replacement, as for vau-x ([Ctx.plug](#/node/Ctx.plug)). vau-e has no substitutable variables,
so there is nothing to capture; symbols are looked up in environments.

## In the Lean

`VauE.Ctx.plug` is defined by recursion on the context. `Sim.plug`: related terms stay related in every
context.
""",
     [q("What is `Ctx.hole.plug t`?",
        ["`t`", "`env []`", "`eval t`", "Undefined"],
        0, "The hole is replaced by `t`."),
      q("What is `(Ctx.evalR (sym 1) .hole).plug e`?",
        ["`eval e (sym 1)`", "`eval (sym 1) e`", "`sym 1`", "`e`"],
        1, "The hole is the environment position of `[eval x _]`."),
      q("Does plugging rename anything?",
        ["Yes", "No", "Only symbols", "Only environments"],
        1, "It is plain replacement.")])
