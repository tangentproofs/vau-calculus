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

- An informal node for now. A planned Lean statement would be in the Lean model of vau-e (namespace
  `VauE`), for example: a
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
