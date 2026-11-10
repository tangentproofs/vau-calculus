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
