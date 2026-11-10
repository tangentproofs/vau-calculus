# Step 8 nodes: an actor-style evaluator for vau-e (Vau/Env/Actors.lean). Node ids are Lean declarations.
from _common import DALE_FEXPR, DALE_EXT, DALE_ACTORS, make, q

NODES = []
node = make(NODES)

MODEL = ("The actor model here is this project's tree-shaped abstraction of Schumacher's design: pending messages "
         "and waiting customers form a tree, and any pending message may be delivered next. It does not model actor "
         "addresses, mailboxes, message order or fairness, environment actors forwarding `#lookup` step by step, or "
         "Humus. The theorems are about this model, not about Schumacher's code or a general actor semantics.")


def L(s):
    return s.replace("%D1", DALE_FEXPR).replace("%D2", DALE_EXT).replace("%D3", DALE_ACTORS)


node("VauE.actor_determinate",
     "Concurrent actor evaluation gives one answer",
     "In a Lean model of Schumacher's actor evaluator, where operands are evaluated concurrently, any two runs "
     "(any two interleavings) that reply primitive data reply the same data.",
     L("""
## Plain English

Dale Schumacher builds an evaluator for a Kernel-like language out of **actors**: objects that react to
messages ([Fexpr the Ultimate Lambda](%D1), [Semantic Extensibility with Vau](%D2),
[Implementing Actors in Kernel](%D3)). In his Humus code:

- an expression answers an `#eval` request; a pair evaluates its left part with a new customer
  `k_comb`, which then sends `#comb` with the right part to the combiner that comes back;
- a combiner answers `#comb`; an applicative evaluates its operands with a fork/join pair, so the
  operands are evaluated **concurrently**, then sends `#comb` to its underlying combiner;
- an environment answers `#lookup`, and forwards it to its parent if it does not have the symbol.

Because messages can be delivered in any order, one program has many possible runs. Does the answer
depend on the order? We found no published confluence proof for such an actor layer. This theorem
answers the question for a Lean model of the design.

## The Lean statement

```
theorem actor_determinate {c : Conf} {n1 n2 : Nat} (h1 : ActorRun c (ret (dat n1)))
    (h2 : ActorRun c (ret (dat n2))) : n1 = n2
```

[Conf](#/node/VauE.Conf) is a configuration of pending messages and waiting customers;
[ActorRun](#/node/VauE.ActorRun) is any sequence of deliveries ([Deliver](#/node/VauE.Deliver)).

## How it is proved

[actor_sound](#/node/VauE.actor_sound): read a configuration back as a vau-e term. Every delivery is
zero or one vau-e step, so every run is a vau-e reduction. Two runs from the same start are two
reductions of one term, and by [confluence of vau-e](#/node/VauE.confluence) a term has at most one
normal form (`normal_unique`); primitive data is a normal form.

Also proved: `actor_results_join` (any two replies have a common reduct), `fork_interleave` (two
deliveries in the two branches of a fork can be done in either order), and `actor_example`, a complete
run of `(f 5 6)` with `f` bound to `list*`, where the second operand is evaluated first.
"""),
     [q("What does `actor_determinate` say?",
        ["Every run terminates", "Two runs that reply primitive data reply the same data", "Messages arrive in order", "There is only one run"],
        1, "It is about results, not about termination or the order of messages."),
      q("Which earlier result does the proof use?",
        ["Environment opacity", "Confluence of vau-e (through `normal_unique`)", "The lambda embedding", "Encapsulation"],
        1, "Each run is a vau-e reduction; confluence makes normal forms unique."),
      q("Is this a proof about Schumacher's Humus code?",
        ["Yes", "No: it is about a Lean model of his design", "Yes, for all actor systems", "Only for `#lookup`"],
        1, "The node lists what the model leaves out."),
      q("Where is concurrency in the model?",
        ["Nowhere", "In `fork`: either branch may take the next delivery", "In environments", "In `ret`"],
        1, "`forkL` and `forkR` let either branch move; `fork_interleave` shows both orders.")],
     caveats=[MODEL,
              "The theorem does not say that a run terminates, or that every vau-e evaluation has an actor run (completeness is not proved).",
              "`#print axioms VauE.actor_determinate` reports `propext` and `Quot.sound`."])

node("VauE.actor_sound",
     "Every actor run is a vau-e reduction",
     "Reading an actor configuration back as a vau-e term, every delivery is zero or one vau-e step, so every "
     "actor run is a reduction sequence.",
     """
## Plain English

A pending `#eval` message for `t` in `e` reads back as `[eval t e]`; a pending `#comb` as
`[combine f x e]`; the customer `k_comb` waiting for an operator reads back as `[combine _ x e]` with the
operator still being computed; a fork reads back as a pair of the two branches; and so on. With this
reading, a delivery either is one vau-e rule (an `#eval` or `#comb` message) or changes nothing (a reply
to a customer).

## The Lean statement

```
theorem actor_sound {c c' : Conf} (h : ActorRun c c') : Steps (readback c) (readback c')
```

and `actor_eval_sound`: if a run from the message `#eval t e` replies `v`, then `[eval t e] ->* v`.
The one-step version is `deliver_sound`.
""",
     [q("What does a fork read back as?",
        ["A combination", "A pair of its two branches", "An environment", "Nothing"],
        1, "The join replies the pair, which is exactly what the read-back already shows."),
      q("How many vau-e steps is a reply to a customer?",
        ["Zero", "One", "Two", "It depends"],
        0, "The read-back term does not change."),
      q("Does soundness say that the actor evaluator finds every answer?",
        ["Yes", "No: it only says that its answers are reducts", "Only for data", "Only for vau-x"],
        1, "Completeness is not proved.")],
     caveats=[MODEL])

node("VauE.Conf",
     "Actor configurations",
     "A configuration is a tree: its leaves are pending `#eval` and `#comb` messages and replies; its inner "
     "nodes are customers waiting for replies, including fork/join pairs.",
     """
## Plain English

In an actor system every request names a **customer**, the actor that receives the reply. In
Schumacher's evaluator each pending computation has exactly one customer, and a fork/join customer
waits for two replies. So the pending work forms a tree.

## In the Lean

`VauE.Conf` has `ret v` (a reply), `evalM t e` (an `#eval` message), `combM f x e` (a `#comb` message),
and the customers `kComb c x e` (Schumacher's `k_comb`), `kWrap c`, `fork c1 c2` and `kArgs c f e`.
""",
     [q("What is `fork c1 c2`?",
        ["A message", "A fork/join pair: two requests that run concurrently", "An environment", "A capsule"],
        1, "The join replies with the pair of the two replies."),
      q("What does `kComb c x e` wait for?",
        ["The operands", "The operator; then it sends `#comb` with `x` and `e`", "An environment", "Nothing"],
        1, "This is Schumacher's `k_comb`."),
      q("Does the model have actor addresses?",
        ["Yes", "No: the tree structure replaces them", "Only for environments", "Only for customers"],
        1, "This is a simplification, stated on the node.")],
     caveats=[MODEL])

node("VauE.Deliver",
     "Delivering one message",
     "`Deliver c c'` delivers one pending message or reply somewhere in the configuration `c`. Messages in "
     "different branches of a fork may be delivered in any order.",
     """
## Plain English

The rules follow Schumacher's actor behaviors: an `#eval` message to a pair creates `k_comb`; `k_comb`
receiving the operator sends `#comb`; `#comb` to an applicative forks the evaluation of the operands;
the join replies the pair; `#comb` to a compound operative sends `#eval` of the body; `#comb` to a
primitive replies its result (the vau-e delta-rules).

## In the Lean

`VauE.Deliver` has one constructor per message kind, and `inComb`, `inWrap`, `forkL`, `forkR`, `inArgs`
to deliver inside a waiting customer or either branch of a fork. [evalArgs](#/node/VauE.evalArgs) builds
the fork tree for the operands.
""",
     [q("Which constructors give concurrency?",
        ["`evalSym`", "`forkL` and `forkR`", "`join`", "`replyComb`"],
        1, "Either branch of a fork may take the next delivery."),
      q("What does `#comb` to an applicative do?",
        ["Calls the combiner at once", "Forks the evaluation of its operands, then sends `#comb` to the underlying combiner", "Replies the applicative", "Nothing"],
        1, "Constructors `combApp` and `replyArgs`."),
      q("Is a symbol lookup one delivery?",
        ["Yes, in this model", "No, it forwards to each parent", "Only in vau-x", "Never"],
        0, "Schumacher's environments forward `#lookup` to their parents; the model does it in one step.")],
     caveats=[MODEL])

node("VauE.ActorRun",
     "An actor run",
     "`ActorRun c c'`: zero or more deliveries lead from `c` to `c'`.",
     """
## Plain English

One run of the actor system: a sequence of deliveries, in one chosen order.

## In the Lean

`abbrev ActorRun := Vau.Star Deliver`.
""",
     [q("Can different runs from the same start make different choices?",
        ["No", "Yes: any pending message may be delivered next", "Only at the end", "Only for environments"],
        1, "That is why determinacy needs a proof."),
      q("Is a run of zero deliveries allowed?",
        ["Yes", "No"], 0, "`Star.refl`."),
      q("Which closure is used?",
        ["`Vau.Star`", "`Vau.EqvGen`", "None"], 0, "The same reflexive-transitive closure as elsewhere.")])

node("VauE.evalArgs",
     "Evaluating operands concurrently",
     "`evalArgs e (T1 ... Tm)` is a tree of forks with one `#eval` message per operand, like Schumacher's "
     "`#map` request with fork/join.",
     """
## Plain English

To evaluate the operands of an applicative, Schumacher sends a `#map` request that forks: one branch
evaluates the first operand, the other maps over the rest. So all operands are evaluated concurrently.

## In the Lean

`evalArgs e (pair x rest) = fork (evalM x e) (evalArgs e rest)`; any other term `t` gives `ret t`.
`readback_evalArgs`: it reads back as `evalList e ts`, the right side of vau-e's combine-app.
""",
     [q("How many forks does `evalArgs e (1 2)` have?",
        ["None", "Two", "One", "Three"], 1, "One per element: `fork (eval 1) (fork (eval 2) (ret ()))`."),
      q("What does it read back as?",
        ["`evalList e ts`", "`ts`", "`[eval ts e]`"], 0, "`readback_evalArgs`."),
      q("Must the operands be evaluated left to right?",
        ["Yes", "No: either branch of each fork may go first"], 1, "That is the concurrency.")],
     caveats=[MODEL])

node("VauE.readback",
     "Reading a configuration as a vau-e term",
     "`readback` turns an actor configuration into the vau-e term it stands for: a pending `#eval` is "
     "`[eval t e]`, a waiting `k_comb` is a combination whose operator is still being computed, a fork is a pair.",
     """
## Plain English

The bridge between the actor model and the calculus. It is what makes "every delivery is a reduction"
precise.

## In the Lean

`readback (ret v) = v`, `readback (evalM t e) = [eval t e]`, `readback (combM f x e) = [combine f x e]`,
`readback (kComb c x e) = [combine (readback c) x e]`, `readback (kWrap c) = <applicative (readback c)>`,
`readback (fork c1 c2) = (readback c1 . readback c2)`, `readback (kArgs c f e) = [combine f (readback c) e]`.
""",
     [q("What is `readback (evalM t e)`?",
        ["`t`", "`[eval t e]`", "`e`"], 1, "A pending `#eval` message is an eval term."),
      q("What is `readback (ret v)`?",
        ["`v`", "`[eval v e]`", "`()`"], 0, "A reply is its value."),
      q("What is `readback (fork c1 c2)`?",
        ["A pair of the two read-backs", "A combination", "An environment"], 0, "The join will reply exactly that pair.")])
