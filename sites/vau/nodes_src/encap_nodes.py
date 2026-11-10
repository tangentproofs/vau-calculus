# Step 7 nodes: encapsulation types in vau-e (Vau/Env/Encapsulation.lean). Node ids are Lean declarations.
from _common import THESIS, make, q

NODES = []
node = make(NODES)

OURS = ("Shutt's thesis gives no calculus rules for encapsulation types. The term `capsule k v` and the "
        "rules for `$encap k`, `$isEncap k`, `$decap k` are this project's model of Kernel's "
        "`make-encapsulation-type` (thesis section 7.2).")
FRESH = ("Kernel's `make-encapsulation-type` makes a fresh type on each call, which needs state. Pure vau-e "
         "has no state, so types are numbered here, as if each type `k` had been made once. `#t` and `#f` "
         "are represented by the data `1` and `0`.")


def L(s):
    return s.replace("%T", THESIS)


node("VauE.capsule_opacity",
     "Encapsulation: without the decapsulator, the content is hidden",
     "Put an encapsulated object of type `k` into any program that holds no decapsulator of type `k`. "
     "Then no observation depends on the content: replacing the content changes nothing the program can see.",
     L("""
## Plain English

Kernel lets a program create a new abstract data type at run time ([thesis section 7.2](%T#page=146)).
`(make-encapsulation-type)` returns three applicatives:

- an **encapsulator** `e`: it takes one value and returns a new encapsulated object that holds it;
- a **type predicate** `p?`: it returns true iff all its arguments were made by `e`;
- a **decapsulator** `d`: it takes an object made by `e` and returns its content.

The content can be read **only** through `d`. If a module keeps `d` private and exports only safe
operations, nobody else can read the content. This theorem proves that promise, in the Lean vau-e.

## The model

The Lean adds an opaque term `capsule k v` (an object of type `k` with content `v`) and three
primitive operatives for each type `k`, with these rules:

```
[combine $encap_k (V) e]                ->  <capsule k V>
[combine $isEncap_k (V1 ... Vn) e]      ->  #t if every Vi is a capsule of type k, else #f
[combine $decap_k (<capsule k V>) e]    ->  V
```

A decapsulator has no rule for an object of another type (`decap_other_stuck`).

## The Lean statement

```
theorem capsule_opacity {k n : Nat} {v v' : Term} (c : Ctx) (hc : Clean k (c.plug (capsule k v))) :
    Steps (c.plug (capsule k v)) (dat n) <-> Steps (c.plug (capsule k v')) (dat n)
```

[Clean](#/node/VauE.Clean) `k t` says that `t` holds no `$decap k`, except inside capsules of type `k`.
So: in any context `c` without the decapsulator, the program reaches the number `n` with content `v`
exactly when it does with any other content `v'`. The program may hold the encapsulator and the type
predicate, and may make, copy and test capsules as much as it likes.

`capsule_observable_with_decap` checks the other side: with `$decap k`, the content **can** be seen.

## How it is proved

`CSim k` relates terms that are equal except for the content of capsules of type `k`. `csim_step`:
every step of a clean program is matched by zero or more steps of any related program. Steps inside a
hidden content are matched by no step. `Clean.step`: reduction never brings a `$decap k` out of a capsule
of type `k`, so the program stays clean.
"""),
     [q("Which of the three applicatives can read the content?",
        ["The encapsulator", "The type predicate", "The decapsulator", "Any of them"],
        2, "Only `$decap k` has a rule that returns the content."),
      q("What may the program hold, by the hypothesis `Clean k`?",
        ["Nothing of type `k`", "Anything except `$decap k` (outside capsules of type `k`)", "Only the decapsulator", "Only values"],
        1, "It may make and test capsules freely."),
      q("Can a program with the decapsulator see the content?",
        ["No, never", "Yes: `capsule_observable_with_decap`", "Only with mutation", "Only for type 0"],
        1, "So the hypothesis is needed."),
      q("Does the Lean model `make-encapsulation-type` making a fresh type?",
        ["Yes", "No: types are numbered, because pure vau-e has no state", "Only for two types", "Yes, with a counter"],
        1, "This is disclosed on the node.")],
     caveats=[OURS, FRESH,
              "The observation is reduction to primitive data, as for environment opacity.",
              "`VauE.confluence` and `VauE.env_opacity` were re-proved for the calculus with these rules.",
              "`#print axioms VauE.capsule_opacity` reports `propext` and `Quot.sound`."])

node("VauE.decap_encap",
     "Decapsulating what was encapsulated",
     "If `e` and `d` are bound to the encapsulator and the decapsulator of type `k`, and `x` evaluates to the "
     "value `v`, then `(d (e x))` evaluates to `v`.",
     """
## Plain English

The basic contract of an encapsulation type: the decapsulator returns what the encapsulator was given.

## The Lean statement

```
theorem decap_encap {k se sd : Nat} {c v : Term} {e : Env}
    (he : Env.lookup se e = some (encapA k)) (hd : Env.lookup sd e = some (decapA k))
    (hc : Steps (eval c (env e)) v) (hv : IsValue v) :
    Steps (eval (list2 (sym sd) (list2 (sym se) c)) (env e)) v
```

Also proved: `isEncap_same` (the predicate gives `#t` on an object of its type), `isEncap_other`
(`#f` on an object of another type), `decap_other_stuck` (no rule for an object of another type).
""",
     [q("What does `(d (e x))` evaluate to?",
        ["An error", "The value of `x`", "A capsule", "`#t`"],
        1, "Decapsulate after encapsulate gives the content back."),
      q("What does `isEncap_other` say?",
        ["The predicate gives `#t` for every capsule", "The predicate gives `#f` (`dat 0`) for an object of another type", "Types are equal", "Decapsulation always works"],
        1, "Types are kept apart."),
      q("What happens when `$decap k` meets an object of another type?",
        ["It returns the content", "No rule applies: the call is stuck", "It returns `#f`", "It makes a new capsule"],
        1, "`decap_other_stuck`.")],
     caveats=[OURS, FRESH])

node("VauE.Clean",
     "A program without the decapsulator",
     "`Clean k t` holds when `t` contains no `$decap k`, except inside the content of capsules of type `k`.",
     """
## Plain English

This is the hypothesis of the encapsulation theorem: the program does not hold the decapsulator of type
`k`. A `$decap k` hidden inside a capsule of type `k` is allowed, because nothing can take it out without
the decapsulator.

## In the Lean

`VauE.Clean k` is an inductive predicate: every constructor of a term is clean if its parts are; the
primitive `prim p` is clean if `p` is not `decap k`; `capsule k v` is clean for any `v` (`hidden`); a
capsule of any type is clean if its content is (`capsule`). `Clean.step`: reduction keeps it.
""",
     [q("Is `prim (.decap k)` clean for `k`?",
        ["Yes", "No", "Only inside an environment", "Only if wrapped"],
        1, "That is exactly what `Clean k` forbids."),
      q("Is `capsule k (prim (.decap k))` clean for `k`?",
        ["No", "Yes: the content of a capsule of type `k` is not checked", "Only if empty", "Only for type 0"],
        1, "Nothing can take that content out without the decapsulator."),
      q("Does reduction keep a term clean?",
        ["Yes: `Clean.step`", "No", "Only in vau-x", "Only for values"],
        0, "No rule brings a `$decap k` out of a capsule of type `k`.")])


def _app(name, prim, word):
    node(f"VauE.{name}",
         f"The {word} of type k",
         f"`{name} k` is `<applicative ${prim} k>`: the {word} of encapsulation type `k`.",
         f"""
## Plain English

One of the three applicatives that Kernel's `make-encapsulation-type` returns. Its operand is evaluated
first, then the primitive `${prim} k` acts on the value.

## In the Lean

`abbrev {name} (k : Nat) : Term := app (prim (.{prim} k))`.
""",
         [q(f"Is `{name} k` an applicative?", ["Yes", "No"], 0, "It is `app (prim ...)`."),
          q("Which type does it belong to?", ["Type `k`", "Every type", "No type"], 0, "Each type has its own three applicatives."),
          q("Are its operands evaluated?", ["Yes", "No"], 0, "Rule combine-app evaluates them first.")],
         caveats=[OURS])


_app("encapA", "encap", "encapsulator")
_app("decapA", "decap", "decapsulator")

node("VauE.isCapsuleOf",
     "Is this an object of type k?",
     "`isCapsuleOf k t` is `true` when `t` is a capsule of type `k`, and `false` for every other term.",
     """
## Plain English

The test that the type predicate applies to each argument.

## In the Lean

`isCapsuleOf k (capsule k' _) = decide (k' = k)` (written `k' == k`), and `false` otherwise.
""",
     [q("What is `isCapsuleOf 3 (capsule 3 v)`?", ["`true`", "`false`"], 0, "Same type."),
      q("What is `isCapsuleOf 3 (capsule 4 v)`?", ["`true`", "`false`"], 1, "Different type."),
      q("What is `isCapsuleOf 3 (dat 3)`?", ["`true`", "`false`"], 1, "Data is not a capsule.")],
     caveats=[OURS])

node("VauE.capsCheck",
     "The answer of the type predicate",
     "`capsCheck k (V1 ... Vn)` is `some true` if every `Vi` is a capsule of type `k`, `some false` if one is "
     "not, and `none` if the arguments are not a proper list.",
     """
## Plain English

Kernel's type predicate `p?` takes zero or more arguments and returns true iff all of them were made by
the matching encapsulator. With no arguments it returns true.

## In the Lean

`capsCheck k nil = some true`; `capsCheck k (pair x rest)` combines `isCapsuleOf k x` with the answer for
`rest`; other terms give `none`. The rule delta-isEncap turns `some b` into `dat 1` or `dat 0`.
""",
     [q("What is `capsCheck k ()`?", ["`some true`", "`some false`", "`none`"], 0, "No arguments: all of them are capsules."),
      q("What is `capsCheck k (1 . 2)`?", ["`some false`", "`none`: not a proper list", "`some true`"], 1, "It must be a proper list."),
      q("How are `#t` and `#f` written in the Lean?", ["As new terms", "As `dat 1` and `dat 0`", "As symbols"], 1, "This is disclosed.")],
     caveats=[OURS])
