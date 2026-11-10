# Review

This page says whether the site's statements are faithful to their sources.

## Status

The Lean in `Vau/` has four headline theorems, with no `sorry`. This page compares each one with the
claim it is named for. The claim-by-claim honesty audit is `VAU_AUDIT.md` in the repository.

| headline | Lean statement (shortened) | faithful to | what is this project's choice |
|---|---|---|---|
| [eval_is_reduction](#/node/eval_is_reduction) | `Run (eval t) v -> Steps (eval t) v /\ IsValue v` | NEPLS talk: evaluation "a special case of term reduction" | the evaluator `Run`; one direction only |
| [conservative_extension](#/node/conservative_extension) | `LConv M N <-> Conv (embed M) (embed N)` | thesis 15.4, map (15.28), informal | vau-x form of the map; call-by-value lambda. Shutt describes the image as the full lambda calculus; for vau-x the Lean shows it is lambda-v (see the embed node) |
| [confluence](#/node/confluence) | `Steps t s1 -> Steps t s2 -> exists u, Steps s1 u /\ Steps s2 u` | thesis 14.1.4 with Theorem 13.104 (Church-Rosser of vau-x) | direct proof; no delta-rules; no SRS framework |
| [nontrivial](#/node/nontrivial) | `Not (eval (dat 5) = dat 5) /\ CtxEquiv (eval (dat 5)) (dat 5) /\ Not (CtxEquiv (dat 5) (dat 6))` | the point of thesis chapter 15 against Wand (1998) | the observation in `CtxEquiv` |
| [VauE.actor_determinate](#/node/VauE.actor_determinate) | `ActorRun c (ret (dat n1)) -> ActorRun c (ret (dat n2)) -> n1 = n2` | Schumacher's actor evaluator (posts, 2011-2012) | the tree model of configurations; lookup in one delivery; no addresses, mailboxes or fairness |
| [VauE.capsule_opacity](#/node/VauE.capsule_opacity) | `Clean k (c.plug (capsule k v)) -> (Steps (c.plug (capsule k v)) (dat n) <-> Steps (c.plug (capsule k v')) (dat n))` | thesis section 7.2 (informal Kernel description; no calculus rules in the thesis) | the capsule term and the rules for `$encap`, `$isEncap`, `$decap`; numbered types (no fresh types); `#t`/`#f` as `dat 1`/`dat 0` |
| [VauE.env_opacity](#/node/VauE.env_opacity) | `(forall s, lookup s bs = lookup s bs') -> (Steps (c.plug (env bs)) (dat n) <-> Steps (c.plug (env bs')) (dat n))` | thesis chapter 5 (encapsulation of environments), chapter 15 | observation is reduction to primitive data; pure vau-e, no mutation |
| [VauE.confluence](#/node/VauE.confluence) | `Steps t s1 -> Steps t s2 -> exists u, Steps s1 u /\ Steps s2 u` (vau-e) | thesis 14.1.4 with Theorem 13.104 | direct proof; this formalization's rules (unsorted environments, `$eval`, `$list*`) |
| [VauE.derived_lambda](#/node/VauE.derived_lambda) | `Ground e0 -> lookup $lambda e = lambdaOp e0 -> ... -> Steps (eval (($lambda p b) . args) e) (eval b (m . e))` | thesis (4.9), (4.10), traces (4.18)-(4.22) | vau-e with unsorted environments; delta-rules for `$eval`, `$list*`; one body expression |

None of the headlines has a PARTIAL or CONDITIONAL label: none uses `sorry`, and none has a hypothesis
beyond what the table shows.

## Definitions checked against the thesis

The definitions on this site and in the Lean were written from Shutt's thesis, chapter 9, and checked by
the drafting model against the extracted text of the PDF. No person has checked them.

| node | source | notes |
|---|---|---|
| [Term](#/node/Term) | thesis (9.16)-(9.18), (9.25) | de Bruijn indices; primitives numbered |
| [IsValue](#/node/IsValue) | thesis (9.25), discussion after (9.5) | "within an operative" read as: inside the body of a compound operative |
| [inst](#/node/inst) | thesis (9.19) | de Bruijn; defined for all terms, used only on values (beta-vau) |
| [Top](#/node/Top) | thesis (9.25) | rule names are this project's; no delta-rules |
| [VauE.Env](#/node/VauE.Env) | thesis (9.1), (9.6), (9.7) | pure vau-e, no mutation; unsorted lists with first-binding lookup |
| [VauE.vau_call](#/node/VauE.vau_call) | thesis (9.7beta), (9.12), section 4.2 | one-step call rule; vau-x itself has no `$vau` rule |
| [VauE.Top](#/node/VauE.Top) | thesis (9.7), (9.12) | (9.7a) read with its environment operand; `$eval`, `$list*` rules are this project's |
| [VauE.unwrap_wrap](#/node/VauE.unwrap_wrap) | thesis (9.12), section 4.2 | standard bindings of `wrap`, `unwrap` by hypothesis |
| [Start](#/node/Start) | thesis 8.4.1 and chapter 15; NEPLS talk; Wand 1998 | motivation; Wand summarized, not quoted |
| [Step](#/node/Step) | thesis section 2.3 | compatible closure, checked by `Step.plug` and `Step.exists_ctx` |

## Nodes that are still PLAN

None. Every node has Lean, except `Start`, which is an overview.

## Claims this site does not make

- It does not claim that the Lean formalizes Shutt's regular substitutive reduction systems, or any
  vau calculus other than vau-x without delta-rules.
- It does not claim that the de Bruijn `inst` is proved equal to Shutt's named substitution.
- It reports that Shutt's thesis obtains Church-Rosser for vau-x through a general theorem
  (sections 13.4 and 14.1.4). It does not check that proof; it proves the vau-x conclusion separately.
- It does not describe Kernel's mutable environments, continuations, or other impure features.
