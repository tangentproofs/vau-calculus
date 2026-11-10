# VAU_AUDIT: honesty audit of the explainer against the Lean

Date: 2026-11-10. Scope: the Lean in `Vau/` and every text on the site
(`sites/vau/nodes_src/*.py`, `sites/vau/pages/*.md`, `sites/vau/site.json`)
and in `README.md`.

Method: a separate AI agent (Claude) read the Lean, the site text and the
extracted text of Shutt's thesis and NEPLS talk. It did not see the drafting
session's own conclusions, and it did not edit files. It compared each claim
with the Lean statement and with the thesis. The drafting session then applied
the fixes below. No person has reviewed this audit.

## Lean facts

- Toolchain `leanprover/lean4:v4.32.2`, no Mathlib, no other dependency.
- `lake build`: "Build completed successfully".
- `sorry`: 0. `axiom` declarations: 0.
- `#print axioms` (`lake env lean scripts/Axioms.lean`):

```
'Vau.eval_is_reduction' does not depend on any axioms
'Vau.confluence' depends on axioms: [propext, Quot.sound]
'Vau.church_rosser' depends on axioms: [propext, Quot.sound]
'Vau.conservative_extension' depends on axioms: [propext, Quot.sound]
'Vau.nontrivial' depends on axioms: [propext, Quot.sound]
'Vau.run_wrapF_F7' does not depend on any axioms
'VauE.lambda_def' depends on axioms: [propext]
'VauE.lambda_expr' depends on axioms: [propext, Quot.sound]
'VauE.lambda_call' depends on axioms: [propext, Quot.sound]
'VauE.derived_lambda' depends on axioms: [propext, Quot.sound]
'VauE.lambda_eq_wrap_vau' depends on axioms: [propext, Quot.sound]
'VauE.vau_call' depends on axioms: [propext]
'VauE.unwrap_wrap' depends on axioms: [propext]
'VauE.lambda_id_seven' depends on axioms: [propext, Quot.sound]
'VauE.lambda_static_scope' depends on axioms: [propext, Quot.sound]
'VauE.confluence' depends on axioms: [propext, Quot.sound]
'VauE.church_rosser' depends on axioms: [propext, Quot.sound]
'VauE.normal_unique' depends on axioms: [propext, Quot.sound]
'VauE.env_opacity' depends on axioms: [propext, Quot.sound]
'VauE.shadow_invisible' depends on axioms: [propext, Quot.sound]
'VauE.order_invisible' depends on axioms: [propext, Quot.sound]
'VauE.match_env_opaque' depends on axioms: [propext]
'VauE.ignore_hygiene' depends on axioms: [propext, Quot.sound]
'VauE.lookup_observable' depends on axioms: [propext, Quot.sound]
'VauE.decap_encap' depends on axioms: [propext]
'VauE.isEncap_same' depends on axioms: [propext, Quot.sound]
'VauE.isEncap_other' depends on axioms: [propext, Quot.sound]
'VauE.decap_other_stuck' depends on axioms: [propext]
'VauE.capsule_opacity' depends on axioms: [propext, Quot.sound]
'VauE.capsule_observable_with_decap' depends on axioms: [propext, Quot.sound]
```

## Headlines: claim against Lean statement

| node | Lean statement | verdict |
|---|---|---|
| `eval_is_reduction` | `Run (eval t) v -> Steps (eval t) v /\ IsValue v` | honest name, one direction only. `Run` is this project's evaluator, and its cases mirror the rules one for one (caveat added). |
| `conservative_extension` | `LConv M N <-> Conv (embed M) (embed N)` | honest for call-by-value lambda. Shutt says the image has the full lambda theory; the Lean shows lambda-v for vau-x (caveat added). |
| `confluence` | `Steps t s1 -> Steps t s2 -> exists u, Steps s1 u /\ Steps s2 u` | honest. Direct proof for the concrete rules; no SRS framework; no delta-rules. |
| `nontrivial` | `Not (eval (dat 5) = dat 5) /\ CtxEquiv (eval (dat 5)) (dat 5) /\ Not (CtxEquiv (dat 5) (dat 6))` | honest shape against Wand. The observation in `CtxEquiv` is this project's choice (caveats present and one added). |
| `DerivedLambda` | none at the time | superseded by the Addendum, Step 4 below. |

## Model fidelity to thesis (9.25)

The term grammar, the self-evaluating terms `S`, the values `V` ("every active
subterm is within an operative", read as inside a compound-operative body),
and the seven schemata match the thesis. Beta needs a value operand;
combine-wrap needs a proper list (including the empty list); parse-pair needs
no values; `Step` is the full compatible closure. Nothing is added. Only the
delta-rules (9.25delta) are missing, and that is disclosed. Disclosed choices:
de Bruijn indices (no proof of agreement with (9.19)), `inst` defined for all
terms, numbered primitives, no delta-rules.

## Findings and fixes

| # | severity | finding | fix |
|---|---|---|---|
| 1 | medium | `embed` node said the image "behaves exactly like the lambda calculus". The Lean shows call-by-value only, which is weaker than Shutt's sentence. | Wording changed; caveat now says Shutt claims the full theory and the Lean gives lambda-v, with the example `(lambda x.c) Omega`. |
| 2 | low-medium | `conservative_extension` summary: "loses no lambda equation". | Now "no lambda-v equation". |
| 3 | medium | Site lead and Start summary stated Wand's result as a general theorem. | Both now say "in his calculus, where evaluation is implicit and fexprs are fully reflective". |
| 4 | medium | `Start` had status PLAN but reports what the Lean proves. | `Start` is an overview with no status pill; Trust page agrees. |
| 5 | medium | `nontrivial`: the 5/6 separation depends on observing which normal form is reached. | Caveat added. |
| 6 | medium | `Run` was called fully independent of the rules; its cases mirror the rules. | Text and caveat now say so. |
| 7 | low | `Run` caveat claimed an evaluation order. | Now: `Run` is a relation and fixes no order. |
| 8 | low-medium | `Top` summary mentioned delta-rules as if included. | Summary now says the Lean has none. |
| 9 | low | "the result does not depend on the order". | Now "any two reduction paths can be joined again". |
| 10 | low | Lazy-substitution remark was about vau-e, not vau-x. | Caveat corrected. |
| 11 | low | `VAU_AUDIT.md` was cited before it existed; Trust page mentioned a build log it did not show. | This file; Trust page wording fixed. |
| 12 | low | README survey claim. | Now "a web search found none; we do not claim that none exists". |
| 13 | low | Two stale names in Lean comments. | Fixed. |
| 14 | low | Constants mapped to primitive data without saying it is a choice. | Marked as this project's choice. |
| 15 | low | Some thesis links point one page into a section. | Left as is: each link is inside the right section. |
| 16 | - | Non-ASCII characters. | None found. |

## Checked and found accurate

- The four quoted headline statements and the `CtxEquiv` definition match the
  Lean source.
- Every Lean name used in the text exists.
- All quiz answer keys point at the correct choice.
- The worked example on the `Top` node is correct step by step and agrees with
  `run_F_F7` and `run_wrapF_F7`.
- The NEPLS quotes are verbatim; the thesis references ((9.12), (9.7beta),
  (4.10), Theorem 13.104, section 14.1.4, Definition 13.90, section 15.4) are
  correct.
- Nodes still marked PLAN claim no proof of their own.

## Addendum, Step 4 (vau-e and derived `$lambda`)

A separate AI agent (Claude) audited the vau-e Lean and its site text, read-only, against thesis
section 9.1 and chapter 4. Its findings and the fixes:

| # | severity | finding | fix |
|---|---|---|---|
| 1 | high | The `vau_call` node quoted a statement with `bind`/`emp`, which no longer exist. | Quote corrected to the source. |
| 2 | high | The `VauE.Env` node said `Env` is `emp` or `bind`. | Now: `List (Prod Nat Term)`. |
| 3 | medium | "Statically scoped" was claimed from `derived_lambda`, where the static and calling environments are the same `e`. | New theorem `lambda_static_scope` (made in `e1`, called from `e2`); wording changed everywhere. |
| 4 | low | A quiz answer relied on `lambda_call` while the question was about `derived_lambda`. | Question now about `lambda_static_scope`. |
| 5 | low | "evaluates to the value of c" suggested uniqueness. | Now "reduces to `v`"; no uniqueness claimed. |
| 6 | low | "Every lookup agrees" ignored shadowed duplicate bindings. | Caveat rewritten. |
| 7 | low | Minor undisclosed details (environment operand must be literal `env e`; value conditions on `$eval`, `$list*`; primitive data numbered; `eparm` may be any parameter tree). | Caveats added. |
| 8-10 | low | Stale headings, link text, audit row. | Fixed. |

The agent found the syntax, values, contexts, `match`, schemata (9.7) and delta-rules (9.12) faithful,
all quoted statements (after fix 1) and Lean names correct, every quiz key correct, and no
non-ASCII text. Summary table:

| node | Lean statement | verdict |
|---|---|---|
| `VauE.derived_lambda` | under `Ground e0`, `lookup $lambda e = lambdaOp e0`, values `p`, `b`, proper list `args` evaluating to values `vs`, and `ematch p vs = some m`: `Steps (eval (($lambda p b) . args) e) (eval b (m . e))` | honest for vau-e with one body expression. Every assumption is a named hypothesis; `lambda_id_seven` shows they can be met. |
| `VauE.lambda_eq_wrap_vau` | `Conv` between `($lambda p b)` and `(wrap ($vau p #ignore b))` evaluated in `e` | honest form of thesis (4.9), under stated bindings. |
| `VauE.vau_call` | one beta-oper step with environment parameter `d` | it is one rule instance; the node says so. |
| `VauE.unwrap_wrap` | if `c` reduces to a value `v`, `(unwrap (wrap c))` reduces to `v` | honest, under stated bindings; no uniqueness claimed. |
| `VauE.lambda_static_scope` | `($lambda p b)` in `e1`, then `(f . args)` from `e2` with `f` bound to the result: the body runs in `m . e1` | added after the audit: the evidence for static scope. |

Disclosed differences from the thesis: unsorted environments (lookup agrees,
term equality weaker); delta-rules for `$eval` and `$list*` are this project's;
(9.7a) read with its environment operand; symbols are numbers; no `$define!`,
so `$lambda` is bound by hypothesis. (At the time of this addendum, confluence of vau-e
was not claimed; see the Step 5 addendum.)

## Addendum, Step 5 (confluence of vau-e)

Self-check by the drafting session; no separate agent audited this step. The Lean is the check of
the proof; this addendum covers the claims in the text.

| node | Lean statement | verdict |
|---|---|---|
| `VauE.confluence` | `Steps t s1 -> Steps t s2 -> exists u, Steps s1 u /\ Steps s2 u` | honest for this formalization's vau-e rules: (9.7), (9.12) for `$vau`/`$wrap`/`$unwrap`, and the project's `$eval`/`$list*` rules, with unsorted environments and steps inside every binding. Not Shutt's SRS framework; not other delta-rules. |
| `VauE.normal_unique` | two normal forms of one term are equal | follows from confluence; does not claim that a normal form exists. |

Text that said "confluence of vau-e is not proved" (banner, Start, About, Trust, README, the
`vau_call`, `derived_lambda`, `unwrap_wrap` and `VauE.Step` nodes) was updated.

## Addendum, Step 6 (environment opacity and hygiene)

Self-check by the drafting session; no separate agent audited this step.

| node | Lean statement | verdict |
|---|---|---|
| `VauE.env_opacity` | same lookups -> same observations (reduction to `dat n`) in every one-hole context | honest; the observation (primitive data) and the setting (pure vau-e, no mutation) are stated on the node. `lookup_observable` shows that different lookups can be observed, so the result is not vacuous. |
| `VauE.shadow_invisible`, `VauE.order_invisible` | instances of `env_opacity` | honest. They address the earlier caveat on unsorted environments for observations; term equality is still weaker, and the node says so. |
| `VauE.match_env_opaque` | a matching parameter tree for an environment is `#ignore` or a symbol | honest. |
| `VauE.ignore_hygiene` | calls from any two dynamic environments reach the same term | honest; the caveat notes that operands are values here, and that applicative arguments are evaluated in the caller's environment. |

Not claimed: Kernel's other hygiene tactics (stable bindings, local-only mutation), mutation,
continuations, or a stronger observation than reduction to data.

## Addendum, Step 7 (encapsulation types)

Self-check by the drafting session; no separate agent audited this step.

| node | Lean statement | verdict |
|---|---|---|
| `VauE.capsule_opacity` | `Clean k (c.plug (capsule k v)) -> (Steps (c.plug (capsule k v)) (dat n) <-> Steps (c.plug (capsule k v')) (dat n))` | honest for this project's model. The model (capsule term, three rules per type, numbered types, `#t`/`#f` as data) is not from the thesis, and every node says so. `capsule_observable_with_decap` shows the hypothesis is needed. |
| `VauE.decap_encap`, `isEncap_same`, `isEncap_other`, `decap_other_stuck` | the contract of the three applicatives | honest. |

Adding the `capsule` term and the three rules changed `VauE.Term`, `VauE.Top` and `VauE.Step`, so
`VauE.confluence` and `VauE.env_opacity` were re-proved; their nodes now name the encapsulation rules.
Not claimed: fresh type generation, Kernel's `$provide!`, or any statement about state.
