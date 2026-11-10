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
```

## Headlines: claim against Lean statement

| node | Lean statement | verdict |
|---|---|---|
| `eval_is_reduction` | `Run (eval t) v -> Steps (eval t) v /\ IsValue v` | honest name, one direction only. `Run` is this project's evaluator, and its cases mirror the rules one for one (caveat added). |
| `conservative_extension` | `LConv M N <-> Conv (embed M) (embed N)` | honest for call-by-value lambda. Shutt says the image has the full lambda theory; the Lean shows lambda-v for vau-x (caveat added). |
| `confluence` | `Steps t s1 -> Steps t s2 -> exists u, Steps s1 u /\ Steps s2 u` | honest. Direct proof for the concrete rules; no SRS framework; no delta-rules. |
| `nontrivial` | `Not (eval (dat 5) = dat 5) /\ CtxEquiv (eval (dat 5)) (dat 5) /\ Not (CtxEquiv (dat 5) (dat 6))` | honest shape against Wand. The observation in `CtxEquiv` is this project's choice (caveats present and one added). |
| `DerivedLambda` | none | PLAN; claims no proof. |

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
