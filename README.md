# tangentproofs/vau-calculus

Plain-English informalization and a Lean 4 formalization of John N. Shutt's vau
calculus, with a later actor layer after Dale Schumacher.

Live site: https://tangentproofs.github.io/vau-calculus/ (the explainer is at
https://tangentproofs.github.io/vau-calculus/vau/).

> **Not official documentation.** This repository holds unreviewed drafts.
> Nothing here is written, reviewed, endorsed, or maintained by John N. Shutt,
> by Dale Schumacher, or by the authors of the sources listed below. An AI
> model drafted the explanations and the Lean. They may contain mistakes. The
> cited papers and posts are the ground truth for the theory. The Lean in this
> repository is the ground truth for what this project proves. It covers the
> pure vau-x calculus only. Do not treat a planned node as a proved theorem.

## Sources

- John N. Shutt, Ph.D. dissertation, Worcester Polytechnic Institute, 2010.
  *Fexprs as the basis of Lisp function application; or, $vau: the ultimate
  abstraction.*
  https://web.cs.wpi.edu/~jshutt/dissertation/etd-090110-124904-Shutt-Dissertation.pdf
- John N. Shutt, NEPLS talk, 2007.
  https://web.cs.wpi.edu/~jshutt/jns-nepls07.txt
- Dale Schumacher, "Fexpr: The Ultimate Lambda", 2011.
  https://dalnefre.com/wp/2011/11/fexpr-the-ultimate-lambda/
- Dale Schumacher, "Semantic Extensibility with Vau", 2011.
  https://dalnefre.com/wp/2011/12/semantic-extensibility-with-vau/
- Dale Schumacher, "Implementing Actors in Kernel", 2012.
  https://dalnefre.com/wp/2012/02/implementing-actors-in-kernel/
- Mitchell Wand, "The Theory of Fexprs is Trivial", Lisp and Symbolic
  Computation, 1998.

## Scope

The Lean formalizes the pure vau-x calculus of Shutt's thesis, section 9.3:
syntax, values, substitution, the seven general reduction schemata
(eval-self, eval-pair, eval-wrap, combine-wrap, beta-vau, parse-nil,
parse-pair), and their compatible closure. Variables are de Bruijn indices.
There are no delta-rules.

**This work does not formalize Shutt's full Regular Substitutive Reduction
Systems framework** (thesis chapter 13). Confluence is proved directly for the
concrete vau-x rules. Environments, `$vau`, the derived `$lambda`,
encapsulation types and an actor layer are not formalized yet; their nodes on
the site are marked PLAN.

A web search on 2026-11-09 found no prior Lean, Coq, Isabelle, or Agda
formalization of vau calculus. We do not claim that none exists.

## Status

- Step 1 (done): a plain-English explainer of what vau calculus is.
- Step 2 (done): a proof graph of the planned formalization.
- Step 3 (done for vau-x): the Lean in `Vau/`. Four headline theorems are
  proved:

| theorem | file | statement, in words |
|---|---|---|
| `Vau.eval_is_reduction` | `Vau/Eval.lean` | if the evaluator `Run` takes `[eval t]` to `v`, then `[eval t] ->* v` and `v` is a value |
| `Vau.conservative_extension` | `Vau/Lambda.lean` | two lambda terms are equal in call-by-value lambda iff their images under Shutt's map (15.28) are equal in vau-x |
| `Vau.confluence` | `Vau/Confluence.lean` | if `t ->* s1` and `t ->* s2`, then `s1` and `s2` have a common reduct |
| `Vau.nontrivial` | `Vau/Contextual.lean` | `[eval 5]` and `5` are different but contextually equivalent; `5` and `6` are not |

The evaluator `Run`, the notion of observation in `CtxEquiv`, and the vau-x
form of the lambda map are this project's choices. The site nodes and
`VAU_AUDIT.md` say where each statement goes beyond, or falls short of, the
thesis.

Still planned (no Lean): derived `$lambda`, environments and `$vau`,
`$wrap`/`$unwrap`, environment opacity, encapsulation types, and the actor
layer.

## Sorry and axiom count

- `sorry`: **0**
- `axiom` declarations: **0**
- `#print axioms` (run `lake env lean scripts/Axioms.lean`):

```
'Vau.eval_is_reduction' does not depend on any axioms
'Vau.confluence' depends on axioms: [propext, Quot.sound]
'Vau.church_rosser' depends on axioms: [propext, Quot.sound]
'Vau.conservative_extension' depends on axioms: [propext, Quot.sound]
'Vau.nontrivial' depends on axioms: [propext, Quot.sound]
'Vau.run_wrapF_F7' does not depend on any axioms
```

No partial results: no theorem uses `sorry`.

## Repository layout

| path | what |
|---|---|
| `Vau/`, `Vau.lean` | the Lean library (Lean 4, toolchain in `lean-toolchain`, no Mathlib) |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | Lean build files |
| `scripts/Axioms.lean` | prints `#print axioms` for each headline |
| `VAU_AUDIT.md` | honesty audit: each site claim against the Lean statement |
| `sites/vau/` | the explainer: `site.json` (config and concept nodes), `nodes_src/*.py` (node text and quizzes), `pages/*.md` (About, Review, Trust) |
| `engine/` | the site engine from informalization-tools, with small local changes (below) |
| `tools/` | hub tools: `update.mjs` writes the root `index.html` from `projects.json` and `hub.json` |
| `hub.json`, `projects.json`, `index.html`, `assets/` | the root index page |
| `.github/workflows/pages.yml` | builds the site and deploys GitHub Pages; it never builds Lean |

## Building the Lean

```sh
lake build                          # builds Vau (Lean core only, no Mathlib)
lake env lean scripts/Axioms.lean   # prints the axioms of each headline
```

CI does not build the Lean. The site reads declarations from the source text.

## Building the site locally

```sh
(cd engine && npm ci)
pip install pyyaml
engine/build.sh vau                                   # -> _site/vau/
python3 tools/sync_projects.py && node tools/update.mjs   # -> index.html
cp index.html _site/ && cp -R assets _site/
python3 -m http.server -d _site 8765                  # http://localhost:8765/
```

The build validates every node (schema, quiz keys, links) and fails on an error.

### Local engine changes

Relative to informalization-tools commit `7260c46`:

- `engine/build.sh`, `engine/gen.py`: a site may set `"self": true`. Then the
  explained project is this repository, and the pinned commit is the commit
  being built.
- `engine/gen.py`: a site may give its own `bannerHtml`, `creditHtml`,
  `footerHtml`, `aboutCreditMd`, and Start page wording (`startTitle`,
  `startIntro`, `startLink`), and the labels for headlines (`headlineLegend`,
  `headlineWord`, `startSide`) so that planned headlines are not called theorems.
- `engine/tools/scan_decls.py`, `engine/assets/app.js`, `engine/assets/style.css`:
  a concept node may carry `"formal": "planned" | "partial" | "proved"`, shown
  as a pill on its page, on the Start page and in the node list. The Start page
  hides an empty Mathlib list.
- `engine/tools/scan_decls.py`: with `"leanFormal": true`, each Lean theorem
  gets the pill "proved in Lean" when its source text has no `sorry`, and
  "partial Lean" when it has one. This is a text check; the build log and
  `#print axioms` are the real check.

All text and Lean written for this project is plain ASCII. The engine's own interface
uses a few symbols (arrows, stars), unchanged from upstream.

## Licence

The MIT License covers the original work in this repository. See LICENSE.
Cited papers and posts keep their own copyright and terms. The site engine
comes from
[tangentproofs/informalization-tools](https://github.com/tangentproofs/informalization-tools)
and is also under the MIT License (`engine/LICENSE`).
