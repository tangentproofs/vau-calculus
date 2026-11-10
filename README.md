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
> repository, once present, is the ground truth for what this project proves.
> Do not treat a planned node as a proved theorem.

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

The first goal is a formalization of the pure vau-x calculus: syntax,
evaluation and combination, wrap, beta-vau, and confluence of those concrete
rules. This work does not formalize Shutt's full Regular Substitutive
Reduction Systems framework. Environments, the derived $lambda, contextual
equivalence, and an actor layer come later.

A survey on 2026-11-09 found no prior Lean, Coq, Isabelle, or Agda
formalization of vau calculus.

## Status

Step 1 is done: a plain-English explainer of what vau calculus is (why
evaluation is explicit, the pure vau-x syntax, values, substitution, the seven
general reduction rules, and informal environments for `$vau`). Every node is a
concept marked PLAN, because no Lean exists yet. Next: a proof graph of the
planned formalization, then the Lean.

## Sorry and axiom count

No Lean is in the repository yet: 0 `sorry`, 0 `axiom`. When Lean lands, this
section will list the counts and will label any partial result.

## Repository layout

| path | what |
|---|---|
| `sites/vau/` | the explainer: `site.json` (config and concept nodes), `nodes_src/*.py` (node text and quizzes), `pages/*.md` (About, Review, Trust) |
| `engine/` | the site engine from informalization-tools, with small local changes (below) |
| `tools/` | hub tools: `update.mjs` writes the root `index.html` from `projects.json` and `hub.json` |
| `hub.json`, `projects.json`, `index.html`, `assets/` | the root index page |
| `.github/workflows/pages.yml` | builds the site and deploys GitHub Pages; it never builds Lean |

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
  `startIntro`, `startLink`).
- `engine/tools/scan_decls.py`, `engine/assets/app.js`, `engine/assets/style.css`:
  a concept node may carry `"formal": "planned" | "partial" | "proved"`, shown
  as a pill on its page, on the Start page and in the node list. The Start page
  hides an empty Mathlib list.

All text written for this project is plain ASCII. The engine's own interface
uses a few symbols (arrows, stars), unchanged from upstream.

## Licence

The MIT License covers the original work in this repository. See LICENSE.
Cited papers and posts keep their own copyright and terms. The site engine,
when added, comes from
[tangentproofs/informalization-tools](https://github.com/tangentproofs/informalization-tools)
and is also under the MIT License (`engine/LICENSE`).
