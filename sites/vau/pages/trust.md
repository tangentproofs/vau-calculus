# Trust: what has and has not been checked

## Lean

| | now |
|---|---|
| Lean files | vau-x: `Vau/Syntax.lean`, `Subst.lean`, `Reduction.lean`, `Confluence.lean`, `Eval.lean`, `Lambda.lean`, `Contextual.lean`. vau-e: `Vau/Env/Syntax.lean`, `Reduction.lean`, `Lambda.lean`, `Confluence.lean` |
| Toolchain | `leanprover/lean4:v4.32.2` (see `lean-toolchain`), no Mathlib, no other dependency |
| Built by this site | no. The site build never builds Lean. It reads the declarations from the source text. |
| Built where | locally by the drafting session with `lake build` (no CI build). |
| `sorry` count | **0** |
| `axiom` declarations | **0** |
| Node status | 6 headlines and their definitions: **proved in Lean** (theorems) or Lean definitions. `EnvironmentOpacity`, `EncapsulationTypes`, `ActorLayer`: **PLAN**, no Lean. `Start` is an overview with no status pill. |

The "proved in Lean" pill on a theorem is set by the site build from the source text: it means the
theorem's text contains no `sorry`. The check that the files compile is a local `lake build`
("Build completed successfully"); CI does not build Lean.

### `#print axioms` for each headline

Output of `lake env lean scripts/Axioms.lean`:

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
```

`propext` and `Quot.sound` are standard axioms of Lean's core logic. `Quot.sound` comes from function
extensionality, used in the substitution lemmas. No result uses `Classical.choice` or `sorryAx`.

## What the Lean does and does not cover

- **Covered:** the pure vau-x calculus of thesis section 9.3: its terms, values, substitution, the seven
  general schemata, and their compatible closure. Variables are de Bruijn indices.
- **Not covered:** delta-rules in vau-x (the Lean vau-x has none); mutation, `$define!`, continuations,
  and the calculi vau-p, vau-i and larger; Shutt's framework of regular substitutive reduction systems (chapter 13); his
  Church-Rosser and standardization theorems for that framework; Kernel itself.
- **This project's own definitions**, each named on its node: the evaluator `Run`, the observation in
  `CtxEquiv`, the vau-x form of the lambda map, and the call-by-value lambda calculus `LStep`.
- **Not proved:** that the de Bruijn `inst` agrees with Shutt's named substitution (9.19). This is the
  usual correspondence and is not checked here.
- **vau-e (namespace `VauE`):** Shutt's vau-e calculus of section 9.1, with symbols (numbers),
  environments, compound operatives, and the rules (9.7) and (9.12). Differences, each stated on the
  nodes: environments are unsorted lists with first-binding lookup (Shutt's are sorted with no symbol
  bound twice: lookups agree, term equality does not); delta-rules for `$eval` and `$list*` are this
  project's; (9.7a) is read with its environment operand. **Confluence of vau-e is proved** (`VauE.confluence`), directly, for these rules only. The
  `$lambda` results are reduction sequences under stated hypotheses; `lambda_id_seven` shows the
  hypotheses can be met.

See the [review](#/review) and `VAU_AUDIT.md` in the repository for the claim-by-claim audit.

## The explanations

- **Drafted by Claude (AI).** No person has reviewed the text or the Lean. The authors of the cited works
  have not seen them. Every node is `review: draft`.
- **Sources.** Definitions follow the extracted text of Shutt's thesis PDF (chapters 2, 4, 5, 7, 8, 9,
  13-15) and his 2007 NEPLS talk script. Schumacher's posts were read for the environment and actor
  views. Wand's 1998 paper is summarized from its well-known result and from Shutt's discussion of it in
  thesis chapter 15; this site does not quote it.
- **Quotes.** Only short phrases are quoted, each with its source. The thesis is not copied into this
  repository.
- **Worked examples.** The reduction trace on the [Top](#/node/Top) node is this site's. Its two results
  are checked in Lean (`run_F_F7`, `run_wrapF_F7`).
- **Comments** on the nodes use GitHub Discussions (giscus, category Announcements) on this repository.
