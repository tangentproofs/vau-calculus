# Review

This page says whether the site's statements are faithful to their sources.

## Status: no theorems yet

There is **no Lean in this repository yet**, so there is no formal statement to review. Every node is a
concept marked **PLAN**. When Lean lands, this page will compare each headline's Lean statement with the
claim it is named for, label any PARTIAL (sorry) or CONDITIONAL result, and record an independent
honesty audit.

## Definitions checked against the thesis

The definitions on this site were written from Shutt's thesis, chapter 9, and checked by the drafting
model against the extracted text of the PDF. No person has checked them.

| node | source | notes |
|---|---|---|
| [Syntax](#/node/Syntax) | thesis (9.16)-(9.18), (9.25) | ASCII notation; primitive data and operatives left as parameters |
| [Values](#/node/Values) | thesis (9.25), discussion after (9.5) | "within an operative" read as: inside the body of a compound operative |
| [Substitution](#/node/Substitution) | thesis (9.19) | defined for values only, as in the thesis |
| [ReductionSchemata](#/node/ReductionSchemata) | thesis (9.25) | rule names are this project's; delta-rules described but not among the seven |
| [Environments](#/node/Environments) | thesis (9.1), (9.6), (9.7) | informal; pure vau-e, no mutation |
| [VauEnvironments](#/node/VauEnvironments) | thesis (9.7beta), (9.12), section 4.2 | informal; vau-x itself has no `$vau` rule |
| [Start](#/node/Start) | thesis 8.4.1 and chapter 15; NEPLS talk; Wand 1998 | motivation; Wand summarized, not quoted |

## Claims this site does not make

- It does not claim that any property of vau calculus is proved in Lean. None is, yet.
- It reports that Shutt's thesis obtains Church-Rosser for vau-x through a general theorem
  (sections 13.4 and 14.1.4). It does not check that proof.
- It does not describe Kernel's mutable environments, continuations, or other impure features.
