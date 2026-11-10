# tangentproofs/vau-calculus

Plain-English informalization and a Lean 4 formalization of John N. Shutt's vau
calculus, with a later actor layer after Dale Schumacher.

Live site (when the first Pages build succeeds):
https://tangentproofs.github.io/vau-calculus/

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

## Sorry and axiom count

No Lean is in the repository yet. When Lean lands, this section will list the
sorry and axiom counts and will label any partial result.

## Licence

The MIT License covers the original work in this repository. See LICENSE.
Cited papers and posts keep their own copyright and terms. The site engine,
when added, comes from
[tangentproofs/informalization-tools](https://github.com/tangentproofs/informalization-tools)
and is also under the MIT License.
