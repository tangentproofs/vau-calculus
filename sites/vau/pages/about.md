# About this site

This site explains **John N. Shutt's vau calculus** in plain English. Vau calculus is a family of
calculi for reasoning about **fexprs**: first-class Lisp combiners that receive their operands
unevaluated. Shutt developed it in his PhD thesis (Worcester Polytechnic Institute, 2010) and used it as
the basis of the Kernel programming language.

## What is here now (Step 1)

- [Start here](#/start): what vau calculus is. The [Start](#/node/Start) node explains why evaluation
  must be explicit. Then come the definitions of the pure **vau-x calculus**: [Syntax](#/node/Syntax),
  [Values](#/node/Values), [Substitution](#/node/Substitution) and the seven general reduction rules in
  [ReductionSchemata](#/node/ReductionSchemata).
- Two informal nodes on environments, [Environments](#/node/Environments) and
  [VauEnvironments](#/node/VauEnvironments), so that `$vau` makes sense.

## What is not here yet

**No Lean exists in this repository yet.** Every node is a *concept* marked **PLAN: no Lean yet**. A node
explains the theory from the cited sources; it does not say that anything is proved. The plan is:

1. a proof graph of the planned formalization, with every node marked as planned;
2. a Lean 4 formalization of the pure vau-x rules in this repository: syntax, substitution, the
   reduction rules, their compatible closure, evaluation as a special case of reduction, a lambda
   embedding, and confluence of the concrete vau-x rules.

The Lean will **not** formalize Shutt's general framework of regular substitutive reduction systems. As
Lean lands, nodes will change from PLAN to proved or partial, and the [Trust](#/trust) page will list the
sorry and axiom counts.

## How to read a node

Each node has a plain-English explanation, faithfulness notes (where the English is looser than the
source), and a short optional quiz. Tick **I think I understand this** when you do. A node counts as
understood once everything it mentions is understood too. Progress stays in your browser.

The box on the right of a node says where the definition comes from. Links to the thesis go to the PDF
page (not the printed page number).

## Sources

- John N. Shutt, *Fexprs as the basis of Lisp function application; or, $vau: the ultimate
  abstraction*, PhD thesis, WPI, 2010.
  [PDF](https://web.cs.wpi.edu/~jshutt/dissertation/etd-090110-124904-Shutt-Dissertation.pdf)
- John N. Shutt, NEPLS talk, 2007. [Talk script](https://web.cs.wpi.edu/~jshutt/jns-nepls07.txt)
- Dale Schumacher, [Fexpr the Ultimate Lambda](https://dalnefre.com/wp/2011/11/fexpr-the-ultimate-lambda/), 2011.
- Dale Schumacher, [Semantic Extensibility with Vau](https://dalnefre.com/wp/2011/12/semantic-extensibility-with-vau/), 2011.
- Dale Schumacher, [Implementing Actors in Kernel](https://dalnefre.com/wp/2012/02/implementing-actors-in-kernel/), 2012.
- Mitchell Wand, *The Theory of Fexprs is Trivial*, Lisp and Symbolic Computation 10(3), 1998.
