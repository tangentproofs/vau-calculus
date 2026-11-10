# About this site

This site explains **John N. Shutt's vau calculus** in plain English. Vau calculus is a family of
calculi for reasoning about **fexprs**: first-class Lisp combiners that receive their operands
unevaluated. Shutt developed it in his PhD thesis (Worcester Polytechnic Institute, 2010) and used it as
the basis of the Kernel programming language.

## What is here now (Step 4)

- [Start here](#/start): the headline statements, then every definition they use, simplest first.
- The [Start](#/node/Start) node explains why evaluation must be explicit.
- The pure **vau-x calculus** in Lean (folder `Vau/`): [Term](#/node/Term), [IsValue](#/node/IsValue),
  substitution [inst](#/node/inst), the seven rules [Top](#/node/Top), and their compatible closure
  [Step](#/node/Step).
- Four vau-x headlines **proved in Lean**:
  [eval_is_reduction](#/node/eval_is_reduction),
  [conservative_extension](#/node/conservative_extension) (through the lambda embedding
  [embed](#/node/embed)), [confluence](#/node/confluence) and [nontrivial](#/node/nontrivial).
- A Lean model of Shutt's **vau-e** calculus (folder `Vau/Env/`, namespace `VauE`), with symbols and
  environments: [VauE.Env](#/node/VauE.Env), the rules [VauE.Top](#/node/VauE.Top), the `$vau` call
  rule [VauE.vau_call](#/node/VauE.vau_call), [VauE.unwrap_wrap](#/node/VauE.unwrap_wrap), and the
  fifth headline [VauE.derived_lambda](#/node/VauE.derived_lambda).
- Still **PLAN** (no Lean): [EnvironmentOpacity](#/node/EnvironmentOpacity),
  [EncapsulationTypes](#/node/EncapsulationTypes) and the [ActorLayer](#/node/ActorLayer).

## What the Lean does not do

The Lean does **not** formalize Shutt's general framework of regular substitutive reduction systems
(thesis chapter 13), and it does not prove confluence of vau-e. The vau-x results are about the concrete
vau-x rules with no delta-rules. The vau-e results use unsorted environments and two delta-rules
(`$eval`, `$list*`) written by this project. Some definitions are this project's own choice (the evaluator, the notion of
observation); their nodes say so. The [Trust](#/trust) page lists the `sorry` and axiom counts and the
`#print axioms` output.

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
