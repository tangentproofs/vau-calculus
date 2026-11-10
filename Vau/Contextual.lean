import Vau.Confluence

/-!
# Contextual equivalence in vau-x is nontrivial

Wand (1998) showed that in a calculus with implicit evaluation and fully reflective fexprs,
contextual equivalence is trivial: it holds only between terms that are the same up to renaming
of bound variables. With de Bruijn indices, that means only between equal terms.

This file uses one simple notion of observation, chosen by this project (Shutt's general notion
is thesis Definition 13.90, for calculi with an operational semantics, which vau-x lacks):

* a context `c` **observes** a normal form `N` of a term `t` if `c[t] ->* N`, where `N` is a
  normal form (a term with no step);
* `t1` and `t2` are **contextually equivalent** if, in every context, they reach the same normal
  forms. In particular, `c[t1]` reaches some normal form iff `c[t2]` does.

This observes more than Shutt's Definition 13.90 in one way (any normal form, not only minimal
observables) and less in another (full reduction, not an evaluation order).

Contexts are the one-hole contexts `Ctx` of `Vau/Reduction.lean`. They may capture free
variables, and they are not required to be closed.

Results:

* `conv_ctxEquiv`: equal terms in the equational theory are contextually equivalent. The proof
  uses confluence.
* `nontrivial`: `[eval 5]` and `5` are two different terms that are contextually equivalent,
  and `5` and `6` are not contextually equivalent. So the relation is neither equality nor
  "everything is equal".
-/

namespace Vau
open Term

/-- Contextual equivalence: in every one-hole context, the two terms reach the same normal
forms. -/
def CtxEquiv (t1 t2 : Term) : Prop :=
  forall (c : Ctx) (N : Term), Normal N -> (Steps (c.plug t1) N <-> Steps (c.plug t2) N)

/-- Reaching a normal form is preserved by the equational theory (uses confluence). -/
theorem Conv.steps_normal {a b N : Term} (hN : Normal N) (h : Conv a b) (ha : Steps a N) :
    Steps b N := by
  exact (church_rosser (EqvGen.trans (EqvGen.symm h) ha.toEqvGen)).elim fun u hu => by
    have hb := hu.1
    rw [<- Steps.normal_eq hN hu.2] at hb
    exact hb

/-- Equal terms in the equational theory of vau-x are contextually equivalent. -/
theorem conv_ctxEquiv {t1 t2 : Term} (h : Conv t1 t2) : CtxEquiv t1 t2 := by
  intro c N hN
  have hc := Conv.plug c h
  exact Iff.intro (Conv.steps_normal hN hc) (Conv.steps_normal hN (EqvGen.symm hc))

/-- **Contextual equivalence in vau-x is nontrivial.** `[eval 5]` and `5` are different terms
and are contextually equivalent; `5` and `6` are not contextually equivalent. -/
theorem nontrivial :
    Not (eval (dat 5) = dat 5) /\ CtxEquiv (eval (dat 5)) (dat 5) /\ Not (CtxEquiv (dat 5) (dat 6)) := by
  refine And.intro (by simp) (And.intro (conv_ctxEquiv (.rel (.top (.evalSelf (.dat 5))))) ?_)
  intro h
  have h6 : Steps (Ctx.hole.plug (dat 6)) (dat 5) := (h .hole (dat 5) (normal_dat 5)).1 (.refl _)
  have := Steps.normal_eq (normal_dat 6) h6
  simp at this

end Vau
