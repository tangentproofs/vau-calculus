import Vau.Confluence

/-!
# The lambda embedding

Shutt's map (15.28) in thesis section 15.4 sends lambda terms to fexpr terms. Written for vau-x
(which has no environments, so the environment argument of (15.28) is dropped; that adaptation is
this project's):

```
embed x           = x
embed c           = c                      (a constant becomes primitive data)
embed (M N)       = [combine (embed M) (embed N)]
embed (lambda x.M) = <vau x.(embed M)>
```

beta-vau fires only on a value operand. The image of a variable, a constant or an abstraction is
a value; the image of an application is not. So the image behaves like the **call-by-value**
lambda calculus (Plotkin's lambda-v): beta fires only when the argument is a value. `LStep` below
is that calculus, with beta-v allowed at any position (including under a lambda).

Results:

* `embed_step`: one lambda-v step is one vau-x step (simulation).
* `step_embed`: every vau-x step from `embed M` is the image of one lambda-v step from `M`
  (no new steps).
-/

namespace Vau
open Term

/-- Lambda terms with constants, de Bruijn indices. -/
inductive LTerm where
  | var : Nat -> LTerm
  | con : Nat -> LTerm
  | app : LTerm -> LTerm -> LTerm
  | lam : LTerm -> LTerm
  deriving DecidableEq, Repr

namespace LTerm

/-- Values of the call-by-value lambda calculus: variables, constants and abstractions. -/
inductive IsValue : LTerm -> Prop where
  | var (n : Nat) : IsValue (var n)
  | con (n : Nat) : IsValue (con n)
  | lam (t : LTerm) : IsValue (lam t)

def rename (rn : Nat -> Nat) : LTerm -> LTerm
  | var n => var (rn n)
  | con n => con n
  | app a b => app (rename rn a) (rename rn b)
  | lam t => lam (rename (lift rn) t)

def up (sg : Nat -> LTerm) : Nat -> LTerm
  | 0 => var 0
  | n + 1 => rename Nat.succ (sg n)

def subst (sg : Nat -> LTerm) : LTerm -> LTerm
  | var n => sg n
  | con n => con n
  | app a b => app (subst sg a) (subst sg b)
  | lam t => lam (subst (up sg) t)

def scons (v : LTerm) (sg : Nat -> LTerm) : Nat -> LTerm
  | 0 => v
  | n + 1 => sg n

/-- Single substitution `t[0 <- v]`. -/
def inst (t v : LTerm) : LTerm := subst (scons v var) t

end LTerm

/-- One step of the call-by-value lambda calculus (beta-v, compatible closure). -/
inductive LStep : LTerm -> LTerm -> Prop where
  | beta {v : LTerm} (t : LTerm) : v.IsValue -> LStep (.app (.lam t) v) (t.inst v)
  | lam {t t' : LTerm} : LStep t t' -> LStep (.lam t) (.lam t')
  | appL {a a' : LTerm} (b : LTerm) : LStep a a' -> LStep (.app a b) (.app a' b)
  | appR (a : LTerm) {b b' : LTerm} : LStep b b' -> LStep (.app a b) (.app a b')

/-- The embedding of lambda terms into vau-x terms, map (15.28). -/
def embed : LTerm -> Term
  | .var n => var n
  | .con n => dat n
  | .app a b => comb (embed a) (embed b)
  | .lam t => vau (embed t)

theorem embed_injective {a b : LTerm} (h : embed a = embed b) : a = b := by
  induction a generalizing b with
  | var n => cases b <;> simp_all [embed]
  | con n => cases b <;> simp_all [embed]
  | app a1 a2 ih1 ih2 =>
    cases b with
    | app b1 b2 =>
      simp only [embed, Term.comb.injEq] at h
      rw [ih1 h.1, ih2 h.2]
    | _ => simp [embed] at h
  | lam t ih =>
    cases b with
    | lam u => simp only [embed, Term.vau.injEq] at h; rw [ih h]
    | _ => simp [embed] at h

theorem embed_rename (rn : Nat -> Nat) (t : LTerm) :
    embed (t.rename rn) = rename rn (embed t) := by
  induction t generalizing rn with
  | var n => rfl
  | con n => rfl
  | app a b iha ihb => simp only [LTerm.rename, embed, Vau.rename, iha, ihb]
  | lam t ih => simp only [LTerm.rename, embed, Vau.rename, ih]

theorem embed_subst (sg : Nat -> LTerm) (t : LTerm) :
    embed (t.subst sg) = subst (Function.comp embed sg) (embed t) := by
  induction t generalizing sg with
  | var n => rfl
  | con n => rfl
  | app a b iha ihb => simp only [LTerm.subst, embed, Vau.subst, iha, ihb]
  | lam t ih =>
    simp only [LTerm.subst, embed, Vau.subst, ih]
    congr 2
    funext n
    cases n with
    | zero => rfl
    | succ n => simp only [Function.comp, LTerm.up, Vau.up, embed_rename]

theorem embed_inst (t v : LTerm) : embed (t.inst v) = inst (embed t) (embed v) := by
  simp only [LTerm.inst, Vau.inst, embed_subst]
  congr 1
  funext n
  cases n <;> rfl

theorem embed_isValue {v : LTerm} (h : v.IsValue) : IsValue (embed v) := by
  cases h with
  | var n => exact .var n
  | con n => exact .dat n
  | lam t => exact .vau _

theorem isValue_of_embed {v : LTerm} (h : IsValue (embed v)) : v.IsValue := by
  cases v with
  | var n => exact .var n
  | con n => exact .con n
  | lam t => exact .lam t
  | app a b => simp [embed] at h; cases h

/-- **Simulation.** One lambda-v step is one vau-x step between the images. -/
theorem embed_step {M N : LTerm} (h : LStep M N) : Step (embed M) (embed N) := by
  induction h with
  | beta t hv =>
    simp only [embed]
    rw [embed_inst]
    exact .top (.beta _ (embed_isValue hv))
  | lam _ ih => exact .vau ih
  | appL b _ ih => exact .combL _ ih
  | appR a _ ih => exact .combR _ ih

/-- **No new steps.** Every vau-x step from the image of `M` is the image of a lambda-v step. -/
theorem step_embed {M : LTerm} {T : Term} (h : Step (embed M) T) :
    exists N, LStep M N /\ T = embed N := by
  induction M generalizing T with
  | var n => cases h with | top h => cases h
  | con n => cases h with | top h => cases h
  | lam t ih =>
    cases h with
    | top h => cases h
    | vau h =>
      exact (ih h).elim fun N hN =>
        Exists.intro (.lam N) (And.intro (.lam hN.1) (by rw [hN.2]; rfl))
  | app a b iha ihb =>
    cases h with
    | top h =>
      cases a with
      | lam t =>
        cases h with
        | beta _ hv =>
          refine Exists.intro (t.inst b) (And.intro (.beta t (isValue_of_embed hv)) ?_)
          rw [embed_inst]
      | var n => cases h
      | con n => cases h
      | app _ _ => cases h
    | combL _ h =>
      exact (iha h).elim fun N hN =>
        Exists.intro (.app N b) (And.intro (.appL b hN.1) (by rw [hN.2]; rfl))
    | combR _ h =>
      exact (ihb h).elim fun N hN =>
        Exists.intro (.app a N) (And.intro (.appR a hN.1) (by rw [hN.2]; rfl))

/-- Zero or more lambda-v steps. -/
abbrev LSteps := Star LStep

/-- The equational theory of lambda-v. -/
abbrev LConv := EqvGen LStep

theorem steps_embed {M : LTerm} {T : Term} (h : Steps (embed M) T) :
    exists N, LSteps M N /\ T = embed N := by
  generalize hM : embed M = T0 at h
  induction h with
  | refl => exact Exists.intro M (And.intro (.refl _) hM.symm)
  | tail _ hs ih =>
    exact ih.elim fun N hN => by
      rw [hN.2] at hs
      exact (step_embed hs).elim fun N' hN' =>
        Exists.intro N' (And.intro (.tail hN.1 hN'.1) hN'.2)

/-- **Conservative extension.** Two lambda terms are equal in the call-by-value lambda calculus
if and only if their images are equal in vau-x. The "if" half uses confluence of vau-x. -/
theorem conservative_extension (M N : LTerm) : LConv M N <-> Conv (embed M) (embed N) := by
  apply Iff.intro
  next =>
    intro h
    induction h with
    | rel h => exact .rel (embed_step h)
    | refl t => exact .refl _
    | symm _ ih => exact .symm ih
    | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  next =>
    intro h
    exact (church_rosser h).elim fun u hu =>
      (steps_embed hu.1).elim fun P hP =>
        (steps_embed hu.2).elim fun Q hQ => by
          have hPQ : Q = P := embed_injective (hQ.2.symm.trans hP.2)
          subst hPQ
          exact .trans hP.1.toEqvGen (.symm hQ.1.toEqvGen)

end Vau
