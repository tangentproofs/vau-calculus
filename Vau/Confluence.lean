import Vau.Reduction

/-!
# Confluence of the vau-x rules

This file proves that `Steps` (zero or more steps of the seven general vau-x schemata, in the
compatible closure) is confluent: `Vau.confluence`.

Method: parallel reduction and complete developments (Tait, Martin-Lof, Takahashi). `Par` fires
any set of redexes that are present in a term at once. `cd t` fires all of them. The key lemma
`Par.to_cd` says that every parallel step from `t` can be continued to `cd t` in one more parallel
step. That gives the diamond property of `Par`, and `Steps` and the closure of `Par` are equal.

**Scope.** This is a direct proof for the concrete vau-x rules with no delta-rules. It does
**not** formalize Shutt's regular substitutive reduction systems (thesis chapter 13) or his
Church-Rosser theorem for them (Theorem 13.104). It only checks the conclusion for vau-x.
-/

namespace Vau
open Term

/-- Parallel reduction. -/
inductive Par : Term -> Term -> Prop where
  | var  (n : Nat) : Par (var n) (var n)
  | dat  (n : Nat) : Par (dat n) (dat n)
  | prim (n : Nat) : Par (prim n) (prim n)
  | ign : Par ign ign
  | nil : Par nil nil
  | vau  {t t' : Term} : Par t t' -> Par (vau t) (vau t')
  | vau0 {t t' : Term} : Par t t' -> Par (vau0 t) (vau0 t')
  | vau2 {t t' : Term} : Par t t' -> Par (vau2 t) (vau2 t')
  | wrap {t t' : Term} : Par t t' -> Par (wrap t) (wrap t')
  | eval {t t' : Term} : Par t t' -> Par (eval t) (eval t')
  | pair {a a' b b' : Term} : Par a a' -> Par b b' -> Par (pair a b) (pair a' b')
  | comb {a a' b b' : Term} : Par a a' -> Par b b' -> Par (comb a b) (comb a' b')
  | evalSelf {s s' : Term} : SelfEval s -> Par s s' -> Par (eval s) s'
  | evalPair {a a' b b' : Term} : Par a a' -> Par b b' -> Par (eval (pair a b)) (comb (eval a') b')
  | evalWrap {t t' : Term} : Par t t' -> Par (eval (wrap t)) (wrap (eval t'))
  | beta {t t' v v' : Term} : IsValue v -> Par t t' -> Par v v' -> Par (comb (vau t) v) (inst t' v')
  | combWrap {t t' ts ts' : Term} : IsList ts -> Par t t' -> Par ts ts' ->
      Par (comb (wrap t) ts) (comb t' (evalList ts'))
  | parsePair {t t' a a' b b' : Term} : Par t t' -> Par a a' -> Par b b' ->
      Par (comb (vau2 t) (pair a b)) (comb (comb t' a') b')
  | parseNil {t t' : Term} : Par t t' -> Par (comb (vau0 t) nil) t'

namespace Par

theorem refl : forall t : Term, Par t t
  | .var n => .var n
  | .dat n => .dat n
  | .prim n => .prim n
  | .ign => .ign
  | .nil => .nil
  | .vau t => .vau (refl t)
  | .vau0 t => .vau0 (refl t)
  | .vau2 t => .vau2 (refl t)
  | .wrap t => .wrap (refl t)
  | .eval t => .eval (refl t)
  | .pair a b => .pair (refl a) (refl b)
  | .comb a b => .comb (refl a) (refl b)

theorem of_top {t t' : Term} (h : Top t t') : Par t t' := by
  cases h with
  | evalSelf hs => exact .evalSelf hs (refl _)
  | evalPair => exact .evalPair (refl _) (refl _)
  | evalWrap => exact .evalWrap (refl _)
  | beta _ hv => exact .beta hv (refl _) (refl _)
  | combWrap _ hl => exact .combWrap hl (refl _) (refl _)
  | parsePair => exact .parsePair (refl _) (refl _) (refl _)
  | parseNil => exact .parseNil (refl _)

theorem of_step {t t' : Term} (h : Step t t') : Par t t' := by
  induction h with
  | top h => exact of_top h
  | vau _ ih => exact .vau ih
  | vau0 _ ih => exact .vau0 ih
  | vau2 _ ih => exact .vau2 ih
  | wrap _ ih => exact .wrap ih
  | eval _ ih => exact .eval ih
  | pairL b _ ih => exact .pair ih (refl b)
  | pairR a _ ih => exact .pair (refl a) ih
  | combL b _ ih => exact .comb ih (refl b)
  | combR a _ ih => exact .comb (refl a) ih

/-! ### What parallel steps preserve -/

theorem selfEval {s s' : Term} (h : Par s s') (hs : SelfEval s) : SelfEval s' := by
  cases hs <;> cases h <;> constructor

theorem isValue {v v' : Term} (h : Par v v') (hv : IsValue v) : IsValue v' := by
  induction h with
  | pair _ _ iha ihb => cases hv with | pair ha hb => exact .pair (iha ha) (ihb hb)
  | wrap _ ih => cases hv with | wrap ht => exact .wrap (ih ht)
  | eval _ _ => cases hv
  | comb _ _ _ _ => cases hv
  | evalSelf _ _ _ => cases hv
  | evalPair _ _ _ _ => cases hv
  | evalWrap _ _ => cases hv
  | beta _ _ _ _ _ => cases hv
  | combWrap _ _ _ _ _ => cases hv
  | parsePair _ _ _ _ _ _ => cases hv
  | parseNil _ _ => cases hv
  | _ => constructor

theorem isList {ts ts' : Term} (h : Par ts ts') (hl : IsList ts) : IsList ts' := by
  induction hl generalizing ts' with
  | nil => cases h; exact .nil
  | cons a _ ih => cases h with | pair _ hb => exact .cons _ (ih hb)

theorem evalList {ts ts' : Term} (h : Par ts ts') (hl : IsList ts) :
    Par (Vau.evalList ts) (Vau.evalList ts') := by
  induction hl generalizing ts' with
  | nil => cases h; exact .nil
  | cons a _ ih => cases h with | pair ha hb => exact .pair (.eval ha) (ih hb)

/-! ### Parallel steps under renaming and substitution -/

theorem rename {t t' : Term} (rn : Nat -> Nat) (h : Par t t') :
    Par (Vau.rename rn t) (Vau.rename rn t') := by
  induction h generalizing rn with
  | var n => exact .var _
  | dat n => exact .dat n
  | prim n => exact .prim n
  | ign => exact .ign
  | nil => exact .nil
  | vau _ ih => exact .vau (ih _)
  | vau0 _ ih => exact .vau0 (ih _)
  | vau2 _ ih => exact .vau2 (ih _)
  | wrap _ ih => exact .wrap (ih _)
  | eval _ ih => exact .eval (ih _)
  | pair _ _ iha ihb => exact .pair (iha _) (ihb _)
  | comb _ _ iha ihb => exact .comb (iha _) (ihb _)
  | evalSelf hs _ ih => exact .evalSelf (hs.rename rn) (ih _)
  | evalPair _ _ iha ihb => exact .evalPair (iha _) (ihb _)
  | evalWrap _ ih => exact .evalWrap (ih _)
  | beta hv _ _ iht ihv =>
    rw [rename_inst]
    exact .beta (hv.rename rn) (iht _) (ihv _)
  | combWrap hl _ hts iht ihts =>
    simp only [Vau.rename]
    rw [rename_evalList rn (hts.isList hl)]
    exact .combWrap (hl.rename rn) (iht _) (ihts _)
  | parsePair _ _ _ iht iha ihb => exact .parsePair (iht _) (iha _) (ihb _)
  | parseNil _ ih => exact .parseNil (ih _)

theorem subst {t t' : Term} {sg tg : Nat -> Term} (h : Par t t') (hsgtg : forall n, Par (sg n) (tg n))
    (hsg : forall n, IsValue (sg n)) : Par (Vau.subst sg t) (Vau.subst tg t') := by
  induction h generalizing sg tg with
  | var n => exact hsgtg n
  | dat n => exact .dat n
  | prim n => exact .prim n
  | ign => exact .ign
  | nil => exact .nil
  | vau _ ih =>
    refine .vau (ih ?_ (IsValue.up hsg))
    intro n; cases n with
    | zero => exact .var 0
    | succ n => exact (hsgtg n).rename Nat.succ
  | vau0 _ ih => exact .vau0 (ih hsgtg hsg)
  | vau2 _ ih => exact .vau2 (ih hsgtg hsg)
  | wrap _ ih => exact .wrap (ih hsgtg hsg)
  | eval _ ih => exact .eval (ih hsgtg hsg)
  | pair _ _ iha ihb => exact .pair (iha hsgtg hsg) (ihb hsgtg hsg)
  | comb _ _ iha ihb => exact .comb (iha hsgtg hsg) (ihb hsgtg hsg)
  | evalSelf hs _ ih => exact .evalSelf (hs.subst sg) (ih hsgtg hsg)
  | evalPair _ _ iha ihb => exact .evalPair (iha hsgtg hsg) (ihb hsgtg hsg)
  | evalWrap _ ih => exact .evalWrap (ih hsgtg hsg)
  | beta hv _ _ iht ihv =>
    rw [subst_inst]
    refine .beta (hv.subst hsg) (iht ?_ (IsValue.up hsg)) (ihv hsgtg hsg)
    intro n; cases n with
    | zero => exact .var 0
    | succ n => exact (hsgtg n).rename Nat.succ
  | combWrap hl _ hts iht ihts =>
    simp only [Vau.subst]
    rw [subst_evalList tg (hts.isList hl)]
    exact .combWrap (hl.subst sg) (iht hsgtg hsg) (ihts hsgtg hsg)
  | parsePair _ _ _ iht iha ihb => exact .parsePair (iht hsgtg hsg) (iha hsgtg hsg) (ihb hsgtg hsg)
  | parseNil _ ih => exact .parseNil (ih hsgtg hsg)

theorem inst {t t' v v' : Term} (ht : Par t t') (hv : Par v v') (hval : IsValue v) :
    Par (Vau.inst t v) (Vau.inst t' v') := by
  refine subst ht ?_ (IsValue.scons hval)
  intro n; cases n with
  | zero => exact hv
  | succ n => exact .var n

end Par

/-! ## Complete development -/

/-- `true` iff the term is a pair. -/
def isPairB : Term -> Bool
  | .pair _ _ => true
  | _ => false

/-- `true` iff the term is `()`. -/
def isNilB : Term -> Bool
  | .nil => true
  | _ => false

/-- The result of parse-pair, read off the development of a pair operand. -/
def parse2 (t' : Term) : Term -> Term
  | .pair a b => .comb (.comb t' a) b
  | b => .comb (.vau2 t') b

/-- Complete development: fire every redex that is present in the term, at once. -/
def cd : Term -> Term
  | .var n => .var n
  | .dat n => .dat n
  | .prim n => .prim n
  | .ign => .ign
  | .nil => .nil
  | .vau t => .vau (cd t)
  | .vau0 t => .vau0 (cd t)
  | .vau2 t => .vau2 (cd t)
  | .pair a b => .pair (cd a) (cd b)
  | .wrap t => .wrap (cd t)
  | .eval t =>
    match t with
    | .pair a b => .comb (.eval (cd a)) (cd b)
    | .wrap u => .wrap (.eval (cd u))
    | .dat n => .dat n
    | .prim n => .prim n
    | .ign => .ign
    | .nil => .nil
    | .vau u => .vau (cd u)
    | .vau0 u => .vau0 (cd u)
    | .vau2 u => .vau2 (cd u)
    | .var n => .eval (.var n)
    | .eval u => .eval (cd (.eval u))
    | .comb u w => .eval (cd (.comb u w))
  | .comb a b =>
    match a with
    | .vau u => if isValueB b then Vau.inst (cd u) (cd b) else .comb (.vau (cd u)) (cd b)
    | .wrap u => if isListB b then .comb (cd u) (evalList (cd b)) else .comb (.wrap (cd u)) (cd b)
    | .vau2 u => if isPairB b then parse2 (cd u) (cd b) else .comb (.vau2 (cd u)) (cd b)
    | .vau0 u => if isNilB b then cd u else .comb (.vau0 (cd u)) (cd b)
    | .var n => .comb (.var n) (cd b)
    | .dat n => .comb (.dat n) (cd b)
    | .prim n => .comb (.prim n) (cd b)
    | .ign => .comb .ign (cd b)
    | .nil => .comb .nil (cd b)
    | .pair x y => .comb (cd (.pair x y)) (cd b)
    | .eval u => .comb (cd (.eval u)) (cd b)
    | .comb u w => .comb (cd (.comb u w)) (cd b)

theorem cd_eval_self {s : Term} (hs : SelfEval s) : cd (.eval s) = cd s := by
  cases hs <;> rfl

/-- Takahashi's lemma: a parallel step from `t` can always be completed to `cd t`. -/
theorem Par.to_cd {t s : Term} (h : Par t s) : Par s (cd t) := by
  induction h with
  | var n => exact .var n
  | dat n => exact .dat n
  | prim n => exact .prim n
  | ign => exact .ign
  | nil => exact .nil
  | vau _ ih => exact .vau ih
  | vau0 _ ih => exact .vau0 ih
  | vau2 _ ih => exact .vau2 ih
  | wrap _ ih => exact .wrap ih
  | pair _ _ iha ihb => exact .pair iha ihb
  | @eval t t' h ih =>
    cases t with
    | pair a b =>
      cases h with
      | pair _ _ => cases ih with | pair ha hb => exact .evalPair ha hb
    | wrap u =>
      cases h with
      | wrap _ => cases ih with | wrap hu => exact .evalWrap hu
    | var n => cases h; exact .eval (.var n)
    | eval u => exact .eval ih
    | comb u w => exact .eval ih
    | dat n => exact .evalSelf (h.selfEval (.dat n)) ih
    | prim n => exact .evalSelf (h.selfEval (.prim n)) ih
    | ign => exact .evalSelf (h.selfEval .ign) ih
    | nil => exact .evalSelf (h.selfEval .nil) ih
    | vau u => exact .evalSelf (h.selfEval (.vau u)) ih
    | vau0 u => exact .evalSelf (h.selfEval (.vau0 u)) ih
    | vau2 u => exact .evalSelf (h.selfEval (.vau2 u)) ih
  | @comb a a' b b' ha hb iha ihb =>
    cases a with
    | vau u =>
      cases ha with
      | vau hu =>
        cases iha with
        | vau hu' =>
          simp only [Vau.cd]
          split
          next hv => exact .beta (hb.isValue ((isValueB_iff b).1 hv)) hu' ihb
          next => exact .comb (.vau hu') ihb
    | wrap u =>
      cases ha with
      | wrap hu =>
        cases iha with
        | wrap hu' =>
          simp only [Vau.cd]
          split
          next hl => exact .combWrap (hb.isList ((isListB_iff b).1 hl)) hu' ihb
          next => exact .comb (.wrap hu') ihb
    | vau2 u =>
      cases ha with
      | vau2 hu =>
        cases iha with
        | vau2 hu' =>
          cases b with
          | pair x y =>
            cases hb with
            | pair hx hy =>
              cases ihb with
              | pair hx' hy' => exact .parsePair hu' hx' hy'
          | _ => exact .comb (.vau2 hu') ihb
    | vau0 u =>
      cases ha with
      | vau0 hu =>
        cases iha with
        | vau0 hu' =>
          cases b with
          | nil => cases hb; exact .parseNil hu'
          | _ => exact .comb (.vau0 hu') ihb
    | _ => exact .comb iha ihb
  | evalSelf hs _ ih => rw [cd_eval_self hs]; exact ih
  | evalPair _ _ iha ihb => exact .comb (.eval iha) ihb
  | evalWrap _ ih => exact .wrap (.eval ih)
  | @beta t t' v v' hv _ hvv iht ihv =>
    have : Vau.cd (Term.comb (Term.vau t) v) = Vau.inst (Vau.cd t) (Vau.cd v) := by
      simp only [Vau.cd, (isValueB_iff v).2 hv, if_true]
    rw [this]
    exact Par.inst iht ihv (hvv.isValue hv)
  | @combWrap t t' ts ts' hl _ hts iht ihts =>
    have : Vau.cd (Term.comb (Term.wrap t) ts) = Term.comb (Vau.cd t) (Vau.evalList (Vau.cd ts)) := by
      simp only [Vau.cd, (isListB_iff ts).2 hl, if_true]
    rw [this]
    exact .comb iht (ihts.evalList (hts.isList hl))
  | parsePair _ _ _ iht iha ihb => exact .comb (.comb iht iha) ihb
  | parseNil _ ih => exact ih

/-- The diamond property of parallel reduction. -/
theorem Par.diamond {t s1 s2 : Term} (h1 : Par t s1) (h2 : Par t s2) :
    exists u, Par s1 u /\ Par s2 u :=
  Exists.intro (cd t) (And.intro h1.to_cd h2.to_cd)

theorem Par.toSteps {t t' : Term} (h : Par t t') : Steps t t' := by
  induction h with
  | var n => exact .refl _
  | dat n => exact .refl _
  | prim n => exact .refl _
  | ign => exact .refl _
  | nil => exact .refl _
  | vau _ ih => exact ih.vau
  | vau0 _ ih => exact ih.vau0
  | vau2 _ ih => exact ih.vau2
  | wrap _ ih => exact ih.wrap
  | eval _ ih => exact ih.eval
  | pair _ _ iha ihb => exact Steps.pair iha ihb
  | comb _ _ iha ihb => exact Steps.comb iha ihb
  | evalSelf hs _ ih => exact Star.head (.top (.evalSelf hs)) ih
  | evalPair _ _ iha ihb => exact (Steps.eval (Steps.pair iha ihb)).trans (Steps.top (.evalPair _ _))
  | evalWrap _ ih => exact (Steps.eval (Steps.wrap ih)).trans (Steps.top (.evalWrap _))
  | beta hv _ hvv iht ihv =>
    exact (Steps.comb (Steps.vau iht) ihv).trans (Steps.top (.beta _ (hvv.isValue hv)))
  | combWrap hl _ hts iht ihts =>
    exact (Steps.comb (Steps.wrap iht) ihts).trans (Steps.top (.combWrap _ (hts.isList hl)))
  | parsePair _ _ _ iht iha ihb =>
    exact (Steps.comb (Steps.vau2 iht) (Steps.pair iha ihb)).trans (Steps.top (.parsePair _ _ _))
  | parseNil _ ih => exact (Steps.top (.parseNil _)).trans ih

theorem steps_iff_par_star {t t' : Term} : Steps t t' <-> Star Par t t' :=
  Iff.intro (Star.mono (fun h => Star.single (Par.of_step h))) (Star.mono Par.toSteps)

/-- The strip lemma for parallel reduction. -/
theorem Par.strip {t s1 s2 : Term} (h1 : Star Par t s1) (h2 : Par t s2) :
    exists u, Par s1 u /\ Star Par s2 u := by
  induction h1 with
  | refl => exact Exists.intro s2 (And.intro h2 (.refl _))
  | tail _ hbc ih =>
    exact ih.elim fun u hu =>
      (Par.diamond hbc hu.1).elim fun w hw =>
        Exists.intro w (And.intro hw.1 (.tail hu.2 hw.2))

theorem Par.star_confluent {t s1 s2 : Term} (h1 : Star Par t s1) (h2 : Star Par t s2) :
    exists u, Star Par s1 u /\ Star Par s2 u := by
  induction h2 with
  | refl => exact Exists.intro s1 (And.intro (.refl _) h1)
  | tail _ hbc ih =>
    exact ih.elim fun u hu =>
      (Par.strip hu.2 hbc).elim fun w hw =>
        Exists.intro w (And.intro (.tail hu.1 hw.1) hw.2)

/-- **Confluence of vau-x** (seven general schemata, no delta-rules, compatible closure):
if `t ->* s1` and `t ->* s2`, then `s1 ->* u` and `s2 ->* u` for some `u`. -/
theorem confluence {t s1 s2 : Term} (h1 : Steps t s1) (h2 : Steps t s2) :
    exists u, Steps s1 u /\ Steps s2 u := by
  exact (Par.star_confluent (steps_iff_par_star.1 h1) (steps_iff_par_star.1 h2)).elim fun u hu =>
    Exists.intro u (And.intro (steps_iff_par_star.2 hu.1) (steps_iff_par_star.2 hu.2))

/-- Church-Rosser form: two terms that are equal in the equational theory have a common reduct. -/
theorem church_rosser {a b : Term} (h : Conv a b) : exists u, Steps a u /\ Steps b u := by
  induction h with
  | rel h => exact Exists.intro _ (And.intro (Star.single h) (.refl _))
  | refl t => exact Exists.intro t (And.intro (.refl _) (.refl _))
  | symm _ ih => exact ih.elim fun u hu => Exists.intro u (And.intro hu.2 hu.1)
  | trans _ _ ih1 ih2 =>
    exact ih1.elim fun u1 h1 => ih2.elim fun u2 h2 =>
      (confluence h1.2 h2.1).elim fun w hw =>
        Exists.intro w (And.intro (h1.1.trans hw.1) (h2.2.trans hw.2))

/-- Two different normal forms are never equal in the equational theory. -/
theorem Conv.normal_eq {a b : Term} (ha : Normal a) (hb : Normal b) (h : Conv a b) : a = b := by
  exact (church_rosser h).elim fun u hu => by
    rw [Steps.normal_eq ha hu.1, Steps.normal_eq hb hu.2]

end Vau
