import Vau.Env.Confluence
import Vau.Env.Lambda

/-!
# Environment opacity and hygiene in vau-e

In Kernel a program cannot list the bindings of an environment or take it apart. It can only
evaluate symbols in it. Shutt counts this encapsulation among his tactics for hygiene (thesis
chapter 5), and as one reason why his fexprs do not make the theory trivial (chapter 15).

This file proves, for this formalization of vau-e:

* `env_opacity`: two environments that give the same answer to every lookup cannot be told apart
  by any program: in every one-hole context, one reduces to primitive data `n` exactly when the
  other does. So the order of bindings and bindings hidden behind an earlier binding of the same
  symbol cannot be observed (`shadow_invisible`, `order_invisible`).
* `match_env_opaque`: a parameter tree can only bind an environment whole or ignore it.
* `ignore_hygiene`: a compound operative whose environment parameter is `#ignore` gives the same
  result when called from any two dynamic environments.

The proof of `env_opacity` uses a simulation `Sim`: the relation that compares terms part by part,
and environments only through their lookups. `Sim.steps` shows that every reduction of one side is
matched by a reduction of the other.

**Scope.** Observation is reduction to primitive data. The contexts are the one-hole contexts `Ctx`
below, which reach every position, including inside environment bindings.
-/

namespace VauE
open Term

/-! ## Lookups in appended environments -/

theorem lookup_append (x : Nat) : forall (pre l : Env),
    Env.lookup x (pre ++ l) = (Env.lookup x pre).or (Env.lookup x l) :=
  Env.lookup_join x

theorem lookup_cons (x s : Nat) (y : Term) (l : Env) :
    Env.lookup x ((s, y) :: l) = if x = s then some y else Env.lookup x l := rfl

/-- Changing the binding at one position changes no lookup of another symbol, and no lookup at
all if an earlier binding hides it. -/
theorem lookup_replace {x s : Nat} {pre post : Env} {y z : Term}
    (h : Not (x = s) \/ Not (Env.lookup s pre = none)) :
    Env.lookup x (pre ++ (s, y) :: post) = Env.lookup x (pre ++ (s, z) :: post) := by
  rw [lookup_append, lookup_append, lookup_cons, lookup_cons]
  cases h with
  | inl hx => simp only [hx, if_false]
  | inr hs =>
    by_cases hx : x = s
    . subst hx
      cases hp : Env.lookup x pre with
      | none => exact absurd hp hs
      | some w => rfl
    . simp only [hx, if_false]

/-! ## The simulation relation -/

/-- Terms that are equal except that environments are compared only by their lookups. -/
inductive Sim : Term -> Term -> Prop where
  | dat (n : Nat) : Sim (dat n) (dat n)
  | prim (p : Prim) : Sim (prim p) (prim p)
  | sym (s : Nat) : Sim (sym s) (sym s)
  | ign : Sim ign ign
  | nil : Sim nil nil
  | env {bs bs' : Env} :
      (forall s, Env.lookup s bs = none <-> Env.lookup s bs' = none) ->
      (forall s u u', Env.lookup s bs = some u -> Env.lookup s bs' = some u' -> Sim u u') ->
      Sim (env bs) (env bs')
  | oper {a a' b b' c c' d d' : Term} :
      Sim a a' -> Sim b b' -> Sim c c' -> Sim d d' -> Sim (oper a b c d) (oper a' b' c' d')
  | pair {a a' b b' : Term} : Sim a a' -> Sim b b' -> Sim (pair a b) (pair a' b')
  | app {t t' : Term} : Sim t t' -> Sim (app t) (app t')
  | eval {a a' b b' : Term} : Sim a a' -> Sim b b' -> Sim (eval a b) (eval a' b')
  | comb {a a' b b' c c' : Term} :
      Sim a a' -> Sim b b' -> Sim c c' -> Sim (comb a b c) (comb a' b' c')

/-- Two binding lists related as by `Sim.env`. -/
def EnvSim (bs bs' : Env) : Prop :=
  (forall s, Env.lookup s bs = none <-> Env.lookup s bs' = none) /\
  (forall s u u', Env.lookup s bs = some u -> Env.lookup s bs' = some u' -> Sim u u')

theorem Sim.ofEnvSim {bs bs' : Env} (h : EnvSim bs bs') : Sim (Term.env bs) (Term.env bs') :=
  Sim.env h.1 h.2

theorem Sim.envSim {bs bs' : Env} (h : Sim (Term.env bs) (Term.env bs')) : EnvSim bs bs' := by
  cases h with
  | env h1 h2 => exact And.intro h1 h2

namespace Sim

mutual
theorem refl : forall t : Term, Sim t t
  | .dat n => .dat n
  | .prim p => .prim p
  | .sym s => .sym s
  | .ign => .ign
  | .nil => .nil
  | .env bs => .env (fun _ => Iff.rfl) (fun s u u' h1 h2 => by
      rw [h1] at h2
      cases h2
      exact reflLookup bs s u h1)
  | .oper a b c d => .oper (refl a) (refl b) (refl c) (refl d)
  | .pair a b => .pair (refl a) (refl b)
  | .app t => .app (refl t)
  | .eval a b => .eval (refl a) (refl b)
  | .comb a b c => .comb (refl a) (refl b) (refl c)
theorem reflLookup : forall (bs : Env) (s : Nat) (u : Term), Env.lookup s bs = some u -> Sim u u
  | [], _, _, h => by simp [Env.lookup] at h
  | (s', t) :: r, s, u, h => by
    rw [lookup_cons] at h
    by_cases hs : s = s'
    . rw [if_pos hs] at h
      cases h
      exact refl t
    . rw [if_neg hs] at h
      exact reflLookup r s u h
end

theorem symm {t t' : Term} (h : Sim t t') : Sim t' t := by
  induction h with
  | dat n => exact .dat n
  | prim p => exact .prim p
  | sym s => exact .sym s
  | ign => exact .ign
  | nil => exact .nil
  | env hn _ ih => exact .env (fun s => (hn s).symm) (fun s u u' h1 h2 => ih s u' u h2 h1)
  | oper _ _ _ _ iha ihb ihc ihd => exact .oper iha ihb ihc ihd
  | pair _ _ iha ihb => exact .pair iha ihb
  | app _ ih => exact .app ih
  | eval _ _ iha ihb => exact .eval iha ihb
  | comb _ _ _ iha ihb ihc => exact .comb iha ihb ihc

/-- Environments with the same lookups are related. -/
theorem of_lookup_eq {bs bs' : Env} (h : forall s, Env.lookup s bs = Env.lookup s bs') :
    Sim (Term.env bs) (Term.env bs') :=
  .env (fun s => by rw [h s]) (fun s u u' h1 h2 => by
    rw [h s] at h1
    rw [h1] at h2
    cases h2
    exact reflLookup bs' s u h1)

/-! ### What the relation keeps -/

theorem isValue {v v' : Term} (h : Sim v v') (hv : IsValue v) : IsValue v' := by
  induction h with
  | dat n => exact .dat n
  | prim p => exact .prim p
  | sym s => exact .sym s
  | ign => exact .ign
  | nil => exact .nil
  | env => exact .env _
  | oper => exact .oper _ _ _ _
  | pair _ _ iha ihb => cases hv with | pair ha hb => exact .pair (iha ha) (ihb hb)
  | app _ ih => cases hv with | app ht => exact .app (ih ht)
  | eval => cases hv
  | comb => cases hv

theorem selfEval {t t' : Term} (h : Sim t t') (hs : SelfEval t) : SelfEval t' := by
  cases hs <;> cases h <;> constructor

theorem isList {ts ts' : Term} (h : Sim ts ts') (hl : IsList ts) : IsList ts' := by
  induction hl generalizing ts' with
  | nil => cases h; exact .nil
  | cons a _ ih => cases h with | pair _ hb => exact .cons _ (ih hb)

theorem evalList {e e' ts ts' : Term} (he : Sim e e') (h : Sim ts ts') (hl : IsList ts) :
    Sim (VauE.evalList e ts) (VauE.evalList e' ts') := by
  induction hl generalizing ts' with
  | nil => cases h; exact .nil
  | cons a _ ih => cases h with | pair ha hb => exact .pair (.eval ha he) (ih hb)

theorem join {a a' b b' : Env} (ha : EnvSim a a') (hb : EnvSim b b') :
    EnvSim (Env.join a b) (Env.join a' b') := by
  refine And.intro (fun s => ?_) (fun s u u' h1 h2 => ?_)
  . rw [Env.lookup_join, Env.lookup_join]
    cases h1 : Env.lookup s a with
    | none =>
      have h1' := (ha.1 s).1 h1
      rw [h1']
      exact hb.1 s
    | some w =>
      cases h1' : Env.lookup s a' with
      | none => exact absurd ((ha.1 s).2 h1') (by rw [h1]; simp)
      | some w' => simp
  . rw [Env.lookup_join] at h1 h2
    cases ha1 : Env.lookup s a with
    | none =>
      have ha1' := (ha.1 s).1 ha1
      rw [ha1] at h1
      rw [ha1'] at h2
      exact hb.2 s u u' h1 h2
    | some w =>
      cases ha1' : Env.lookup s a' with
      | none => exact absurd ((ha.1 s).2 ha1') (by rw [ha1]; simp)
      | some w' =>
        rw [ha1] at h1
        rw [ha1'] at h2
        simp only [Option.some_or, Option.some.injEq] at h1 h2
        subst h1; subst h2
        exact ha.2 s _ _ ha1 ha1'

theorem syms_eq : forall {p p' : Term}, Sim p p' -> syms p' = syms p
  | .sym _, _, h => by cases h; rfl
  | .pair a b, _, h => by
    cases h with
    | pair ha hb => simp only [syms, syms_eq ha, syms_eq hb]
  | .dat _, _, h => by cases h; rfl
  | .prim _, _, h => by cases h; rfl
  | .ign, _, h => by cases h; rfl
  | .nil, _, h => by cases h; rfl
  | .env _, _, h => by cases h; rfl
  | .oper _ _ _ _, _, h => by cases h; rfl
  | .app _, _, h => by cases h; rfl
  | .eval _ _, _, h => by cases h; rfl
  | .comb _ _ _, _, h => by cases h; rfl

theorem ematch : forall {p p' t t' : Term} {m : Env}, VauE.ematch p t = some m -> Sim p p' ->
    Sim t t' -> exists m', VauE.ematch p' t' = some m' /\ EnvSim m m'
  | .ign, _, _, _, _, hm, hp, _ => by
    cases hp
    simp only [VauE.ematch] at hm; cases hm
    exact Exists.intro [] (And.intro rfl (And.intro (fun _ => Iff.rfl)
      (fun s u u' h1 _ => by simp [Env.lookup] at h1)))
  | .nil, _, t, _, _, hm, hp, ht => by
    cases hp
    cases t <;> simp [VauE.ematch] at hm
    cases hm; cases ht
    exact Exists.intro [] (And.intro rfl (And.intro (fun _ => Iff.rfl)
      (fun s u u' h1 _ => by simp [Env.lookup] at h1)))
  | .sym s, _, t, t', _, hm, hp, ht => by
    cases hp
    simp only [VauE.ematch] at hm; cases hm
    refine Exists.intro [(s, t')] (And.intro rfl (And.intro (fun x => ?_) (fun x u u' h1 h2 => ?_)))
    . simp only [Env.lookup]
      split <;> simp
    . simp only [Env.lookup] at h1 h2
      split at h1
      next =>
        rw [if_pos (by assumption)] at h2
        cases h1; cases h2; exact ht
      next => cases h1
  | .pair a b, _, t, _, _, hm, hp, ht => by
    cases hp with
    | pair ha hb =>
      cases t with
      | pair c d =>
        cases ht with
        | pair hc hd =>
          simp only [VauE.ematch] at hm
          split at hm
          next hdis =>
            split at hm
            next m1 m2 h1 h2 =>
              cases hm
              exact (ematch h1 ha hc).elim fun m1' h1' => (ematch h2 hb hd).elim fun m2' h2' =>
                Exists.intro (Env.join m1' m2') (And.intro
                  (by simp only [VauE.ematch, syms_eq ha, syms_eq hb, hdis, if_true, h1'.1, h2'.1])
                  (join h1'.2 h2'.2))
            next => cases hm
          next => cases hm
      | _ => simp [VauE.ematch] at hm
  | .dat _, _, _, _, _, hm, _, _ => by simp [VauE.ematch] at hm
  | .prim _, _, _, _, _, hm, _, _ => by simp [VauE.ematch] at hm
  | .env _, _, _, _, _, hm, _, _ => by simp [VauE.ematch] at hm
  | .oper _ _ _ _, _, _, _, _, hm, _, _ => by simp [VauE.ematch] at hm
  | .app _, _, _, _, _, hm, _, _ => by simp [VauE.ematch] at hm
  | .eval _ _, _, _, _, _, hm, _, _ => by simp [VauE.ematch] at hm
  | .comb _ _ _, _, _, _, _, hm, _, _ => by simp [VauE.ematch] at hm

theorem buildListStar : forall {x x' r : Term}, VauE.buildListStar x = some r -> Sim x x' ->
    exists r', VauE.buildListStar x' = some r' /\ Sim r r'
  | .pair a rest, .pair a' rest', _, hb, .pair ha hr => by
      cases rest with
      | nil =>
        cases hr
        simp only [VauE.buildListStar] at hb; cases hb
        exact Exists.intro _ (And.intro rfl ha)
      | pair c d =>
        cases hr with
        | pair hc hd =>
          simp only [VauE.buildListStar, Option.map_eq_some_iff] at hb
          exact hb.elim fun r0 hr0 =>
            (buildListStar hr0.1 (.pair hc hd)).elim fun r1 hr1 => by
              refine Exists.intro (.pair a' r1) (And.intro ?_ ?_)
              . simp only [VauE.buildListStar, hr1.1, Option.map_some]
              . rw [<- hr0.2]; exact .pair ha hr1.2
      | _ => simp [VauE.buildListStar] at hb
  | .dat _, _, _, hb, _ => by simp [VauE.buildListStar] at hb
  | .prim _, _, _, hb, _ => by simp [VauE.buildListStar] at hb
  | .sym _, _, _, hb, _ => by simp [VauE.buildListStar] at hb
  | .ign, _, _, hb, _ => by simp [VauE.buildListStar] at hb
  | .nil, _, _, hb, _ => by simp [VauE.buildListStar] at hb
  | .env _, _, _, hb, _ => by simp [VauE.buildListStar] at hb
  | .oper _ _ _ _, _, _, hb, _ => by simp [VauE.buildListStar] at hb
  | .app _, _, _, hb, _ => by simp [VauE.buildListStar] at hb
  | .eval _ _, _, _, hb, _ => by simp [VauE.buildListStar] at hb
  | .comb _ _ _, _, _, hb, _ => by simp [VauE.buildListStar] at hb

end Sim

/-! ## Reducing inside the visible binding of a symbol -/

/-- Replace the first binding of `s` (if any) by `s <- v`. -/
def Env.update (s : Nat) (v : Term) : Env -> Env
  | [] => []
  | (s', t) :: r => if s = s' then (s', v) :: r else (s', t) :: Env.update s v r

theorem lookup_update_same {s : Nat} {v u : Term} : forall {bs : Env},
    Env.lookup s bs = some u -> Env.lookup s (Env.update s v bs) = some v
  | [], h => by simp [Env.lookup] at h
  | (s', t) :: r, h => by
    simp only [Env.update]
    by_cases hs : s = s'
    . rw [if_pos hs, lookup_cons, if_pos hs]
    . rw [if_neg hs, lookup_cons, if_neg hs]
      rw [lookup_cons, if_neg hs] at h
      exact lookup_update_same h

theorem lookup_update_other {s x : Nat} {v : Term} (hx : Not (x = s)) : forall {bs : Env},
    Env.lookup x (Env.update s v bs) = Env.lookup x bs
  | [] => rfl
  | (s', t) :: r => by
    simp only [Env.update]
    by_cases hs : s = s'
    . rw [if_pos hs, lookup_cons, lookup_cons]
      subst hs
      simp only [hx, if_false]
    . rw [if_neg hs, lookup_cons, lookup_cons, lookup_update_other hx]

theorem steps_update {s : Nat} {u v : Term} (hv : Steps u v) : forall {bs : Env},
    Env.lookup s bs = some u -> Steps (env bs) (env (Env.update s v bs))
  | [], h => by simp [Env.lookup] at h
  | (s', t) :: r, h => by
    simp only [Env.update]
    by_cases hs : s = s'
    . rw [if_pos hs]
      rw [lookup_cons, if_pos hs] at h
      cases h
      exact Steps.envCons hv (Steps.refl _)
    . rw [if_neg hs]
      rw [lookup_cons, if_neg hs] at h
      exact Steps.envCons (Steps.refl t) (steps_update hv h)

/-! ## The simulation -/

theorem sim_top {t u t' : Term} (h : Top t u) (hs : Sim t t') :
    exists u', Steps t' u' /\ Sim u u' := by
  cases h with
  | evalSelf e hse =>
    cases hs with
    | eval ha he =>
      cases he with
      | env hn hsm =>
        exact Exists.intro _ (And.intro (Steps.top (.evalSelf _ (ha.selfEval hse))) ha)
  | @evalSym x e t0 hl =>
    cases hs with
    | eval ha he =>
      cases ha
      cases he with
      | @env _ bs' hn hsm =>
        cases hb : Env.lookup x bs' with
        | none => exact absurd ((hn x).2 hb) (by rw [hl]; simp)
        | some w => exact Exists.intro w (And.intro (Steps.top (.evalSym hb)) (hsm x _ _ hl hb))
  | evalPair a b e =>
    cases hs with
    | eval ha he =>
      cases ha with
      | pair h1 h2 =>
        cases he with
        | env hn hsm =>
          exact Exists.intro _ (And.intro (Steps.top (.evalPair _ _ _))
            (.comb (.eval h1 (.env hn hsm)) h2 (.env hn hsm)))
  | evalApp t0 e =>
    cases hs with
    | eval ha he =>
      cases ha with
      | app h1 =>
        cases he with
        | env hn hsm =>
          exact Exists.intro _ (And.intro (Steps.top (.evalApp _ _)) (.app (.eval h1 (.env hn hsm))))
  | beta hv1 hv2 hv3 hm =>
    cases hs with
    | comb hf hx he =>
      cases hf with
      | oper h1 h2 h3 h4 =>
        cases h4 with
        | env hn1 hsm1 =>
          cases he with
          | env hn2 hsm2 =>
            exact (Sim.ematch hm (.pair h1 h2) (.pair hx (.env hn2 hsm2))).elim fun m' hm' =>
              Exists.intro _ (And.intro
                (Steps.top (.beta (h1.isValue hv1) (h2.isValue hv2) (hx.isValue hv3) hm'.1))
                (.eval h3 (Sim.ofEnvSim (Sim.join hm'.2 (And.intro hn1 hsm1)))))
  | combApp t0 e hl =>
    cases hs with
    | comb hf hx he =>
      cases hf with
      | app h1 =>
        cases he with
        | env hn hsm =>
          exact Exists.intro _ (And.intro (Steps.top (.combApp _ _ (hx.isList hl)))
            (.comb h1 (Sim.evalList (.env hn hsm) hx hl) (.env hn hsm)))
  | deltaVau e hv1 hv2 hv3 =>
    cases hs with
    | comb hf hx he =>
      cases hf
      cases hx with
      | pair h1 hr1 => cases hr1 with
        | pair h2 hr2 => cases hr2 with
          | pair h3 hr3 =>
            cases hr3
            cases he with
            | env hn hsm =>
              exact Exists.intro _ (And.intro
                (Steps.top (.deltaVau _ (h1.isValue hv1) (h2.isValue hv2) (h3.isValue hv3)))
                (.oper h1 h2 h3 (.env hn hsm)))
  | deltaWrap e hv =>
    cases hs with
    | comb hf hx he =>
      cases hf
      cases hx with
      | pair h1 hr1 =>
        cases hr1
        cases he
        exact Exists.intro _ (And.intro (Steps.top (.deltaWrap _ (h1.isValue hv))) (.app h1))
  | deltaUnwrap e hv =>
    cases hs with
    | comb hf hx he =>
      cases hf
      cases hx with
      | pair h1 hr1 =>
        cases hr1
        cases h1 with
        | app h2 =>
          cases he
          exact Exists.intro _ (And.intro (Steps.top (.deltaUnwrap _ (h2.isValue hv))) h2)
  | deltaEval e1 e hv =>
    cases hs with
    | comb hf hx he =>
      cases hf
      cases hx with
      | pair h1 hr1 => cases hr1 with
        | pair h2 hr2 =>
          cases hr2
          cases h2 with
          | env hn hsm =>
            cases he
            exact Exists.intro _ (And.intro (Steps.top (.deltaEval _ _ (h1.isValue hv)))
              (.eval h1 (.env hn hsm)))
  | deltaListStar e hv hr =>
    cases hs with
    | comb hf hx he =>
      cases hf
      cases he
      exact (Sim.buildListStar hr hx).elim fun r' hr' =>
        Exists.intro r' (And.intro (Steps.top (.deltaListStar _ (hx.isValue hv) hr'.1)) hr'.2)

/-- A step inside one binding of a related environment. -/
theorem env_sim_step {pre post : Env} {s : Nat} {a a1 t' : Term}
    (ha : forall a', Sim a a' -> exists a1', Steps a' a1' /\ Sim a1 a1')
    (hs : Sim (env (pre ++ (s, a) :: post)) t') :
    exists u', Steps t' u' /\ Sim (env (pre ++ (s, a1) :: post)) u' := by
  cases hs with
  | @env _ bs' hn hsm =>
    by_cases hv : Env.lookup s pre = none
    . have hla : Env.lookup s (pre ++ (s, a) :: post) = some a := by
        rw [lookup_append, hv, lookup_cons, if_pos rfl]; rfl
      cases hb : Env.lookup s bs' with
      | none => exact absurd ((hn s).2 hb) (by rw [hla]; simp)
      | some a' =>
        exact (ha a' (hsm s _ _ hla hb)).elim fun a1' h1 => by
          refine Exists.intro (env (Env.update s a1' bs')) (And.intro (steps_update h1.1 hb) ?_)
          refine Sim.env (fun x => ?_) (fun x u u' hu hu' => ?_)
          . by_cases hx : x = s
            . subst hx
              rw [lookup_append, hv, lookup_cons, if_pos rfl, lookup_update_same hb]
              simp
            . rw [lookup_replace (Or.inl hx) (z := a), lookup_update_other hx]
              exact hn x
          . by_cases hx : x = s
            . subst hx
              rw [lookup_append, hv, lookup_cons, if_pos rfl] at hu
              rw [lookup_update_same hb] at hu'
              simp only [Option.none_or, Option.some.injEq] at hu hu'
              subst hu; subst hu'
              exact h1.2
            . rw [lookup_replace (Or.inl hx) (z := a)] at hu
              rw [lookup_update_other hx] at hu'
              exact hsm x u u' hu hu'
    . refine Exists.intro (env bs') (And.intro (Steps.refl _) ?_)
      refine Sim.env (fun x => ?_) (fun x u u' hu hu' => ?_)
      . rw [lookup_replace (Or.inr hv) (z := a)]; exact hn x
      . rw [lookup_replace (Or.inr hv) (z := a)] at hu; exact hsm x u u' hu hu'

/-- **The simulation.** A step of `t` is matched by zero or more steps of any related `t'`. The
second part describes a step inside an environment: one binding changes. -/
theorem sim_step {t u : Term} (h : Step t u) :
    (forall t', Sim t t' -> exists u', Steps t' u' /\ Sim u u') /\
    (forall l l1, t = env l -> u = env l1 ->
      exists (pre post : Env) (s : Nat) (a a1 : Term),
        l = pre ++ (s, a) :: post /\ l1 = pre ++ (s, a1) :: post /\
        (forall a', Sim a a' -> exists a1', Steps a' a1' /\ Sim a1 a1')) := by
  induction h with
  | top h =>
    refine And.intro (fun t' ht => sim_top h ht) (fun l l1 e1 _ => ?_)
    subst e1
    cases h
  | @envHere s t0 t1 r _ ih =>
    refine And.intro (fun t' ht => env_sim_step (pre := []) ih.1 ht) (fun l l1 e1 e2 => ?_)
    cases e1; cases e2
    exact Exists.intro [] (Exists.intro r (Exists.intro s (Exists.intro t0 (Exists.intro t1
      (And.intro rfl (And.intro rfl ih.1))))))
  | @envThere b r r1 _ ih =>
    exact (ih.2 r r1 rfl rfl).elim fun pre hpre => hpre.elim fun post hpost =>
      hpost.elim fun s hs => hs.elim fun a ha => ha.elim fun a1 ha1 => by
        have hr := ha1.1
        have hr1 := ha1.2.1
        subst hr; subst hr1
        refine And.intro (fun t' ht => env_sim_step (pre := b :: pre) ha1.2.2 ht)
          (fun l l1 e1 e2 => ?_)
        cases e1; cases e2
        exact Exists.intro (b :: pre) (Exists.intro post (Exists.intro s (Exists.intro a
          (Exists.intro a1 (And.intro rfl (And.intro rfl ha1.2.2))))))
  | oper1 b c d _ ih =>
    refine And.intro (fun t' ht => ?_) (fun l l1 e1 _ => by cases e1)
    cases ht with
    | oper ha hb hc hd =>
      exact (ih.1 _ ha).elim fun a1 h1 => Exists.intro _
        (And.intro (Steps.oper h1.1 (Steps.refl _) (Steps.refl _) (Steps.refl _)) (.oper h1.2 hb hc hd))
  | oper2 a c d _ ih =>
    refine And.intro (fun t' ht => ?_) (fun l l1 e1 _ => by cases e1)
    cases ht with
    | oper ha hb hc hd =>
      exact (ih.1 _ hb).elim fun b1 h1 => Exists.intro _
        (And.intro (Steps.oper (Steps.refl _) h1.1 (Steps.refl _) (Steps.refl _)) (.oper ha h1.2 hc hd))
  | oper3 a b d _ ih =>
    refine And.intro (fun t' ht => ?_) (fun l l1 e1 _ => by cases e1)
    cases ht with
    | oper ha hb hc hd =>
      exact (ih.1 _ hc).elim fun c1 h1 => Exists.intro _
        (And.intro (Steps.oper (Steps.refl _) (Steps.refl _) h1.1 (Steps.refl _)) (.oper ha hb h1.2 hd))
  | oper4 a b c _ ih =>
    refine And.intro (fun t' ht => ?_) (fun l l1 e1 _ => by cases e1)
    cases ht with
    | oper ha hb hc hd =>
      exact (ih.1 _ hd).elim fun d1 h1 => Exists.intro _
        (And.intro (Steps.oper (Steps.refl _) (Steps.refl _) (Steps.refl _) h1.1) (.oper ha hb hc h1.2))
  | pairL b _ ih =>
    refine And.intro (fun t' ht => ?_) (fun l l1 e1 _ => by cases e1)
    cases ht with
    | pair ha hb =>
      exact (ih.1 _ ha).elim fun a1 h1 => Exists.intro _
        (And.intro (Steps.pair h1.1 (Steps.refl _)) (.pair h1.2 hb))
  | pairR a _ ih =>
    refine And.intro (fun t' ht => ?_) (fun l l1 e1 _ => by cases e1)
    cases ht with
    | pair ha hb =>
      exact (ih.1 _ hb).elim fun b1 h1 => Exists.intro _
        (And.intro (Steps.pair (Steps.refl _) h1.1) (.pair ha h1.2))
  | app _ ih =>
    refine And.intro (fun t' ht => ?_) (fun l l1 e1 _ => by cases e1)
    cases ht with
    | app ha =>
      exact (ih.1 _ ha).elim fun a1 h1 => Exists.intro _ (And.intro (Steps.app h1.1) (.app h1.2))
  | evalL b _ ih =>
    refine And.intro (fun t' ht => ?_) (fun l l1 e1 _ => by cases e1)
    cases ht with
    | eval ha hb =>
      exact (ih.1 _ ha).elim fun a1 h1 => Exists.intro _
        (And.intro (Steps.eval h1.1 (Steps.refl _)) (.eval h1.2 hb))
  | evalR a _ ih =>
    refine And.intro (fun t' ht => ?_) (fun l l1 e1 _ => by cases e1)
    cases ht with
    | eval ha hb =>
      exact (ih.1 _ hb).elim fun b1 h1 => Exists.intro _
        (And.intro (Steps.eval (Steps.refl _) h1.1) (.eval ha h1.2))
  | comb1 b c _ ih =>
    refine And.intro (fun t' ht => ?_) (fun l l1 e1 _ => by cases e1)
    cases ht with
    | comb ha hb hc =>
      exact (ih.1 _ ha).elim fun a1 h1 => Exists.intro _
        (And.intro (Steps.comb3 h1.1 (Steps.refl _) (Steps.refl _)) (.comb h1.2 hb hc))
  | comb2 a c _ ih =>
    refine And.intro (fun t' ht => ?_) (fun l l1 e1 _ => by cases e1)
    cases ht with
    | comb ha hb hc =>
      exact (ih.1 _ hb).elim fun b1 h1 => Exists.intro _
        (And.intro (Steps.comb3 (Steps.refl _) h1.1 (Steps.refl _)) (.comb ha h1.2 hc))
  | comb3 a b _ ih =>
    refine And.intro (fun t' ht => ?_) (fun l l1 e1 _ => by cases e1)
    cases ht with
    | comb ha hb hc =>
      exact (ih.1 _ hc).elim fun c1 h1 => Exists.intro _
        (And.intro (Steps.comb3 (Steps.refl _) (Steps.refl _) h1.1) (.comb ha hb h1.2))

/-- Every reduction of `t` is matched by a reduction of any related `t'`. -/
theorem Sim.steps {t t' u : Term} (hs : Sim t t') (h : Steps t u) :
    exists u', Steps t' u' /\ Sim u u' := by
  induction h with
  | refl => exact Exists.intro t' (And.intro (Steps.refl _) hs)
  | tail _ hstep ih =>
    exact ih.elim fun v' hv => ((sim_step hstep).1 v' hv.2).elim fun w' hw =>
      Exists.intro w' (And.intro (hv.1.trans hw.1) hw.2)

/-! ## Contexts -/

/-- One-hole contexts for vau-e. The hole may be anywhere, including inside one binding of an
environment (`envAt pre s c post` is the environment `pre ++ (s <- c) :: post`). -/
inductive Ctx where
  | hole : Ctx
  | envAt : Env -> Nat -> Ctx -> Env -> Ctx
  | oper1 : Ctx -> Term -> Term -> Term -> Ctx
  | oper2 : Term -> Ctx -> Term -> Term -> Ctx
  | oper3 : Term -> Term -> Ctx -> Term -> Ctx
  | oper4 : Term -> Term -> Term -> Ctx -> Ctx
  | pairL : Ctx -> Term -> Ctx
  | pairR : Term -> Ctx -> Ctx
  | app : Ctx -> Ctx
  | evalL : Ctx -> Term -> Ctx
  | evalR : Term -> Ctx -> Ctx
  | comb1 : Ctx -> Term -> Term -> Ctx
  | comb2 : Term -> Ctx -> Term -> Ctx
  | comb3 : Term -> Term -> Ctx -> Ctx

/-- Put a term into the hole. Plugging does not rename anything. -/
def Ctx.plug : Ctx -> Term -> Term
  | .hole, t => t
  | .envAt pre s c post, t => Term.env (pre ++ (s, c.plug t) :: post)
  | .oper1 c b c' d, t => Term.oper (c.plug t) b c' d
  | .oper2 a c c' d, t => Term.oper a (c.plug t) c' d
  | .oper3 a b c d, t => Term.oper a b (c.plug t) d
  | .oper4 a b c' c, t => Term.oper a b c' (c.plug t)
  | .pairL c b, t => Term.pair (c.plug t) b
  | .pairR a c, t => Term.pair a (c.plug t)
  | .app c, t => Term.app (c.plug t)
  | .evalL c b, t => Term.eval (c.plug t) b
  | .evalR a c, t => Term.eval a (c.plug t)
  | .comb1 c b c', t => Term.comb (c.plug t) b c'
  | .comb2 a c c', t => Term.comb a (c.plug t) c'
  | .comb3 a b c, t => Term.comb a b (c.plug t)

theorem Sim.envAt {pre post : Env} {s : Nat} {y y' : Term} (h : Sim y y') :
    Sim (Term.env (pre ++ (s, y) :: post)) (Term.env (pre ++ (s, y') :: post)) := by
  refine Sim.env (fun x => ?_) (fun x u u' hu hu' => ?_)
  . rw [lookup_append, lookup_append, lookup_cons, lookup_cons]
    cases Env.lookup x pre with
    | some w => simp
    | none => by_cases hx : x = s <;> simp [hx]
  . rw [lookup_append, lookup_cons] at hu hu'
    cases hp : Env.lookup x pre with
    | some w =>
      rw [hp] at hu hu'
      simp only [Option.some_or, Option.some.injEq] at hu hu'
      subst hu; subst hu'
      exact Sim.reflLookup pre x w hp
    | none =>
      rw [hp] at hu hu'
      by_cases hx : x = s
      . simp only [hx, if_true, Option.none_or, Option.some.injEq] at hu hu'
        subst hu; subst hu'
        exact h
      . simp only [hx, if_false, Option.none_or] at hu hu'
        rw [hu] at hu'
        cases hu'
        exact Sim.reflLookup post x u hu

theorem Sim.plug (c : Ctx) {t t' : Term} (h : Sim t t') : Sim (c.plug t) (c.plug t') := by
  induction c with
  | hole => exact h
  | envAt pre s c post ih => exact Sim.envAt ih
  | oper1 c b c' d ih => exact .oper ih (Sim.refl _) (Sim.refl _) (Sim.refl _)
  | oper2 a c c' d ih => exact .oper (Sim.refl _) ih (Sim.refl _) (Sim.refl _)
  | oper3 a b c d ih => exact .oper (Sim.refl _) (Sim.refl _) ih (Sim.refl _)
  | oper4 a b c' c ih => exact .oper (Sim.refl _) (Sim.refl _) (Sim.refl _) ih
  | pairL c b ih => exact .pair ih (Sim.refl _)
  | pairR a c ih => exact .pair (Sim.refl _) ih
  | app c ih => exact .app ih
  | evalL c b ih => exact .eval ih (Sim.refl _)
  | evalR a c ih => exact .eval (Sim.refl _) ih
  | comb1 c b c' ih => exact .comb ih (Sim.refl _) (Sim.refl _)
  | comb2 a c c' ih => exact .comb (Sim.refl _) ih (Sim.refl _)
  | comb3 a b c ih => exact .comb (Sim.refl _) (Sim.refl _) ih

/-! ## Environment opacity -/

theorem Sim.observe {t t' : Term} {n : Nat} (hs : Sim t t') (h : Steps t (Term.dat n)) :
    Steps t' (Term.dat n) :=
  (Sim.steps hs h).elim fun u' hu => by
    have hsim := hu.2
    cases hsim
    exact hu.1

/-- **Environment opacity.** Two environments that give the same answer to every lookup cannot be
told apart by any program: in every one-hole context, one reduces to primitive data `n` exactly
when the other does. -/
theorem env_opacity {bs bs' : Env} (h : forall s, Env.lookup s bs = Env.lookup s bs') (c : Ctx)
    (n : Nat) : Steps (c.plug (env bs)) (dat n) <-> Steps (c.plug (env bs')) (dat n) :=
  Iff.intro (Sim.observe (Sim.plug c (Sim.of_lookup_eq h)))
    (Sim.observe (Sim.plug c (Sim.of_lookup_eq (fun s => (h s).symm))))

/-- A binding hidden behind an earlier binding of the same symbol cannot be observed. -/
theorem shadow_invisible (s : Nat) (a b : Term) (r : Env) (c : Ctx) (n : Nat) :
    Steps (c.plug (env ((s, a) :: (s, b) :: r))) (dat n) <-> Steps (c.plug (env ((s, a) :: r))) (dat n) :=
  env_opacity (fun x => by by_cases hx : x = s <;> simp [lookup_cons, hx]) c n

/-- The order of bindings of different symbols cannot be observed. -/
theorem order_invisible {s1 s2 : Nat} (hne : Not (s1 = s2)) (a b : Term) (r : Env) (c : Ctx)
    (n : Nat) :
    Steps (c.plug (env ((s1, a) :: (s2, b) :: r))) (dat n) <->
      Steps (c.plug (env ((s2, b) :: (s1, a) :: r))) (dat n) := by
  refine env_opacity (fun x => ?_) c n
  by_cases h1 : x = s1
  . subst h1; simp [lookup_cons, hne]
  . by_cases h2 : x = s2
    . subst h2; simp [lookup_cons, h1]
    . simp [lookup_cons, h1, h2]

/-- A parameter tree cannot take an environment apart: matching an environment either ignores it
or binds it whole to one symbol. -/
theorem match_env_opaque {p : Term} {bs m : Env} (h : ematch p (env bs) = some m) :
    (p = ign /\ m = []) \/ (exists s, p = sym s /\ m = [(s, env bs)]) := by
  cases p with
  | ign => simp only [ematch] at h; cases h; exact Or.inl (And.intro rfl rfl)
  | sym s => simp only [ematch] at h; cases h; exact Or.inr (Exists.intro s (And.intro rfl rfl))
  | _ => simp [ematch] at h

theorem normal_dat (n : Nat) : Normal (Term.dat n) := by
  intro t' h
  cases h with
  | top h => cases h

/-- The other direction: lookups **can** be observed. The context `[eval x _]` tells
`{{x <- 5}}` from `{{x <- 6}}`, so opacity does not make all environments equal. -/
theorem lookup_observable :
    Steps ((Ctx.evalR (sym 1) .hole).plug (env [(1, dat 5)])) (dat 5) /\
    Not (Steps ((Ctx.evalR (sym 1) .hole).plug (env [(1, dat 6)])) (dat 5)) := by
  refine And.intro (Steps.top (.evalSym rfl)) (fun h => ?_)
  have h6 : Steps ((Ctx.evalR (sym 1) .hole).plug (env [(1, dat 6)])) (dat 6) :=
    Steps.top (.evalSym rfl)
  have := normal_unique h h6 (normal_dat 5) (normal_dat 6)
  cases this

/-! ## Hygiene: ignoring the dynamic environment -/

/-- **Hygiene of `#ignore`.** A compound operative whose environment parameter is `#ignore` reduces
to the same term when called from any dynamic environment: the caller's environment cannot affect
the call. -/
theorem ignore_hygiene {p v b : Term} {e1 e2 e3 m : Env} (hp : IsValue p) (hv : IsValue v)
    (hm : ematch p v = some m) :
    Steps (comb (oper p ign b (env e1)) v (env e2)) (eval b (env (Env.join m e1))) /\
    Steps (comb (oper p ign b (env e1)) v (env e3)) (eval b (env (Env.join m e1))) := by
  have key : forall e : Env, ematch (pair p ign) (pair v (env e)) = some (Env.join m []) := by
    intro e
    simp only [ematch, syms, disjoint_nil, hm, if_true]
  have h2 := Top.beta (body := b) (e1 := e1) hp .ign hv (key e2)
  have h3 := Top.beta (body := b) (e1 := e1) hp .ign hv (key e3)
  rw [Env.join_emp] at h2 h3
  exact And.intro (Steps.top h2) (Steps.top h3)

/-- The same, as an equation: the two calls are equal in the equational theory. -/
theorem ignore_hygiene_conv {p v b : Term} {e1 e2 e3 m : Env} (hp : IsValue p) (hv : IsValue v)
    (hm : ematch p v = some m) :
    Conv (comb (oper p ign b (env e1)) v (env e2)) (comb (oper p ign b (env e1)) v (env e3)) :=
  let h := ignore_hygiene (b := b) (e1 := e1) (e2 := e2) (e3 := e3) hp hv hm
  Vau.EqvGen.trans h.1.toEqvGen (Vau.EqvGen.symm h.2.toEqvGen)

end VauE
