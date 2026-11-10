import Vau.Env.Opacity

/-!
# Encapsulation types

Kernel's `make-encapsulation-type` (thesis section 7.2) returns three applicatives `(e p? d)` for a
new type: the encapsulator `e` makes an encapsulated object that holds a content; the type
predicate `p?` returns true iff all its arguments were made by `e`; the decapsulator `d` returns
the content of an object made by `e`. Only code that holds `d` can read the content.

Shutt's thesis gives no calculus rules for encapsulation types. This project adds them to the Lean
vau-e (see `Vau/Env/Syntax.lean` and `Vau/Env/Reduction.lean`):

* a term `capsule k v`: an encapsulated object of type `k` with content `v`; it is self-evaluating
  and opaque, like an environment;
* primitive operatives `$encap k`, `$isEncap k`, `$decap k`, with the delta-rules
  `[combine $encap_k (V) e] -> <capsule k V>`,
  `[combine $isEncap_k (V1 ... Vn) e] -> #t` or `#f`, and
  `[combine $decap_k (<capsule k V>) e] -> V`.

**Not modeled:** `make-encapsulation-type` itself, which makes a *fresh* type on each call. That
needs state, which pure vau-e does not have. Here types are numbered, as if each type `k` had been
made once, and the theorems assume that the program holds the three applicatives of `k` (or not).
`#t` and `#f` are represented by the data `1` and `0`.

Results:

* `decap_encap`: `(d (e x))` evaluates to the value of `x`;
* `isEncap_same`, `isEncap_other`: the type predicate answers `#t` for an object of its own type and
  `#f` for an object of another type;
* `decap_other_stuck`: a decapsulator has no rule for an object of another type;
* `capsule_opacity`: a program with no `$decap k` (outside capsules of type `k`) cannot observe the
  content of a capsule of type `k`: replacing the content changes no observation.

`VauE.confluence` and `VauE.env_opacity` cover these new rules too.
-/

namespace VauE
open Term

/-- The applicative `e` (encapsulator) of type `k`. -/
abbrev encapA (k : Nat) : Term := app (prim (.encap k))
/-- The applicative `p?` (type predicate) of type `k`. -/
abbrev isEncapA (k : Nat) : Term := app (prim (.isEncap k))
/-- The applicative `d` (decapsulator) of type `k`. -/
abbrev decapA (k : Nat) : Term := app (prim (.decap k))

/-! ## The three applicatives -/

/-- **decapsulate after encapsulate.** If the symbols `se` and `sd` are bound to the encapsulator
and the decapsulator of type `k`, and `c` evaluates to a value `v`, then `(sd (se c))` evaluates
to `v`. -/
theorem decap_encap {k se sd : Nat} {c v : Term} {e : Env}
    (he : Env.lookup se e = some (encapA k)) (hd : Env.lookup sd e = some (decapA k))
    (hc : Steps (eval c (env e)) v) (hv : IsValue v) :
    Steps (eval (list2 (sym sd) (list2 (sym se) c)) (env e)) v := by
  refine Steps.head (.evalPair _ _ _) ?_
  refine Steps.trans (Steps.combOp _ _ (.evalSym hd)) ?_
  refine Steps.head (.combApp _ _ (by repeat constructor)) ?_
  have hin : Steps (eval (list2 (sym se) c) (env e)) (capsule k v) := by
    refine Steps.head (.evalPair _ _ _) ?_
    refine Steps.trans (Steps.combOp _ _ (.evalSym he)) ?_
    refine Steps.head (.combApp _ _ (by repeat constructor)) ?_
    refine Steps.trans (Steps.comb _ (Steps.refl _) (Steps.pair hc (Steps.refl _))) ?_
    exact Steps.top (.deltaEncap k _ hv)
  refine Steps.trans (Steps.comb _ (Steps.refl _) (Steps.pair hin (Steps.refl _))) ?_
  exact Steps.top (.deltaDecap k _)

/-- The type predicate answers `#t` (`dat 1`) for an object of its own type. -/
theorem isEncap_same (k : Nat) (v : Term) (e : Env) :
    Steps (comb (prim (.isEncap k)) (list1 (capsule k v)) (env e)) (dat 1) := by
  have hk : isCapsuleOf k (capsule k v) = true := by
    simp only [isCapsuleOf]; exact decide_eq_true rfl
  have h := Top.deltaIsEncap (b := true) k e (.pair (.capsule k v) .nil)
    (by simp only [capsCheck, hk, Bool.and_self, Option.map_some])
  exact Steps.top h

/-- The type predicate answers `#f` (`dat 0`) for an object of another type. -/
theorem isEncap_other {k k' : Nat} (hk : Not (k' = k)) (v : Term) (e : Env) :
    Steps (comb (prim (.isEncap k)) (list1 (capsule k' v)) (env e)) (dat 0) := by
  have h := Top.deltaIsEncap (b := false) k e (.pair (.capsule k' v) .nil)
    (by simp [capsCheck, isCapsuleOf, hk])
  exact Steps.top h

/-- A decapsulator has no rule for an object of another type: the call is stuck at the top. -/
theorem decap_other_stuck {k k' : Nat} (hk : Not (k' = k)) (v u : Term) (e : Env) :
    Not (Top (comb (prim (.decap k)) (list1 (capsule k' v)) (env e)) u) := by
  intro h
  cases h with
  | deltaDecap => exact hk rfl

/-! ## Programs without the decapsulator -/

/-- `Clean k t`: `t` contains no `$decap k`, except inside the content of capsules of type `k`
(which no rule can reach without `$decap k`). -/
inductive Clean (k : Nat) : Term -> Prop where
  | dat (n : Nat) : Clean k (dat n)
  | prim {p : Prim} : Not (p = .decap k) -> Clean k (prim p)
  | sym (s : Nat) : Clean k (sym s)
  | ign : Clean k ign
  | nil : Clean k nil
  | envNil : Clean k (env [])
  | envCons (s : Nat) {t : Term} {r : Env} : Clean k t -> Clean k (env r) -> Clean k (env ((s, t) :: r))
  | oper {a b c d : Term} : Clean k a -> Clean k b -> Clean k c -> Clean k d -> Clean k (oper a b c d)
  | pair {a b : Term} : Clean k a -> Clean k b -> Clean k (pair a b)
  | app {t : Term} : Clean k t -> Clean k (app t)
  | eval {a b : Term} : Clean k a -> Clean k b -> Clean k (eval a b)
  | comb {a b c : Term} : Clean k a -> Clean k b -> Clean k c -> Clean k (comb a b c)
  | hidden (v : Term) : Clean k (capsule k v)
  | capsule (k' : Nat) {v : Term} : Clean k v -> Clean k (capsule k' v)

/-- Terms that are equal except for the content of capsules of type `k`. -/
inductive CSim (k : Nat) : Term -> Term -> Prop where
  | dat (n : Nat) : CSim k (dat n) (dat n)
  | prim (p : Prim) : CSim k (prim p) (prim p)
  | sym (s : Nat) : CSim k (sym s) (sym s)
  | ign : CSim k ign ign
  | nil : CSim k nil nil
  | envNil : CSim k (env []) (env [])
  | envCons (s : Nat) {t t' : Term} {r r' : Env} :
      CSim k t t' -> CSim k (env r) (env r') -> CSim k (env ((s, t) :: r)) (env ((s, t') :: r'))
  | oper {a a' b b' c c' d d' : Term} :
      CSim k a a' -> CSim k b b' -> CSim k c c' -> CSim k d d' -> CSim k (oper a b c d) (oper a' b' c' d')
  | pair {a a' b b' : Term} : CSim k a a' -> CSim k b b' -> CSim k (pair a b) (pair a' b')
  | app {t t' : Term} : CSim k t t' -> CSim k (app t) (app t')
  | eval {a a' b b' : Term} : CSim k a a' -> CSim k b b' -> CSim k (eval a b) (eval a' b')
  | comb {a a' b b' c c' : Term} :
      CSim k a a' -> CSim k b b' -> CSim k c c' -> CSim k (comb a b c) (comb a' b' c')
  | capsule (k' : Nat) {v v' : Term} : CSim k v v' -> CSim k (capsule k' v) (capsule k' v')
  | hidden (v v' : Term) : CSim k (capsule k v) (capsule k v')

namespace CSim

mutual
theorem refl {k : Nat} : forall t : Term, CSim k t t
  | .dat n => .dat n
  | .prim p => .prim p
  | .sym s => .sym s
  | .ign => .ign
  | .nil => .nil
  | .env bs => reflEnv bs
  | .oper a b c d => .oper (refl a) (refl b) (refl c) (refl d)
  | .pair a b => .pair (refl a) (refl b)
  | .app t => .app (refl t)
  | .eval a b => .eval (refl a) (refl b)
  | .comb a b c => .comb (refl a) (refl b) (refl c)
  | .capsule k' v => .capsule k' (refl v)
theorem reflEnv {k : Nat} : forall bs : Env, CSim k (.env bs) (.env bs)
  | [] => .envNil
  | (s, t) :: r => .envCons s (refl t) (reflEnv r)
end

theorem symm {k : Nat} {t t' : Term} (h : CSim k t t') : CSim k t' t := by
  induction h with
  | dat n => exact .dat n
  | prim p => exact .prim p
  | sym s => exact .sym s
  | ign => exact .ign
  | nil => exact .nil
  | envNil => exact .envNil
  | envCons s _ _ iht ihr => exact .envCons s iht ihr
  | oper _ _ _ _ iha ihb ihc ihd => exact .oper iha ihb ihc ihd
  | pair _ _ iha ihb => exact .pair iha ihb
  | app _ ih => exact .app ih
  | eval _ _ iha ihb => exact .eval iha ihb
  | comb _ _ _ iha ihb ihc => exact .comb iha ihb ihc
  | capsule k' _ ih => exact .capsule k' ih
  | hidden v v' => exact .hidden v' v

theorem isValue {k : Nat} {v v' : Term} (h : CSim k v v') (hv : IsValue v) : IsValue v' := by
  induction h with
  | dat n => exact .dat n
  | prim p => exact .prim p
  | sym s => exact .sym s
  | ign => exact .ign
  | nil => exact .nil
  | envNil => exact .env _
  | envCons => exact .env _
  | oper => exact .oper _ _ _ _
  | pair _ _ iha ihb => cases hv with | pair ha hb => exact .pair (iha ha) (ihb hb)
  | app _ ih => cases hv with | app ht => exact .app (ih ht)
  | eval => cases hv
  | comb => cases hv
  | capsule => exact .capsule _ _
  | hidden => exact .capsule _ _

theorem selfEval {k : Nat} {t t' : Term} (h : CSim k t t') (hs : SelfEval t) : SelfEval t' := by
  cases hs <;> cases h <;> constructor

theorem isList {k : Nat} {ts ts' : Term} (h : CSim k ts ts') (hl : IsList ts) : IsList ts' := by
  induction hl generalizing ts' with
  | nil => cases h; exact .nil
  | cons a _ ih => cases h with | pair _ hb => exact .cons _ (ih hb)

theorem evalList {k : Nat} {e e' ts ts' : Term} (he : CSim k e e') (h : CSim k ts ts')
    (hl : IsList ts) : CSim k (VauE.evalList e ts) (VauE.evalList e' ts') := by
  induction hl generalizing ts' with
  | nil => cases h; exact .nil
  | cons a _ ih => cases h with | pair ha hb => exact .pair (.eval ha he) (ih hb)

theorem join {k : Nat} {a a' b b' : Env} (ha : CSim k (.env a) (.env a'))
    (hb : CSim k (.env b) (.env b')) : CSim k (.env (Env.join a b)) (.env (Env.join a' b')) := by
  induction a generalizing a' with
  | nil => cases ha; exact hb
  | cons x r ih =>
    cases ha with
    | envCons s ht hr => exact .envCons s ht (ih hr)

theorem lookup {k : Nat} {bs bs' : Env} (h : CSim k (.env bs) (.env bs')) (s : Nat) :
    (Env.lookup s bs = none -> Env.lookup s bs' = none) /\
    (forall u, Env.lookup s bs = some u -> exists u', Env.lookup s bs' = some u' /\ CSim k u u') := by
  induction bs generalizing bs' with
  | nil =>
    cases h
    exact And.intro (fun _ => rfl) (fun u hu => by simp [Env.lookup] at hu)
  | cons x r ih =>
    cases h with
    | envCons s' ht hr =>
      simp only [Env.lookup]
      by_cases hs : s = s'
      . simp only [hs, if_true]
        exact And.intro (fun h => by cases h)
          (fun u hu => by cases hu; exact Exists.intro _ (And.intro rfl ht))
      . simp only [hs, if_false]
        exact ih hr

theorem syms_eq {k : Nat} : forall {p p' : Term}, CSim k p p' -> syms p' = syms p
  | .sym _, _, h => by cases h; rfl
  | .pair a b, _, h => by
    cases h with
    | pair ha hb => simp only [syms, syms_eq ha, syms_eq hb]
  | .dat _, _, h => by cases h; rfl
  | .prim _, _, h => by cases h; rfl
  | .ign, _, h => by cases h; rfl
  | .nil, _, h => by cases h; rfl
  | .env _, _, h => by cases h <;> rfl
  | .oper _ _ _ _, _, h => by cases h; rfl
  | .app _, _, h => by cases h; rfl
  | .eval _ _, _, h => by cases h; rfl
  | .comb _ _ _, _, h => by cases h; rfl
  | .capsule _ _, _, h => by cases h <;> rfl

theorem ematch {k : Nat} : forall {p p' t t' : Term} {m : Env}, VauE.ematch p t = some m ->
    CSim k p p' -> CSim k t t' -> exists m', VauE.ematch p' t' = some m' /\ CSim k (.env m) (.env m')
  | .ign, _, _, _, _, hm, hp, _ => by
    cases hp
    simp only [VauE.ematch] at hm; cases hm
    exact Exists.intro [] (And.intro rfl .envNil)
  | .nil, _, t, _, _, hm, hp, ht => by
    cases hp
    cases t <;> simp [VauE.ematch] at hm
    cases hm; cases ht
    exact Exists.intro [] (And.intro rfl .envNil)
  | .sym s, _, _, t', _, hm, hp, ht => by
    cases hp
    simp only [VauE.ematch] at hm; cases hm
    exact Exists.intro [(s, t')] (And.intro rfl (.envCons s ht .envNil))
  | .pair a b, _, t, _, _, hm, hp, ht => by
    cases hp with
    | pair ha hb =>
      cases t with
      | pair c d =>
        cases ht with
        | pair hc hd =>
          have hsa : syms _ = syms a := syms_eq ha
          have hsb : syms _ = syms b := syms_eq hb
          simp only [VauE.ematch] at hm
          split at hm
          next hdis =>
            split at hm
            next m1 m2 h1 h2 =>
              cases hm
              exact (ematch h1 ha hc).elim fun m1' h1' => (ematch h2 hb hd).elim fun m2' h2' =>
                Exists.intro (Env.join m1' m2') (And.intro
                  (by simp only [VauE.ematch, hsa, hsb, hdis, if_true, h1'.1, h2'.1])
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
  | .capsule _ _, _, _, _, _, hm, _, _ => by simp [VauE.ematch] at hm

theorem buildListStar {k : Nat} : forall {x x' r : Term}, VauE.buildListStar x = some r ->
    CSim k x x' -> exists r', VauE.buildListStar x' = some r' /\ CSim k r r'
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
  | .capsule _ _, _, _, hb, _ => by simp [VauE.buildListStar] at hb

theorem isCapsuleOf_eq {k j : Nat} {x x' : Term} (h : CSim k x x') :
    isCapsuleOf j x' = isCapsuleOf j x := by
  cases h <;> rfl

theorem capsCheck {k j : Nat} : forall {vs vs' : Term} {b : Bool}, VauE.capsCheck j vs = some b ->
    CSim k vs vs' -> VauE.capsCheck j vs' = some b
  | .nil, _, _, hc, h => by cases h; exact hc
  | .pair x rest, _, _, hc, h => by
    cases h with
    | pair h1 h2 =>
      simp only [VauE.capsCheck, Option.map_eq_some_iff] at hc
      exact hc.elim fun b0 hb0 => by
        simp only [VauE.capsCheck, capsCheck hb0.1 h2, Option.map_some, isCapsuleOf_eq h1]
        exact congrArg some hb0.2
  | .dat _, _, _, hc, _ => by simp [VauE.capsCheck] at hc
  | .prim _, _, _, hc, _ => by simp [VauE.capsCheck] at hc
  | .sym _, _, _, hc, _ => by simp [VauE.capsCheck] at hc
  | .ign, _, _, hc, _ => by simp [VauE.capsCheck] at hc
  | .env _, _, _, hc, _ => by simp [VauE.capsCheck] at hc
  | .oper _ _ _ _, _, _, hc, _ => by simp [VauE.capsCheck] at hc
  | .app _, _, _, hc, _ => by simp [VauE.capsCheck] at hc
  | .eval _ _, _, _, hc, _ => by simp [VauE.capsCheck] at hc
  | .comb _ _ _, _, _, hc, _ => by simp [VauE.capsCheck] at hc
  | .capsule _ _, _, _, hc, _ => by simp [VauE.capsCheck] at hc

end CSim

/-! ## Cleanliness is kept by reduction -/

namespace Clean

theorem lookup {k : Nat} {bs : Env} (h : Clean k (.env bs)) {s : Nat} {u : Term}
    (hl : Env.lookup s bs = some u) : Clean k u := by
  induction bs with
  | nil => simp [Env.lookup] at hl
  | cons x r ih =>
    cases h with
    | envCons s' ht hr =>
      simp only [Env.lookup] at hl
      split at hl
      next => cases hl; exact ht
      next => exact ih hr hl

theorem join {k : Nat} {a b : Env} (ha : Clean k (.env a)) (hb : Clean k (.env b)) :
    Clean k (.env (Env.join a b)) := by
  induction a with
  | nil => exact hb
  | cons x r ih =>
    cases ha with
    | envCons s ht hr => exact .envCons s ht (ih hr)

theorem ematch {k : Nat} : forall {p t : Term} {m : Env}, VauE.ematch p t = some m -> Clean k t ->
    Clean k (.env m)
  | .ign, _, _, hm, _ => by simp only [VauE.ematch] at hm; cases hm; exact .envNil
  | .nil, t, _, hm, _ => by cases t <;> simp [VauE.ematch] at hm; cases hm; exact .envNil
  | .sym s, _, _, hm, ht => by simp only [VauE.ematch] at hm; cases hm; exact .envCons s ht .envNil
  | .pair a b, t, _, hm, ht => by
    cases t with
    | pair c d =>
      cases ht with
      | pair hc hd =>
        simp only [VauE.ematch] at hm
        split at hm
        next =>
          split at hm
          next m1 m2 h1 h2 => cases hm; exact join (ematch h1 hc) (ematch h2 hd)
          next => cases hm
        next => cases hm
    | _ => simp [VauE.ematch] at hm
  | .dat _, _, _, hm, _ => by simp [VauE.ematch] at hm
  | .prim _, _, _, hm, _ => by simp [VauE.ematch] at hm
  | .env _, _, _, hm, _ => by simp [VauE.ematch] at hm
  | .oper _ _ _ _, _, _, hm, _ => by simp [VauE.ematch] at hm
  | .app _, _, _, hm, _ => by simp [VauE.ematch] at hm
  | .eval _ _, _, _, hm, _ => by simp [VauE.ematch] at hm
  | .comb _ _ _, _, _, hm, _ => by simp [VauE.ematch] at hm
  | .capsule _ _, _, _, hm, _ => by simp [VauE.ematch] at hm

theorem evalList {k : Nat} {e ts : Term} (he : Clean k e) (h : Clean k ts) (hl : IsList ts) :
    Clean k (VauE.evalList e ts) := by
  induction hl with
  | nil => exact h
  | cons a _ ih => cases h with | pair ha hb => exact .pair (.eval ha he) (ih hb)

theorem buildListStar {k : Nat} : forall {x r : Term}, VauE.buildListStar x = some r ->
    Clean k x -> Clean k r
  | .pair a rest, _, hb, h => by
    cases h with
    | pair ha hr =>
      cases rest with
      | nil => simp only [VauE.buildListStar] at hb; cases hb; exact ha
      | pair c d =>
        simp only [VauE.buildListStar, Option.map_eq_some_iff] at hb
        exact hb.elim fun r0 hr0 => by
          rw [<- hr0.2]; exact .pair ha (buildListStar hr0.1 hr)
      | _ => simp [VauE.buildListStar] at hb
  | .dat _, _, hb, _ => by simp [VauE.buildListStar] at hb
  | .prim _, _, hb, _ => by simp [VauE.buildListStar] at hb
  | .sym _, _, hb, _ => by simp [VauE.buildListStar] at hb
  | .ign, _, hb, _ => by simp [VauE.buildListStar] at hb
  | .nil, _, hb, _ => by simp [VauE.buildListStar] at hb
  | .env _, _, hb, _ => by simp [VauE.buildListStar] at hb
  | .oper _ _ _ _, _, hb, _ => by simp [VauE.buildListStar] at hb
  | .app _, _, hb, _ => by simp [VauE.buildListStar] at hb
  | .eval _ _, _, hb, _ => by simp [VauE.buildListStar] at hb
  | .comb _ _ _, _, hb, _ => by simp [VauE.buildListStar] at hb
  | .capsule _ _, _, hb, _ => by simp [VauE.buildListStar] at hb

theorem top {k : Nat} {t u : Term} (hc : Clean k t) (h : Top t u) : Clean k u := by
  cases h with
  | evalSelf e hs => cases hc with | eval ha _ => exact ha
  | evalSym hl => cases hc with | eval _ he => exact lookup he hl
  | evalPair a b e =>
    cases hc with
    | eval ha he => cases ha with | pair h1 h2 => exact .comb (.eval h1 he) h2 he
  | evalApp t0 e =>
    cases hc with
    | eval ha he => cases ha with | app h1 => exact .app (.eval h1 he)
  | beta hv1 hv2 hv3 hm =>
    cases hc with
    | comb hf hx he =>
      cases hf with
      | oper _ _ hb hs => exact .eval hb (join (ematch hm (.pair hx he)) hs)
  | combApp t0 e hl =>
    cases hc with
    | comb hf hx he => cases hf with | app h1 => exact .comb h1 (evalList he hx hl) he
  | deltaVau e hv1 hv2 hv3 =>
    cases hc with
    | comb _ hx he =>
      cases hx with
      | pair h1 hr1 => cases hr1 with
        | pair h2 hr2 => cases hr2 with
          | pair h3 _ => exact .oper h1 h2 h3 he
  | deltaWrap e hv =>
    cases hc with
    | comb _ hx _ => cases hx with | pair h1 _ => exact .app h1
  | deltaUnwrap e hv =>
    cases hc with
    | comb _ hx _ => cases hx with | pair h1 _ => cases h1 with | app h2 => exact h2
  | deltaEval e1 e hv =>
    cases hc with
    | comb _ hx _ =>
      cases hx with
      | pair h1 hr1 => cases hr1 with | pair h2 _ => exact .eval h1 h2
  | deltaListStar e hv hr => cases hc with | comb _ hx _ => exact buildListStar hr hx
  | deltaEncap k' e hv =>
    cases hc with
    | comb _ hx _ => cases hx with | pair h1 _ => exact .capsule k' h1
  | deltaIsEncap k' e hv hcs => exact .dat _
  | deltaDecap k' e =>
    cases hc with
    | comb hf hx _ =>
      cases hf with
      | prim hne =>
        cases hx with
        | pair h1 _ =>
          cases h1 with
          | hidden => exact absurd rfl hne
          | capsule _ h2 => exact h2

theorem step {k : Nat} {t u : Term} (h : Step t u) (hc : Clean k t) : Clean k u := by
  induction h with
  | top h => exact top hc h
  | envHere s r _ ih => cases hc with | envCons _ ht hr => exact .envCons s (ih ht) hr
  | envThere b _ ih => cases hc with | envCons s ht hr => exact .envCons s ht (ih hr)
  | oper1 b c d _ ih => cases hc with | oper ha hb hc' hd => exact .oper (ih ha) hb hc' hd
  | oper2 a c d _ ih => cases hc with | oper ha hb hc' hd => exact .oper ha (ih hb) hc' hd
  | oper3 a b d _ ih => cases hc with | oper ha hb hc' hd => exact .oper ha hb (ih hc') hd
  | oper4 a b c _ ih => cases hc with | oper ha hb hc' hd => exact .oper ha hb hc' (ih hd)
  | pairL b _ ih => cases hc with | pair ha hb => exact .pair (ih ha) hb
  | pairR a _ ih => cases hc with | pair ha hb => exact .pair ha (ih hb)
  | app _ ih => cases hc with | app ha => exact .app (ih ha)
  | evalL b _ ih => cases hc with | eval ha hb => exact .eval (ih ha) hb
  | evalR a _ ih => cases hc with | eval ha hb => exact .eval ha (ih hb)
  | comb1 b c _ ih => cases hc with | comb ha hb hc' => exact .comb (ih ha) hb hc'
  | comb2 a c _ ih => cases hc with | comb ha hb hc' => exact .comb ha (ih hb) hc'
  | comb3 a b _ ih => cases hc with | comb ha hb hc' => exact .comb ha hb (ih hc')
  | capsule k' _ ih =>
    cases hc with
    | hidden => exact .hidden _
    | capsule _ hv => exact .capsule k' (ih hv)

theorem steps {k : Nat} {t u : Term} (h : Steps t u) (hc : Clean k t) : Clean k u := by
  induction h with
  | refl => exact hc
  | tail _ hs ih => exact step hs ih

theorem csim {k : Nat} {t t' : Term} (hc : Clean k t) (h : CSim k t t') : Clean k t' := by
  induction h with
  | dat n => exact .dat n
  | prim p => exact hc
  | sym s => exact .sym s
  | ign => exact .ign
  | nil => exact .nil
  | envNil => exact .envNil
  | envCons s _ _ iht ihr => cases hc with | envCons _ ht hr => exact .envCons s (iht ht) (ihr hr)
  | oper _ _ _ _ iha ihb ihc ihd =>
    cases hc with | oper ha hb hc' hd => exact .oper (iha ha) (ihb hb) (ihc hc') (ihd hd)
  | pair _ _ iha ihb => cases hc with | pair ha hb => exact .pair (iha ha) (ihb hb)
  | app _ ih => cases hc with | app ha => exact .app (ih ha)
  | eval _ _ iha ihb => cases hc with | eval ha hb => exact .eval (iha ha) (ihb hb)
  | comb _ _ _ iha ihb ihc => cases hc with | comb ha hb hc' => exact .comb (iha ha) (ihb hb) (ihc hc')
  | capsule k' _ ih =>
    cases hc with
    | hidden => exact .hidden _
    | capsule _ hv => exact .capsule k' (ih hv)
  | hidden v v' => exact .hidden _

end Clean

/-! ## The simulation -/

theorem CSim.env_inv {k : Nat} {bs : Env} {y : Term} (h : CSim k (.env bs) y) :
    exists bs', y = .env bs' := by
  cases h with
  | envNil => exact Exists.intro [] rfl
  | envCons s _ _ => exact Exists.intro _ rfl

theorem CSim.env_inv_right {k : Nat} {bs : Env} {y : Term} (h : CSim k y (.env bs)) :
    exists bs', y = .env bs' := by
  cases h with
  | envNil => exact Exists.intro [] rfl
  | envCons s _ _ => exact Exists.intro _ rfl

theorem csim_top {k : Nat} {t u t' : Term} (hc : Clean k t) (hs : CSim k t t') (h : Top t u) :
    exists u', Steps t' u' /\ CSim k u u' := by
  cases h with
  | evalSelf e hse =>
    cases hs with
    | eval ha he =>
      exact (CSim.env_inv he).elim fun bs' hb => by
        subst hb
        exact Exists.intro _ (And.intro (Steps.top (.evalSelf _ (ha.selfEval hse))) ha)
  | @evalSym x e t0 hl =>
    cases hs with
    | eval ha he =>
      cases ha
      exact (CSim.env_inv he).elim fun bs' hb => by
        subst hb
        exact ((CSim.lookup he x).2 _ hl).elim fun u' hu' =>
          Exists.intro u' (And.intro (Steps.top (.evalSym hu'.1)) hu'.2)
  | evalPair a b e =>
    cases hs with
    | eval ha he =>
      cases ha with
      | pair h1 h2 =>
        exact (CSim.env_inv he).elim fun bs' hb => by
          subst hb
          exact Exists.intro _ (And.intro (Steps.top (.evalPair _ _ _)) (.comb (.eval h1 he) h2 he))
  | evalApp t0 e =>
    cases hs with
    | eval ha he =>
      cases ha with
      | app h1 =>
        exact (CSim.env_inv he).elim fun bs' hb => by
          subst hb
          exact Exists.intro _ (And.intro (Steps.top (.evalApp _ _)) (.app (.eval h1 he)))
  | beta hv1 hv2 hv3 hm =>
    cases hs with
    | comb hf hx he =>
      cases hf with
      | oper h1 h2 h3 h4 =>
        exact (CSim.env_inv h4).elim fun e1' he1 => by
          subst he1
          exact (CSim.env_inv he).elim fun e2' he2 => by
            subst he2
            exact (CSim.ematch hm (.pair h1 h2) (.pair hx he)).elim fun m' hm' =>
              Exists.intro _ (And.intro
                (Steps.top (.beta (h1.isValue hv1) (h2.isValue hv2) (hx.isValue hv3) hm'.1))
                (.eval h3 (CSim.join hm'.2 h4)))
  | combApp t0 e hl =>
    cases hs with
    | comb hf hx he =>
      cases hf with
      | app h1 =>
        exact (CSim.env_inv he).elim fun bs' hb => by
          subst hb
          exact Exists.intro _ (And.intro (Steps.top (.combApp _ _ (hx.isList hl)))
            (.comb h1 (CSim.evalList he hx hl) he))
  | deltaVau e hv1 hv2 hv3 =>
    cases hs with
    | comb hf hx he =>
      cases hf
      cases hx with
      | pair h1 hr1 => cases hr1 with
        | pair h2 hr2 => cases hr2 with
          | pair h3 hr3 =>
            cases hr3
            exact (CSim.env_inv he).elim fun bs' hb => by
              subst hb
              exact Exists.intro _ (And.intro
                (Steps.top (.deltaVau _ (h1.isValue hv1) (h2.isValue hv2) (h3.isValue hv3)))
                (.oper h1 h2 h3 he))
  | deltaWrap e hv =>
    cases hs with
    | comb hf hx he =>
      cases hf
      cases hx with
      | pair h1 hr1 =>
        cases hr1
        exact (CSim.env_inv he).elim fun bs' hb => by
          subst hb
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
          exact (CSim.env_inv he).elim fun bs' hb => by
            subst hb
            exact Exists.intro _ (And.intro (Steps.top (.deltaUnwrap _ (h2.isValue hv))) h2)
  | deltaEval e1 e hv =>
    cases hs with
    | comb hf hx he =>
      cases hf
      cases hx with
      | pair h1 hr1 => cases hr1 with
        | pair h2 hr2 =>
          cases hr2
          exact (CSim.env_inv h2).elim fun e1' he1 => by
            subst he1
            exact (CSim.env_inv he).elim fun bs' hb => by
              subst hb
              exact Exists.intro _ (And.intro (Steps.top (.deltaEval _ _ (h1.isValue hv)))
                (.eval h1 h2))
  | deltaListStar e hv hr =>
    cases hs with
    | comb hf hx he =>
      cases hf
      exact (CSim.env_inv he).elim fun bs' hb => by
        subst hb
        exact (CSim.buildListStar hr hx).elim fun r' hr' =>
          Exists.intro r' (And.intro (Steps.top (.deltaListStar _ (hx.isValue hv) hr'.1)) hr'.2)
  | deltaEncap k' e hv =>
    cases hs with
    | comb hf hx he =>
      cases hf
      cases hx with
      | pair h1 hr1 =>
        cases hr1
        exact (CSim.env_inv he).elim fun bs' hb => by
          subst hb
          exact Exists.intro _ (And.intro (Steps.top (.deltaEncap k' _ (h1.isValue hv)))
            (.capsule k' h1))
  | deltaIsEncap k' e hv hcs =>
    cases hs with
    | comb hf hx he =>
      cases hf
      exact (CSim.env_inv he).elim fun bs' hb => by
        subst hb
        exact Exists.intro _ (And.intro
          (Steps.top (.deltaIsEncap k' _ (hx.isValue hv) (CSim.capsCheck hcs hx))) (.dat _))
  | deltaDecap k' e =>
    cases hc with
    | comb hcf _ _ =>
      cases hcf with
      | prim hne =>
        cases hs with
        | comb hf hx he =>
          cases hf
          cases hx with
          | pair h1 hr1 =>
            cases hr1
            cases h1 with
            | capsule _ h2 =>
              exact (CSim.env_inv he).elim fun bs' hb => by
                subst hb
                exact Exists.intro _ (And.intro (Steps.top (.deltaDecap k' _)) h2)
            | hidden => exact absurd rfl hne

theorem csim_step {k : Nat} {t u : Term} (h : Step t u) :
    forall t', Clean k t -> CSim k t t' -> exists u', Steps t' u' /\ CSim k u u' := by
  induction h with
  | top h => exact fun t' hc hs => csim_top hc hs h
  | envHere s r _ ih =>
    intro t' hc hs
    cases hc with
    | envCons _ hct _ =>
      cases hs with
      | envCons _ ha hr =>
        exact (ih _ hct ha).elim fun a1 h1 =>
          Exists.intro _ (And.intro (Steps.envCons h1.1 (Steps.refl _)) (.envCons s h1.2 hr))
  | envThere b _ ih =>
    intro t' hc hs
    cases b with
    | mk s a =>
      cases hc with
      | envCons _ _ hcr =>
        cases hs with
        | envCons _ ha hr =>
          exact (ih _ hcr hr).elim fun u1 h1 => (CSim.env_inv_right (CSim.symm h1.2)).elim fun l hl => by
            subst hl
            exact Exists.intro _ (And.intro (Steps.envCons (Steps.refl _) h1.1) (.envCons s ha h1.2))
  | oper1 b c d _ ih =>
    intro t' hc hs
    cases hc with
    | oper hca _ _ _ =>
      cases hs with
      | oper ha hb hc' hd =>
        exact (ih _ hca ha).elim fun a1 h1 => Exists.intro _
          (And.intro (Steps.oper h1.1 (Steps.refl _) (Steps.refl _) (Steps.refl _)) (.oper h1.2 hb hc' hd))
  | oper2 a c d _ ih =>
    intro t' hc hs
    cases hc with
    | oper _ hcb _ _ =>
      cases hs with
      | oper ha hb hc' hd =>
        exact (ih _ hcb hb).elim fun b1 h1 => Exists.intro _
          (And.intro (Steps.oper (Steps.refl _) h1.1 (Steps.refl _) (Steps.refl _)) (.oper ha h1.2 hc' hd))
  | oper3 a b d _ ih =>
    intro t' hc hs
    cases hc with
    | oper _ _ hcc _ =>
      cases hs with
      | oper ha hb hc' hd =>
        exact (ih _ hcc hc').elim fun c1 h1 => Exists.intro _
          (And.intro (Steps.oper (Steps.refl _) (Steps.refl _) h1.1 (Steps.refl _)) (.oper ha hb h1.2 hd))
  | oper4 a b c _ ih =>
    intro t' hc hs
    cases hc with
    | oper _ _ _ hcd =>
      cases hs with
      | oper ha hb hc' hd =>
        exact (ih _ hcd hd).elim fun d1 h1 => Exists.intro _
          (And.intro (Steps.oper (Steps.refl _) (Steps.refl _) (Steps.refl _) h1.1) (.oper ha hb hc' h1.2))
  | pairL b _ ih =>
    intro t' hc hs
    cases hc with
    | pair hca _ =>
      cases hs with
      | pair ha hb =>
        exact (ih _ hca ha).elim fun a1 h1 => Exists.intro _
          (And.intro (Steps.pair h1.1 (Steps.refl _)) (.pair h1.2 hb))
  | pairR a _ ih =>
    intro t' hc hs
    cases hc with
    | pair _ hcb =>
      cases hs with
      | pair ha hb =>
        exact (ih _ hcb hb).elim fun b1 h1 => Exists.intro _
          (And.intro (Steps.pair (Steps.refl _) h1.1) (.pair ha h1.2))
  | app _ ih =>
    intro t' hc hs
    cases hc with
    | app hca =>
      cases hs with
      | app ha =>
        exact (ih _ hca ha).elim fun a1 h1 => Exists.intro _ (And.intro (Steps.app h1.1) (.app h1.2))
  | evalL b _ ih =>
    intro t' hc hs
    cases hc with
    | eval hca _ =>
      cases hs with
      | eval ha hb =>
        exact (ih _ hca ha).elim fun a1 h1 => Exists.intro _
          (And.intro (Steps.eval h1.1 (Steps.refl _)) (.eval h1.2 hb))
  | evalR a _ ih =>
    intro t' hc hs
    cases hc with
    | eval _ hcb =>
      cases hs with
      | eval ha hb =>
        exact (ih _ hcb hb).elim fun b1 h1 => Exists.intro _
          (And.intro (Steps.eval (Steps.refl _) h1.1) (.eval ha h1.2))
  | comb1 b c _ ih =>
    intro t' hc hs
    cases hc with
    | comb hca _ _ =>
      cases hs with
      | comb ha hb hc' =>
        exact (ih _ hca ha).elim fun a1 h1 => Exists.intro _
          (And.intro (Steps.comb3 h1.1 (Steps.refl _) (Steps.refl _)) (.comb h1.2 hb hc'))
  | comb2 a c _ ih =>
    intro t' hc hs
    cases hc with
    | comb _ hcb _ =>
      cases hs with
      | comb ha hb hc' =>
        exact (ih _ hcb hb).elim fun b1 h1 => Exists.intro _
          (And.intro (Steps.comb3 (Steps.refl _) h1.1 (Steps.refl _)) (.comb ha h1.2 hc'))
  | comb3 a b _ ih =>
    intro t' hc hs
    cases hc with
    | comb _ _ hcc =>
      cases hs with
      | comb ha hb hc' =>
        exact (ih _ hcc hc').elim fun c1 h1 => Exists.intro _
          (And.intro (Steps.comb3 (Steps.refl _) (Steps.refl _) h1.1) (.comb ha hb h1.2))
  | capsule k' _ ih =>
    intro t' hc hs
    cases hs with
    | capsule _ hv =>
      cases hc with
      | hidden => exact Exists.intro _ (And.intro (Steps.refl _) (.hidden _ _))
      | capsule _ hcv =>
        exact (ih _ hcv hv).elim fun v1 h1 => Exists.intro _
          (And.intro (Steps.capsule h1.1) (.capsule k' h1.2))
    | hidden v v' => exact Exists.intro _ (And.intro (Steps.refl _) (.hidden _ _))

theorem csim_steps {k : Nat} {t t' u : Term} (hc : Clean k t) (hs : CSim k t t') (h : Steps t u) :
    exists u', Steps t' u' /\ CSim k u u' := by
  induction h with
  | refl => exact Exists.intro t' (And.intro (Steps.refl _) hs)
  | tail hp hstep ih =>
    exact ih.elim fun v' hv => (csim_step hstep v' (Clean.steps hp hc) hv.2).elim fun w' hw =>
      Exists.intro w' (And.intro (hv.1.trans hw.1) hw.2)

theorem CSim.envAt {k : Nat} {s : Nat} {y y' : Term} (h : CSim k y y') : forall (pre post : Env),
    CSim k (.env (pre ++ (s, y) :: post)) (.env (pre ++ (s, y') :: post))
  | [], post => .envCons s h (CSim.reflEnv post)
  | (s', t) :: pre, post => .envCons s' (CSim.refl t) (CSim.envAt h pre post)

theorem CSim.plug {k : Nat} (c : Ctx) {t t' : Term} (h : CSim k t t') : CSim k (c.plug t) (c.plug t') := by
  induction c with
  | hole => exact h
  | envAt pre s c post ih => exact CSim.envAt ih pre post
  | oper1 c b c' d ih => exact .oper ih (CSim.refl _) (CSim.refl _) (CSim.refl _)
  | oper2 a c c' d ih => exact .oper (CSim.refl _) ih (CSim.refl _) (CSim.refl _)
  | oper3 a b c d ih => exact .oper (CSim.refl _) (CSim.refl _) ih (CSim.refl _)
  | oper4 a b c' c ih => exact .oper (CSim.refl _) (CSim.refl _) (CSim.refl _) ih
  | pairL c b ih => exact .pair ih (CSim.refl _)
  | pairR a c ih => exact .pair (CSim.refl _) ih
  | app c ih => exact .app ih
  | evalL c b ih => exact .eval ih (CSim.refl _)
  | evalR a c ih => exact .eval (CSim.refl _) ih
  | comb1 c b c' ih => exact .comb ih (CSim.refl _) (CSim.refl _)
  | comb2 a c c' ih => exact .comb (CSim.refl _) ih (CSim.refl _)
  | comb3 a b c ih => exact .comb (CSim.refl _) (CSim.refl _) ih
  | capsule k' c ih => exact .capsule k' ih

/-! ## The encapsulation theorem -/

theorem CSim.observe {k n : Nat} {t t' : Term} (hc : Clean k t) (hs : CSim k t t')
    (h : Steps t (Term.dat n)) : Steps t' (Term.dat n) :=
  (csim_steps hc hs h).elim fun u' hu => by
    have hsim := hu.2
    cases hsim
    exact hu.1

/-- **Encapsulation.** Put a capsule of type `k` into any context `c` that contains no `$decap k`
(outside capsules of type `k`). Then the program reduces to primitive data `n` with content `v`
exactly when it does with any other content `v'`: without the decapsulator, the content cannot
be observed. -/
theorem capsule_opacity {k n : Nat} {v v' : Term} (c : Ctx) (hc : Clean k (c.plug (capsule k v))) :
    Steps (c.plug (capsule k v)) (dat n) <-> Steps (c.plug (capsule k v')) (dat n) := by
  have hs : CSim k (c.plug (capsule k v)) (c.plug (capsule k v')) := CSim.plug c (.hidden v v')
  exact Iff.intro (CSim.observe hc hs) (CSim.observe (Clean.csim hc hs) hs.symm)

/-- The other side: with the decapsulator, the content **can** be observed. -/
theorem capsule_observable_with_decap (k : Nat) :
    Steps (comb (prim (.decap k)) (list1 (capsule k (dat 5))) (env [])) (dat 5) /\
    Not (Steps (comb (prim (.decap k)) (list1 (capsule k (dat 6))) (env [])) (dat 5)) := by
  refine And.intro (Steps.top (.deltaDecap k _)) (fun h => ?_)
  have h6 : Steps (comb (prim (.decap k)) (list1 (capsule k (dat 6))) (env [])) (dat 6) :=
    Steps.top (.deltaDecap k _)
  have := normal_unique h h6 (normal_dat 5) (normal_dat 6)
  cases this

end VauE
