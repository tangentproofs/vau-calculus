import Vau.Env.Reduction
import Vau.Confluence

/-!
# Confluence of the vau-e rules

This file proves that `VauE.Steps` (zero or more steps of the vau-e rules of `Vau/Env/Reduction.lean`,
in the compatible closure) is confluent: `VauE.confluence`.

Method: parallel reduction and complete developments (Tait, Martin-Lof, Takahashi), as for vau-x in
`Vau/Confluence.lean`. vau-e has no substitution, so there is no substitution lemma. Instead the
proof needs that parallel steps keep the shape that a rule looks at: the bindings of an environment
(for `lookup`), the parameter tree and operand tree (for `match`), proper lists (for combine-app),
and the argument list of `$list*`.

**Scope.** This is a direct proof for the rules of this formalization: Shutt's general schemata
(9.7), his delta-rules (9.12) for `$vau`, `$wrap`, `$unwrap`, and this project's delta-rules for
`$eval` and `$list*`, with environments as unsorted lists. It does **not** formalize Shutt's regular
substitutive reduction systems (thesis chapter 13), and it does not cover other delta-rules.
-/

namespace VauE
open Term

/-! ## Decision procedures -/

/-- Decision procedure for `IsValue`. -/
def isValueB : Term -> Bool
  | dat _ => true
  | prim _ => true
  | sym _ => true
  | ign => true
  | nil => true
  | env _ => true
  | oper _ _ _ _ => true
  | pair a b => isValueB a && isValueB b
  | app t => isValueB t
  | eval _ _ => false
  | comb _ _ _ => false
  | capsule _ _ => true

theorem isValueB_iff : forall t : Term, isValueB t = true <-> IsValue t
  | dat n => Iff.intro (fun _ => .dat n) (fun _ => rfl)
  | prim p => Iff.intro (fun _ => .prim p) (fun _ => rfl)
  | sym s => Iff.intro (fun _ => .sym s) (fun _ => rfl)
  | ign => Iff.intro (fun _ => .ign) (fun _ => rfl)
  | nil => Iff.intro (fun _ => .nil) (fun _ => rfl)
  | env e => Iff.intro (fun _ => .env e) (fun _ => rfl)
  | oper a b c d => Iff.intro (fun _ => .oper a b c d) (fun _ => rfl)
  | pair a b => by
    simp only [isValueB, Bool.and_eq_true, isValueB_iff a, isValueB_iff b]
    exact Iff.intro (fun h => IsValue.pair h.1 h.2)
      (fun h => by cases h; exact And.intro (by assumption) (by assumption))
  | app t => by
    simp only [isValueB, isValueB_iff t]
    exact Iff.intro (fun h => .app h) (fun h => by cases h; assumption)
  | eval a b => Iff.intro (fun h => (nomatch h)) (fun h => (nomatch h))
  | comb a b c => Iff.intro (fun h => (nomatch h)) (fun h => (nomatch h))
  | capsule k v => Iff.intro (fun _ => .capsule k v) (fun _ => rfl)

/-- Decision procedure for `IsList`. -/
def isListB : Term -> Bool
  | nil => true
  | pair _ b => isListB b
  | _ => false

theorem isListB_iff : forall t : Term, isListB t = true <-> IsList t
  | nil => Iff.intro (fun _ => .nil) (fun _ => rfl)
  | pair a b => by
    simp only [isListB, isListB_iff b]
    exact Iff.intro (fun h => .cons a h) (fun h => by cases h; assumption)
  | dat _ => Iff.intro (fun h => (nomatch h)) (fun h => (nomatch h))
  | prim _ => Iff.intro (fun h => (nomatch h)) (fun h => (nomatch h))
  | sym _ => Iff.intro (fun h => (nomatch h)) (fun h => (nomatch h))
  | ign => Iff.intro (fun h => (nomatch h)) (fun h => (nomatch h))
  | env _ => Iff.intro (fun h => (nomatch h)) (fun h => (nomatch h))
  | oper _ _ _ _ => Iff.intro (fun h => (nomatch h)) (fun h => (nomatch h))
  | app _ => Iff.intro (fun h => (nomatch h)) (fun h => (nomatch h))
  | eval _ _ => Iff.intro (fun h => (nomatch h)) (fun h => (nomatch h))
  | comb _ _ _ => Iff.intro (fun h => (nomatch h)) (fun h => (nomatch h))
  | capsule _ _ => Iff.intro (fun h => (nomatch h)) (fun h => (nomatch h))

/-! ## Parallel reduction -/

/-- Parallel reduction for vau-e. Side conditions of rules are stated on the reducts of the
parts (for example the lookup is in the reduced environment); `Par.toSteps` checks that this is
still reduction. -/
inductive Par : Term -> Term -> Prop where
  | dat (n : Nat) : Par (dat n) (dat n)
  | prim (p : Prim) : Par (prim p) (prim p)
  | sym (s : Nat) : Par (sym s) (sym s)
  | ign : Par ign ign
  | nil : Par nil nil
  | envNil : Par (env []) (env [])
  | envCons (s : Nat) {t t' : Term} {r r' : Env} :
      Par t t' -> Par (env r) (env r') -> Par (env ((s, t) :: r)) (env ((s, t') :: r'))
  | oper {a a' b b' c c' d d' : Term} :
      Par a a' -> Par b b' -> Par c c' -> Par d d' -> Par (oper a b c d) (oper a' b' c' d')
  | pair {a a' b b' : Term} : Par a a' -> Par b b' -> Par (pair a b) (pair a' b')
  | app {t t' : Term} : Par t t' -> Par (app t) (app t')
  | eval {a a' b b' : Term} : Par a a' -> Par b b' -> Par (eval a b) (eval a' b')
  | comb {a a' b b' c c' : Term} :
      Par a a' -> Par b b' -> Par c c' -> Par (comb a b c) (comb a' b' c')
  | evalSelf {t t' : Term} (bs : Env) : SelfEval t -> Par t t' -> Par (eval t (env bs)) t'
  | evalSym {s : Nat} {bs bs' : Env} {u : Term} :
      Par (env bs) (env bs') -> Env.lookup s bs' = some u -> Par (eval (sym s) (env bs)) u
  | evalPair {a a' b b' : Term} {bs bs' : Env} : Par a a' -> Par b b' -> Par (env bs) (env bs') ->
      Par (eval (pair a b) (env bs)) (comb (eval a' (env bs')) b' (env bs'))
  | evalApp {t t' : Term} {bs bs' : Env} : Par t t' -> Par (env bs) (env bs') ->
      Par (eval (app t) (env bs)) (app (eval t' (env bs')))
  | beta {v1 v1' v2 v2' v3 v3' body body' : Term} {e1 e1' e2 e2' m : Env} :
      IsValue v1 -> IsValue v2 -> IsValue v3 ->
      Par v1 v1' -> Par v2 v2' -> Par body body' -> Par v3 v3' ->
      Par (env e1) (env e1') -> Par (env e2) (env e2') ->
      ematch (pair v1' v2') (pair v3' (env e2')) = some m ->
      Par (comb (oper v1 v2 body (env e1)) v3 (env e2)) (eval body' (env (Env.join m e1')))
  | combApp {t t' ts ts' : Term} {bs bs' : Env} : IsList ts -> Par t t' -> Par ts ts' ->
      Par (env bs) (env bs') ->
      Par (comb (app t) ts (env bs)) (comb t' (evalList (env bs') ts') (env bs'))
  | deltaVau {v1 v1' v2 v2' v3 v3' : Term} {bs bs' : Env} :
      IsValue v1 -> IsValue v2 -> IsValue v3 -> Par v1 v1' -> Par v2 v2' -> Par v3 v3' ->
      Par (env bs) (env bs') ->
      Par (comb (prim .vau) (list3 v1 v2 v3) (env bs)) (oper v1' v2' v3' (env bs'))
  | deltaWrap {v v' : Term} (bs : Env) : IsValue v -> Par v v' ->
      Par (comb (prim .wrap) (list1 v) (env bs)) (app v')
  | deltaUnwrap {v v' : Term} (bs : Env) : IsValue v -> Par v v' ->
      Par (comb (prim .unwrap) (list1 (app v)) (env bs)) v'
  | deltaEval {v v' : Term} {e1 e1' : Env} (bs : Env) : IsValue v -> Par v v' ->
      Par (env e1) (env e1') ->
      Par (comb (prim .eval) (list2 v (env e1)) (env bs)) (eval v' (env e1'))
  | deltaListStar {vs vs' r : Term} (bs : Env) : IsValue vs -> Par vs vs' ->
      buildListStar vs' = some r -> Par (comb (prim .listStar) vs (env bs)) r
  | capsule (k : Nat) {v v' : Term} : Par v v' -> Par (capsule k v) (capsule k v')
  | deltaEncap {v v' : Term} (k : Nat) (bs : Env) : IsValue v -> Par v v' ->
      Par (comb (prim (.encap k)) (list1 v) (env bs)) (capsule k v')
  | deltaIsEncap {vs vs' : Term} {b : Bool} (k : Nat) (bs : Env) : IsValue vs -> Par vs vs' ->
      capsCheck k vs' = some b -> Par (comb (prim (.isEncap k)) vs (env bs)) (dat (if b then 1 else 0))
  | deltaDecap {v v' : Term} (k : Nat) (bs : Env) : Par v v' ->
      Par (comb (prim (.decap k)) (list1 (capsule k v)) (env bs)) v'

namespace Par

mutual
theorem refl : forall t : Term, Par t t
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
  | .capsule k v => .capsule k (refl v)
theorem reflEnv : forall bs : Env, Par (.env bs) (.env bs)
  | [] => .envNil
  | (s, t) :: r => .envCons s (refl t) (reflEnv r)
end

/-! ### What parallel steps keep -/

theorem isValue {v v' : Term} (h : Par v v') (hv : IsValue v) : IsValue v' := by
  induction h with
  | dat n => exact .dat n
  | prim p => exact .prim p
  | sym s => exact .sym s
  | ign => exact .ign
  | nil => exact .nil
  | envNil => exact .env _
  | envCons => exact .env _
  | oper => exact .oper _ _ _ _
  | capsule => exact .capsule _ _
  | pair _ _ iha ihb => cases hv with | pair ha hb => exact .pair (iha ha) (ihb hb)
  | app _ ih => cases hv with | app ht => exact .app (ih ht)
  | _ => cases hv

theorem selfEval {t t' : Term} (h : Par t t') (hs : SelfEval t) : SelfEval t' := by
  cases hs <;> cases h <;> constructor

theorem isList {ts ts' : Term} (h : Par ts ts') (hl : IsList ts) : IsList ts' := by
  induction hl generalizing ts' with
  | nil => cases h; exact .nil
  | cons a _ ih => cases h with | pair _ hb => exact .cons _ (ih hb)

theorem evalList {e e' ts ts' : Term} (he : Par e e') (h : Par ts ts') (hl : IsList ts) :
    Par (VauE.evalList e ts) (VauE.evalList e' ts') := by
  induction hl generalizing ts' with
  | nil => cases h; exact .nil
  | cons a _ ih => cases h with | pair ha hb => exact .pair (.eval ha he) (ih hb)

theorem join {a a' b b' : Env} (ha : Par (.env a) (.env a')) (hb : Par (.env b) (.env b')) :
    Par (.env (Env.join a b)) (.env (Env.join a' b')) := by
  induction a generalizing a' with
  | nil => cases ha; exact hb
  | cons x r ih =>
    cases ha with
    | envCons s ht hr => exact .envCons s ht (ih hr)

theorem lookup_some {bs bs' : Env} (h : Par (.env bs) (.env bs')) {s : Nat} {u : Term}
    (hl : Env.lookup s bs = some u) : exists u', Env.lookup s bs' = some u' /\ Par u u' := by
  induction bs generalizing bs' with
  | nil => simp [Env.lookup] at hl
  | cons x r ih =>
    cases h with
    | envCons s' ht hr =>
      simp only [Env.lookup] at hl
      simp only [Env.lookup]
      split
      next hs =>
        rw [if_pos hs] at hl
        cases hl
        exact Exists.intro _ (And.intro rfl ht)
      next hs =>
        rw [if_neg hs] at hl
        exact ih hr hl

theorem pattern : forall {p p' t : Term} {m : Env}, ematch p t = some m -> Par p p' -> p' = p
  | .ign, _, _, _, _, h => by cases h; rfl
  | .nil, _, _, _, _, h => by cases h; rfl
  | .sym _, _, _, _, _, h => by cases h; rfl
  | .pair a b, _, t, _, hm, h => by
    cases t with
    | pair c d =>
      simp only [ematch] at hm
      split at hm
      next =>
        split at hm
        next m1 m2 h1 h2 =>
          cases h with
          | pair ha hb => rw [pattern h1 ha, pattern h2 hb]
        next => cases hm
      next => cases hm
    | _ => simp [ematch] at hm
  | .dat _, _, _, _, hm, _ => by simp [ematch] at hm
  | .prim _, _, _, _, hm, _ => by simp [ematch] at hm
  | .env _, _, _, _, hm, _ => by simp [ematch] at hm
  | .oper _ _ _ _, _, _, _, hm, _ => by simp [ematch] at hm
  | .app _, _, _, _, hm, _ => by simp [ematch] at hm
  | .eval _ _, _, _, _, hm, _ => by simp [ematch] at hm
  | .comb _ _ _, _, _, _, hm, _ => by simp [ematch] at hm
  | .capsule _ _, _, _, _, hm, _ => by simp [ematch] at hm

theorem ematch_some : forall {p t t' : Term} {m : Env}, ematch p t = some m -> Par t t' ->
    exists m', ematch p t' = some m' /\ Par (.env m) (.env m')
  | .ign, _, _, _, hm, _ => by
    simp only [ematch] at hm; cases hm
    exact Exists.intro [] (And.intro rfl .envNil)
  | .nil, t, _, _, hm, h => by
    cases t <;> simp [ematch] at hm
    cases hm; cases h
    exact Exists.intro [] (And.intro rfl .envNil)
  | .sym s, _, t', _, hm, h => by
    simp only [ematch] at hm; cases hm
    exact Exists.intro [(s, t')] (And.intro rfl (.envCons s h .envNil))
  | .pair a b, t, _, _, hm, h => by
    cases t with
    | pair c d =>
      cases h with
      | pair hc hd =>
        simp only [ematch] at hm
        split at hm
        next hdis =>
          split at hm
          next m1 m2 h1 h2 =>
            cases hm
            exact (ematch_some h1 hc).elim fun m1' h1' => (ematch_some h2 hd).elim fun m2' h2' =>
              Exists.intro (Env.join m1' m2')
                (And.intro (by simp only [ematch, hdis, if_true, h1'.1, h2'.1]) (join h1'.2 h2'.2))
          next => cases hm
        next => cases hm
    | _ => simp [ematch] at hm
  | .dat _, _, _, _, hm, _ => by simp [ematch] at hm
  | .prim _, _, _, _, hm, _ => by simp [ematch] at hm
  | .env _, _, _, _, hm, _ => by simp [ematch] at hm
  | .oper _ _ _ _, _, _, _, hm, _ => by simp [ematch] at hm
  | .app _, _, _, _, hm, _ => by simp [ematch] at hm
  | .eval _ _, _, _, _, hm, _ => by simp [ematch] at hm
  | .comb _ _ _, _, _, _, hm, _ => by simp [ematch] at hm
  | .capsule _ _, _, _, _, hm, _ => by simp [ematch] at hm

theorem buildListStar_some : forall {x x' r : Term}, buildListStar x = some r -> Par x x' ->
    exists r', buildListStar x' = some r' /\ Par r r'
  | .pair a rest, .pair a' rest', _, hb, .pair ha hr => by
      cases rest with
      | nil =>
        cases hr
        simp only [buildListStar] at hb; cases hb
        exact Exists.intro _ (And.intro rfl ha)
      | pair c d =>
        cases hr with
        | pair hc hd =>
          simp only [buildListStar, Option.map_eq_some_iff] at hb
          exact hb.elim fun r0 hr0 =>
            (buildListStar_some hr0.1 (.pair hc hd)).elim fun r1 hr1 => by
              refine Exists.intro (.pair a' r1) (And.intro ?_ ?_)
              . simp only [buildListStar, hr1.1, Option.map_some]
              . rw [<- hr0.2]; exact .pair ha hr1.2
      | _ => simp [buildListStar] at hb
  | .dat _, _, _, hb, _ => by simp [buildListStar] at hb
  | .prim _, _, _, hb, _ => by simp [buildListStar] at hb
  | .sym _, _, _, hb, _ => by simp [buildListStar] at hb
  | .ign, _, _, hb, _ => by simp [buildListStar] at hb
  | .nil, _, _, hb, _ => by simp [buildListStar] at hb
  | .env _, _, _, hb, _ => by simp [buildListStar] at hb
  | .oper _ _ _ _, _, _, hb, _ => by simp [buildListStar] at hb
  | .app _, _, _, hb, _ => by simp [buildListStar] at hb
  | .eval _ _, _, _, hb, _ => by simp [buildListStar] at hb
  | .comb _ _ _, _, _, hb, _ => by simp [buildListStar] at hb
  | .capsule _ _, _, _, hb, _ => by simp [buildListStar] at hb

theorem isCapsuleOf_eq {k : Nat} {x x' : Term} (hv : IsValue x) (h : Par x x') :
    isCapsuleOf k x' = isCapsuleOf k x := by
  cases hv <;> cases h <;> rfl

theorem capsCheck_some {k : Nat} : forall {vs vs' : Term} {b : Bool}, IsValue vs ->
    capsCheck k vs = some b -> Par vs vs' -> capsCheck k vs' = some b
  | .nil, _, _, _, hc, h => by cases h; exact hc
  | .pair x rest, _, _, hv, hc, h => by
    cases hv with
    | pair hx hr =>
      cases h with
      | pair h1 h2 =>
        simp only [capsCheck, Option.map_eq_some_iff] at hc
        exact hc.elim fun b0 hb0 => by
          simp only [capsCheck, capsCheck_some hr hb0.1 h2, Option.map_some, isCapsuleOf_eq hx h1]
          exact congrArg some hb0.2
  | .dat _, _, _, _, hc, _ => by simp [capsCheck] at hc
  | .prim _, _, _, _, hc, _ => by simp [capsCheck] at hc
  | .sym _, _, _, _, hc, _ => by simp [capsCheck] at hc
  | .ign, _, _, _, hc, _ => by simp [capsCheck] at hc
  | .env _, _, _, _, hc, _ => by simp [capsCheck] at hc
  | .oper _ _ _ _, _, _, _, hc, _ => by simp [capsCheck] at hc
  | .app _, _, _, _, hc, _ => by simp [capsCheck] at hc
  | .eval _ _, _, _, _, hc, _ => by simp [capsCheck] at hc
  | .comb _ _ _, _, _, _, hc, _ => by simp [capsCheck] at hc
  | .capsule _ _, _, _, _, hc, _ => by simp [capsCheck] at hc

theorem env_inv {bs : Env} {y : Term} (h : Par (.env bs) y) : exists bs', y = .env bs' := by
  cases h with
  | envNil => exact Exists.intro [] rfl
  | envCons s _ _ => exact Exists.intro _ rfl

end Par

/-! ## Complete development -/

/-- The bindings of an environment term (and `[]` for any other term). -/
def envOf : Term -> Env
  | env bs => bs
  | _ => []

/-- Development of `[eval t e]`, given the developments `t'` of `t` and `e'` of `e`. -/
def cdEval (t e t' e' : Term) : Term :=
  match e, t with
  | env _, sym s =>
    match Env.lookup s (envOf e') with
    | some u => u
    | none => eval t' e'
  | env _, pair _ _ =>
    match t' with
    | pair a b => comb (eval a e') b e'
    | _ => eval t' e'
  | env _, app _ =>
    match t' with
    | app u => app (eval u e')
    | _ => eval t' e'
  | env _, dat _ => t'
  | env _, prim _ => t'
  | env _, env _ => t'
  | env _, ign => t'
  | env _, nil => t'
  | env _, oper _ _ _ _ => t'
  | env _, capsule _ _ => t'
  | _, _ => eval t' e'

/-- Development of `[combine <operative v1 v2 body se> x e]` (beta-oper), given developments. -/
def cdBeta (v1 v2 x f' x' e' : Term) : Term :=
  if isValueB v1 && isValueB v2 && isValueB x then
    match f' with
    | oper w1 w2 body' (env sb') =>
      match ematch (pair w1 w2) (pair x' e') with
      | some m => eval body' (env (Env.join m sb'))
      | none => comb f' x' e'
    | _ => comb f' x' e'
  else comb f' x' e'

/-- Development of `[combine o x e]` for a primitive operative `o`, given developments. -/
def cdDelta (p : Prim) (x f' x' e' : Term) : Term :=
  match p with
  | .vau =>
    match x with
    | pair v1 (pair v2 (pair v3 nil)) =>
      if isValueB v1 && isValueB v2 && isValueB v3 then
        match x' with
        | pair a (pair b (pair c nil)) => oper a b c e'
        | _ => comb f' x' e'
      else comb f' x' e'
    | _ => comb f' x' e'
  | .wrap =>
    match x with
    | pair v nil =>
      if isValueB v then
        match x' with
        | pair a nil => app a
        | _ => comb f' x' e'
      else comb f' x' e'
    | _ => comb f' x' e'
  | .unwrap =>
    match x with
    | pair (app v) nil =>
      if isValueB v then
        match x' with
        | pair (app a) nil => a
        | _ => comb f' x' e'
      else comb f' x' e'
    | _ => comb f' x' e'
  | .eval =>
    match x with
    | pair v (pair (env _) nil) =>
      if isValueB v then
        match x' with
        | pair a (pair w nil) => eval a w
        | _ => comb f' x' e'
      else comb f' x' e'
    | _ => comb f' x' e'
  | .listStar =>
    if isValueB x then
      match buildListStar x' with
      | some r => r
      | none => comb f' x' e'
    else comb f' x' e'
  | .encap k =>
    match x with
    | pair v nil =>
      if isValueB v then
        match x' with
        | pair a nil => capsule k a
        | _ => comb f' x' e'
      else comb f' x' e'
    | _ => comb f' x' e'
  | .isEncap k =>
    if isValueB x then
      match capsCheck k x' with
      | some b => dat (if b then 1 else 0)
      | none => comb f' x' e'
    else comb f' x' e'
  | .decap k =>
    match x with
    | pair (capsule k' _) nil =>
      if k' = k then
        match x' with
        | pair (capsule _ a) nil => a
        | _ => comb f' x' e'
      else comb f' x' e'
    | _ => comb f' x' e'

/-- Development of `[combine f x e]`, given the developments `f'`, `x'`, `e'`. -/
def cdComb (f x e f' x' e' : Term) : Term :=
  match e, f with
  | env _, oper v1 v2 _ (env _) => cdBeta v1 v2 x f' x' e'
  | env _, app _ =>
    if isListB x then
      match f' with
      | app u => comb u (evalList e' x') e'
      | _ => comb f' x' e'
    else comb f' x' e'
  | env _, prim p => cdDelta p x f' x' e'
  | _, _ => comb f' x' e'

mutual
/-- Complete development: fire every redex that is present in the term, at once. -/
def cd : Term -> Term
  | dat n => dat n
  | prim p => prim p
  | sym s => sym s
  | ign => ign
  | nil => nil
  | env bs => env (cdL bs)
  | oper a b c d => oper (cd a) (cd b) (cd c) (cd d)
  | pair a b => pair (cd a) (cd b)
  | app t => app (cd t)
  | eval t e => cdEval t e (cd t) (cd e)
  | comb f x e => cdComb f x e (cd f) (cd x) (cd e)
  | capsule k v => capsule k (cd v)
/-- Complete development of every binding of an environment. -/
def cdL : Env -> Env
  | [] => []
  | (s, t) :: r => (s, cd t) :: cdL r
end

theorem cd_env (bs : Env) : cd (env bs) = env (cdL bs) := by simp [cd]

theorem cdEval_nonenv {t e t' e' : Term} (he : forall bs, Not (e = env bs)) :
    cdEval t e t' e' = eval t' e' := by
  cases e <;> first | exact absurd rfl (he _) | (cases t <;> rfl)

theorem cdComb_nonenv {f x e f' x' e' : Term} (he : forall bs, Not (e = env bs)) :
    cdComb f x e f' x' e' = comb f' x' e' := by
  cases e <;> first | exact absurd rfl (he _) | (cases f <;> rfl)

theorem cdEval_self {t t' e' : Term} {bs : Env} (hs : SelfEval t) : cdEval t (env bs) t' e' = t' := by
  cases hs <;> rfl

/-- The development of a congruence step on `[eval a b]`. -/
theorem Par.eval_case {a a' b b' : Term} (ha : Par a a') (hb : Par b b') (iha : Par a' (cd a))
    (ihb : Par b' (cd b)) : Par (Term.eval a' b') (cdEval a b (cd a) (cd b)) := by
  cases b with
  | env bs =>
    exact (Par.env_inv hb).elim fun bs' hbs => by
      subst hbs
      rw [cd_env] at ihb
      rw [cd_env]
      cases a with
      | sym s =>
        cases ha
        simp only [cdEval, envOf]
        split
        next u hu => exact .evalSym ihb hu
        next => simp only [cd]; exact .eval (.sym s) ihb
      | pair x y =>
        cases ha with
        | pair hx hy =>
          simp only [cd] at iha
          cases iha with
          | pair hx' hy' => simp only [cd, cdEval]; exact .evalPair hx' hy' ihb
      | app u =>
        cases ha with
        | app hu =>
          simp only [cd] at iha
          cases iha with
          | app hu' => simp only [cd, cdEval]; exact .evalApp hu' ihb
      | dat n => exact .evalSelf bs' (ha.selfEval (.dat n)) iha
      | prim q => exact .evalSelf bs' (ha.selfEval (.prim q)) iha
      | env cs => exact .evalSelf bs' (ha.selfEval (.env cs)) iha
      | ign => exact .evalSelf bs' (ha.selfEval .ign) iha
      | nil => exact .evalSelf bs' (ha.selfEval .nil) iha
      | oper p q r w => exact .evalSelf bs' (ha.selfEval (.oper p q r w)) iha
      | eval u w => exact .eval iha ihb
      | comb u w z => exact .eval iha ihb
      | capsule k v => exact .evalSelf bs' (ha.selfEval (.capsule k v)) iha
  | _ => rw [cdEval_nonenv (by intro bs h; cases h)]; exact .eval iha ihb

/-- The development of a congruence step on `[combine f x e]`. -/
theorem Par.comb_case {f f1 x x1 e e1 : Term} (hf : Par f f1) (hx : Par x x1) (he : Par e e1)
    (ihf : Par f1 (cd f)) (ihx : Par x1 (cd x)) (ihe : Par e1 (cd e)) :
    Par (Term.comb f1 x1 e1) (cdComb f x e (cd f) (cd x) (cd e)) := by
  have fb : Par (Term.comb f1 x1 e1) (Term.comb (cd f) (cd x) (cd e)) := .comb ihf ihx ihe
  cases e with
  | env bs =>
    exact (Par.env_inv he).elim fun bs1 hbs1 => by
      subst hbs1
      rw [cd_env] at ihe fb
      rw [cd_env]
      cases f with
      | oper v1 v2 body se =>
        cases hf with
        | oper h1 h2 h3 h4 =>
          cases se with
          | env sb =>
            exact (Par.env_inv h4).elim fun sb1 hsb1 => by
              subst hsb1
              simp only [cd] at ihf fb
              simp only [cd, cdComb, cdBeta]
              rw [<- cd_env] at ihf fb
              rw [<- cd_env]
              cases ihf with
              | oper i1 i2 i3 i4 =>
                rw [cd_env] at i4
                split
                next hv =>
                  simp only [Bool.and_eq_true, isValueB_iff] at hv
                  rw [cd_env]
                  split
                  next m hm =>
                    exact .beta (h1.isValue hv.1.1) (h2.isValue hv.1.2) (hx.isValue hv.2)
                      i1 i2 i3 ihx i4 ihe hm
                  next => rw [<- cd_env]; exact fb
                next => exact fb
          | _ => exact fb
      | app u =>
        cases hf with
        | app hu =>
          simp only [cd] at ihf fb
          cases ihf with
          | app hu' =>
            simp only [cd, cdComb]
            split
            next hl => exact .combApp (hx.isList ((isListB_iff x).1 hl)) hu' ihx ihe
            next => exact fb
      | prim q =>
        cases hf
        simp only [cd] at fb
        simp only [cd, cdComb]
        cases q with
        | vau =>
          simp only [cdDelta]
          split
          next v1 v2 v3 =>
            split
            next hv =>
              simp only [Bool.and_eq_true, isValueB_iff] at hv
              cases hx with
              | pair ha1 hr1 => cases hr1 with
                | pair ha2 hr2 => cases hr2 with
                  | pair ha3 hr3 =>
                    cases hr3
                    simp only [cd] at ihx
                    cases ihx with
                    | pair j1 jr1 => cases jr1 with
                      | pair j2 jr2 => cases jr2 with
                        | pair j3 jr3 =>
                          simp only [cd]
                          exact .deltaVau (ha1.isValue hv.1.1) (ha2.isValue hv.1.2)
                            (ha3.isValue hv.2) j1 j2 j3 ihe
            next => exact fb
          next => exact fb
        | wrap =>
          simp only [cdDelta]
          split
          next v =>
            split
            next hv =>
              rw [isValueB_iff] at hv
              cases hx with
              | pair ha1 hr1 =>
                cases hr1
                simp only [cd] at ihx
                cases ihx with
                | pair j1 jr1 =>
                  simp only [cd]
                  exact .deltaWrap bs1 (ha1.isValue hv) j1
            next => exact fb
          next => exact fb
        | unwrap =>
          simp only [cdDelta]
          split
          next v =>
            split
            next hv =>
              rw [isValueB_iff] at hv
              cases hx with
              | pair ha1 hr1 =>
                cases hr1
                cases ha1 with
                | app hav =>
                  simp only [cd] at ihx
                  cases ihx with
                  | pair j1 jr1 =>
                    cases j1 with
                    | app j =>
                      simp only [cd]
                      exact .deltaUnwrap bs1 (hav.isValue hv) j
            next => exact fb
          next => exact fb
        | eval =>
          simp only [cdDelta]
          split
          next v eb =>
            split
            next hv =>
              rw [isValueB_iff] at hv
              cases hx with
              | pair ha1 hr1 => cases hr1 with
                | pair hen hr2 =>
                  cases hr2
                  exact (Par.env_inv hen).elim fun eb1 heb1 => by
                    subst heb1
                    simp only [cd] at ihx
                    rw [<- cd_env] at ihx
                    cases ihx with
                    | pair j1 jr1 => cases jr1 with
                      | pair j2 jr2 =>
                        simp only [cd]
                        rw [cd_env] at j2
                        exact .deltaEval bs1 (ha1.isValue hv) j1 j2
            next => exact fb
          next => exact fb
        | listStar =>
          simp only [cdDelta]
          split
          next hv =>
            rw [isValueB_iff] at hv
            split
            next r hr => exact .deltaListStar bs1 (hx.isValue hv) ihx hr
            next => exact fb
          next => exact fb
        | encap k =>
          simp only [cdDelta]
          split
          next v =>
            split
            next hv =>
              rw [isValueB_iff] at hv
              cases hx with
              | pair ha1 hr1 =>
                cases hr1
                simp only [cd] at ihx
                cases ihx with
                | pair j1 jr1 =>
                  simp only [cd]
                  exact .deltaEncap k bs1 (ha1.isValue hv) j1
            next => exact fb
          next => exact fb
        | isEncap k =>
          simp only [cdDelta]
          split
          next hv =>
            rw [isValueB_iff] at hv
            split
            next b hb => exact .deltaIsEncap k bs1 (hx.isValue hv) ihx hb
            next => exact fb
          next => exact fb
        | decap k =>
          simp only [cdDelta]
          split
          next k' v =>
            split
            next hk =>
              subst hk
              cases hx with
              | pair ha1 hr1 =>
                cases hr1
                cases ha1 with
                | capsule _ hv1 =>
                  simp only [cd] at ihx
                  cases ihx with
                  | pair j1 jr1 =>
                    cases j1 with
                    | capsule _ j =>
                      simp only [cd]
                      exact .deltaDecap _ bs1 j
            next => exact fb
          next => exact fb
      | _ => exact fb
  | _ => rw [cdComb_nonenv (by intro bs h; cases h)]; exact fb

/-- Takahashi's lemma: a parallel step from `t` can always be completed to `cd t`. -/
theorem Par.to_cd {t s : Term} (h : Par t s) : Par s (cd t) := by
  induction h with
  | dat n => exact .dat n
  | prim p => exact .prim p
  | sym s => exact .sym s
  | ign => exact .ign
  | nil => exact .nil
  | envNil => rw [cd_env]; exact .envNil
  | envCons s _ _ iht ihr =>
    rw [cd_env] at ihr
    rw [cd_env]
    exact .envCons s iht ihr
  | oper _ _ _ _ iha ihb ihc ihd => simp only [cd]; exact .oper iha ihb ihc ihd
  | pair _ _ iha ihb => simp only [cd]; exact .pair iha ihb
  | app _ ih => simp only [cd]; exact .app ih
  | eval ha hb iha ihb => simp only [cd]; exact Par.eval_case ha hb iha ihb
  | comb hf hx he ihf ihx ihe => simp only [cd]; exact Par.comb_case hf hx he ihf ihx ihe
  | evalSelf bs hs _ ih => simp only [cd]; rw [cdEval_self hs]; exact ih
  | evalSym _ hl ihb =>
    rw [cd_env] at ihb
    simp only [cd]
    rw [<- cd_env]
    simp only [cd_env, cdEval, envOf]
    exact (Par.lookup_some ihb (u := _) hl).elim fun u' hu' => by
      rw [hu'.1]; exact hu'.2
  | evalPair _ _ _ iha ihb ihe =>
    rw [cd_env] at ihe
    simp only [cd]
    rw [<- cd_env]
    simp only [cd_env, cdEval]
    exact .comb (.eval iha ihe) ihb ihe
  | evalApp _ _ iht ihe =>
    rw [cd_env] at ihe
    simp only [cd]
    rw [<- cd_env]
    simp only [cd_env, cdEval]
    exact .app (.eval iht ihe)
  | @beta v1 v1' v2 v2' v3 v3' body body' e1 e1' e2 e2' m hv1 hv2 hv3 _ _ _ hp3 _ _ hm
      ih1 ih2 ihb ih3 ihe1 ihe2 =>
    rw [cd_env] at ihe1 ihe2
    have hpat := Par.pattern hm (Par.pair ih1 ih2)
    simp only [Term.pair.injEq] at hpat
    exact (Par.ematch_some hm (Par.pair ih3 ihe2)).elim fun m2 hm2 => by
      simp only [cd]
      rw [<- cd_env, <- cd_env]
      simp only [cd_env, cdComb, cdBeta, (isValueB_iff v1).2 hv1, (isValueB_iff v2).2 hv2,
        (isValueB_iff v3).2 hv3, Bool.and_self, if_true, hpat.1, hpat.2, hm2.1]
      exact .eval ihb (Par.join hm2.2 ihe1)
  | @combApp t t' ts ts' bs bs' hl _ hts _ iht ihts ihe =>
    rw [cd_env] at ihe
    simp only [cd]
    rw [<- cd_env]
    simp only [cd_env, cdComb, (isListB_iff ts).2 hl, if_true]
    exact .comb iht (Par.evalList ihe ihts (hts.isList hl)) ihe
  | @deltaVau v1 v1' v2 v2' v3 v3' bs bs' hv1 hv2 hv3 _ _ _ _ ih1 ih2 ih3 ihe =>
    rw [cd_env] at ihe
    simp only [cd]
    rw [<- cd_env]
    simp only [cd_env, cdComb, cdDelta, (isValueB_iff v1).2 hv1, (isValueB_iff v2).2 hv2,
      (isValueB_iff v3).2 hv3, Bool.and_self, if_true]
    exact .oper ih1 ih2 ih3 ihe
  | @deltaWrap v v' bs hv _ ih =>
    simp only [cd]
    rw [<- cd_env]
    simp only [cd_env, cdComb, cdDelta, (isValueB_iff v).2 hv, if_true]
    exact .app ih
  | @deltaUnwrap v v' bs hv _ ih =>
    simp only [cd]
    rw [<- cd_env]
    simp only [cd_env, cdComb, cdDelta, (isValueB_iff v).2 hv, if_true]
    exact ih
  | @deltaEval v v' e1 e1' bs hv _ _ ih ihe =>
    rw [cd_env] at ihe
    simp only [cd]
    rw [<- cd_env, <- cd_env]
    simp only [cd_env, cdComb, cdDelta, (isValueB_iff v).2 hv, if_true]
    exact .eval ih ihe
  | @deltaListStar vs vs' r bs hv hvs hr ih =>
    exact (Par.buildListStar_some hr ih).elim fun r' hr' => by
      simp only [cd]
      rw [<- cd_env]
      simp only [cd_env, cdComb, cdDelta, (isValueB_iff vs).2 hv, if_true, hr'.1]
      exact hr'.2
  | capsule k _ ih => simp only [cd]; exact .capsule k ih
  | @deltaEncap v v' k bs hv _ ih =>
    simp only [cd]
    rw [<- cd_env]
    simp only [cd_env, cdComb, cdDelta, (isValueB_iff v).2 hv, if_true]
    exact .capsule k ih
  | @deltaIsEncap vs vs' b k bs hv hvs hc ih =>
    have hc' := Par.capsCheck_some (hvs.isValue hv) hc ih
    simp only [cd]
    rw [<- cd_env]
    simp only [cd_env, cdComb, cdDelta, (isValueB_iff vs).2 hv, if_true, hc']
    exact .dat _
  | @deltaDecap v v' k bs _ ih =>
    simp only [cd]
    rw [<- cd_env]
    simp only [cd_env, cdComb, cdDelta, if_true]
    exact ih

/-- The diamond property of parallel reduction. -/
theorem Par.diamond {t s1 s2 : Term} (h1 : Par t s1) (h2 : Par t s2) :
    exists u, Par s1 u /\ Par s2 u :=
  Exists.intro (cd t) (And.intro h1.to_cd h2.to_cd)

/-! ## Parallel steps and ordinary steps -/

namespace Steps
open Vau

theorem step_env_inv {l : Env} {b : Term} (h : Step (env l) b) : exists l', b = env l' := by
  cases h with
  | top h => cases h
  | envHere s r _ => exact Exists.intro _ rfl
  | envThere b _ => exact Exists.intro _ rfl

theorem envTail (x : Prod Nat Term) {r : Env} {b : Term} (h : Steps (env r) b) :
    exists l, b = env l /\ Steps (env (x :: r)) (env (x :: l)) := by
  induction h with
  | refl => exact Exists.intro r (And.intro rfl (.refl _))
  | tail _ hs ih =>
    exact ih.elim fun l hl => by
      have e1 := hl.1
      subst e1
      exact (step_env_inv hs).elim fun l' hl' => by
        subst hl'
        exact Exists.intro l' (And.intro rfl (Star.tail hl.2 (Step.envThere x hs)))

theorem envCons {s : Nat} {t t' : Term} {r r' : Env} (ht : Steps t t') (hr : Steps (env r) (env r')) :
    Steps (env ((s, t) :: r)) (env ((s, t') :: r')) := by
  refine Star.trans (Star.map (fun y => Term.env ((s, y) :: r)) (fun h => Step.envHere s r h) ht) ?_
  exact (envTail (s, t') hr).elim fun l hl => by
    have e1 : Term.env r' = Term.env l := hl.1
    cases e1
    exact hl.2

theorem oper {a a' b b' c c' d d' : Term} (ha : Steps a a') (hb : Steps b b') (hc : Steps c c')
    (hd : Steps d d') : Steps (Term.oper a b c d) (Term.oper a' b' c' d') :=
  Star.trans (Star.map (fun y => Term.oper y b c d) (fun h => Step.oper1 b c d h) ha)
    (Star.trans (Star.map (fun y => Term.oper a' y c d) (fun h => Step.oper2 a' c d h) hb)
      (Star.trans (Star.map (fun y => Term.oper a' b' y d) (fun h => Step.oper3 a' b' d h) hc)
        (Star.map (fun y => Term.oper a' b' c' y) (fun h => Step.oper4 a' b' c' h) hd)))

theorem eval {a a' b b' : Term} (ha : Steps a a') (hb : Steps b b') :
    Steps (Term.eval a b) (Term.eval a' b') :=
  Star.trans (Star.map (fun y => Term.eval y b) (fun h => Step.evalL b h) ha)
    (Star.map (fun y => Term.eval a' y) (fun h => Step.evalR a' h) hb)

theorem comb3 {a a' b b' c c' : Term} (ha : Steps a a') (hb : Steps b b') (hc : Steps c c') :
    Steps (Term.comb a b c) (Term.comb a' b' c') :=
  Star.trans (Steps.comb c ha hb)
    (Star.map (fun y => Term.comb a' b' y) (fun h => Step.comb3 a' b' h) hc)

theorem capsule {k : Nat} {v v' : Term} (h : Steps v v') : Steps (Term.capsule k v) (Term.capsule k v') :=
  Star.map (Term.capsule k) (fun h => Step.capsule k h) h

end Steps

theorem Par.of_top {t t' : Term} (h : Top t t') : Par t t' := by
  cases h with
  | evalSelf e hs => exact .evalSelf e hs (Par.refl _)
  | evalSym hl => exact .evalSym (Par.reflEnv _) hl
  | evalPair a b e => exact .evalPair (Par.refl a) (Par.refl b) (Par.reflEnv e)
  | evalApp t e => exact .evalApp (Par.refl t) (Par.reflEnv e)
  | beta hv1 hv2 hv3 hm =>
    exact .beta hv1 hv2 hv3 (Par.refl _) (Par.refl _) (Par.refl _) (Par.refl _)
      (Par.reflEnv _) (Par.reflEnv _) hm
  | combApp t e hl => exact .combApp hl (Par.refl t) (Par.refl _) (Par.reflEnv e)
  | deltaVau e hv1 hv2 hv3 =>
    exact .deltaVau hv1 hv2 hv3 (Par.refl _) (Par.refl _) (Par.refl _) (Par.reflEnv e)
  | deltaWrap e hv => exact .deltaWrap e hv (Par.refl _)
  | deltaUnwrap e hv => exact .deltaUnwrap e hv (Par.refl _)
  | deltaEval e1 e hv => exact .deltaEval e hv (Par.refl _) (Par.reflEnv e1)
  | deltaListStar e hv hr => exact .deltaListStar e hv (Par.refl _) hr
  | deltaEncap k e hv => exact .deltaEncap k e hv (Par.refl _)
  | deltaIsEncap k e hv hc => exact .deltaIsEncap k e hv (Par.refl _) hc
  | deltaDecap k e => exact .deltaDecap k e (Par.refl _)

theorem Par.of_step {t t' : Term} (h : Step t t') : Par t t' := by
  induction h with
  | top h => exact Par.of_top h
  | envHere s r _ ih => exact .envCons s ih (Par.reflEnv r)
  | envThere b _ ih => cases b with | mk s t => exact .envCons s (Par.refl t) ih
  | oper1 b c d _ ih => exact .oper ih (Par.refl b) (Par.refl c) (Par.refl d)
  | oper2 a c d _ ih => exact .oper (Par.refl a) ih (Par.refl c) (Par.refl d)
  | oper3 a b d _ ih => exact .oper (Par.refl a) (Par.refl b) ih (Par.refl d)
  | oper4 a b c _ ih => exact .oper (Par.refl a) (Par.refl b) (Par.refl c) ih
  | pairL b _ ih => exact .pair ih (Par.refl b)
  | pairR a _ ih => exact .pair (Par.refl a) ih
  | app _ ih => exact .app ih
  | evalL b _ ih => exact .eval ih (Par.refl b)
  | evalR a _ ih => exact .eval (Par.refl a) ih
  | comb1 b c _ ih => exact .comb ih (Par.refl b) (Par.refl c)
  | comb2 a c _ ih => exact .comb (Par.refl a) ih (Par.refl c)
  | comb3 a b _ ih => exact .comb (Par.refl a) (Par.refl b) ih
  | capsule k _ ih => exact .capsule k ih

theorem Par.toSteps {t t' : Term} (h : Par t t') : Steps t t' := by
  induction h with
  | dat n => exact .refl _
  | prim p => exact .refl _
  | sym s => exact .refl _
  | ign => exact .refl _
  | nil => exact .refl _
  | envNil => exact .refl _
  | envCons s _ _ iht ihr => exact Steps.envCons iht ihr
  | oper _ _ _ _ iha ihb ihc ihd => exact Steps.oper iha ihb ihc ihd
  | pair _ _ iha ihb => exact Steps.pair iha ihb
  | app _ ih => exact Steps.app ih
  | eval _ _ iha ihb => exact Steps.eval iha ihb
  | comb _ _ _ iha ihb ihc => exact Steps.comb3 iha ihb ihc
  | evalSelf bs hs _ ih => exact Vau.Star.head (Step.top (.evalSelf bs hs)) ih
  | evalSym _ hl ihb => exact (Steps.eval (Steps.refl _) ihb).trans (Steps.top (.evalSym hl))
  | evalPair _ _ _ iha ihb ihe =>
    exact (Steps.eval (Steps.pair iha ihb) ihe).trans (Steps.top (.evalPair _ _ _))
  | evalApp _ _ iht ihe =>
    exact (Steps.eval (Steps.app iht) ihe).trans (Steps.top (.evalApp _ _))
  | beta hv1 hv2 hv3 h1 h2 _ h3 _ _ hm ih1 ih2 ihb ih3 ihe1 ihe2 =>
    exact (Steps.comb3 (Steps.oper ih1 ih2 ihb ihe1) ih3 ihe2).trans
      (Steps.top (.beta (h1.isValue hv1) (h2.isValue hv2) (h3.isValue hv3) hm))
  | combApp hl _ hts _ iht ihts ihe =>
    exact (Steps.comb3 (Steps.app iht) ihts ihe).trans (Steps.top (.combApp _ _ (hts.isList hl)))
  | deltaVau hv1 hv2 hv3 h1 h2 h3 _ ih1 ih2 ih3 ihe =>
    exact (Steps.comb3 (Steps.refl _) (Steps.pair ih1 (Steps.pair ih2 (Steps.pair ih3 (Steps.refl _))))
      ihe).trans (Steps.top (.deltaVau _ (h1.isValue hv1) (h2.isValue hv2) (h3.isValue hv3)))
  | deltaWrap bs hv h ih =>
    exact (Steps.comb3 (Steps.refl _) (Steps.pair ih (Steps.refl _)) (Steps.refl _)).trans
      (Steps.top (.deltaWrap bs (h.isValue hv)))
  | deltaUnwrap bs hv h ih =>
    exact (Steps.comb3 (Steps.refl _) (Steps.pair (Steps.app ih) (Steps.refl _)) (Steps.refl _)).trans
      (Steps.top (.deltaUnwrap bs (h.isValue hv)))
  | deltaEval bs hv h _ ih ihe =>
    exact (Steps.comb3 (Steps.refl _) (Steps.pair ih (Steps.pair ihe (Steps.refl _))) (Steps.refl _)).trans
      (Steps.top (.deltaEval _ bs (h.isValue hv)))
  | deltaListStar bs hv h hr ih =>
    exact (Steps.comb3 (Steps.refl _) ih (Steps.refl _)).trans
      (Steps.top (.deltaListStar bs (h.isValue hv) hr))
  | capsule k _ ih => exact Steps.capsule ih
  | deltaEncap k bs hv h ih =>
    exact (Steps.comb3 (Steps.refl _) (Steps.pair ih (Steps.refl _)) (Steps.refl _)).trans
      (Steps.top (.deltaEncap k bs (h.isValue hv)))
  | deltaIsEncap k bs hv h hc ih =>
    exact (Steps.comb3 (Steps.refl _) ih (Steps.refl _)).trans
      (Steps.top (.deltaIsEncap k bs (h.isValue hv) hc))
  | deltaDecap k bs _ ih =>
    exact (Steps.comb3 (Steps.refl _) (Steps.pair (Steps.capsule ih) (Steps.refl _)) (Steps.refl _)).trans
      (Steps.top (.deltaDecap k bs))

theorem steps_iff_par_star {t t' : Term} : Steps t t' <-> Vau.Star Par t t' :=
  Iff.intro (Vau.Star.mono (fun h => Vau.Star.single (Par.of_step h))) (Vau.Star.mono Par.toSteps)

theorem Par.strip {t s1 s2 : Term} (h1 : Vau.Star Par t s1) (h2 : Par t s2) :
    exists u, Par s1 u /\ Vau.Star Par s2 u := by
  induction h1 with
  | refl => exact Exists.intro s2 (And.intro h2 (.refl _))
  | tail _ hbc ih =>
    exact ih.elim fun u hu =>
      (Par.diamond hbc hu.1).elim fun w hw =>
        Exists.intro w (And.intro hw.1 (.tail hu.2 hw.2))

theorem Par.star_confluent {t s1 s2 : Term} (h1 : Vau.Star Par t s1) (h2 : Vau.Star Par t s2) :
    exists u, Vau.Star Par s1 u /\ Vau.Star Par s2 u := by
  induction h2 with
  | refl => exact Exists.intro s1 (And.intro (.refl _) h1)
  | tail _ hbc ih =>
    exact ih.elim fun u hu =>
      (Par.strip hu.2 hbc).elim fun w hw =>
        Exists.intro w (And.intro (.tail hu.1 hw.1) hw.2)

/-- **Confluence of vau-e** (the rules of `VauE.Top`, compatible closure): if `t ->* s1` and
`t ->* s2`, then `s1 ->* u` and `s2 ->* u` for some `u`. -/
theorem confluence {t s1 s2 : Term} (h1 : Steps t s1) (h2 : Steps t s2) :
    exists u, Steps s1 u /\ Steps s2 u :=
  (Par.star_confluent (steps_iff_par_star.1 h1) (steps_iff_par_star.1 h2)).elim fun u hu =>
    Exists.intro u (And.intro (steps_iff_par_star.2 hu.1) (steps_iff_par_star.2 hu.2))

/-- Church-Rosser form: two terms that are equal in the equational theory of vau-e have a common
reduct. -/
theorem church_rosser {a b : Term} (h : Conv a b) : exists u, Steps a u /\ Steps b u := by
  induction h with
  | rel h => exact Exists.intro _ (And.intro (Vau.Star.single h) (.refl _))
  | refl t => exact Exists.intro t (And.intro (.refl _) (.refl _))
  | symm _ ih => exact ih.elim fun u hu => Exists.intro u (And.intro hu.2 hu.1)
  | trans _ _ ih1 ih2 =>
    exact ih1.elim fun u1 h1 => ih2.elim fun u2 h2 =>
      (confluence h1.2 h2.1).elim fun w hw =>
        Exists.intro w (And.intro (h1.1.trans hw.1) (h2.2.trans hw.2))

/-- `t` has no step. -/
def Normal (t : Term) : Prop := forall t', Not (Step t t')

theorem Steps.normal_eq {t t' : Term} (hn : Normal t) (h : Steps t t') : t = t' := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; exact absurd hs (hn _)

/-- **Normal forms are unique** in vau-e: a term reduces to at most one normal form. -/
theorem normal_unique {t n1 n2 : Term} (h1 : Steps t n1) (h2 : Steps t n2) (hn1 : Normal n1)
    (hn2 : Normal n2) : n1 = n2 :=
  (confluence h1 h2).elim fun u hu => by
    rw [Steps.normal_eq hn1 hu.1, Steps.normal_eq hn2 hu.2]

end VauE
