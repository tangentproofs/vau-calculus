import Vau.Subst

/-!
# Reduction schemata and their compatible closure

The seven general schemata of vau-x (thesis (9.25)), with this project's names:

| name        | rule                                                              | thesis     |
|-------------|-------------------------------------------------------------------|------------|
| eval-self   | `[eval S] -> S`                                                   | (9.25S)    |
| eval-pair   | `[eval (T1 . T2)] -> [combine [eval T1] T2]`                      | (9.25p)    |
| eval-wrap   | `[eval <T>] -> <[eval T]>`                                        | (9.25a)    |
| beta-vau    | `[combine <vau x.T> V] -> T[x <- V]`                              | (9.25beta) |
| combine-wrap| `[combine <T0> (T1 ... Tm)] -> [combine T0 ([eval T1] ... [eval Tm])]` | (9.25gamma) |
| parse-pair  | `[combine <vau2.T0> (T1 . T2)] -> [combine [combine T0 T1] T2]`   | (9.25vau2) |
| parse-nil   | `[combine <vau0.T> ()] -> T`                                      | (9.25vau0) |

The delta-rule schema (9.25delta) is left out: the set of delta-rules is empty here.

`Top` is the rules at the top of a term. `Step` is their compatible closure: a rule may fire at
any position, including inside operands and inside operative bodies. `Steps` is zero or more
steps, and `Conv` is the equational theory (the equivalence closure of `Step`).
-/

namespace Vau
open Term

/-- The seven general schemata, at the top of a term. -/
inductive Top : Term -> Term -> Prop where
  | evalSelf {s : Term} : SelfEval s -> Top (eval s) s
  | evalPair (a b : Term) : Top (eval (pair a b)) (comb (eval a) b)
  | evalWrap (t : Term) : Top (eval (wrap t)) (wrap (eval t))
  | beta {v : Term} (t : Term) : IsValue v -> Top (comb (vau t) v) (inst t v)
  | combWrap {ts : Term} (t : Term) : IsList ts -> Top (comb (wrap t) ts) (comb t (evalList ts))
  | parsePair (t a b : Term) : Top (comb (vau2 t) (pair a b)) (comb (comb t a) b)
  | parseNil (t : Term) : Top (comb (vau0 t) nil) t

/-- One step: the compatible closure of `Top`. -/
inductive Step : Term -> Term -> Prop where
  | top {t t' : Term} : Top t t' -> Step t t'
  | vau  {t t' : Term} : Step t t' -> Step (vau t) (vau t')
  | vau0 {t t' : Term} : Step t t' -> Step (vau0 t) (vau0 t')
  | vau2 {t t' : Term} : Step t t' -> Step (vau2 t) (vau2 t')
  | wrap {t t' : Term} : Step t t' -> Step (wrap t) (wrap t')
  | eval {t t' : Term} : Step t t' -> Step (eval t) (eval t')
  | pairL {a a' : Term} (b : Term) : Step a a' -> Step (pair a b) (pair a' b)
  | pairR (a : Term) {b b' : Term} : Step b b' -> Step (pair a b) (pair a b')
  | combL {a a' : Term} (b : Term) : Step a a' -> Step (comb a b) (comb a' b)
  | combR (a : Term) {b b' : Term} : Step b b' -> Step (comb a b) (comb a b')

/-- Reflexive-transitive closure of a relation (defined here to avoid a Mathlib dependency). -/
inductive Star {X : Type} (r : X -> X -> Prop) : X -> X -> Prop where
  | refl (t : X) : Star r t t
  | tail {a b c : X} : Star r a b -> r b c -> Star r a c

/-- Zero or more steps, `->*`. -/
abbrev Steps := Star Step

/-- Equivalence closure of a relation. -/
inductive EqvGen {X : Type} (r : X -> X -> Prop) : X -> X -> Prop where
  | rel {a b : X} : r a b -> EqvGen r a b
  | refl (t : X) : EqvGen r t t
  | symm {a b : X} : EqvGen r a b -> EqvGen r b a
  | trans {a b c : X} : EqvGen r a b -> EqvGen r b c -> EqvGen r a c

/-- The equational theory of vau-x: `T1 = T2` iff they are joined by a zigzag of steps. -/
abbrev Conv := EqvGen Step

namespace Star
variable {X Y : Type} {r : X -> X -> Prop}

theorem single {a b : X} (h : r a b) : Star r a b := .tail (.refl a) h

theorem trans {a b c : X} (h1 : Star r a b) (h2 : Star r b c) : Star r a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hs ih => exact .tail ih hs

theorem head {a b c : X} (h1 : r a b) (h2 : Star r b c) : Star r a c :=
  trans (single h1) h2

/-- A closure is preserved by any map that preserves single steps. -/
theorem map {r' : Y -> Y -> Prop} (f : X -> Y) (hf : forall {a b}, r a b -> r' (f a) (f b))
    {a b : X} (h : Star r a b) : Star r' (f a) (f b) := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih => exact .tail ih (hf hs)

theorem mono {r' : X -> X -> Prop} (hr : forall {a b}, r a b -> Star r' a b) {a b : X}
    (h : Star r a b) : Star r' a b := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih => exact trans ih (hr hs)

theorem toEqvGen {a b : X} (h : Star r a b) : EqvGen r a b := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih => exact .trans ih (.rel hs)

end Star

/-! ## Congruence of `Steps` -/

namespace Steps

theorem vau {t t' : Term} (h : Steps t t') : Steps (.vau t) (.vau t') := Star.map Term.vau (fun h => Step.vau h) h
theorem vau0 {t t' : Term} (h : Steps t t') : Steps (.vau0 t) (.vau0 t') := Star.map Term.vau0 (fun h => Step.vau0 h) h
theorem vau2 {t t' : Term} (h : Steps t t') : Steps (.vau2 t) (.vau2 t') := Star.map Term.vau2 (fun h => Step.vau2 h) h
theorem wrap {t t' : Term} (h : Steps t t') : Steps (.wrap t) (.wrap t') := Star.map Term.wrap (fun h => Step.wrap h) h
theorem eval {t t' : Term} (h : Steps t t') : Steps (.eval t) (.eval t') := Star.map Term.eval (fun h => Step.eval h) h

theorem pair {a a' b b' : Term} (ha : Steps a a') (hb : Steps b b') :
    Steps (.pair a b) (.pair a' b') :=
  Star.trans (Star.map (fun x => Term.pair x b) (fun h => Step.pairL b h) ha)
    (Star.map (fun y => Term.pair a' y) (fun h => Step.pairR a' h) hb)

theorem comb {a a' b b' : Term} (ha : Steps a a') (hb : Steps b b') :
    Steps (.comb a b) (.comb a' b') :=
  Star.trans (Star.map (fun x => Term.comb x b) (fun h => Step.combL b h) ha)
    (Star.map (fun y => Term.comb a' y) (fun h => Step.combR a' h) hb)

theorem top {a b : Term} (h : Top a b) : Steps a b := Star.single (Step.top h)

end Steps

/-! ## Contexts: `Step` is compatible -/

/-- One-hole contexts. Plugging does not rename: a context may capture free variables of the
term put into the hole, as contexts do in the thesis. -/
inductive Ctx where
  | hole : Ctx
  | vau  : Ctx -> Ctx
  | vau0 : Ctx -> Ctx
  | vau2 : Ctx -> Ctx
  | wrap : Ctx -> Ctx
  | eval : Ctx -> Ctx
  | pairL : Ctx -> Term -> Ctx
  | pairR : Term -> Ctx -> Ctx
  | combL : Ctx -> Term -> Ctx
  | combR : Term -> Ctx -> Ctx

/-- Put a term into the hole of a context. -/
def Ctx.plug : Ctx -> Term -> Term
  | .hole, t => t
  | .vau c, t => .vau (c.plug t)
  | .vau0 c, t => .vau0 (c.plug t)
  | .vau2 c, t => .vau2 (c.plug t)
  | .wrap c, t => .wrap (c.plug t)
  | .eval c, t => .eval (c.plug t)
  | .pairL c b, t => .pair (c.plug t) b
  | .pairR a c, t => .pair a (c.plug t)
  | .combL c b, t => .comb (c.plug t) b
  | .combR a c, t => .comb a (c.plug t)

/-- `Step` is compatible: a step inside any one-hole context is a step of the whole term. -/
theorem Step.plug (c : Ctx) {t t' : Term} (h : Step t t') : Step (c.plug t) (c.plug t') := by
  induction c with
  | hole => exact h
  | vau _ ih => exact .vau ih
  | vau0 _ ih => exact .vau0 ih
  | vau2 _ ih => exact .vau2 ih
  | wrap _ ih => exact .wrap ih
  | eval _ ih => exact .eval ih
  | pairL _ b ih => exact .pairL b ih
  | pairR a _ ih => exact .pairR a ih
  | combL _ b ih => exact .combL b ih
  | combR a _ ih => exact .combR a ih

/-- Conversely, every step is a top-level rule inside some one-hole context. So `Step` is the
smallest compatible relation that contains the rules. -/
theorem Step.exists_ctx {t t' : Term} (h : Step t t') :
    exists (c : Ctx) (u u' : Term), Top u u' /\ t = c.plug u /\ t' = c.plug u' := by
  induction h with
  | top h => exact Exists.intro Ctx.hole (Exists.intro _ (Exists.intro _ (And.intro h (And.intro rfl rfl))))
  | vau _ ih => exact ih.elim fun c hc => Exists.intro (Ctx.vau c) (by simpa [Ctx.plug] using hc)
  | vau0 _ ih => exact ih.elim fun c hc => Exists.intro (Ctx.vau0 c) (by simpa [Ctx.plug] using hc)
  | vau2 _ ih => exact ih.elim fun c hc => Exists.intro (Ctx.vau2 c) (by simpa [Ctx.plug] using hc)
  | wrap _ ih => exact ih.elim fun c hc => Exists.intro (Ctx.wrap c) (by simpa [Ctx.plug] using hc)
  | eval _ ih => exact ih.elim fun c hc => Exists.intro (Ctx.eval c) (by simpa [Ctx.plug] using hc)
  | pairL b _ ih => exact ih.elim fun c hc => Exists.intro (Ctx.pairL c b) (by simpa [Ctx.plug] using hc)
  | pairR a _ ih => exact ih.elim fun c hc => Exists.intro (Ctx.pairR a c) (by simpa [Ctx.plug] using hc)
  | combL b _ ih => exact ih.elim fun c hc => Exists.intro (Ctx.combL c b) (by simpa [Ctx.plug] using hc)
  | combR a _ ih => exact ih.elim fun c hc => Exists.intro (Ctx.combR a c) (by simpa [Ctx.plug] using hc)

theorem Steps.plug (c : Ctx) {t t' : Term} (h : Steps t t') : Steps (c.plug t) (c.plug t') :=
  Star.map c.plug (fun h => Step.plug c h) h

theorem Conv.plug (c : Ctx) {t t' : Term} (h : Conv t t') : Conv (c.plug t) (c.plug t') := by
  induction h with
  | rel h => exact .rel (Step.plug c h)
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

/-! ## Normal forms -/

/-- `t` has no step. -/
def Normal (t : Term) : Prop := forall t', Not (Step t t')

theorem normal_dat (n : Nat) : Normal (.dat n) := by
  intro t' h
  cases h with
  | top h => cases h

theorem Steps.normal_eq {t t' : Term} (hn : Normal t) (h : Steps t t') : t = t' := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; exact absurd hs (hn _)

end Vau
