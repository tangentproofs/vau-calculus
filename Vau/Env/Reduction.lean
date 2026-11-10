import Vau.Env.Syntax

/-!
# vau-e: reduction rules

The general schemata (9.7) and the delta-rules for combiner primitives (9.12) of Shutt's vau-e
calculus, with this project's names:

| name        | rule                                                                    | thesis   |
|-------------|-------------------------------------------------------------------------|----------|
| eval-self   | `[eval S e] -> S`                                                       | (9.7S)   |
| eval-sym    | `[eval s e] -> lookup(s, e)`, if defined                                | (9.7s)   |
| eval-pair   | `[eval (T1 . T2) e] -> [combine [eval T1 e] T2 e]`                      | (9.7p)   |
| eval-app    | `[eval <applicative T> e] -> <applicative [eval T e]>`                  | (9.7a)   |
| beta-oper   | `[combine <operative V1 V2 T e1> V3 e2] -> [eval T match((V1 . V2), (V3 . e2)) . e1]` | (9.7beta) |
| combine-app | `[combine <applicative T> (T1 ... Tm) e] -> [combine T ([eval T1 e] ... [eval Tm e]) e]` | (9.7gamma) |
| delta-vau   | `[combine $vau (V1 V2 V3) e] -> <operative V1 V2 V3 e>`                 | (9.12)   |
| delta-wrap  | `[combine $wrap (V1) e] -> <applicative V1>`                            | (9.12)   |
| delta-unwrap| `[combine $unwrap (<applicative V1>) e] -> V1`                          | (9.12)   |
| delta-eval  | `[combine $eval (V1 e1) e] -> [eval V1 e1]`                             | this project |
| delta-list* | `[combine $list* (V1 ... Vn) e] -> (V1 ... Vn-1 . Vn)`                  | this project |

In (9.7a) the thesis text prints `[eval <applicative T>]` without its environment operand; we
read it as `[eval <applicative T> e] -> <applicative [eval T e]>`.

`Step` is the compatible closure: a rule may fire at any position, including inside the bindings
of an environment and inside every part of a compound operative. `Steps` is zero or more steps.
-/

namespace VauE
open Term

/-- The rules at the top of a term. -/
inductive Top : Term -> Term -> Prop where
  | evalSelf {s : Term} (e : Env) : SelfEval s -> Top (eval s (env e)) s
  | evalSym {s : Nat} {e : Env} {t : Term} : Env.lookup s e = some t -> Top (eval (sym s) (env e)) t
  | evalPair (a b : Term) (e : Env) : Top (eval (pair a b) (env e)) (comb (eval a (env e)) b (env e))
  | evalApp (t : Term) (e : Env) : Top (eval (app t) (env e)) (app (eval t (env e)))
  | beta {v1 v2 v3 body : Term} {e1 e2 m : Env} :
      IsValue v1 -> IsValue v2 -> IsValue v3 ->
      ematch (pair v1 v2) (pair v3 (env e2)) = some m ->
      Top (comb (oper v1 v2 body (env e1)) v3 (env e2)) (eval body (env (Env.join m e1)))
  | combApp {ts : Term} (t : Term) (e : Env) : IsList ts ->
      Top (comb (app t) ts (env e)) (comb t (evalList (env e) ts) (env e))
  | deltaVau {v1 v2 v3 : Term} (e : Env) : IsValue v1 -> IsValue v2 -> IsValue v3 ->
      Top (comb (prim .vau) (list3 v1 v2 v3) (env e)) (oper v1 v2 v3 (env e))
  | deltaWrap {v : Term} (e : Env) : IsValue v -> Top (comb (prim .wrap) (list1 v) (env e)) (app v)
  | deltaUnwrap {v : Term} (e : Env) : IsValue v ->
      Top (comb (prim .unwrap) (list1 (app v)) (env e)) v
  | deltaEval {v : Term} (e1 e : Env) : IsValue v ->
      Top (comb (prim .eval) (list2 v (env e1)) (env e)) (eval v (env e1))
  | deltaListStar {vs r : Term} (e : Env) : IsValue vs -> buildListStar vs = some r ->
      Top (comb (prim .listStar) vs (env e)) r
  /-- `[combine $encap_k (V) e] -> <capsule k V>` (this project's rule). -/
  | deltaEncap {v : Term} (k : Nat) (e : Env) : IsValue v ->
      Top (comb (prim (.encap k)) (list1 v) (env e)) (capsule k v)
  /-- `[combine $isEncap_k (V1 ... Vn) e] -> #t` if every `Vi` is a capsule of type `k`, else
  `#f`; `#t` and `#f` are `dat 1` and `dat 0` (this project's rule). -/
  | deltaIsEncap {vs : Term} {b : Bool} (k : Nat) (e : Env) : IsValue vs -> capsCheck k vs = some b ->
      Top (comb (prim (.isEncap k)) vs (env e)) (dat (if b then 1 else 0))
  /-- `[combine $decap_k (<capsule k V>) e] -> V` (this project's rule). -/
  | deltaDecap {v : Term} (k : Nat) (e : Env) :
      Top (comb (prim (.decap k)) (list1 (capsule k v)) (env e)) v

/-- One step: the compatible closure of `Top`. -/
inductive Step : Term -> Term -> Prop where
  | top {t t' : Term} : Top t t' -> Step t t'
  /-- A step inside the first binding of an environment. -/
  | envHere (s : Nat) {t t' : Term} (r : Env) : Step t t' -> Step (env ((s, t) :: r)) (env ((s, t') :: r))
  /-- A step inside a later binding of an environment. -/
  | envThere (b : Prod Nat Term) {r r' : Env} : Step (env r) (env r') -> Step (env (b :: r)) (env (b :: r'))
  | oper1 {a a' : Term} (b c d : Term) : Step a a' -> Step (oper a b c d) (oper a' b c d)
  | oper2 (a : Term) {b b' : Term} (c d : Term) : Step b b' -> Step (oper a b c d) (oper a b' c d)
  | oper3 (a b : Term) {c c' : Term} (d : Term) : Step c c' -> Step (oper a b c d) (oper a b c' d)
  | oper4 (a b c : Term) {d d' : Term} : Step d d' -> Step (oper a b c d) (oper a b c d')
  | pairL {a a' : Term} (b : Term) : Step a a' -> Step (pair a b) (pair a' b)
  | pairR (a : Term) {b b' : Term} : Step b b' -> Step (pair a b) (pair a b')
  | app {t t' : Term} : Step t t' -> Step (app t) (app t')
  | evalL {a a' : Term} (b : Term) : Step a a' -> Step (eval a b) (eval a' b)
  | evalR (a : Term) {b b' : Term} : Step b b' -> Step (eval a b) (eval a b')
  | comb1 {a a' : Term} (b c : Term) : Step a a' -> Step (comb a b c) (comb a' b c)
  | comb2 (a : Term) {b b' : Term} (c : Term) : Step b b' -> Step (comb a b c) (comb a b' c)
  | comb3 (a b : Term) {c c' : Term} : Step c c' -> Step (comb a b c) (comb a b c')
  | capsule (k : Nat) {v v' : Term} : Step v v' -> Step (capsule k v) (capsule k v')

/-- Zero or more steps. -/
abbrev Steps := Vau.Star Step

/-- The equational theory of vau-e. -/
abbrev Conv := Vau.EqvGen Step

namespace Steps
open Vau

theorem refl (t : Term) : Steps t t := Star.refl t

theorem trans {a b c : Term} (h1 : Steps a b) (h2 : Steps b c) : Steps a c := Star.trans h1 h2

theorem top {a b : Term} (h : Top a b) : Steps a b := Star.single (Step.top h)

theorem pair {a a' b b' : Term} (ha : Steps a a') (hb : Steps b b') :
    Steps (.pair a b) (.pair a' b') :=
  Star.trans (Star.map (fun x => Term.pair x b) (fun h => Step.pairL b h) ha)
    (Star.map (fun y => Term.pair a' y) (fun h => Step.pairR a' h) hb)

theorem app {t t' : Term} (h : Steps t t') : Steps (.app t) (.app t') :=
  Star.map Term.app (fun h => Step.app h) h

theorem evalL {a a' : Term} (b : Term) (h : Steps a a') : Steps (.eval a b) (.eval a' b) :=
  Star.map (fun x => Term.eval x b) (fun h => Step.evalL b h) h

theorem comb {a a' b b' : Term} (c : Term) (ha : Steps a a') (hb : Steps b b') :
    Steps (.comb a b c) (.comb a' b' c) :=
  Star.trans (Star.map (fun x => Term.comb x b c) (fun h => Step.comb1 b c h) ha)
    (Star.map (fun y => Term.comb a' y c) (fun h => Step.comb2 a' c h) hb)

end Steps

end VauE
