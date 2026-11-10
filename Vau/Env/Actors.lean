import Vau.Env.Encapsulation

/-!
# An actor-style evaluator with concurrent operand evaluation

Dale Schumacher implements a Kernel-like language with actors in his language Humus ("Fexpr the
Ultimate Lambda" and "Semantic Extensibility with Vau", 2011). In his design:

* an expression is an actor that answers an `#eval` request: a pair evaluates its left part with a
  new customer `k_comb`, and `k_comb` sends a `#comb` request with the right part to the combiner
  that comes back;
* a combiner answers a `#comb` request; an applicative evaluates its operands with a `#map`
  request, which uses a fork/join pair to evaluate the operands **concurrently**, then sends
  `#comb` to its underlying combiner;
* an environment answers `#lookup`.

This file models that structure for the Lean vau-e and relates it to vau-e reduction.

**The model** (this project's). A configuration `Conf` is a tree. Its leaves are pending messages
(`evalM` for `#eval`, `combM` for `#comb`) and replies (`ret`); its inner nodes are customers that
wait for replies: `kComb` (Schumacher's `k_comb`), `kWrap` (waits for the combiner inside an
applicative that is being evaluated), `fork` (a fork/join pair), and `kArgs` (an applicative that
waits for its evaluated arguments). `Deliver c c'` delivers one message or reply. A message may be
delivered anywhere in the tree, so both branches of a fork run in any interleaving. A symbol lookup
is one delivery (Schumacher's environment actors forward `#lookup` to their parent; that chain is
not modeled step by step).

**Not modeled:** actor addresses, mailboxes, message order and fairness, actor state changes other
than the customers above, environment mutation (Schumacher's `&define!` and `#bind`; without
mutation there are no races), concurrent parameter matching (here `match` is one step), and Humus
itself. In Schumacher's posts an applicative evaluates to itself; here evaluating an applicative
follows Shutt's (9.7a), as in the rest of the Lean vau-e. The theorems are about this tree model, not about
Schumacher's code or a general actor semantics.

Results:

* `deliver_sound`, `actor_sound`: read a configuration back as a vau-e term (`readback`). Every
  delivery is zero or one vau-e step, so every actor run is a vau-e reduction;
* `actor_eval_sound`: if the actor evaluator replies `v` to `[eval t e]`, then `[eval t e] ->* v`;
* `actor_determinate`: any two runs (any two interleavings) that reply primitive data reply the
  same data;
* `actor_results_join`: any two replies can be reduced to a common term;
* `fork_interleave`: two deliveries in the two branches of a fork can be done in either order, and
  both orders reach the same configuration.
-/

namespace VauE
open Term

/-- Actor configurations, as a tree of pending messages and waiting customers. -/
inductive Conf where
  /-- A reply carrying a value to the customer above. -/
  | ret : Term -> Conf
  /-- A pending `#eval` message: evaluate `t` in `e`. -/
  | evalM : Term -> Term -> Conf
  /-- A pending `#comb` message: combiner `f`, operand tree `x`, dynamic environment `e`. -/
  | combM : Term -> Term -> Term -> Conf
  /-- Customer `k_comb`: waits for the operator, then sends `#comb` with operands `x` and `e`. -/
  | kComb : Conf -> Term -> Term -> Conf
  /-- Customer: waits for the evaluated combiner inside an applicative, then wraps it. -/
  | kWrap : Conf -> Conf
  /-- A fork/join pair: two requests run concurrently; the join replies with the pair. -/
  | fork : Conf -> Conf -> Conf
  /-- Customer: an applicative with underlying combiner `c` waits for its evaluated arguments,
  then sends `#comb` to `c`. -/
  | kArgs : Conf -> Term -> Term -> Conf

open Conf

/-- The concurrent `#map` of `#eval` over an operand list: one fork per element. -/
def evalArgs (e : Term) : Term -> Conf
  | .pair x rest => fork (evalM x e) (evalArgs e rest)
  | t => ret t

/-- Read a configuration back as a vau-e term. -/
def readback : Conf -> Term
  | ret v => v
  | evalM t e => Term.eval t e
  | combM f x e => Term.comb f x e
  | kComb c x e => Term.comb (readback c) x e
  | kWrap c => Term.app (readback c)
  | fork c1 c2 => Term.pair (readback c1) (readback c2)
  | kArgs c f e => Term.comb f (readback c) e

/-- Delivering one message or reply. -/
inductive Deliver : Conf -> Conf -> Prop where
  /-- `#eval` to a self-evaluating object: it replies itself. -/
  | evalSelf {s : Term} (bs : Env) : SelfEval s -> Deliver (evalM s (env bs)) (ret s)
  /-- `#eval` to a symbol: the environment replies the bound value. -/
  | evalSym {s : Nat} {bs : Env} {t : Term} : Env.lookup s bs = some t ->
      Deliver (evalM (sym s) (env bs)) (ret t)
  /-- `#eval` to a pair: evaluate the left part, with customer `k_comb`. -/
  | evalPair (a b : Term) (bs : Env) :
      Deliver (evalM (pair a b) (env bs)) (kComb (evalM a (env bs)) b (env bs))
  /-- `#eval` to an applicative: evaluate the combiner inside, then wrap it. -/
  | evalApp (t : Term) (bs : Env) : Deliver (evalM (app t) (env bs)) (kWrap (evalM t (env bs)))
  /-- `k_comb` receives the operator and sends `#comb`. -/
  | replyComb (f b e : Term) : Deliver (kComb (ret f) b e) (combM f b e)
  /-- The wrapping customer receives the combiner. -/
  | replyWrap (v : Term) : Deliver (kWrap (ret v)) (ret (app v))
  /-- The join receives both replies. -/
  | join (v1 v2 : Term) : Deliver (fork (ret v1) (ret v2)) (ret (pair v1 v2))
  /-- The applicative receives its arguments and sends `#comb` to its underlying combiner. -/
  | replyArgs (vs c e : Term) : Deliver (kArgs (ret vs) c e) (combM c vs e)
  /-- `#comb` to an applicative: evaluate the operands concurrently. -/
  | combApp {ts : Term} (c : Term) (bs : Env) : IsList ts ->
      Deliver (combM (app c) ts (env bs)) (kArgs (evalArgs (env bs) ts) c (env bs))
  /-- `#comb` to a compound operative: evaluate the body in the extended static environment. -/
  | beta {v1 v2 v3 body : Term} {e1 e2 m : Env} : IsValue v1 -> IsValue v2 -> IsValue v3 ->
      ematch (pair v1 v2) (pair v3 (env e2)) = some m ->
      Deliver (combM (oper v1 v2 body (env e1)) v3 (env e2)) (evalM body (env (Env.join m e1)))
  | deltaVau {v1 v2 v3 : Term} (bs : Env) : IsValue v1 -> IsValue v2 -> IsValue v3 ->
      Deliver (combM (prim .vau) (list3 v1 v2 v3) (env bs)) (ret (oper v1 v2 v3 (env bs)))
  | deltaWrap {v : Term} (bs : Env) : IsValue v ->
      Deliver (combM (prim .wrap) (list1 v) (env bs)) (ret (app v))
  | deltaUnwrap {v : Term} (bs : Env) : IsValue v ->
      Deliver (combM (prim .unwrap) (list1 (app v)) (env bs)) (ret v)
  | deltaEval {v : Term} (e1 bs : Env) : IsValue v ->
      Deliver (combM (prim .eval) (list2 v (env e1)) (env bs)) (evalM v (env e1))
  | deltaListStar {vs r : Term} (bs : Env) : IsValue vs -> buildListStar vs = some r ->
      Deliver (combM (prim .listStar) vs (env bs)) (ret r)
  | deltaEncap {v : Term} (k : Nat) (bs : Env) : IsValue v ->
      Deliver (combM (prim (.encap k)) (list1 v) (env bs)) (ret (capsule k v))
  | deltaIsEncap {vs : Term} {b : Bool} (k : Nat) (bs : Env) : IsValue vs -> capsCheck k vs = some b ->
      Deliver (combM (prim (.isEncap k)) vs (env bs)) (ret (dat (if b then 1 else 0)))
  | deltaDecap {v : Term} (k : Nat) (bs : Env) :
      Deliver (combM (prim (.decap k)) (list1 (capsule k v)) (env bs)) (ret v)
  /-- Deliveries inside waiting customers and inside either branch of a fork (concurrency). -/
  | inComb {c c' : Conf} (b e : Term) : Deliver c c' -> Deliver (kComb c b e) (kComb c' b e)
  | inWrap {c c' : Conf} : Deliver c c' -> Deliver (kWrap c) (kWrap c')
  | forkL {c1 c1' : Conf} (c2 : Conf) : Deliver c1 c1' -> Deliver (fork c1 c2) (fork c1' c2)
  | forkR (c1 : Conf) {c2 c2' : Conf} : Deliver c2 c2' -> Deliver (fork c1 c2) (fork c1 c2')
  | inArgs {c c' : Conf} (f e : Term) : Deliver c c' -> Deliver (kArgs c f e) (kArgs c' f e)

/-- An actor run: zero or more deliveries. -/
abbrev ActorRun := Vau.Star Deliver

theorem readback_evalArgs (e : Term) : forall ts : Term, readback (evalArgs e ts) = evalList e ts
  | .pair x rest => by simp only [evalArgs, readback, evalList, readback_evalArgs e rest]
  | .dat _ => rfl
  | .prim _ => rfl
  | .sym _ => rfl
  | .ign => rfl
  | .nil => rfl
  | .env _ => rfl
  | .oper _ _ _ _ => rfl
  | .app _ => rfl
  | .eval _ _ => rfl
  | .comb _ _ _ => rfl
  | .capsule _ _ => rfl

/-- **Soundness of one delivery.** Every delivery is zero or one vau-e step on the read-back term. -/
theorem deliver_sound {c c' : Conf} (h : Deliver c c') : Steps (readback c) (readback c') := by
  induction h with
  | evalSelf bs hs => exact Steps.top (.evalSelf bs hs)
  | evalSym hl => exact Steps.top (.evalSym hl)
  | evalPair a b bs => exact Steps.top (.evalPair a b bs)
  | evalApp t bs => exact Steps.top (.evalApp t bs)
  | replyComb f b e => exact Steps.refl _
  | replyWrap v => exact Steps.refl _
  | join v1 v2 => exact Steps.refl _
  | replyArgs vs c e => exact Steps.refl _
  | combApp c bs hl =>
    simp only [readback, readback_evalArgs]
    exact Steps.top (.combApp c bs hl)
  | beta hv1 hv2 hv3 hm => exact Steps.top (.beta hv1 hv2 hv3 hm)
  | deltaVau bs hv1 hv2 hv3 => exact Steps.top (.deltaVau bs hv1 hv2 hv3)
  | deltaWrap bs hv => exact Steps.top (.deltaWrap bs hv)
  | deltaUnwrap bs hv => exact Steps.top (.deltaUnwrap bs hv)
  | deltaEval e1 bs hv => exact Steps.top (.deltaEval e1 bs hv)
  | deltaListStar bs hv hr => exact Steps.top (.deltaListStar bs hv hr)
  | deltaEncap k bs hv => exact Steps.top (.deltaEncap k bs hv)
  | deltaIsEncap k bs hv hc => exact Steps.top (.deltaIsEncap k bs hv hc)
  | deltaDecap k bs => exact Steps.top (.deltaDecap k bs)
  | inComb b e _ ih => exact Steps.comb _ ih (Steps.refl _)
  | inWrap _ ih => exact Steps.app ih
  | forkL c2 _ ih => exact Steps.pair ih (Steps.refl _)
  | forkR c1 _ ih => exact Steps.pair (Steps.refl _) ih
  | inArgs f e _ ih => exact Steps.comb _ (Steps.refl _) ih

/-- **Soundness of runs.** Every actor run is a vau-e reduction of the read-back terms. -/
theorem actor_sound {c c' : Conf} (h : ActorRun c c') : Steps (readback c) (readback c') := by
  induction h with
  | refl => exact Steps.refl _
  | tail _ hd ih => exact ih.trans (deliver_sound hd)

/-- If the actor evaluator, started with an `#eval` request for `t` in `e`, replies `v` (in any
interleaving), then `[eval t e] ->* v` in vau-e. -/
theorem actor_eval_sound {t v : Term} {e : Env} (h : ActorRun (evalM t (env e)) (ret v)) :
    Steps (Term.eval t (env e)) v :=
  actor_sound h

/-- **Determinacy of results.** Any two runs from the same configuration (any two interleavings of
the concurrent deliveries) that reply primitive data reply the same data. -/
theorem actor_determinate {c : Conf} {n1 n2 : Nat} (h1 : ActorRun c (ret (dat n1)))
    (h2 : ActorRun c (ret (dat n2))) : n1 = n2 := by
  have := normal_unique (actor_sound h1) (actor_sound h2) (normal_dat n1) (normal_dat n2)
  cases this
  rfl

/-- Any two replies from the same configuration can be reduced to a common term (by confluence of
vau-e). -/
theorem actor_results_join {c : Conf} {v1 v2 : Term} (h1 : ActorRun c (ret v1))
    (h2 : ActorRun c (ret v2)) : exists u, Steps v1 u /\ Steps v2 u :=
  confluence (actor_sound h1) (actor_sound h2)

/-- **Concurrency.** Two deliveries in the two branches of a fork can be done in either order:
left then right, or right then left, and both orders reach the same configuration. -/
theorem fork_interleave {c1 c1' c2 c2' : Conf} (h1 : Deliver c1 c1') (h2 : Deliver c2 c2') :
    (Deliver (fork c1 c2) (fork c1' c2) /\ Deliver (fork c1' c2) (fork c1' c2')) /\
    (Deliver (fork c1 c2) (fork c1 c2') /\ Deliver (fork c1 c2') (fork c1' c2')) :=
  And.intro (And.intro (Deliver.forkL c2 h1) (Deliver.forkR c1' h2))
    (And.intro (Deliver.forkR c1 h2) (Deliver.forkL c2' h1))

/-! ## A complete run -/

/-- `(f 5 6)` where `f` (symbol 0) is the applicative `list*`: the two operands are evaluated in a
fork, and the run replies `(5 . 6)`. -/
theorem actor_example :
    ActorRun (evalM (list3 (sym 0) (dat 5) (dat 6)) (env [(0, app (prim .listStar))]))
      (ret (pair (dat 5) (dat 6))) := by
  refine Vau.Star.head (Deliver.evalPair _ _ _) ?_
  refine Vau.Star.head (Deliver.inComb _ _ (Deliver.evalSym rfl)) ?_
  refine Vau.Star.head (Deliver.replyComb _ _ _) ?_
  refine Vau.Star.head (Deliver.combApp _ _ (by repeat constructor)) ?_
  -- the second operand is evaluated first here: any order is allowed
  refine Vau.Star.head (Deliver.inArgs _ _ (Deliver.forkR _ (Deliver.forkL _ (Deliver.evalSelf _ (.dat 6))))) ?_
  refine Vau.Star.head (Deliver.inArgs _ _ (Deliver.forkL _ (Deliver.evalSelf _ (.dat 5)))) ?_
  refine Vau.Star.head (Deliver.inArgs _ _ (Deliver.forkR _ (Deliver.join _ _))) ?_
  refine Vau.Star.head (Deliver.inArgs _ _ (Deliver.join _ _)) ?_
  refine Vau.Star.head (Deliver.replyArgs _ _ _) ?_
  exact Vau.Star.single (Deliver.deltaListStar _ (by repeat constructor) rfl)

end VauE
