import Vau.Env.Reduction

/-!
# Derived `$lambda`, static and dynamic environments, wrap and unwrap

Kernel has no primitive `$lambda`. Shutt defines it (thesis (4.10)) as

```
($define! $lambda
   ($vau (ptree . body) static-env
      (wrap (eval (list* $vau ptree #ignore body) static-env))))
```

and states its intended behavior (4.9): `($lambda ptree x)` is equivalent to
`(wrap ($vau ptree #ignore x))`. This file proves, in vau-e (with one body expression, since
vau-e operatives have one body):

* `lambda_def`: evaluating the `$vau` expression of (4.10) in `e0` gives the compound operative
  `lambdaOp e0` (thesis (4.18));
* `lambda_expr`: evaluating `($lambda p b)` in `e1` gives `<applicative <operative p #ignore b e1>>`
  (thesis (4.20)-(4.22)): the environment `e1` where the `$lambda` expression is evaluated
  becomes the static environment;
* `lambda_call`: calling that applicative with operands evaluated in any environment `e2`
  evaluates `b` in `e1` extended with the parameters bound to the evaluated arguments; `e2` is
  ignored;
* `derived_lambda`: the two together, for `(($lambda p b) . args)` in one environment `e`;
* `lambda_static_scope`: the result of `($lambda p b)` in `e1`, called from another environment
  `e2`, runs its body in `e1`, not `e2`;
* `lambda_eq_wrap_vau`: (4.9): `($lambda p b)` and `(wrap ($vau p #ignore b))` reduce to the
  same term, so they are equal in the equational theory;
* `vau_call`: a compound operative made by `$vau` with environment parameter `d` evaluates its
  body in its static environment, extended with the operand bindings and `d` bound to the
  dynamic environment;
* `unwrap_wrap`: if `c` reduces to a value `v`, then `(unwrap (wrap c))` reduces to `v`.

Hypotheses are stated in the theorems: which symbols the environments bind, and that the
operands are values (source code is always a value, since it has no active subterm).
-/

namespace VauE
open Term

/-! ## Symbols and standard applicatives -/

/-! Symbols are numbers. These notations name the ones used here (they are not declarations). -/
scoped notation "sVau" => (0 : Nat)
scoped notation "sWrap" => (1 : Nat)
scoped notation "sEval" => (2 : Nat)
scoped notation "sListStar" => (3 : Nat)
scoped notation "sLambda" => (4 : Nat)
scoped notation "sPtree" => (5 : Nat)
scoped notation "sBody" => (6 : Nat)
scoped notation "sStatic" => (7 : Nat)
scoped notation "sUnwrap" => (8 : Nat)

/-- The applicative `wrap = <applicative $wrap>`. -/
abbrev wrapA : Term := app (prim .wrap)
/-- The applicative `unwrap = <applicative $unwrap>`. -/
abbrev unwrapA : Term := app (prim .unwrap)
/-- The applicative `eval = <applicative $eval>`. -/
abbrev evalA : Term := app (prim .eval)
/-- The applicative `list* = <applicative $list*>`. -/
abbrev listStarA : Term := app (prim .listStar)

/-- An environment with the standard bindings that the definition of `$lambda` uses:
`$vau`, `wrap`, `eval` and `list*` (the environment `e0` of thesis (4.18)). -/
structure Ground (e : Env) : Prop where
  vau : Env.lookup sVau e = some (prim .vau)
  wrap : Env.lookup sWrap e = some wrapA
  eval : Env.lookup sEval e = some evalA
  listStar : Env.lookup sListStar e = some listStarA

/-! ## The definition (4.10) as data -/

/-- `(list* $vau ptree #ignore body)`. -/
abbrev srcListStar : Term := pair (sym sListStar) (list4 (sym sVau) (sym sPtree) ign (sym sBody))
/-- `(eval (list* $vau ptree #ignore body) static-env)`. -/
abbrev srcEval : Term := list3 (sym sEval) srcListStar (sym sStatic)
/-- `(wrap (eval (list* $vau ptree #ignore body) static-env))`: the body of `$lambda`. -/
abbrev lambdaBody : Term := list2 (sym sWrap) srcEval
/-- `($vau (ptree . body) static-env (wrap ...))`: the source of `$lambda`. -/
abbrev lambdaSrc : Term := list4 (sym sVau) (pair (sym sPtree) (sym sBody)) (sym sStatic) lambdaBody

/-- The compound operative `$lambda`, with static environment `e0`. -/
abbrev lambdaOp (e0 : Env) : Term := oper (pair (sym sPtree) (sym sBody)) (sym sStatic) lambdaBody (env e0)

/-! ## Helpers -/

theorem disjoint_nil (xs : List Nat) : disjoint xs [] = true := by
  simp [disjoint]

/-- One rule at the top, then more steps. -/
theorem Steps.head {a b c : Term} (h : Top a b) (h2 : Steps b c) : Steps a c :=
  Vau.Star.head (Step.top h) h2

/-- Reduce the operator of a combination by one rule. -/
theorem Steps.combOp {f f' : Term} (x e : Term) (h : Top f f') :
    Steps (Term.comb f x e) (Term.comb f' x e) :=
  Steps.comb e (Steps.top h) (Steps.refl x)

/-! ## (4.18): evaluating the definition -/

/-- Evaluating the `$vau` expression of (4.10) in an environment where `$vau` is bound to the
primitive gives the compound operative `$lambda` with static environment `e0`. -/
theorem lambda_def {e0 : Env} (h0 : Env.lookup sVau e0 = some (prim .vau)) :
    Steps (eval lambdaSrc (env e0)) (lambdaOp e0) := by
  refine Steps.head (.evalPair _ _ _) ?_
  refine Steps.trans (Steps.combOp _ _ (.evalSym h0)) ?_
  refine Steps.top (.deltaVau _ ?_ ?_ ?_) <;> repeat (first | constructor)

/-! ## (4.20)-(4.22): evaluating `($lambda p b)` -/

/-- The local environment `e0'` of the call to `$lambda` (thesis (4.20)). -/
abbrev lambdaLocal (p b : Term) (e1 e0 : Env) : Env :=
  (sPtree, p) :: (sBody, list1 b) :: (sStatic, env e1) :: e0

/-- The list `($vau p #ignore b)` that `list*` builds, with the primitive `$vau` in it. -/
abbrev builtVau (p b : Term) : Term := list4 (prim .vau) p ign b

theorem lookup_local_ground {p b : Term} {e1 e0 : Env} {s : Nat} (hs : s < 5) :
    Env.lookup s (lambdaLocal p b e1 e0) = Env.lookup s e0 := by
  have h5 : (s = sPtree) = False := by simp only [eq_iff_iff, iff_false]; omega
  have h6 : (s = sBody) = False := by simp only [eq_iff_iff, iff_false]; omega
  have h7 : (s = sStatic) = False := by simp only [eq_iff_iff, iff_false]; omega
  simp only [Env.lookup, h5, h6, h7, if_false]

/-- `(list* $vau ptree #ignore body)` evaluates, in the local environment, to `($vau p #ignore b)`
with the primitive `$vau`. -/
theorem eval_srcListStar {p b : Term} {e1 e0 : Env} (h0 : Ground e0) (hp : IsValue p)
    (hb : IsValue b) :
    Steps (eval srcListStar (env (lambdaLocal p b e1 e0))) (builtVau p b) := by
  have hls : Env.lookup sListStar (lambdaLocal p b e1 e0) = some listStarA := by
    rw [lookup_local_ground (by decide)]; exact h0.listStar
  have hv : Env.lookup sVau (lambdaLocal p b e1 e0) = some (prim .vau) := by
    rw [lookup_local_ground (by decide)]; exact h0.vau
  refine Steps.head (.evalPair _ _ _) ?_
  refine Steps.trans (Steps.combOp _ _ (.evalSym hls)) ?_
  refine Steps.head (.combApp _ _ (by repeat constructor)) ?_
  refine Steps.trans (Steps.comb _ (Steps.refl _)
    (Steps.pair (Steps.top (.evalSym hv))
      (Steps.pair (Steps.top (.evalSym (t := p) rfl))
        (Steps.pair (Steps.top (.evalSelf _ .ign))
          (Steps.pair (Steps.top (.evalSym (t := list1 b) rfl))
            (Steps.refl _)))))) ?_
  refine Steps.top (.deltaListStar _ ?_ rfl)
  repeat (first | assumption | constructor)

/-- `(eval (list* ...) static-env)` evaluates, in the local environment, to the compound
operative `<operative p #ignore b e1>` (thesis (4.21)). -/
theorem eval_srcEval {p b : Term} {e1 e0 : Env} (h0 : Ground e0) (hp : IsValue p)
    (hb : IsValue b) :
    Steps (eval srcEval (env (lambdaLocal p b e1 e0))) (oper p ign b (env e1)) := by
  have he : Env.lookup sEval (lambdaLocal p b e1 e0) = some evalA := by
    rw [lookup_local_ground (by decide)]; exact h0.eval
  refine Steps.head (.evalPair _ _ _) ?_
  refine Steps.trans (Steps.combOp _ _ (.evalSym he)) ?_
  refine Steps.head (.combApp _ _ (by repeat constructor)) ?_
  refine Steps.trans (Steps.comb _ (Steps.refl _)
    (Steps.pair (eval_srcListStar h0 hp hb)
      (Steps.pair (Steps.top (.evalSym (t := env e1) rfl))
        (Steps.refl _)))) ?_
  refine Steps.head (.deltaEval _ _ (by repeat (first | assumption | constructor))) ?_
  refine Steps.head (.evalPair _ _ _) ?_
  refine Steps.trans (Steps.combOp _ _ (.evalSelf _ (.prim _))) ?_
  exact Steps.top (.deltaVau _ hp .ign hb)

/-- **Evaluating `($lambda p b)`** in `e1`, where `$lambda` is bound to the compound operative
of (4.10) with a static environment `e0` that has the standard bindings, gives
`<applicative <operative p #ignore b e1>>`. `e1` needs no other binding. -/
theorem lambda_expr {p b : Term} {e0 e1 : Env} (h0 : Ground e0)
    (h1 : Env.lookup sLambda e1 = some (lambdaOp e0)) (hp : IsValue p) (hb : IsValue b) :
    Steps (eval (list3 (sym sLambda) p b) (env e1)) (app (oper p ign b (env e1))) := by
  refine Steps.head (.evalPair _ _ _) ?_
  refine Steps.trans (Steps.combOp _ _ (.evalSym h1)) ?_
  have hm : ematch (pair (pair (sym sPtree) (sym sBody)) (sym sStatic)) (pair (list2 p b) (env e1))
      = some [(sPtree, p), (sBody, list1 b), (sStatic, env e1)] := rfl
  refine Steps.head (.beta (by repeat constructor) (.sym _) (by repeat (first | assumption | constructor)) hm) ?_
  have hw : Env.lookup sWrap (lambdaLocal p b e1 e0) = some wrapA := by
    rw [lookup_local_ground (by decide)]; exact h0.wrap
  refine Steps.head (.evalPair _ _ _) ?_
  refine Steps.trans (Steps.combOp _ _ (.evalSym hw)) ?_
  refine Steps.head (.combApp _ _ (by repeat constructor)) ?_
  refine Steps.trans (Steps.comb _ (Steps.refl _) (Steps.pair (eval_srcEval h0 hp hb) (Steps.refl _))) ?_
  exact Steps.top (.deltaWrap _ (.oper _ _ _ _))

/-! ## Calling the result -/

/-- **Calling the applicative made by `$lambda`.** The operands are evaluated in the dynamic
environment `e2`, to values `vs`. Then the body `b` is evaluated in the static environment `e1`,
extended with the bindings `m` of the parameter tree `p` to `vs`. `e2` itself is ignored. -/
theorem lambda_call {p b args vs : Term} {e1 e2 m : Env} (hp : IsValue p) (hargs : IsList args)
    (hev : Steps (evalList (env e2) args) vs) (hvs : IsValue vs) (hm : ematch p vs = some m) :
    Steps (comb (app (oper p ign b (env e1))) args (env e2)) (eval b (env (Env.join m e1))) := by
  refine Steps.head (.combApp _ _ hargs) ?_
  refine Steps.trans (Steps.comb _ (Steps.refl _) hev) ?_
  have hmatch : ematch (pair p ign) (pair vs (env e2)) = some (Env.join m []) := by
    simp only [ematch, syms, disjoint_nil, if_true, hm]
  have := Top.beta (body := b) (e1 := e1) hp .ign hvs hmatch
  rw [Env.join_emp] at this
  exact Steps.top this

/-- **Derived `$lambda`.** In an environment `e` where `$lambda` is bound to the compound
operative of (4.10) (made in a standard environment `e0`), the combination
`(($lambda p b) . args)` reduces to `b` evaluated in `e` extended with the parameters bound to the
evaluated arguments. (Here the static and the calling environment are the same `e`; see
`lambda_static_scope` for a call from a different environment.) -/
theorem derived_lambda {p b args vs : Term} {e0 e m : Env} (h0 : Ground e0)
    (h1 : Env.lookup sLambda e = some (lambdaOp e0)) (hp : IsValue p) (hb : IsValue b)
    (hargs : IsList args) (hev : Steps (evalList (env e) args) vs) (hvs : IsValue vs)
    (hm : ematch p vs = some m) :
    Steps (eval (pair (list3 (sym sLambda) p b) args) (env e)) (eval b (env (Env.join m e))) := by
  refine Steps.head (.evalPair _ _ _) ?_
  refine Steps.trans (Steps.comb _ (lambda_expr h0 h1 hp hb) (Steps.refl _)) ?_
  exact lambda_call hp hargs hev hvs hm

/-- **Static scope.** Evaluate `($lambda p b)` in `e1`, and bind the result `A` to a symbol `f` in
some other environment `e2`. Calling `(f . args)` from `e2` evaluates the arguments in `e2`, but runs
the body `b` in `e1` (extended with the parameters), not in `e2`. -/
theorem lambda_static_scope {p b args vs : Term} {e0 e1 e2 m : Env} {f : Nat} (h0 : Ground e0)
    (h1 : Env.lookup sLambda e1 = some (lambdaOp e0)) (hp : IsValue p) (hb : IsValue b)
    (hf : Env.lookup f e2 = some (app (oper p ign b (env e1))))
    (hargs : IsList args) (hev : Steps (evalList (env e2) args) vs) (hvs : IsValue vs)
    (hm : ematch p vs = some m) :
    Steps (eval (list3 (sym sLambda) p b) (env e1)) (app (oper p ign b (env e1))) /\
    Steps (eval (pair (sym f) args) (env e2)) (eval b (env (Env.join m e1))) := by
  refine And.intro (lambda_expr h0 h1 hp hb) ?_
  refine Steps.head (.evalPair _ _ _) ?_
  refine Steps.trans (Steps.combOp _ _ (.evalSym hf)) ?_
  exact lambda_call hp hargs hev hvs hm

/-! ## (4.9): `$lambda` is a wrapped `$vau` that ignores its dynamic environment -/

theorem wrap_vau_expr {p b : Term} {e : Env} (hw : Env.lookup sWrap e = some wrapA)
    (hv : Env.lookup sVau e = some (prim .vau)) (hp : IsValue p) (hb : IsValue b) :
    Steps (eval (list2 (sym sWrap) (list4 (sym sVau) p ign b)) (env e))
      (app (oper p ign b (env e))) := by
  refine Steps.head (.evalPair _ _ _) ?_
  refine Steps.trans (Steps.combOp _ _ (.evalSym hw)) ?_
  refine Steps.head (.combApp _ _ (by repeat constructor)) ?_
  have hin : Steps (eval (list4 (sym sVau) p ign b) (env e)) (oper p ign b (env e)) := by
    refine Steps.head (.evalPair _ _ _) ?_
    refine Steps.trans (Steps.combOp _ _ (.evalSym hv)) ?_
    exact Steps.top (.deltaVau _ hp .ign hb)
  refine Steps.trans (Steps.comb _ (Steps.refl _) (Steps.pair hin (Steps.refl _))) ?_
  exact Steps.top (.deltaWrap _ (.oper _ _ _ _))

/-- **Thesis (4.9).** Where `$lambda`, `wrap` and `$vau` have their standard bindings,
`($lambda p b)` and `(wrap ($vau p #ignore b))` reduce to the same applicative, so they are
equal in the equational theory of vau-e. -/
theorem lambda_eq_wrap_vau {p b : Term} {e0 e : Env} (h0 : Ground e0)
    (h1 : Env.lookup sLambda e = some (lambdaOp e0)) (hw : Env.lookup sWrap e = some wrapA)
    (hv : Env.lookup sVau e = some (prim .vau)) (hp : IsValue p) (hb : IsValue b) :
    Conv (eval (list3 (sym sLambda) p b) (env e))
      (eval (list2 (sym sWrap) (list4 (sym sVau) p ign b)) (env e)) :=
  Vau.EqvGen.trans (lambda_expr h0 h1 hp hb).toEqvGen
    (Vau.EqvGen.symm (wrap_vau_expr hw hv hp hb).toEqvGen)

/-! ## Static and dynamic environment of a compound operative -/

/-- **`$vau`: static and dynamic environment.** Calling `<operative p (sym d) b e1>` (as made by
`($vau p d b)` in `e1`) on a value operand tree `v` in a dynamic environment `e2` evaluates the
body in the static environment `e1`, extended with the operand bindings `m` and with `d` bound to
the dynamic environment `e2`. -/
theorem vau_call {p b v : Term} {d : Nat} {e1 e2 m : Env} (hp : IsValue p) (hv : IsValue v)
    (hd : disjoint (syms p) [d] = true) (hm : ematch p v = some m) :
    Steps (comb (oper p (sym d) b (env e1)) v (env e2))
      (eval b (env (Env.join (Env.join m [(d, env e2)]) e1))) := by
  have hmatch : ematch (pair p (sym d)) (pair v (env e2)) = some (Env.join m [(d, env e2)]) := by
    simp only [ematch, syms, hd, if_true, hm]
  exact Steps.top (.beta hp (.sym d) hv hmatch)

/-- In the body's environment of `vau_call`, `d` is the dynamic environment unless the parameter
tree binds `d` too (it cannot: `hd` says `d` is not in `p`), and other symbols not bound by `p`
are looked up in the static environment. -/
theorem vau_call_lookup (m e1 e2 : Env) (d s : Nat) (hms : Env.lookup s m = none) :
    Env.lookup s (Env.join (Env.join m [(d, env e2)]) e1)
      = if s = d then some (env e2) else Env.lookup s e1 := by
  simp only [Env.lookup_join, hms, Env.lookup, Option.none_or]
  split <;> simp

/-! ## wrap and unwrap -/

/-- **unwrap after wrap.** If `c` evaluates to a value `v` in `e`, and `wrap` and `unwrap` have
their standard bindings, then `(unwrap (wrap c))` evaluates to `v`. -/
theorem unwrap_wrap {c v : Term} {e : Env} (hw : Env.lookup sWrap e = some wrapA)
    (hu : Env.lookup sUnwrap e = some unwrapA) (hc : Steps (eval c (env e)) v) (hv : IsValue v) :
    Steps (eval (list2 (sym sUnwrap) (list2 (sym sWrap) c)) (env e)) v := by
  refine Steps.head (.evalPair _ _ _) ?_
  refine Steps.trans (Steps.combOp _ _ (.evalSym hu)) ?_
  refine Steps.head (.combApp _ _ (by repeat constructor)) ?_
  have hin : Steps (eval (list2 (sym sWrap) c) (env e)) (app v) := by
    refine Steps.head (.evalPair _ _ _) ?_
    refine Steps.trans (Steps.combOp _ _ (.evalSym hw)) ?_
    refine Steps.head (.combApp _ _ (by repeat constructor)) ?_
    refine Steps.trans (Steps.comb _ (Steps.refl _) (Steps.pair hc (Steps.refl _))) ?_
    exact Steps.top (.deltaWrap _ hv)
  refine Steps.trans (Steps.comb _ (Steps.refl _) (Steps.pair hin (Steps.refl _))) ?_
  exact Steps.top (.deltaUnwrap _ hv)

/-! ## A concrete check: the hypotheses can be met -/

/-- A standard environment with exactly the four bindings that `$lambda` needs. -/
abbrev groundEnv : Env :=
  [(sVau, prim .vau), (sWrap, wrapA), (sEval, evalA), (sListStar, listStarA)]

theorem ground_groundEnv : Ground groundEnv := Ground.mk rfl rfl rfl rfl

/-- An environment where `$lambda` is bound to the operative that (4.10) makes in `groundEnv`. -/
abbrev userEnv : Env := [(sLambda, lambdaOp groundEnv)]

/-- The source of `$lambda` really evaluates to `lambdaOp groundEnv`. -/
theorem lambda_def_ground : Steps (eval lambdaSrc (env groundEnv)) (lambdaOp groundEnv) :=
  lambda_def rfl

/-- `(($lambda (x) x) 7)` reduces to `7`, with `x` the symbol `9`. -/
theorem lambda_id_seven :
    Steps (eval (pair (list3 (sym sLambda) (list1 (sym 9)) (sym 9)) (list1 (dat 7))) (env userEnv))
      (dat 7) := by
  refine Steps.trans (derived_lambda (vs := list1 (dat 7)) (m := [(9, dat 7)])
    ground_groundEnv rfl (by repeat constructor) (.sym 9) (by repeat constructor)
    (Steps.pair (Steps.top (.evalSelf _ (.dat 7))) (Steps.refl _)) (by repeat constructor) rfl) ?_
  exact Steps.top (.evalSym rfl)

end VauE
