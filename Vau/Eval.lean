import Vau.Reduction

/-!
# Evaluation is a special case of reduction

Shutt's 2007 NEPLS talk says that explicit evaluation "makes term evaluation a special case of
term reduction". This file makes one precise version of that sentence.

`Run t r` is a **big-step evaluator** for vau-x, written in the style of a Lisp interpreter. It is
this project's own definition: the thesis gives no operational semantics for vau-x. `Run` is
defined by its own rules, independently of the compatible closure `Step`:

* data (atoms, operatives, pairs, applicatives) is run part by part, and an operative body is
  not entered;
* to run `[eval t]`: run `t` to a value; then a self-evaluating value is the result, a pair
  `(a . b)` continues as `[combine [eval a] b]`, and an applicative `<u>` gives `<f>` where
  `[eval u]` runs to `f`;
* to run `[combine f x]`: run `f` and `x` to values; then call the combiner. A `<vau x.T>`
  substitutes the operand, a wrapper `<c>` evaluates each operand of a proper list, a `<vau2.T>`
  takes a pair apart, and a `<vau0.T>` accepts `()`.

The headline `eval_is_reduction` says: if `[eval t]` runs to `v`, then `[eval t] ->* v`, and
`v` is a value. It is one direction only. Reduction has many steps that `Run` never takes (for
example, steps inside an operative body), so the converse is not claimed.
-/

namespace Vau
open Term

/-- Big-step evaluator for vau-x (this project's definition). -/
inductive Run : Term -> Term -> Prop where
  | var  (n : Nat) : Run (var n) (var n)
  | dat  (n : Nat) : Run (dat n) (dat n)
  | prim (n : Nat) : Run (prim n) (prim n)
  | ign : Run ign ign
  | nil : Run nil nil
  | vau  (t : Term) : Run (vau t) (vau t)
  | vau0 (t : Term) : Run (vau0 t) (vau0 t)
  | vau2 (t : Term) : Run (vau2 t) (vau2 t)
  | pair {a a' b b' : Term} : Run a a' -> Run b b' -> Run (pair a b) (pair a' b')
  | wrap {t t' : Term} : Run t t' -> Run (wrap t) (wrap t')
  | evalSelf {t s : Term} : Run t s -> SelfEval s -> Run (eval t) s
  | evalPair {t a b r : Term} : Run t (pair a b) -> Run (comb (eval a) b) r -> Run (eval t) r
  | evalWrap {t u f : Term} : Run t (wrap u) -> Run (eval u) f -> Run (eval t) (wrap f)
  | combVau {f x body v r : Term} :
      Run f (vau body) -> Run x v -> Run (inst body v) r -> Run (comb f x) r
  | combWrap {f x c xs r : Term} :
      Run f (wrap c) -> Run x xs -> IsList xs -> Run (comb c (evalList xs)) r -> Run (comb f x) r
  | combVau2 {f x c a b r : Term} :
      Run f (vau2 c) -> Run x (pair a b) -> Run (comb (comb c a) b) r -> Run (comb f x) r
  | combVau0 {f x c r : Term} : Run f (vau0 c) -> Run x nil -> Run c r -> Run (comb f x) r

/-- Every result of the evaluator is a value. -/
theorem Run.isValue {t r : Term} (h : Run t r) : IsValue r := by
  induction h with
  | var n => exact .var n
  | dat n => exact .dat n
  | prim n => exact .prim n
  | ign => exact .ign
  | nil => exact .nil
  | vau t => exact .vau t
  | vau0 t => exact .vau0 t
  | vau2 t => exact .vau2 t
  | pair _ _ iha ihb => exact .pair iha ihb
  | wrap _ ih => exact .wrap ih
  | evalSelf _ hs _ => exact hs.isValue
  | evalPair _ _ _ ih => exact ih
  | evalWrap _ _ _ ih => exact .wrap ih
  | combVau _ _ _ _ _ ih => exact ih
  | combWrap _ _ _ _ _ _ ih => exact ih
  | combVau2 _ _ _ _ _ ih => exact ih
  | combVau0 _ _ _ _ _ ih => exact ih

/-- Every run of the evaluator is a reduction sequence. -/
theorem Run.toSteps {t r : Term} (h : Run t r) : Steps t r := by
  induction h with
  | var n => exact .refl _
  | dat n => exact .refl _
  | prim n => exact .refl _
  | ign => exact .refl _
  | nil => exact .refl _
  | vau t => exact .refl _
  | vau0 t => exact .refl _
  | vau2 t => exact .refl _
  | pair _ _ iha ihb => exact Steps.pair iha ihb
  | wrap _ ih => exact Steps.wrap ih
  | evalSelf _ hs ih => exact (Steps.eval ih).trans (Steps.top (.evalSelf hs))
  | evalPair _ _ iht ihr =>
    exact ((Steps.eval iht).trans (Steps.top (.evalPair _ _))).trans ihr
  | evalWrap _ _ iht ihf =>
    exact ((Steps.eval iht).trans (Steps.top (.evalWrap _))).trans (Steps.wrap ihf)
  | combVau _ hx _ ihf ihx ihr =>
    exact ((Steps.comb ihf ihx).trans (Steps.top (.beta _ hx.isValue))).trans ihr
  | combWrap _ _ hl _ ihf ihx ihr =>
    exact ((Steps.comb ihf ihx).trans (Steps.top (.combWrap _ hl))).trans ihr
  | combVau2 _ _ _ ihf ihx ihr =>
    exact ((Steps.comb ihf ihx).trans (Steps.top (.parsePair _ _ _))).trans ihr
  | combVau0 _ _ _ ihf ihx ihr =>
    exact ((Steps.comb ihf ihx).trans (Steps.top (.parseNil _))).trans ihr

/-- **Evaluation is a special case of reduction.** If the evaluator runs `[eval t]` to `v`, then
`[eval t] ->* v` in the compatible closure of the vau-x rules, and `v` is a value. -/
theorem eval_is_reduction {t v : Term} (h : Run (eval t) v) : Steps (eval t) v /\ IsValue v :=
  And.intro h.toSteps h.isValue

/-! ## A worked example

`F = <vau2.<vau x.<vau0.x>>>` returns its single operand unevaluated. So `[eval (F (F 7))]`
runs to the data `(F 7)`. With the wrapper, `[eval (<F> (F 7))]` runs to `7`. These are the
examples on the Top node of the site. -/

/-- `<vau2.<vau x.<vau0.x>>>`. -/
abbrev F : Term := vau2 (vau (vau0 (var 0)))

/-- `(F 7)` as data. -/
abbrev F7 : Term := pair F (pair (dat 7) nil)

theorem run_F : Run F F := .vau2 _

theorem run_F7_data : Run F7 F7 := .pair run_F (.pair (.dat 7) .nil)

/-- `[combine <vau x.<vau0.x>> T] ->* <vau0.T>`, then `[combine <vau0.T> ()] -> T`. -/
theorem run_body {T : Term} (hT : Run T T) :
    Run (comb (comb (vau (vau0 (var 0))) T) nil) T := by
  refine .combVau0 (c := T) ?_ .nil hT
  refine .combVau (.vau _) hT ?_
  have : inst (vau0 (var 0)) T = vau0 T := rfl
  rw [this]
  exact .vau0 T

/-- `[eval (F 7)]` runs to `7`. -/
theorem run_F7 : Run (eval F7) (dat 7) :=
  .evalPair run_F7_data
    (.combVau2 (.evalSelf run_F (.vau2 _)) (.pair (.dat 7) .nil) (run_body (.dat 7)))

/-- `[eval (F (F 7))]` runs to the data `(F 7)`: the operand is not evaluated. -/
theorem run_F_F7 : Run (eval (pair F (pair F7 nil))) F7 :=
  .evalPair (.pair run_F (.pair run_F7_data .nil))
    (.combVau2 (.evalSelf run_F (.vau2 _)) (.pair run_F7_data .nil)
      (run_body run_F7_data))

/-- `[eval (<F> (F 7))]` runs to `7`: the wrapper evaluates the operand first. -/
theorem run_wrapF_F7 : Run (eval (pair (wrap F) (pair F7 nil))) (dat 7) :=
  .evalPair (.pair (.wrap run_F) (.pair run_F7_data .nil))
    (.combWrap (.evalWrap (.wrap run_F) (.evalSelf run_F (.vau2 _))) (.pair run_F7_data .nil)
      (.cons _ .nil)
      (.combVau2 run_F (.pair run_F7 .nil) (run_body (.dat 7))))

end Vau
