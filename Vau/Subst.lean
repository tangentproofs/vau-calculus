import Vau.Syntax

/-!
# Free variables and substitution

Shutt's substitution `T[x <- V]` (thesis (9.19)) is defined only for values `V`, and renames the
bound variable of `<vau x.T>` to a fresh one. With de Bruijn indices, no renaming is needed:
this file defines parallel renaming `rename` and parallel substitution `subst`, and the
single substitution `inst t v` (written `t[0 <- v]`), which replaces index `0` by `v` and lowers
the other free indices by one.

`inst` is defined for every term `v`. The reduction rule beta-vau uses it only when `v` is a
value, as in the thesis.
-/

namespace Vau
open Term

/-- Free variables, as de Bruijn indices. -/
def FreeIn : Nat -> Term -> Prop
  | n, var m => n = m
  | _, dat _ => False
  | _, prim _ => False
  | _, ign => False
  | _, nil => False
  | n, vau t => FreeIn (n + 1) t
  | n, vau0 t => FreeIn n t
  | n, vau2 t => FreeIn n t
  | n, pair a b => FreeIn n a \/ FreeIn n b
  | n, wrap t => FreeIn n t
  | n, eval t => FreeIn n t
  | n, comb a b => FreeIn n a \/ FreeIn n b

/-- Lift a renaming under one binder. -/
def lift (rn : Nat -> Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 => rn n + 1

/-- Parallel renaming of free variables. -/
def rename (rn : Nat -> Nat) : Term -> Term
  | var n => var (rn n)
  | dat n => dat n
  | prim n => prim n
  | ign => ign
  | nil => nil
  | vau t => vau (rename (lift rn) t)
  | vau0 t => vau0 (rename rn t)
  | vau2 t => vau2 (rename rn t)
  | pair a b => pair (rename rn a) (rename rn b)
  | wrap t => wrap (rename rn t)
  | eval t => eval (rename rn t)
  | comb a b => comb (rename rn a) (rename rn b)

/-- Lift a substitution under one binder. -/
def up (sg : Nat -> Term) : Nat -> Term
  | 0 => var 0
  | n + 1 => rename Nat.succ (sg n)

/-- Parallel substitution of terms for free variables. -/
def subst (sg : Nat -> Term) : Term -> Term
  | var n => sg n
  | dat n => dat n
  | prim n => prim n
  | ign => ign
  | nil => nil
  | vau t => vau (subst (up sg) t)
  | vau0 t => vau0 (subst sg t)
  | vau2 t => vau2 (subst sg t)
  | pair a b => pair (subst sg a) (subst sg b)
  | wrap t => wrap (subst sg t)
  | eval t => eval (subst sg t)
  | comb a b => comb (subst sg a) (subst sg b)

/-- `scons v sg` sends `0` to `v` and `n + 1` to `sg n`. -/
def scons (v : Term) (sg : Nat -> Term) : Nat -> Term
  | 0 => v
  | n + 1 => sg n

/-- Single substitution `t[0 <- v]`: the body `t` of `<vau x.t>` with `v` for `x`. -/
def inst (t v : Term) : Term := subst (scons v var) t

/-! ## The substitution algebra -/

theorem lift_comp (rn xi : Nat -> Nat) : Function.comp (lift rn) (lift xi) = lift (Function.comp rn xi) := by
  funext n; cases n <;> rfl

theorem rename_rename (rn xi : Nat -> Nat) (t : Term) :
    rename rn (rename xi t) = rename (Function.comp rn xi) t := by
  induction t generalizing rn xi with
  | vau t ih => simp only [rename, ih, lift_comp]
  | _ => simp_all [rename]

theorem up_comp_lift (sg : Nat -> Term) (xi : Nat -> Nat) : Function.comp (up sg) (lift xi) = up (Function.comp sg xi) := by
  funext n; cases n <;> rfl

theorem subst_rename (sg : Nat -> Term) (xi : Nat -> Nat) (t : Term) :
    subst sg (rename xi t) = subst (Function.comp sg xi) t := by
  induction t generalizing sg xi with
  | vau t ih => simp only [rename, subst, ih, up_comp_lift]
  | _ => simp_all [rename, subst]

theorem lift_comp_succ (rn : Nat -> Nat) : Function.comp (lift rn) Nat.succ = Function.comp Nat.succ rn := by
  funext n; rfl

theorem rename_comp_up (rn : Nat -> Nat) (sg : Nat -> Term) :
    Function.comp (rename (lift rn)) (up sg) = up (Function.comp (rename rn) sg) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Function.comp, up, rename_rename]
    rfl

theorem rename_subst (rn : Nat -> Nat) (sg : Nat -> Term) (t : Term) :
    rename rn (subst sg t) = subst (Function.comp (rename rn) sg) t := by
  induction t generalizing rn sg with
  | vau t ih => simp only [rename, subst, ih, rename_comp_up]
  | var n => rfl
  | _ => simp_all [rename, subst]

theorem up_comp_succ (sg : Nat -> Term) : Function.comp (up sg) Nat.succ = Function.comp (rename Nat.succ) sg := by
  funext n; rfl

theorem subst_comp_up (tg sg : Nat -> Term) :
    Function.comp (subst (up tg)) (up sg) = up (Function.comp (subst tg) sg) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Function.comp, up, subst_rename, rename_subst]
    rfl

theorem subst_subst (tg sg : Nat -> Term) (t : Term) :
    subst tg (subst sg t) = subst (Function.comp (subst tg) sg) t := by
  induction t generalizing tg sg with
  | vau t ih => simp only [subst, ih, subst_comp_up]
  | var n => rfl
  | _ => simp_all [subst]

theorem up_var : up var = var := by
  funext n; cases n <;> rfl

theorem subst_var (t : Term) : subst var t = t := by
  induction t with
  | vau t ih => simp only [subst, up_var, ih]
  | _ => simp_all [subst]

theorem up_var_comp (rn : Nat -> Nat) : up (Function.comp var rn) = Function.comp var (lift rn) := by
  funext n; cases n <;> rfl

/-- Renaming is a special case of substitution. -/
theorem rename_eq_subst (rn : Nat -> Nat) (t : Term) : rename rn t = subst (Function.comp var rn) t := by
  induction t generalizing rn with
  | vau t ih => simp only [rename, subst, ih, up_var_comp]
  | _ => simp_all [rename, subst]

/-- Substitution commutes with single substitution (the key lemma for beta-vau). -/
theorem subst_inst (sg : Nat -> Term) (t v : Term) :
    subst sg (inst t v) = inst (subst (up sg) t) (subst sg v) := by
  simp only [inst, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Function.comp, scons, up, subst, subst_rename]
    exact (subst_var (sg n)).symm

theorem rename_inst (rn : Nat -> Nat) (t v : Term) :
    rename rn (inst t v) = inst (rename (lift rn) t) (rename rn v) := by
  simp only [rename_eq_subst, subst_inst, up_var_comp]

/-! ## Values, self-evaluating terms and lists under renaming and substitution -/

theorem SelfEval.rename {s : Term} (rn : Nat -> Nat) (h : SelfEval s) : SelfEval (rename rn s) := by
  cases h <;> constructor

theorem SelfEval.subst {s : Term} (sg : Nat -> Term) (h : SelfEval s) : SelfEval (subst sg s) := by
  cases h <;> constructor

theorem IsValue.rename {v : Term} (rn : Nat -> Nat) (h : IsValue v) : IsValue (rename rn v) := by
  induction h generalizing rn with
  | pair _ _ iha ihb => exact .pair (iha rn) (ihb rn)
  | wrap _ ih => exact .wrap (ih rn)
  | _ => constructor

theorem IsValue.subst {v : Term} {sg : Nat -> Term} (hsg : forall n, IsValue (sg n)) (h : IsValue v) :
    IsValue (subst sg v) := by
  induction h with
  | var n => exact hsg n
  | pair _ _ iha ihb => exact .pair iha ihb
  | wrap _ ih => exact .wrap ih
  | _ => constructor

theorem IsValue.up {sg : Nat -> Term} (hsg : forall n, IsValue (sg n)) : forall n, IsValue (up sg n)
  | 0 => .var 0
  | n + 1 => (hsg n).rename Nat.succ

theorem IsValue.scons {v : Term} (hv : IsValue v) : forall n, IsValue (scons v Term.var n)
  | 0 => hv
  | n + 1 => .var n

theorem IsList.rename {t : Term} (rn : Nat -> Nat) (h : IsList t) : IsList (rename rn t) := by
  induction h with
  | nil => exact .nil
  | cons a _ ih => exact .cons _ ih

theorem IsList.subst {t : Term} (sg : Nat -> Term) (h : IsList t) : IsList (subst sg t) := by
  induction h with
  | nil => exact .nil
  | cons a _ ih => exact .cons _ ih

theorem IsList.evalList {t : Term} (h : IsList t) : IsList (evalList t) := by
  induction h with
  | nil => exact .nil
  | cons a _ ih => exact .cons _ ih

theorem rename_evalList {t : Term} (rn : Nat -> Nat) (h : IsList t) :
    rename rn (evalList t) = evalList (rename rn t) := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [evalList, rename, ih]

theorem subst_evalList {t : Term} (sg : Nat -> Term) (h : IsList t) :
    subst sg (evalList t) = evalList (subst sg t) := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [evalList, subst, ih]

end Vau
