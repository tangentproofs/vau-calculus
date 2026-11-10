/-!
# Syntax of the pure vau-x calculus

This file follows the syntax of Shutt's vau-x calculus (PhD thesis, WPI 2010, section 9.3,
schema group (9.25)):

```
S ::= d | o | #ignore | () | <vau2.T> | <vau0.T> | <vau x.T>     (self-evaluating terms)
A ::= [eval T] | [combine T T]                                   (active terms)
T ::= S | x | (T . T) | <T> | A                                  (terms)
V  =  terms whose every active subterm is within an operative     (values)
```

Representation choices (this project's, not Shutt's):

* Variables are de Bruijn indices. `vau t` binds index `0` in `t`. So terms are identified up to
  renaming of bound variables, and substitution needs no fresh-name renaming.
* Primitive data `d` and primitive operatives `o` are indexed by natural numbers.
* There are **no delta-rules**: primitive operatives have no rule of their own (the set of
  delta-rules is empty). See `Vau/Reduction.lean`.
-/

namespace Vau

/-- Terms of vau-x. -/
inductive Term where
  /-- A variable, as a de Bruijn index. -/
  | var  : Nat -> Term
  /-- Primitive data `d`. -/
  | dat  : Nat -> Term
  /-- A primitive operative `o`. It has no delta-rule in this formalization. -/
  | prim : Nat -> Term
  /-- `#ignore`. -/
  | ign  : Term
  /-- The empty list `()`. -/
  | nil  : Term
  /-- The compound operative `<vau x.T>`. It binds de Bruijn index `0` in its body. -/
  | vau  : Term -> Term
  /-- The compound operative `<vau0.T>`. It binds nothing. -/
  | vau0 : Term -> Term
  /-- The compound operative `<vau2.T>`. It binds nothing. -/
  | vau2 : Term -> Term
  /-- A pair `(T1 . T2)`. -/
  | pair : Term -> Term -> Term
  /-- An applicative `<T>`: the combiner `T` in a wrapper. -/
  | wrap : Term -> Term
  /-- The active term `[eval T]`. -/
  | eval : Term -> Term
  /-- The active term `[combine T1 T2]`. -/
  | comb : Term -> Term -> Term
  deriving DecidableEq, Repr

open Term

/-- Self-evaluating terms `S`. -/
inductive SelfEval : Term -> Prop where
  | dat  (n : Nat) : SelfEval (dat n)
  | prim (n : Nat) : SelfEval (prim n)
  | ign : SelfEval ign
  | nil : SelfEval nil
  | vau  (t : Term) : SelfEval (vau t)
  | vau0 (t : Term) : SelfEval (vau0 t)
  | vau2 (t : Term) : SelfEval (vau2 t)

/-- Values: every active subterm is within (the body of) a compound operative. Variables are
values, because they have no active subterm. -/
inductive IsValue : Term -> Prop where
  | var  (n : Nat) : IsValue (var n)
  | dat  (n : Nat) : IsValue (dat n)
  | prim (n : Nat) : IsValue (prim n)
  | ign : IsValue ign
  | nil : IsValue nil
  | vau  (t : Term) : IsValue (vau t)
  | vau0 (t : Term) : IsValue (vau0 t)
  | vau2 (t : Term) : IsValue (vau2 t)
  | pair {a b : Term} : IsValue a -> IsValue b -> IsValue (pair a b)
  | wrap {t : Term} : IsValue t -> IsValue (wrap t)

/-- Proper lists `(T1 ... Tm)`: nested pairs that end in `()`. -/
inductive IsList : Term -> Prop where
  | nil : IsList nil
  | cons (a : Term) {b : Term} : IsList b -> IsList (pair a b)

/-- `([eval T1] ... [eval Tm])` from `(T1 ... Tm)`. On a term that is not a pair it is the
identity; it is only used on proper lists. -/
def evalList : Term -> Term
  | pair a b => pair (eval a) (evalList b)
  | var n => var n
  | dat n => dat n
  | prim n => prim n
  | ign => ign
  | nil => nil
  | vau t => vau t
  | vau0 t => vau0 t
  | vau2 t => vau2 t
  | wrap t => wrap t
  | eval t => eval t
  | comb a b => comb a b

theorem SelfEval.isValue {s : Term} (h : SelfEval s) : IsValue s := by
  cases h <;> constructor

/-- Decision procedure for `IsValue` (used to define complete developments). -/
def isValueB : Term -> Bool
  | var _ => true
  | dat _ => true
  | prim _ => true
  | ign => true
  | nil => true
  | vau _ => true
  | vau0 _ => true
  | vau2 _ => true
  | pair a b => isValueB a && isValueB b
  | wrap t => isValueB t
  | eval _ => false
  | comb _ _ => false

theorem isValueB_iff (t : Term) : isValueB t = true <-> IsValue t := by
  induction t with
  | pair a b iha ihb =>
    simp only [isValueB, Bool.and_eq_true, iha, ihb]
    exact Iff.intro (fun h => IsValue.pair h.1 h.2)
      (fun h => by cases h; exact And.intro (by assumption) (by assumption))
  | wrap t ih =>
    simp only [isValueB, ih]
    exact Iff.intro (fun h => .wrap h) (fun h => by cases h; assumption)
  | eval t _ => simp only [isValueB]; exact Iff.intro (fun h => (nomatch h)) (fun h => (nomatch h))
  | comb a b _ _ => simp only [isValueB]; exact Iff.intro (fun h => (nomatch h)) (fun h => (nomatch h))
  | _ => simp only [isValueB, true_iff]; constructor

/-- Decision procedure for `IsList`. -/
def isListB : Term -> Bool
  | nil => true
  | pair _ b => isListB b
  | _ => false

theorem isListB_iff (t : Term) : isListB t = true <-> IsList t := by
  induction t with
  | nil => simp only [isListB, true_iff]; exact .nil
  | pair a b _ ihb =>
    simp only [isListB, ihb]
    exact Iff.intro (fun h => .cons a h) (fun h => by cases h; assumption)
  | _ => simp only [isListB]; exact Iff.intro (fun h => (nomatch h)) (fun h => (nomatch h))

end Vau
