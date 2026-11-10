import Vau.Reduction

/-!
# vau-e: the vau calculus with environments (syntax and auxiliary functions)

This follows Shutt's vau-e calculus (PhD thesis, WPI 2010, section 9.1, (9.1) and (9.6)):

```
S ::= d | o | e | #ignore | () | <operative T T T T>     (self-evaluating terms)
A ::= [eval T T] | [combine T T T]                      (active terms)
T ::= S | s | (T . T) | <applicative T> | A              (terms)
      | <capsule k T>                                    (this project's addition)
e ::= <<B*>>,  B ::= s <- T                              (environments)
V  =  terms whose every active subterm is within an operative or environment   (values)
```

Representation choices (this project's, not Shutt's):

* Symbols are natural numbers. The `$lambda` file names the few symbols it uses.
* An environment is a plain list of bindings (`List (Nat x Term)`). Shutt's grammar keeps the bindings sorted, with no
  symbol bound twice, and his join `e1 . e2` merges them so that a binding in `e1` wins. Here
  `join` is list append and `lookup` takes the first binding. The two agree on every lookup, but
  two environments that list the same bindings in a different order are different terms here,
  so this equational theory is weaker than Shutt's.
* Primitive operatives are the ones named in `Prim`. `$vau`, `$wrap` and `$unwrap` have Shutt's
  delta-rules (9.12). `$eval` and `$list*` have delta-rules written by this project (Shutt uses
  them in (4.20)-(4.22) and calls their rules self-evident).
* Encapsulation types are this project's addition: the term `capsule k v` and the primitives
  `$encap k`, `$isEncap k`, `$decap k` (see `Vau/Env/Encapsulation.lean`).
-/

namespace VauE

/-- Primitive operatives. For a standard applicative `foo`, `$foo` is its underlying operative,
as in the thesis: `foo = <applicative $foo>`. -/
inductive Prim where
  | vau | wrap | unwrap | eval | listStar
  /-- `$encap k`: the encapsulator of encapsulation type `k` (see `Vau/Env/Encapsulation.lean`). -/
  | encap (k : Nat)
  /-- `$isEncap k`: the type predicate of encapsulation type `k`. -/
  | isEncap (k : Nat)
  /-- `$decap k`: the decapsulator of encapsulation type `k`. -/
  | decap (k : Nat)
  deriving DecidableEq, Repr

/-- Terms of vau-e. An environment is a list of bindings `(s, T)`, stored inside the term. -/
inductive Term where
  /-- Primitive data. -/
  | dat  : Nat -> Term
  /-- A primitive operative. -/
  | prim : Prim -> Term
  /-- A symbol. -/
  | sym  : Nat -> Term
  /-- `#ignore`. -/
  | ign  : Term
  /-- The empty list `()`. -/
  | nil  : Term
  /-- An environment `<<s1 <- T1, ..., sn <- Tn>>`, as a term. -/
  | env  : List (Prod Nat Term) -> Term
  /-- `<operative ptree eparm body senv>`: a compound operative with parameter tree `ptree`,
  environment parameter `eparm`, body `body` and static environment `senv`. -/
  | oper : Term -> Term -> Term -> Term -> Term
  /-- A pair `(T1 . T2)`. -/
  | pair : Term -> Term -> Term
  /-- `<applicative T>`. -/
  | app  : Term -> Term
  /-- `[eval T e]`. -/
  | eval : Term -> Term -> Term
  /-- `[combine T1 T2 e]`. -/
  | comb : Term -> Term -> Term -> Term
  /-- An encapsulated object of encapsulation type `k` with content `T` (this project's addition,
  for Kernel's encapsulation types; see `Vau/Env/Encapsulation.lean`). -/
  | capsule : Nat -> Term -> Term

/-- Environments: lists of bindings `s <- T`, first binding first. -/
abbrev Env := List (Prod Nat Term)

open Term

/-- Join of environments, `e1 . e2`: bindings of `e1` come first, so they win in `lookup`. -/
def Env.join (e1 e2 : Env) : Env := e1 ++ e2

/-- `lookup(s, e)`: the term bound to `s` by the first binding of `s` in `e`. -/
def Env.lookup (s : Nat) : Env -> Option Term
  | [] => none
  | (s', t) :: r => if s = s' then some t else Env.lookup s r

theorem Env.join_emp (e : Env) : Env.join e [] = e := List.append_nil e

theorem Env.lookup_join (s : Nat) : forall e1 e2 : Env,
    Env.lookup s (Env.join e1 e2) = (Env.lookup s e1).or (Env.lookup s e2)
  | [], e2 => by simp [Env.join, Env.lookup]
  | (s', t) :: r, e2 => by
    simp only [Env.join, List.cons_append, Env.lookup]
    split
    next => rfl
    next => exact Env.lookup_join s r e2

/-- The symbols in a parameter tree. -/
def syms : Term -> List Nat
  | sym s => [s]
  | pair a b => syms a ++ syms b
  | _ => []

/-- `true` iff the two lists have no element in common. -/
def disjoint (xs ys : List Nat) : Bool := xs.all (fun x => !(ys.contains x))

/-- `match(ptree, T)` (thesis (9.6)): the bindings made by matching a parameter tree against an
operand tree, or `none` if they do not match. -/
def ematch : Term -> Term -> Option Env
  | ign, _ => some []
  | nil, nil => some []
  | sym s, t => some [(s, t)]
  | pair a b, pair c d =>
    if disjoint (syms a) (syms b) then
      match ematch a c, ematch b d with
      | some m1, some m2 => some (Env.join m1 m2)
      | _, _ => none
    else none
  | _, _ => none

/-- Self-evaluating terms `S`. -/
inductive SelfEval : Term -> Prop where
  | dat (n : Nat) : SelfEval (dat n)
  | prim (p : Prim) : SelfEval (prim p)
  | env (e : Env) : SelfEval (env e)
  | ign : SelfEval ign
  | nil : SelfEval nil
  | oper (p q b s : Term) : SelfEval (oper p q b s)
  | capsule (k : Nat) (v : Term) : SelfEval (capsule k v)

/-- Values: every active subterm is within an operative or an environment. -/
inductive IsValue : Term -> Prop where
  | dat (n : Nat) : IsValue (dat n)
  | prim (p : Prim) : IsValue (prim p)
  | sym (s : Nat) : IsValue (sym s)
  | ign : IsValue ign
  | nil : IsValue nil
  | env (e : Env) : IsValue (env e)
  | oper (p q b s : Term) : IsValue (oper p q b s)
  | pair {a b : Term} : IsValue a -> IsValue b -> IsValue (pair a b)
  | app {t : Term} : IsValue t -> IsValue (app t)
  | capsule (k : Nat) (v : Term) : IsValue (capsule k v)

/-- Proper lists `(T1 ... Tm)`. -/
inductive IsList : Term -> Prop where
  | nil : IsList nil
  | cons (a : Term) {b : Term} : IsList b -> IsList (pair a b)

/-- `([eval T1 e] ... [eval Tm e])` from `(T1 ... Tm)`. -/
def evalList (e : Term) : Term -> Term
  | pair a b => pair (eval a e) (evalList e b)
  | t => t

/-- `list*` on an argument list: `(x1 ... xn-1 xn)` gives `(x1 ... xn-1 . xn)`. Defined on
nonempty proper lists. -/
def buildListStar : Term -> Option Term
  | pair x nil => some x
  | pair x rest => Option.map (pair x) (buildListStar rest)
  | _ => none

/-- `true` iff the term is an encapsulated object of type `k`. -/
def isCapsuleOf (k : Nat) : Term -> Bool
  | capsule k' _ => k' == k
  | _ => false

/-- The answer of the type predicate of type `k` on an argument list: `some true` if every
argument is an encapsulated object of type `k`, `some false` if some argument is not, and `none`
if the arguments are not a proper list. -/
def capsCheck (k : Nat) : Term -> Option Bool
  | nil => some true
  | pair x rest => Option.map (fun b => isCapsuleOf k x && b) (capsCheck k rest)
  | _ => none

/-- The list `(a)`. -/
abbrev list1 (a : Term) : Term := pair a nil
/-- The list `(a b)`. -/
abbrev list2 (a b : Term) : Term := pair a (list1 b)
/-- The list `(a b c)`. -/
abbrev list3 (a b c : Term) : Term := pair a (list2 b c)
/-- The list `(a b c d)`. -/
abbrev list4 (a b c d : Term) : Term := pair a (list3 b c d)

end VauE
