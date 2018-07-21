From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition predn n :=
  if n is p.+1 then p else n.

Compute predn 3.
Eval compute in predn.

Definition same_bool b1 b2 :=
  match b1, b2 with
  | true, true => true
  | false, false => true
  | _, _ => false
  end.

Fixpoint eqn m n :=
  match m, n with
  | O, O => true
  | p.+1, q.+1 => eqn p q
  | _, _ => false
  end.

Notation "x == y" := (eqn x y).

Eval compute in subn.

About cons.
Check cons 2 nil.

Eval compute in [seq i.+1 | i <- [:: 1; 2; 3; 4]].

Eval compute in (true, false).1.

Record point : Type :=
  Point { x : nat; y : nat; z : nat }.

Section iterators.

  Variables (T : Type) (A : Type).
  Variables (f : T -> A -> A).

  Implicit Type x : T.

  Fixpoint iter n op x :=
    if n is p.+1 then op (iter p op x) else x.

  Fixpoint foldr a s :=
    if s is y :: ys then f y (foldr a ys) else a.

  Variable init : A.
  Variables x1 x2 : T.
  Eval compute in foldr init [:: x1; x2].
  
End iterators.

About foldr.

Eval compute in iter 5 predn 7.

Fixpoint add n m :=
  if n is p.+1 then add p m.+1 else m.

Variable n : nat.
Eval simpl in (add n.+1 7).-1.
Eval simpl in (addn n.+1 7).-1.

Eval compute in iota 1 10.
Eval compute in \sum_(1 <= i < 5)(i * 2 - 1).

Locate "<=".

(* Excercises *)

Record triple (A B C : Type) :=
  mk_triple { fst : A; snd : B; thrd : C }.

Notation "( a , b , c )" := (mk_triple a b c).
Notation "p .1T" := (fst p) (at level 2).
Notation "p .2T" := (snd p) (at level 2).
Notation "p .3T" := (thrd p) (at level 2).
Eval compute in (4, 5, 8).1T.
Eval compute in (true, false, 1).2T.
Eval compute in (2, true, false).3T.

Definition add_iter (n m : nat) :=
  iter n S m.

Eval compute in add_iter 5 9.

Definition mult_iter (n m : nat) :=
  iter n (add_iter m) 0.

Eval compute in mult_iter 5 8.

Fixpoint nth {A : Type} (default : A) (xs : seq A) (n : nat) : A :=
  match n, xs with
  | O, (x :: xs') => x
  | m, (x :: xs') => nth default xs' n.-1
  | _, _ => default 
  end.

Eval compute in nth 99 [:: 3; 7; 11; 22] 2.
Eval compute in nth 99 [:: 3; 7; 11; 22] 7.

Definition rev {A : Type} (xs : seq A) :=
  if xs is x :: xs' then (rev xs') ++ [:: x] else nil.

Eval compute in rev [:: 1; 2; 3; 4; 5].

Eval cbv delta in [:: 1] ++ [:: 1].

Definition flatten {A : Type} (xs : seq (seq A)) : seq A :=
  foldr cat nil xs.

Eval compute in flatten [:: [:: 1; 2; 3]; [:: 4; 5] ].
