From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Locate "=".
About eq.
About orbT.
About leq.

Lemma my_first_lemma : 3 = 3.
Proof. by []. Qed.

About my_first_lemma.

Lemma my_second_lemma : 2 + 1 = 3.
Proof. by []. Qed.

Lemma addSn m n : m.+1 + n = (m + n).+1.
Proof. by []. Qed.

Lemma negbK (b : bool) : ~~ (~~ b) = b.
Proof.
  case: b.
  - by [].
  - by [].
Qed.

Lemma leqn0 n : (n <= 0) = (n == 0).
Proof. by case n => [|k ].
Qed.

Lemma muln_eq0 m n : (m * n == 0) = (m == 0) || (n == 0).
Proof.
  case: m => [|m] //.
  case: n => [|k] //.
  by rewrite muln0.
Qed.  (*
  case: m => [|m].
  - by [].
  - case: n => [|k]; last first.
     + by [].
     + *)

Lemma leqE m n : (m <= n) = (m - n == 0).
Proof. by []. Qed.

Lemma leq_mul2l m n1 n2 : (m * n1 <= m * n2) = (m == 0) || (n1 <= n2).
Proof.
  by rewrite !leqE -mulnBr muln_eq0.
Qed.

About nat_ind.
Eval compute in (fun n : nat => (odd n && prime n) = true) 0.

Inductive bintree :=
  leaf
| graft (u v : bintree).

About bintree_rec.
About list_ind.

Lemma addn0 m : m + 0 = m.
Proof.
  elim: m => [ // |m IHm].
    by [].
Qed.

