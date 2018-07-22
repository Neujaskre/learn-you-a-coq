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

Lemma example m p : prime p -> p %| m`! + 1 -> m < p.
Proof.
  move=> prime_p.
  apply contraLR.
  rewrite -leqNgt => leq_p_m.
  rewrite dvdn_addr ?dvdn_fact ?prime_gt0 //.
    by rewrite gtnNdvd // prime_gt1.
Qed.

Lemma silly_example n : n + 0 = (n + 0) + 0.
Proof.
    by rewrite [in RHS] addn0.
Qed.

Lemma simplify_me : size [:: true] = 1.
Proof.
  rewrite //=.
Qed.

Lemma leq_mul2l' m n1 n2 : (m * n1 <= m * n2) = (m == 0) || (n1 <= n2).
Proof.
    by rewrite /leq -mulnBr muln_eq0.
Qed.

(* Exercises *)

Lemma orbA b1 b2 b3 : b1 || (b2 || b3) = b1 || b2 || b3.
Proof.
  case: b1 => //.
Qed.

Lemma implybE a b : (a ==> b) = ~~ a || b.
Proof.
  case: a => //.
Qed.

Lemma negb_and (a b : bool) : ~~ (a && b) = ~~ a || ~~ b.
Proof.
  case: a => //.
Qed. 

Lemma subn_sqr m n : m ^ 2 - n ^ 2 = (m - n) * (m + n).
Proof.
  rewrite -!mulnn.
Admitted.

Lemma z_muln m : 0 * m = 0.
Proof. 
  by [].
Qed.  

Lemma expn_zero m : (0 ^ m == 0) || (0 ^ m == 1).
Proof.
  elim: m => [|m0 IHm] //.
  rewrite !expnS !z_muln //.
Qed.

Lemma expn_zero2 m n : 0 ^ m == n = (n == 0) || (n == 1).
Proof.
  elim: m => [|m0 IHm].
  simpl.


              
  elim: n => [|n0 IHn].
  - simpl.
  
Lemma odd_exp m n : odd (m ^ n) = (n == 0) || odd m.
Proof.
  elim: m => [|m' IHm].
  Search "ex