From Definitions Require Export Combinator Rules Axioms.
From Proofs Require Import Ch1D.

(* 
    CHAPTER 2
    Section B
*)

(* Subsection 1. The B Sequence *)

(* Definitions 1, 2 *)
Fixpoint Bn (n : nat) : combinator :=
    match n with 
    | O => cI
    | S O => B
    | S n' => B @ B @ (Bn n')
    end.

Lemma reduce_Bxyz : forall (x y z : combinator),
    reduce (B @ x @ y @ z) = x @ (y @ z).
Proof. reflexivity. Qed.

(* Lemma BSn_eq_BBBSn : forall (n : nat),
    0 < n -> 
        Bn (S n) = B @ B @ Bn n.
Proof. 
    intros. unfold Bn.
    induction n.
    - contradict H. apply PeanoNat.Nat.lt_irrefl.
    - replace (Bn (S (S n))) with (B @ B @ (B @ B @ Bn n)). rewrite IHn.
      reflexivity. *)

(* 
    This one doesn't seem to be provable without a definition of reduce that
    allows for infinite loops :(
*)
Theorem BSn_xyz_eq_Bn_x_yz : forall (x y z : combinator) (n : nat),
    reduce (Bn (S n) @ x @ y @ z) = reduce (Bn n @ x @ (y @ z)).
Admitted. 
(* Proof.
    intros. induction n.
    - cbv [Bn]. rewrite reduce_Bxyz. apply reduce_Ixy.
    - replace (Bn (S n)) with (B @ B @ Bn n).
      replace (Bn (S (S n))) with (B @ B @ (B @ B @ Bn n)). simpl.
      unfold RuleB. *)
