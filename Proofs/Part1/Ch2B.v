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

(* Theorem 1 *)
Theorem BSn_xyz_eq_Bn_x_yz : forall (x y z : combinator) (n : nat),
    Bn (S n) @ x @ y @ z = Bn n @ x @ (y @ z).
Proof.
    intros. induction n.
    - cbv [Bn]. repeat step. reflexivity.
    - cbv [Bn]. repeat step. reflexivity.
Qed.
