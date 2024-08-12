From Definitions Require Export Combinator Rules Axioms.
From Proofs Require Import Ch1D.

Require Import List.

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
    intros. induction n; 
        unfold Bn; repeat step; reflexivity.
Qed.

(* Theorem 2 *)
Definition get_option {A : Type} (a : option A) (default : A) : A :=
    match a with 
    | None => default
    | Some x => x
    end.
Theorem Bnm_xyz2m_eq_Bnx_yz2m : 
    forall (n m : nat) (x y z right : combinator) (zm : list combinator)
    (LEN_ZM_IS_M : length zm = m)
    (M0_Z : m = 0 -> right = y)
    (MN0_Z : m <> 0 -> right = y |@ get_option (comblist_to_app zm) z),
    (Bn (n + m) @ x) |@ right = 
        (Bn n @ x) @ right.
Proof.
    intros. induction m; simpl in *.
    - replace zm with (nil : list combinator). simpl.
      rewrite PeanoNat.Nat.add_0_r. 
      repeat step. rewrite M0_Z. destruct (Bn n @ x).
       reflexivity. destruct zm. 
        reflexivity. 
        contradict LEN_ZM_IS_M.
        discriminate.
    - rewrite MN0_Z. unfold get_option. destruct (comblist_to_app zm).
      rewrite PeanoNat.Nat.add_comm. simpl. 
      destruct (m + n).
        -- replace n with 0. simpl.
