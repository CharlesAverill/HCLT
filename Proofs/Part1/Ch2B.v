From Proofs Require Import Ch1D.

(* Section 1 : The B Sequence *)
Fixpoint B_seq (n : nat) : combinator :=
    match n with
    | 0 => _I
    | 1 => B
    | S n' => B @ B @ B_seq n'
    end.

Lemma B_seq_Sn : forall n,
    1 <= n ->
    B_seq (S n) = B @ B @ B_seq n.
Proof. 
    intros. simpl. destruct n. inversion H.
    destruct n; simpl; reflexivity.
Qed.

(* Theorem 1 *)
Theorem B_Sn_xyz__Bn_xyz :
    forall x y z n,
    Q (B_seq (S n) @ x @ y @ z) (B_seq n @ x @ (y @ z)).
Proof.
    intros. destruct n.
    - hauto.
    - rewrite B_seq_Sn.
        etransitivity.
            apply Qlr. hauto.
        etransitivity.
            apply Qlr. hauto.
        hauto. apply le_n_S, PeanoNat.Nat.le_0_l.
Qed.
