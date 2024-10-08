From Proofs Require Import Ch1D.

(* Section 1 : The B Sequence *)
Fixpoint Bseq (n : nat) : combinator :=
    match n with
    | 0 => _I
    | 1 => B
    | S n' => B @ B @ Bseq n'
    end.

Lemma Bseq_Sn : forall n,
    1 <= n ->
    Bseq (S n) = B @ B @ Bseq n.
Proof. 
    intros. simpl. destruct n. inversion H.
    destruct n; simpl; reflexivity.
Qed.

(* Theorem 1 *)
Theorem Bseq_Sn_xyz__Bseq_n_xyz :
    forall x y z n,
    Q (Bseq (S n) @ x @ y @ z) (Bseq n @ x @ (y @ z)).
Proof with hauto.
    intros; destruct n...
Qed.

(* Theorem 2 *)
(* Compute (Bseq (0 + 0), Bseq 0 @ Bseq 0).
Compute (Bseq (0 + 1), Bseq 0 @ Bseq 1).
Compute (Bseq (1 + 0), Bseq 1 @ Bseq 0).
Compute (Bseq (1 + 1), Bseq 1 @ Bseq 1).

Lemma Bseq_plus :
    forall n m,
    Q (Bseq (n + m)) (Bseq n @ Bseq m).
Proof with hauto.
    induction n; intros.
    - repeat step right.
    - change (S n + m) with (S (n + m)).
      destruct (PeanoNat.Nat.le_ge_cases 1 n).
      -- rewrite Bseq_Sn, Bseq_Sn, IHn.
         step right. rewrite <- IHn. *)

Theorem Bseq_nm_xyzm__Bseq_n_x_yzm :
    forall (m n : nat) (x y z : combinator) (Zl : list combinator),
    Some z = app_comb_list Zl ->
    m = length Zl ->
    Q (Bseq (n + m) @ x @ y @ z) (Bseq n @ x @ (y @ z)).
Proof.
    induction m as [| k IH]; intros.
    - rewrite PeanoNat.Nat.add_0_r. symmetry in H0.
      apply -> List.length_zero_iff_nil in H0. subst.
      inversion H.
    - destruct k.
        now rewrite <- PeanoNat.Nat.add_comm, Bseq_Sn_xyz__Bseq_n_xyz.
        rewrite <- PeanoNat.Nat.add_succ_comm.
        change (S n + S k) with (S (n + S k)).
        rewrite Bseq_Sn_xyz__Bseq_n_xyz.
        rewrite <- PeanoNat.Nat.add_succ_comm.
        change (S n + k) with (S (n + k)).
Admitted.

(* Theorem 3 *)
Theorem Bseq_m_xyzm__x_yzm :
    forall m x y z Zl,
    Some z = app_comb_list Zl ->
    m = length Zl ->
    Q (Bseq m @ x @ y @ z) (x @ (y @ z)).
Proof.
    intros. pose proof (Bseq_nm_xyzm__Bseq_n_x_yzm m 0 x y z Zl H H0).
    simpl in H1. transitivity (_I @ x @ (y @ z)).
        assumption.
    step left. step left. reflexivity.
Qed.

(* Theorem 4 *)
Theorem X_nm__BmXn :
    forall (m n : nat) (Xl : list combinator) (d : combinator),
    1 <= n < length Xl ->
    (forall n, Q (List.nth (S n) Xl d) (B @ (List.nth n Xl d))) ->
    Q (List.nth (n + m) Xl d) (Bseq m @ (List.nth n Xl d)).
Proof with hauto.
    induction m; intros.
    - simpl. step right. step right. rewrite PeanoNat.Nat.add_0_r...
    - destruct m.
        rewrite PeanoNat.Nat.add_comm...
        remember (S m) as k.
        rewrite <- PeanoNat.Nat.add_succ_comm.
        change (S n + k) with (S (n + k)).
        rewrite H0, IHm...
        rewrite Bseq_Sn... subst. apply le_n_S, PeanoNat.Nat.le_0_l.
Qed.

(* Theorem 5 *)
Theorem Bm_BnX__BmnX :
    forall (n m : nat) (X : combinator),
    Q (Bseq m @ (Bseq n @ X)) (Bseq (m + n) @ X).
Proof with hauto.
    induction n as [| n']; intros.
    - rewrite PeanoNat.Nat.add_0_r...
    - rewrite PeanoNat.Nat.add_comm. change (S n' + m) with (S (n' + m)).
      destruct (PeanoNat.Nat.eq_dec n' 0).
      -- subst. specialize (IHn' m X). 
         rewrite PeanoNat.Nat.add_0_r in IHn'. simpl in IHn'.
         destruct m. step left. step left. reflexivity.
         rewrite Bseq_Sn with (n := 0 + S m).
         step right. change (0 + S m) with (S m). rewrite <- IHn'.
         simpl (Bseq 1).
         assert (Q (_I @ X) X) by now step left. rewrite H. clear H.
Admitted. (* Almost... *)
