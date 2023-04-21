Require Import Nat.
Require Import NArith.

Declare Scope combinator_scope.
Open Scope combinator_scope.

Inductive combinator : Type :=
    (* Schönfinkel Composition Function *)
    (* B x y z = x (y z) *)
    | B
    (* Schönfinkel Interchange Function *)
    (* C x y z = x z y *)
    | C
    (* Schönfinkel Constancy Function *)
    (* K x y = x *)
    | K
    (* Doubling Function *)
    (* W x y = W x y y *)
    | W
    | Apply (c1 c2 : combinator).

Notation "a @ b" :=
    (Apply a b)
    (at level 50, left associativity)
    : combinator_scope.

(* I = WK *)
(* Definition I := W @ K. *)
(* S = B(BW)(BBC) *)
(* Definition S := B @ (B @ W) @ (B @ B @ C). *)

Fixpoint size (c : combinator) : nat :=
    match c with 
    | Apply a b => (size a) + (size b)
    | _ => 1
    end.

Lemma size_ge_1 : forall (c : combinator),
    1 <= size c.
Proof.
    induction c; try reflexivity.
    apply PeanoNat.Nat.add_le_mono with (n := 1) (p := 0) (m := size c1) (q := size c2).
    apply IHc1. apply le_0_n.
Qed.

Fixpoint nth_comb (c : combinator) (n : nat) : option combinator :=
    match n with
    | O => Some c
    | S n' => match c with 
        | Apply a b => let left_result := nth_comb a n' in
            match left_result with 
            | None => nth_comb b n'
            | _ => left_result
            end
        | _ => None
        end
    end.

Lemma comb0_size1_impl_BCKW : forall (c X : combinator),
    size c = 1 ->
        nth_comb c 0 = Some X ->
            c = X.
Proof.
    intros. induction c; simpl in *; 
        try inversion H0; try reflexivity.
Qed.

Lemma le_n_x_le_n_y_impl_lt_sum_n_x_y : forall (n x y : nat),
    n > 0 -> 
    n <= x -> n <= y -> n < x + y.
Admitted.

Lemma combSn_size1_eq_none : forall (c : combinator) (n : nat),
    size c = 1 ->
        nth_comb c (S n) = None.
Proof.
    intros. destruct c; try reflexivity.
    contradict H; simpl.
    apply not_eq_sym. apply PeanoNat.Nat.lt_neq.
    apply le_n_x_le_n_y_impl_lt_sum_n_x_y. auto.
    apply size_ge_1. apply size_ge_1.
Qed.

(* Lemma nthcomb_Si_impl_nthcomb_i : 
    forall (c : combinator) (i : nat),
    exists (Y X : combinator),
    nth_comb c (S i) = Some X -> nth_comb c i = Some Y.
Proof.
    intros. induction i. 
        exists c. 
        unfold nth_comb. admit. *)
    
(* Lemma nthcomb_i_none_impl_i_ge_size : forall (c : combinator) (i : nat),
    nth_comb c i = None -> size c <= i.
Proof.
    intros. induction c; simpl in *.
        assert (exists x, i = S x).
          destruct i. congruence.
          exists i. reflexivity.
        destruct i in H. contradict H. congruence.
        simpl. destruct H0. rewrite H0.
        apply le_n_S, le_0_n.

        assert (exists x, i = S x).
            destruct i. congruence.
            exists i. reflexivity.
          destruct i in H. contradict H. congruence.
          simpl. destruct H0. rewrite H0.
          apply le_n_S, le_0_n.

        assert (exists x, i = S x).
            destruct i. congruence.
            exists i. reflexivity.
          destruct i in H. contradict H. congruence.
          simpl. destruct H0. rewrite H0.
          apply le_n_S, le_0_n.

        assert (exists x, i = S x).
            destruct i. congruence.
            exists i. reflexivity.
          destruct i in H. contradict H. congruence.
          simpl. destruct H0. rewrite H0.
          apply le_n_S, le_0_n.

    - destruct i. discriminate H.
      destruct (nth_comb c1 i) in H. discriminate H.
      admit.
Admitted. *)
         

(* Lemma i_lt_n_impl_nthcomb_some : 
    forall (c : combinator) (i : nat)
        (I_LT_SC : i < size c),
    exists (X : combinator),
    nth_comb c i = Some X.
Proof.
    intros. induction c; 
    (* Base Cases *)
        simpl in I_LT_SC; try apply PeanoNat.Nat.lt_1_r in I_LT_SC;
        try rewrite I_LT_SC; simpl; try congruence.
    (* c = Apply c1 c2 *)
        exists B. reflexivity.
        exists C. reflexivity.
        exists K. reflexivity.
        exists W. reflexivity.
        destruct i. exists (c1 @ c2). reflexivity.
        apply IHc1. *)
        

