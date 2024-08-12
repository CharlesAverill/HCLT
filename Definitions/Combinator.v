Require Import Nat.
Require Import NArith.
Require Import Lia.
Require Import List.
Import ListNotations.

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

Fixpoint farleftapply (x c : combinator) :=
    match c with 
    | a @ b => (farleftapply x a) @ b
    | _ => x @ c
    end.

Notation "a |@ b" :=
    (farleftapply a b)
    (at level 40, left associativity)
    : combinator_scope.

Definition is_app (c : combinator) : Prop :=
    match c with
    | _ @ _ => True
    | _ => False
    end.

Definition comblist_to_app (l : list combinator) : option combinator :=
    let fix rechelper (l : list combinator) : option combinator :=
        match l with 
        | [] => None
        | h :: t => let t' := rechelper t in
            match t' with | None => Some h | Some x => Some (x @ h) end
        end
    in rechelper (rev l).

Lemma rev_append_nnil : forall (A : Type) (l m : list A),
    0 < length m -> 
        rev_append l m <> [].
Proof.
    intros. induction l.
    - simpl. induction m. contradict H. apply PeanoNat.Nat.lt_irrefl.
             apply not_eq_sym, nil_cons.
    - simpl.
Admitted.

Lemma comblist_notnil_impl_cl2a_notnone : forall (l : list combinator),
    l <> nil ->
        comblist_to_app l <> None.
Proof.
    intros. unfold comblist_to_app. 
        assert (rev l <> []). {
            induction l. contradict H. reflexivity.
            unfold rev. rewrite <- rev_append_rev.
            apply rev_append_nnil. apply le_n.
        } destruct (rev l). contradiction. 
        destruct ((fix rechelper (l1 : list combinator) : option combinator :=
        match l1 with
        | [] => None
        | h :: t =>
            match rechelper t with
            | Some x => Some (x @ h)
            | None => Some h
            end
        end) l0); discriminate.
Qed.
(* 
    I will use the 'c' prefix to denote 
    "constructed" (derivable) combinators
*)
(* I = WK *)
Definition cI := W @ K.
(* S = B(BW)(BBC) *)
Definition cS := B @ (B @ W) @ (B @ B @ C).

Fixpoint size (c : combinator) : nat :=
    match c with 
    | a @ b => (size a) + (size b)
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
    match c with
    | a @ b => let left_result := nth_comb a n in 
        match left_result with
        | None => nth_comb b (n - 1)
        | _ => left_result
        end
    | _ => match n with O => Some c | _ => None end
    end.

Lemma two_sizes_geq_2 : forall (a b : combinator),
    2 <= size a + size b.
Proof.
    intros. apply PeanoNat.Nat.add_le_mono with (n := 1) (m := size a); 
    apply size_ge_1.
Qed.

Lemma two_sizes_gt_1 : forall (a b : combinator),
    1 < size a + size b.
Proof.
    intros. apply PeanoNat.Nat.lt_le_trans with (m := 2). 
    apply le_n. 
    apply two_sizes_geq_2.
Qed.

Lemma two_sizes_neq_1 : forall (a b : combinator),
    1 <> size a + size b.
Proof.
    intros. apply PeanoNat.Nat.lt_neq, two_sizes_gt_1.
Qed.

Lemma comb0_size1_impl_BCKW : forall (c X : combinator),
    size c = 1 ->
        nth_comb c 0 = Some X ->
            c = X.
Proof.
    intros. induction c; simpl in *; 
        try inversion H0; try reflexivity.

        contradict H. apply not_eq_sym. 
        apply PeanoNat.Nat.lt_neq, two_sizes_gt_1.
Qed.

Lemma le_n_x_le_n_y_impl_lt_sum_n_x_y : forall (n x y : nat),
    0 < n -> 
    n <= x -> n <= y -> n < x + y.
Proof. lia. Qed.
