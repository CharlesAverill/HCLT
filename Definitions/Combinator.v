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

Definition is_app (c : combinator) : Prop :=
    match c with
    | _ @ _ => True
    | _ => False
    end.

(* I = WK *)
(* Definition I := W @ K. *)
(* S = B(BW)(BBC) *)
(* Definition S := B @ (B @ W) @ (B @ B @ C). *)

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

Lemma size_app : forall (a b : combinator),
    size (a @ b) = size a + size b.
Proof.
    intros. destruct a; reflexivity.
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

Lemma comb0_size1_impl_BCKW : forall (c X : combinator),
    size c = 1 ->
        nth_comb c 0 = Some X ->
            c = X.
Proof.
    intros. induction c; simpl in *; 
        try inversion H0; try reflexivity.

        admit.
Admitted.

Lemma le_n_x_le_n_y_impl_lt_sum_n_x_y : forall (n x y : nat),
    n > 0 -> 
    n <= x -> n <= y -> n < x + y.
Admitted.
