From Definitions Require Export Combinator.

Definition Q (x y : combinator) : Prop :=
    x = y.

Theorem AxQ : forall (x y : combinator),
    Q x y -> x = y.
Proof. intros. unfold Q in H. apply H. Qed.
