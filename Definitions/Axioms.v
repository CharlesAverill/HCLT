From Definitions Require Export Combinator Rules.

Definition Q (x y : combinator) : Prop :=
    x = y.

Theorem AxQ : forall (x y : combinator),
    Q x y -> x = y.
Proof. intros. unfold Q in H. apply H. Qed.

Axiom AxB : forall (x y z : combinator),
    B @ x @ y @ z = RuleB x y z.

Axiom AxC : forall (x y z : combinator),
    C @ x @ y @ z = RuleC x y z.

Axiom AxK : forall (x y : combinator),
    K @ x @ y = RuleK x y.

Axiom AxW : forall (x y : combinator),
    W @ x @ y = RuleW x y.



Ltac step :=
    unfold cI || unfold cS ||
    match goal with
        | |- context [B @ ?x @ ?y @ ?z] => rewrite AxB; unfold RuleB
        | |- context [C @ ?x @ ?y @ ?z] => rewrite AxC; unfold RuleC
        | |- context [K @ ?x @ ?y] => rewrite AxK; unfold RuleK 
        | |- context [W @ ?x @ ?y] => rewrite AxW; unfold RuleW
    end.
