From Definitions Require Export Combinators Semantics.

Theorem Q_refl:
    forall x, Q x x.
Proof.
    intros. apply Def2.
    reflexivity.
Qed.

Theorem Q_sym:
    forall x y, Q x y -> Q y x.
Proof.
    intros. induction H; subst.
    apply Def2. reflexivity.
    apply Qrl. assumption.
    apply Qlr. assumption.
    apply (Qmid1 y x y' x'); try assumption.
    apply (Qmid2 y x y' x'); try assumption.
    apply RuleQ2. assumption.
Qed.

(* Lemma test:
    forall x y z,
    y ~> x -> Q y z -> Q x z.
Proof.
    intros. induction H0; subst.
    apply Qrl. assumption.
    apply (Qmid2 x y x0 x0); try assumption. apply Q_refl.
    apply (Qmid2 x y x0 y). 
        assumption. apply ExecNull. apply Qrl. assumption.
     *)

Theorem Q_trans:
    forall x y z, Q x y -> Q y z -> Q x z.
Proof.
    intros. induction H; subst.
    assumption.
    apply (Qmid1 x z y z). 
        assumption. apply ExecNull. assumption.
    apply (Qmid2 x z y z).
        assumption. apply ExecNull. assumption.
    apply (Qmid1 x z x' z).
        assumption. apply ExecNull. apply IHQ.
        apply (Qmid2 y' z y z). assumption. apply ExecNull. assumption.
    apply (Qmid2 x z x' z).
        assumption. apply ExecNull. apply IHQ.
        apply (Qmid1 y' z y z). assumption. apply ExecNull. assumption.
    induction H; subst.
        assumption.
Admitted.
