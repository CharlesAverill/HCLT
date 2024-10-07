From Definitions Require Export Combinators.

Create HintDb hclt.
Ltac hauto := eauto with hclt.

Reserved Notation "a ~> b" (at level 20).
Inductive sstep : combinator -> combinator -> Prop :=
| ExecB : forall x y z, (B @ x @ y @ z) ~> (x @ (y @ z))
| ExecC : forall x y z, (C @ x @ y @ z) ~> (x @ z @ y)
| ExecK : forall x y,   (K @ x @ y) ~> x
| ExecW : forall x y,   (W @ x @ y) ~> (x @ y @ y)
| ExecAppL : forall x x' y, x ~> x' -> (x @ y) ~> (x' @ y)
| ExecAppR : forall x y y', y ~> y' -> (x @ y) ~> (x @ y')
    where "a ~> b" := (sstep a b).

Hint Constructors sstep : hclt.

Inductive Q : combinator -> combinator -> Prop :=
| Def2 : forall x y, x = y -> Q x y
| Qlr : forall x y, x ~> y -> Q x y
| Qrl : forall x y, y ~> x -> Q x y
| Qstepl : forall x x' y, x ~> x' -> Q x' y -> Q x y
| Qstepr : forall x y y', y ~> y' -> Q x y' -> Q x y
| Q_trans : forall x y z, Q x y -> Q y z -> Q x z. 

Hint Constructors Q : hclt.

(* Definition 3 *)
Definition _I := W @ K.

(* Remark *)
Definition _S : combinator :=
    B @ (B @ (B @ W) @ C) @ (B @ B).

Theorem Q_app_l : forall x y w,
    Q x y -> Q (w @ x) (w @ y).
Proof with hauto.
    intros. induction H... subst...
Qed.

Theorem RuleB : forall x y z,
    Q (B @ x @ y @ z) (x @ (y @ z)).
Proof. hauto. Qed.

Theorem RuleC : forall x y z,
    Q (C @ x @ y @ z) (x @ z @ y).
Proof. hauto. Qed.

Theorem RuleW : forall x y,
    Q (W @ x @ y) (x @ y @ y).
Proof. hauto. Qed.

Theorem RuleK : forall x y,
    Q (K @ x @ y) x.
Proof. hauto. Qed.

Hint Resolve Q_app_l RuleB RuleC RuleW RuleK : hclt.
