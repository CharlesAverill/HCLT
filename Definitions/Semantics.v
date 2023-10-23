From Definitions Require Export Combinators.

Inductive exec : combinator -> combinator -> Prop :=
| ExecB : forall x y z, exec (B @ x @ y @ z) (x @ (y @ z))
| ExecC : forall x y z, exec (C @ x @ y @ z) (x @ z @ y)
| ExecK : forall x y,   exec (K @ x @ y) x
| ExecW : forall x y,   exec (W @ x @ y) (x @ y @ y)
| ExecNull: forall x,   exec x x.
(* | ExecL : forall x y z, exec x y -> exec (x @ z) (y @ z)
| ExecR : forall x y z, exec x y -> exec (z @ x) (z @ y). *)

Notation "a ~> b" := (exec a b) (at level 55, left associativity).

Inductive Q : combinator -> combinator -> Prop :=
| Def2 : forall x y, x = y -> Q x y
| Qlr : forall x y, x ~> y -> Q x y
| Qrl : forall x y, y ~> x -> Q x y
| Qmid1 : forall x y x' y', x ~> x' -> y ~> y' -> Q x' y' -> Q x y
| Qmid2 : forall x y x' y', x' ~> x -> y' ~> y -> Q x' y' -> Q x y
| RuleQ2 : forall x y w, Q x y -> Q (w @ x) (w @ y).
