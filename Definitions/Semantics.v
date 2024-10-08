From Definitions Require Export Combinators Properties.

Create HintDb hclt.
Ltac hauto := eauto with hclt.

Reserved Notation "a ~> b" (at level 20).
Inductive step : combinator -> combinator -> Prop :=
| StepB : forall x y z, (B @ x @ y @ z) ~> (x @ (y @ z))
| StepC : forall x y z, (C @ x @ y @ z) ~> (x @ z @ y)
| StepK : forall x y,   (K @ x @ y) ~> x
| StepW : forall x y,   (W @ x @ y) ~> (x @ y @ y)
| StepAppL : 
    forall x x' y, 
    x ~> x' -> 
    (x @ y) ~> (x' @ y)
| StepAppR : 
    forall x y y',
    y ~> y' -> 
    (x @ y) ~> (x @ y')
where "a ~> b" := (step a b).

Hint Constructors step : hclt.

Reserved Notation "a ~>* b" (at level 21).
Inductive multistep : combinator -> combinator -> Prop :=
| step_none : forall c, c ~>* c
| step_one : forall c c', c ~> c' -> c ~>* c'
| step_multi : forall c c' c'', c ~> c' -> c' ~>* c'' -> c ~>* c''
where "a ~>* b" := (multistep a b).

Hint Constructors multistep : hclt.

Theorem multistep_trans :
    transitive multistep.
Proof. unfold transitive. hauto. Qed.

Hint Resolve multistep_trans : hclt.

Inductive Q : combinator -> combinator -> Prop :=
| Def2 : forall x y, x = y -> Q x y
| Qlr : forall x y, x ~>* y -> Q x y
| Qrl : forall x y, y ~>* x -> Q x y
| Qstepl : forall x x' y, x ~>* x' -> Q x' y -> Q x y
| Qstepr : forall x y y', y ~>* y' -> Q x y' -> Q x y
| Q_trans : forall x y z, Q x y -> Q y z -> Q x z. 

Hint Constructors Q : hclt.

Tactic Notation "step" "right" :=
    solve [now constructor] || (eapply Qstepr; 
    [eapply step_multi; repeat constructor; hauto |]).
Tactic Notation "step" "left" :=
    solve [now constructor] || (eapply Qstepl; 
    [eapply step_multi; repeat constructor; hauto |]).

(* Definition 3 *)
Definition _I := W @ K.

(* Remark *)
Definition _S : combinator :=
    B @ (B @ W) @ (B @ B @ C).

Lemma mstep_app_r : forall x y z,
    y ~>* z ->
    (x @ y) ~>* (x @ z).
Proof with hauto. intros; induction H... Qed.

Lemma mstep_app_l : forall x y z,
    x ~>* y ->
    (x @ z) ~>* (y @ z).
Proof with hauto. intros; induction H... Qed.

Hint Resolve mstep_app_r : hclt.
Hint Resolve mstep_app_l : hclt.

Theorem Q_app_l : forall x y w,
    Q x y -> Q (w @ x) (w @ y).
Proof with hauto.
    intros. induction H; subst...
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
