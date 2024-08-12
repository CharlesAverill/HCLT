From Definitions Require Export Combinator Rules.

Inductive step_comb : combinator -> combinator -> Prop :=
    | StepB x y z : 
        step_comb (B @ x @ y @ z) (RuleB x y z)
    | StepC x y z : 
        step_comb (C @ x @ y @ z) (RuleC x y z)
    | StepK x y :
        step_comb (K @ x @ y) (RuleK x y)
    | StepW x y :
        step_comb (W @ x @ y) (RuleW x y)
    | StepRefl x : 
        step_comb x x.

Fixpoint converge_after_n_steps (a b : combinator) (n : nat) {struct n} : Prop :=
    match n with 
    | O => a = b
    | S n' => exists a', step_comb a a' /\
        converge_after_n_steps a' b n'
    end.

Definition Q (x y : combinator) : Prop :=
    exists n m x' y',
    converge_after_n_steps x x' n /\
    converge_after_n_steps y y' m /\
    x' = y'.

Notation "a 'q=' b" :=
    (Q a b)
    (at level 99, no associativity)
    : combinator_scope.

Lemma cvgn_impl_cvgSn : forall (x y : combinator) (n : nat),
    converge_after_n_steps x y n ->
        converge_after_n_steps x y (S n).
Proof.
    intros. exists x. split. 
        apply StepRefl. 
        apply H.
Qed.

(* Lemma cvgn_transitive : forall a b c n1 n2,
    converge_after_n_steps a b n1 ->
    converge_after_n_steps b c n2 ->
    converge_after_n_steps a c (n1 + n2).
Proof.
    intros. induction n1.
    - rewrite H. apply H0.
    - destruct H as [b' [H_step H_converge]]. replace (n1 + S n2) with (S (n1 + n2)).
      apply cvgn_impl_cvgSn.
      apply step_comb_cvg_Sn with (x := a) (y := b') (z := c) (n := 0).
      apply eqab_impl_cvg0.
      apply H_step.

      

Lemma step_nonapp_impl_eq : forall (x y : combinator),
    ~ is_app x ->
        x q= y ->
            x = y.
Proof.
    intros. destruct x. 
    all: unfold Q in H0; destruct H0; induction x;
      try apply H0; destruct H0 as [x0 [H0_split H0_converge]];
      inversion H0_split; try rewrite <- H1 in H0_converge;
      try apply IHx, H0_converge.

    all: contradict H; simpl; auto.
Qed. *)

Ltac unfold_composites :=
    unfold cI || unfold cS.

Ltac step :=
    unfold_composites ||
    cbv [converge_after_n_steps RuleB RuleC RuleK RuleW] ||
    reflexivity ||
    split ||
    match goal with
        | |- context [B @ ?x @ ?y @ ?z] => apply StepB
        | |- context [C @ ?x @ ?y @ ?z] => apply StepC
        | |- context [K @ ?x @ ?y] => apply StepK 
        | |- context [W @ ?x @ ?y] => apply StepW
        | |- context [step_comb ?x ?x] => apply StepRefl
        | |- exists a : combinator, step_comb (?c @ ?x @ ?y) ?b /\ _ =>
                pattern c, x, y; match c with 
                | W => exists (RuleW x y)
                | K => exists (RuleK x y)
                end
        | |- context [exists a : combinator, step_comb ?b a /\ _] => 
                pattern b; exists b
        | |- context [?a q= ?a] => exists 0; reflexivity
        | |- context [exists n : nat, converge_after_n_steps ?a ?a n] =>
                exists 0
    end.

Ltac cvgnm n m :=
    exists n, m; repeat step.

Ltac cvgright n :=
    exists n, 0; match goal with 
    | |- context [exists a b : combinator, 
                    converge_after_n_steps _ a _ /\ 
                    converge_after_n_steps ?x b _ /\ _] =>
            pattern x; exists x, x 
    end.

Ltac cvgleft n :=
    exists 0, n; match goal with 
    | |- context [exists a b : combinator,
                    converge_after_n_steps ?x a _ /\ 
                    converge_after_n_steps _ b _ /\ _] =>
            pattern x; exists x, x
    end.

(* Ltac cvgmono n :=
    try (cvgright n || cvgleft n); repeat step. *)

(* Tactic Notation "cvgn" constr(n) "in" ident(H) :=
    exists n in H; repeat step in H. *)

Theorem test : forall x : combinator,
    x q= cI @ x.
Proof.
    intros. cvgleft 2. repeat step.
Qed.

