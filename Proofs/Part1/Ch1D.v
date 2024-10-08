From Definitions Require Export Combinators Semantics.

(* Theorem 1 *)
Theorem Q_refl:
    forall x, Q x x.
Proof. hauto. Qed.

(* Theorem 2 *)
Theorem Q_sym:
    forall x y, Q x y -> Q y x.
Proof with hauto. 
    intros; induction H...
Qed.

(* Theorem 3 *)
Theorem Q_trans:
    forall x y z, Q x y -> Q y z -> Q x z.
Proof. hauto. Qed.

(* Theorem 4 *)
Theorem Q_app_r :
    forall x y z,
    Q x y -> Q (x @ z) (y @ z).
Proof with hauto.
    intros; induction H; subst...
Qed.

(* Theorem 6 *)
Require Export Classes.RelationClasses.
Require Export Setoids.Setoid.
Require Export Classes.Morphisms.

Instance: Equivalence Q.
Proof.
  constructor.
    unfold Reflexive. apply Q_refl.
    unfold Symmetric. apply Q_sym. 
    unfold Transitive. apply Q_trans.
Qed.

Add Parametric Relation : combinator Q
  reflexivity proved by Q_refl
  symmetry proved by Q_sym
  transitivity proved by Q_trans
  as Q_setoid.

Instance : Proper (eq ==> Q ==> Q) Apply.
Proof with hauto.
    intros x y eq x0 y0 H. subst...
Qed.

(* Theorem 7 *)
Require Import List.
Export ListNotations.
Fixpoint app_comb_list (l : list combinator) : option combinator :=
    match l with
    | [] => None
    | h :: t =>
        match app_comb_list t with
        | None => Some h
        | Some a => Some (a @ h)
        end
    end.

Lemma app_comb_list_cons_inv :
    forall h t1 t2 A B,
    Some A = app_comb_list (h :: t1) ->
    Some B = app_comb_list (h :: t2) ->
    t1 = t2 ->
    A = B.
Proof.
    intros. subst. rewrite <- H in H0.
    now inversion H0.
Qed.

Fixpoint sublist {A : Type} (l : list A) (i : nat) : list A :=
    match i, l with
    | O, _ => []
    | S i', [] => []
    | S i', h :: t =>
        h :: sublist t i'
    end.

Lemma sublist_length : forall (A : Type) (l : list A),
    sublist l (length l) = l.
Proof.
    induction l; simpl.
        reflexivity.
    now rewrite IHl.
Qed.

Lemma nth_eq_sublist_eq :
    forall (A : Type) (l1 l2 : list A)
           (n i : nat)
           (d : A),
    length l1 = length l2 ->
    n < i ->
    nth n l1 d = nth n l2 d ->
    sublist l1 i = sublist l2 i.
Admitted.

Lemma nth_eq_list_eq :
    forall (A : Type) (l1 l2 : list A)
           (i : nat)
           (d : A),
    length l1 = length l2 ->
    i < length l1 ->
    nth i l1 d = nth i l2 d ->
    l1 = l2.
Proof.
    intros.
    pose proof (nth_eq_sublist_eq A l1 l2 i (length l1) d H H0 H1).
    now rewrite sublist_length, H, sublist_length in H2.
Qed.

Theorem list_comb_app_inv :
    forall (Xl Dl : list combinator)
           (X D default : combinator)
           (i : nat),
    Some X = app_comb_list Xl ->
    Some D = app_comb_list Dl ->
    length Xl = length Dl ->
    i < length Xl ->
    nth i Xl default = nth i Dl default ->
    X = D.
Proof.
    intros.
    pose proof (nth_eq_list_eq combinator Xl Dl i default H1 H2 H3).
    subst. rewrite <- H in H0. now inversion H0.
Qed.

(* Theorem 9 *)
Theorem id_x : forall x,
    Q (_I @ x) x.
Proof. hauto. Qed.

Corollary Schonfinkel_KSB : forall x y z,
    Q (B @ x @ y @ z) (_S @ (K @ _S) @ K @ x @ y @ z).
Proof.
    intros. unfold _S.
    step left.
    repeat (step right).
Qed.

Corollary Schonfinkel_KSC : forall x y z,
    Q (C @ x @ y @ z) (_S @ (B @ B @ _S) @ (K @ K) @ x @ y @ z).
Proof.
    intros. unfold _S.
    step left.
    do 14 (step right).
Abort.

Corollary Schonfinkel_KSW : forall x y,
    Q (W @ x @ y) (_S @ _S @ (_S @ K) @ x @ y).
Proof.
    intros. unfold _S.
    step left.
    do 12 (step right).
Abort.

Corollary Schonfinkel_KSI : forall x,
    Q (_I @ x) (_S @ K @ K @ x).
Proof.
    intros. unfold _I, _S.
    step left. step left.
    repeat step right.
Qed.
