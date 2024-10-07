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
    Unshelve. exact B.
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
    intros; induction H...
    subst...
Qed.

(* Theorem 6 *)
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Setoids.Setoid.

Instance Q_equiv : Equivalence Q.
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
Abort.

(* Theorem 9 *)
Theorem id_x : forall x,
    Q (_I @ x) x.
Proof. hauto. Qed.

Corollary Schonfinkel_KSB :
    Q B (_S @ (K @ _S) @ K).
Abort.

Corollary Schonfinkel_KSC :
    Q C (_S @ (B @ B @ _S) @ (K @ K)).
Abort.

Corollary Schonfinkel_KSW :
    Q W (_S @ _S @ (_S @ K)).
Abort.

Corollary Schonfinkel_KSI :
    Q _I (_S @ K @ K).
Abort.
