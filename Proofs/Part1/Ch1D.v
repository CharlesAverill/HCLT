From Definitions Require Export Combinator Rules Axioms.
Require Import Coq.Classes.RelationClasses.
Require Import Lia.

(* 
    CHAPTER 1
    Section D
*)

(* 
    Foreword
    --------

    These first few theorems are very trivial
    if you're approaching the field from a 
    modern perspective. However, as combinatory
    logic was nearly brand-new in 1930, defining
    concepts like reflexivity is essential to
    defining the behavior and properties of
    combinators as a whole.

    These theorems refer to "entities" in the
    original text, which I'm interpreting to 
    be combinators. I will generally disregard 
    combinator expressions with non-combinator
    subexpressions (free variables), such as 
        Bxyz. 

    The proofs of these theorems in the 
    original text use Curry's defined 
    axioms from Chapter 1 Section C, however 
    they're done in a sort of backwards manner. 
        In Coq, we start with a goal to prove and work
    towards reducing it to something provable
    by axioms or other theorems. Curry
    writes some of his proofs starting from 
    axioms and working towards building
    the theorem. I'm going to follow the 
    standard  Coq proof structure for 
    the most part.
*)

(* Theorem 1 *)
(* Axiom of Equality *)
Theorem Qxx : forall (x : combinator),
    Q x x.
Proof. intros. cvgleft 1. repeat step. Qed.

Global Instance Q_reflexive : Reflexive Q := Qxx.

(* Theorem 2 *)
(* Equality is Symmetric *)
Theorem Qsym : forall (x y : combinator),
    Q x y -> Q y x.
Proof.
    intros. unfold Q in *.
Admitted.

Global Instance Q_symmetric : Symmetric Q := Qsym.

(* Theorem 3 *)
(* Equality is Transitive *)
Theorem Qxy_Qyz_Qxz : forall (x y z : combinator),
    Q x y -> Q y z -> Q x z.
Proof.
    intros. destruct H, H0.
    exists (x0 + x1). revert x H. induction x0; intros; simpl in *.
    - rewrite H. apply H0.
    - destruct H as [x2 [H1 H2]]. apply IHx0 in H2.
      exists x2. split. apply H1. apply H2.
Qed.

Global Instance Q_transitive : Transitive Q := Qxy_Qyz_Qxz.

(* Theorem 4 *)
(* Inverse functional extensoinality *)
Theorem Qxy_impl_Q_xz_yz : forall (x y z : combinator),
    Q x y -> Q (x @ z) (y @ z).
Proof. 
    intros. destruct H. revert x H. induction x0; intros; simpl in *.
    - rewrite H. step.
    - destruct H as [x2 [H_step H_converge]]. exists x0.
      apply IHx0 in H_converge. 
Admitted.

(* Theorem 5 *)
Theorem x_equiv_y_impl_Qxy : forall (x y : combinator),
    x = y -> Q x y.
Proof.
    intros. rewrite H. reflexivity. Qed.

(* Theorem 6 *)
(* Equality is reflexive, transitive, and symmetric *)
(* This is a summary of the previous theorems *)

(* Theorem 7 *)
Lemma apply_equivalence : forall (X Y Z W : combinator),
    Q (X @ Y) (Z @ W) <->
        Q X Z /\ Q Y W.
Proof.
    split; intros.
    - destruct H. induction x.
        -- simpl in H. inversion H. split; reflexivity.
        -- destruct H as [x0 [H_step H_converge]]. admit.  
    - destruct H. destruct H, H0. induction x, x0.
        -- rewrite H, H0. reflexivity.
        -- rewrite H. destruct H0 as [x1 [H_step H_converge]]. 
Admitted.

Theorem alpha_equivalence : forall (X R x1 x2 r1 r2 : combinator) (i : nat)
    (X_R_HAVE_SIZE_N : size R = size X)
    (I_LT_N : i < size X)
    (EQ_Xi_Ri : nth_comb X i = nth_comb R i)
    (CHILDREN_IF_APP_X : is_app X -> Q X (x1 @ x2))
    (CHILDREN_IF_APP_R : is_app R -> Q R (r1 @ r2))
    (SUBTREES_EQ : X q= x1 @ x2 -> R q= r1 @ r2 -> Q x1 r1 /\ Q x2 r2),
    Q X R.
Proof.
    intros. induction X, R; try reflexivity.
    - contradict EQ_Xi_Ri. induction i. discriminate. contradict I_LT_N.
        simpl. lia.
    - contradict EQ_Xi_Ri. induction i. discriminate. contradict I_LT_N.
        simpl. lia.
    - contradict EQ_Xi_Ri. induction i. discriminate. contradict I_LT_N.
        simpl. lia.
    - contradict X_R_HAVE_SIZE_N. simpl. assert (1 < size R1 + size R2). {
        apply PeanoNat.Nat.lt_le_trans with (n := 1) (m := 2) (p := size R1 + size R2).
        lia. apply two_sizes_geq_2.
      } apply not_eq_sym, PeanoNat.Nat.lt_neq, H.
    - contradict EQ_Xi_Ri. induction i. discriminate. contradict I_LT_N.
        simpl. lia.
    - contradict EQ_Xi_Ri. induction i. discriminate. contradict I_LT_N.
        simpl. lia.
    - contradict EQ_Xi_Ri. induction i. discriminate. contradict I_LT_N.
        simpl. lia.
    - contradict X_R_HAVE_SIZE_N. simpl. assert (1 < size R1 + size R2). {
        apply PeanoNat.Nat.lt_le_trans with (n := 1) (m := 2) (p := size R1 + size R2).
        lia. apply two_sizes_geq_2.
        } apply not_eq_sym, PeanoNat.Nat.lt_neq, H.
    - contradict EQ_Xi_Ri. induction i. discriminate. contradict I_LT_N.
        simpl. lia.
    - contradict EQ_Xi_Ri. induction i. discriminate. contradict I_LT_N.
        simpl. lia.
    - contradict EQ_Xi_Ri. induction i. discriminate. contradict I_LT_N.
        simpl. lia.
    - contradict X_R_HAVE_SIZE_N. simpl. assert (1 < size R1 + size R2). {
        apply PeanoNat.Nat.lt_le_trans with (n := 1) (m := 2) (p := size R1 + size R2).
        lia. apply two_sizes_geq_2.
        } apply not_eq_sym, PeanoNat.Nat.lt_neq, H.
    - contradict EQ_Xi_Ri. induction i. discriminate. contradict I_LT_N.
        simpl. lia.
    - contradict EQ_Xi_Ri. induction i. discriminate. contradict I_LT_N.
        simpl. lia.
    - contradict EQ_Xi_Ri. induction i. discriminate. contradict I_LT_N.
        simpl. lia.
    - contradict X_R_HAVE_SIZE_N. simpl. assert (1 < size R1 + size R2). {
        apply PeanoNat.Nat.lt_le_trans with (n := 1) (m := 2) (p := size R1 + size R2).
        lia. apply two_sizes_geq_2.
        } apply not_eq_sym, PeanoNat.Nat.lt_neq, H.
    - contradict X_R_HAVE_SIZE_N. simpl. assert (1 < size X1 + size X2). {
        apply PeanoNat.Nat.lt_le_trans with (n := 1) (m := 2) (p := size X1 + size X2).
        lia. apply two_sizes_geq_2.
        } apply PeanoNat.Nat.lt_neq, H.
    - contradict X_R_HAVE_SIZE_N. simpl. assert (1 < size X1 + size X2). {
        apply PeanoNat.Nat.lt_le_trans with (n := 1) (m := 2) (p := size X1 + size X2).
        lia. apply two_sizes_geq_2.
        } apply PeanoNat.Nat.lt_neq, H.
    - contradict X_R_HAVE_SIZE_N. simpl. assert (1 < size X1 + size X2). {
        apply PeanoNat.Nat.lt_le_trans with (n := 1) (m := 2) (p := size X1 + size X2).
        lia. apply two_sizes_geq_2.
        } apply PeanoNat.Nat.lt_neq, H.
    - contradict X_R_HAVE_SIZE_N. simpl. assert (1 < size X1 + size X2). {
        apply PeanoNat.Nat.lt_le_trans with (n := 1) (m := 2) (p := size X1 + size X2).
        lia. apply two_sizes_geq_2.
        } apply PeanoNat.Nat.lt_neq, H.
    - admit.
Qed.

(* Theorem 8 *)
(* 
    The theorems 
        "X is equivalent to R" 
    and
        "From the previously given theorems
         of the form 
            'x_i is equivalent to y_i,`
         the theorem 
            '|- X = R'
         can be proved using only
         Theorem 5 and properties of equality"
    are equivalent.
*)
(* 
    I am not confident that this theorem 
    can be accurately and succinctly 
    constructed in Coq.
*)

(* Theorem 9 *)
Theorem reduce_Ix : forall (x : combinator),
    cI @ x = x.
Proof. 
    intros. repeat step.
    reflexivity. 
Qed.

Lemma reduce_Ixy : forall (x y : combinator),
    cI @ x @ y = x @ y.
Proof. 
    intros. repeat step. 
    reflexivity.
Qed.
