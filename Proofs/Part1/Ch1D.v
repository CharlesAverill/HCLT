From Definitions Require Export Combinator.
From Definitions Require Export Axioms.

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
Proof. intros. reflexivity. Qed.

(* Theorem 2 *)
(* Equality is Symmetric *)
Theorem Qxy_Qyx : forall (x y : combinator),
    Q x y -> Q y x.
Proof. intros. symmetry. apply H. Qed.

(* Theorem 3 *)
(* Equality is Transitive *)
Theorem Qxy_Qyz_Qxz : forall (x y z : combinator),
    Q x y -> Q y z -> Q x z.
Proof.
    intros. rewrite <- H0. apply H.
Qed.

(* Theorem 4 *)
(* Inverse functional extensoinality *)
Theorem Qxy_impl_Q_xz_yz : forall (x y z : combinator),
    Q x y -> Q (x @ z) (y @ z).
Proof. intros. rewrite H. reflexivity. Qed.

(* Theorem 5 *)
Theorem x_equiv_y_impl_Qxy : forall (x y : combinator),
    x = y -> Q x y.
Proof.
    intros. apply H. Qed.

(* Theorem 6 *)
(* Equality is reflexive, transitive, and symmetric *)
(* This is a summary of the previous theorems *)

Lemma no_Sn_lt_1 : forall (n : nat),
    ~ S n < 1.
Proof.
    intros. induction n.
    - apply PeanoNat.Nat.lt_irrefl.
    - admit.
Admitted.

(* Theorem 7 *)
Theorem alpha_equivalence : forall (X R : combinator) (n i : nat)
    (X_HAS_SIZE_N : size X = n)
    (R_HAS_SIZE_N : size R = n)
    (I_LT_N : i < n)
    (EQ_Xi_Ri : nth_comb X i = nth_comb R i),
    X = R.
Proof.
    intros. induction X; simpl in *.
    5: {
        destruct i. contradict EQ_Xi_Ri. 
        destruct R; simpl; try congruence.

        admit.
        admit.
    }
    - rewrite <- X_HAS_SIZE_N in R_HAS_SIZE_N.
        destruct i; simpl in *. 
            symmetry. apply comb0_size1_impl_BCKW.
            apply R_HAS_SIZE_N. symmetry. apply EQ_Xi_Ri.

            contradict I_LT_N. rewrite <- X_HAS_SIZE_N.
            apply no_Sn_lt_1.
    - rewrite <- X_HAS_SIZE_N in R_HAS_SIZE_N.
        destruct i; simpl in *. 
        symmetry. apply comb0_size1_impl_BCKW.
        apply R_HAS_SIZE_N. symmetry. apply EQ_Xi_Ri.

        contradict I_LT_N. rewrite <- X_HAS_SIZE_N.
        apply no_Sn_lt_1.
    - rewrite <- X_HAS_SIZE_N in R_HAS_SIZE_N.
        destruct i; simpl in *. 
        symmetry. apply comb0_size1_impl_BCKW.
        apply R_HAS_SIZE_N. symmetry. apply EQ_Xi_Ri.

        contradict I_LT_N. rewrite <- X_HAS_SIZE_N.
        apply no_Sn_lt_1.
    - rewrite <- X_HAS_SIZE_N in R_HAS_SIZE_N.
        destruct i; simpl in *. 
        symmetry. apply comb0_size1_impl_BCKW.
        apply R_HAS_SIZE_N. symmetry. apply EQ_Xi_Ri.

        contradict I_LT_N. rewrite <- X_HAS_SIZE_N.
        apply no_Sn_lt_1.
Admitted. 
            
