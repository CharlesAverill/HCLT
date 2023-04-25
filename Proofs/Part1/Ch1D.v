From Definitions Require Export Combinator Rules Axioms.

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

(* Theorem 7 *)
Lemma apply_equivalence : forall (A B C D : combinator),
    Q (A @ B) (C @ D) <->
        Q A C /\ Q B D.
Proof.
    split.
    - split; inversion H; reflexivity.
    - intros. destruct H. rewrite H, H0. reflexivity. 
Qed.

Theorem alpha_equivalence : forall (X R x1 x2 r1 r2 : combinator) (i : nat)
    (X_R_HAVE_SIZE_N : size R = size X)
    (I_LT_N : i < size X)
    (EQ_Xi_Ri : nth_comb X i = nth_comb R i)
    (CHILDREN_IF_APP_X : is_app X -> Q X (x1 @ x2))
    (CHILDREN_IF_APP_R : is_app R -> Q R (r1 @ r2))
    (SUBTREES_EQ : X = Apply x1 x2 -> R = r1 @ r2 -> Q x1 r1 /\ Q x2 r2),
    Q X R.
Proof.
    intros.
    destruct X; simpl in *.
    5: {
        destruct R; simpl in *.
        5: {
            specialize (CHILDREN_IF_APP_X I).
            specialize (CHILDREN_IF_APP_R I).
            destruct SUBTREES_EQ. trivial. trivial.
            apply apply_equivalence in CHILDREN_IF_APP_R.
            apply apply_equivalence in CHILDREN_IF_APP_X.
            destruct CHILDREN_IF_APP_R, CHILDREN_IF_APP_X.
            rewrite H1, H2, H3, H4.
            apply apply_equivalence. split. apply H. apply H0.
        }

        contradict X_R_HAVE_SIZE_N.
        assert (2 <= size X1 + size X2). {
            apply PeanoNat.Nat.add_le_mono with (n := 1) (m := size X1) (p := 1) (q := size X2);
                try apply size_ge_1.
        } assert (1 < size X1 + size X2). {
            apply PeanoNat.Nat.lt_le_trans with (m := 2). apply le_n.
            apply H.
        } apply PeanoNat.Nat.lt_neq, H0.

        contradict X_R_HAVE_SIZE_N.
        assert (2 <= size X1 + size X2). {
            apply PeanoNat.Nat.add_le_mono with (n := 1) (m := size X1) (p := 1) (q := size X2);
                try apply size_ge_1.
        } assert (1 < size X1 + size X2). {
            apply PeanoNat.Nat.lt_le_trans with (m := 2). apply le_n.
            apply H.
        } apply PeanoNat.Nat.lt_neq, H0.

        contradict X_R_HAVE_SIZE_N.
        assert (2 <= size X1 + size X2). {
            apply PeanoNat.Nat.add_le_mono with (n := 1) (m := size X1) (p := 1) (q := size X2);
                try apply size_ge_1.
        } assert (1 < size X1 + size X2). {
            apply PeanoNat.Nat.lt_le_trans with (m := 2). apply le_n.
            apply H.
        } apply PeanoNat.Nat.lt_neq, H0.

        contradict X_R_HAVE_SIZE_N.
        assert (2 <= size X1 + size X2). {
            apply PeanoNat.Nat.add_le_mono with (n := 1) (m := size X1) (p := 1) (q := size X2);
                try apply size_ge_1.
        } assert (1 < size X1 + size X2). {
            apply PeanoNat.Nat.lt_le_trans with (m := 2). apply le_n.
            apply H.
        } apply PeanoNat.Nat.lt_neq, H0.
    }
    - destruct i; simpl in *. 
        symmetry. apply comb0_size1_impl_BCKW.
        apply X_R_HAVE_SIZE_N. symmetry. apply EQ_Xi_Ri.
        apply PeanoNat.Nat.lt_1_r in I_LT_N. 
        contradict I_LT_N. apply PeanoNat.Nat.neq_succ_0.
    - destruct i; simpl in *. 
        symmetry. apply comb0_size1_impl_BCKW.
        apply X_R_HAVE_SIZE_N. symmetry. apply EQ_Xi_Ri.
        apply PeanoNat.Nat.lt_1_r in I_LT_N. 
        contradict I_LT_N. apply PeanoNat.Nat.neq_succ_0.
    - destruct i; simpl in *. 
        symmetry. apply comb0_size1_impl_BCKW.
        apply X_R_HAVE_SIZE_N. symmetry. apply EQ_Xi_Ri.
        apply PeanoNat.Nat.lt_1_r in I_LT_N. 
        contradict I_LT_N. apply PeanoNat.Nat.neq_succ_0.
    - destruct i; simpl in *. 
        symmetry. apply comb0_size1_impl_BCKW.
        apply X_R_HAVE_SIZE_N. symmetry. apply EQ_Xi_Ri.
        apply PeanoNat.Nat.lt_1_r in I_LT_N. 
        contradict I_LT_N. apply PeanoNat.Nat.neq_succ_0.
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
    reduce (cI @ x) = x.
Proof. reflexivity. Qed.

Lemma reduce_Ixy : forall (x y : combinator),
    reduce (cI @ x @ y) = x @ y.
Proof. intros. simpl. reflexivity. Qed.
