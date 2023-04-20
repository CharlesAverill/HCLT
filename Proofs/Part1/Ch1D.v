From Definitions Require Export Combinator.

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

    The proofs of these theorems in the original
    text use Curry's defined axioms from 
    Chapter 1 Section C, however I'm uncomfortable
    with using Axiom definitions in Coq for fear
    of breaking the internal proof checker.
    Therefore, my proofs here and many after
    will not directly follow the structure 
    of Curry's proofs but will instead take
    inspiration from them where it is 
    necessary.
*)

(* Theorem 1 *)
(* Axiom of Equality *)
Theorem Qxx : forall x : combinator,
    x = x.
Proof. trivial. Qed.

(* Theorem 2 *)
(* Equality is reflexive *)
Theorem Qxy_Qyx : forall x y : combinator,
    x = y -> y = x.
Proof. intros. symmetry. apply H. Qed.

(* Theorem 3 *)
(* Transitive Property *)
Theorem Qxy_Qyz_Qxz : forall x y z : combinator,
    x = y -> y = z -> x = z.
Proof.
    intros. rewrite <- H0. apply H.
Qed.

(* Theorem 4 *)
(* Inverse functional extensoinality *)
Theorem Qxy_impl_Q_xz_yz : forall x y z : combinator,
    x = y -> x @ z = y @ z.
Proof. intros. rewrite H. reflexivity. Qed.
