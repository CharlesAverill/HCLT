From Definitions Require Export Combinator.

(* Schönfinkel Composition Function *)
Definition RuleB (x y z : combinator) : combinator :=
    x @ (y @ z).

(* Schönfinkel Interchange Function *)
Definition RuleC (x y z : combinator) : combinator :=
    x @ z @ y.

(* Schönfinkel Constancy Function *)
Definition RuleK (x y : combinator) : combinator :=
    x.

(* Doubling Function *)
Definition RuleW (x y : combinator) : combinator :=
    x @ y @ y.

(* Fixpoint reduce (expr : combinator) : combinator :=
    match expr with
    (* Special rules for I *)
    | W @ K 
        @ x @ y => (RuleI x) @ y
    | W @ K @ x     => RuleI x
    (* Special rule for S *)
    | B @ (B @ W) 
      @ (B @ B @ C)
      @ x @ y @ z   => RuleS x y z
    (* Base combinators *)
    | B @ x @ y @ z => RuleB x y z
    | C @ x @ y @ z => RuleC x y z 
    | K @ x @ y     => RuleK x y
    | W @ x @ y     => RuleW x y
    | e1 @ e2 => match e1 with
        (* 
            The recursive call here *should* be 
                reduce ((reduce x) @ y)
            but unfortunately Coq does not allow
            recursive calls with non-strictly-decreasing
            arguments. 
            
            The partially correct but non-sufficient rule
                (reduce x) @ (reduce y)
            is guaranteed to be smaller than 
                x @ y,
            but the proper implementation is not.
            
            BCKW is isomorphic to untyped lambda calculus,
            so infinite loops would be possible if the 
            recursive argument was allowed to grow.
         *)
        | x @ y => (reduce x) @ (reduce y) @ e2
        | _ => e1
        end
    | _ => expr
    end. *)

(* Gives the right answer by chance *)
(* Compute reduce ((B @ K) @ (B @ K) @ (B @ K)). *)

(* Two combinators are beta-equivalent if their reductions are equal *)
(* Definition beta_equivalent (a b : combinator) : Prop :=
    reduce a = reduce b. *)
