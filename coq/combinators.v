Require Import List.
Import ListNotations.

Declare Scope combinator_scope.
Open Scope combinator_scope.

Inductive combinator : Type :=
    | B
    | C
    | K
    | W
    | Apply (c1 c2 : combinator).

Definition combinator_dec : forall s1 s2 : combinator, {s1 = s2} + {s1 <> s2}.
Proof.
    decide equality.
Defined.

Notation "a @ b" :=
    (Apply a b)
    (at level 50, left associativity)
    : combinator_scope.

(* I = WK *)
Definition I := W @ K.
(* S = B(BW)(BBC) *)
Definition S := B @ (B @ W) @ (B @ B @ C).

(* X0 X1 X2 ... XN = (((X0 X1) X2) ... XN)*)
Definition comb_list_to_comb (cl : list combinator) : combinator :=
    match cl with
    | [] => I
    | h :: t => List.fold_left (fun (acc item : combinator) => acc @ item) t h
    end.

Fixpoint reduce (expr : combinator) : combinator :=
    match expr with
    | e1 @ e2 => match e1 with
        | B => match e2 with 
            | x @ y @ z => x @ (y @ z)
            | _ => B @ reduce e2
            end
        | C => match e2 with 
            | x @ y @ z => x @ z @ y
            | _ => C @ reduce e2
            end
        | K => match e2 with 
            | x @ y => x
            | _ => K @ reduce e2
            end
        | W => match e2 with
            | x @ y => x @ y @ y
            | _ => W @ e2
            end
        (* 
            The recursive call here *should* be 
                reduce ((reduce x) @ y)
            but unfortunately Coq does not allow
            recursive calls with non-strictly-decreasing
            arguments. 
                (reduce x) @ (reduce y)
            is guaranteed to be smaller than 
                x @ y,
            but the proper implementation is not.
            
            BCKW is isomorphic to untyped lambda calculus,
            so infinite loops (that Coq also does not allow)
            would be possible if the recursive argument
            was allowed to grow.
         *)
        | x @ y => (reduce x) @ (reduce y)
        end
    | _ => expr
    end.

(* Gives the right answer by chance *)
Compute reduce ((B @ K) @ (B @ K) @ (B @ K)).
