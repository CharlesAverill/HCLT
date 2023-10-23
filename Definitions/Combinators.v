Declare Scope combinator_scope.
Open Scope combinator_scope.

Inductive combinator : Type := 
    B | C | K | W 
    | Apply (x y : combinator).

Notation "a @ b" :=
    (Apply a b)
    (at level 50, left associativity)
    : combinator_scope.
