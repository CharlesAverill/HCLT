Definition relation (X : Type) := X -> X -> Prop.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Definition transitive {X : Type} (R : relation X) :=
    forall a b c, R a b -> R b c -> R a b.

Definition symmetric {X : Type} (R : relation X) :=
    forall a b, R a b -> R b a.

Definition reflexive {X : Type} (R : relation X) :=
    forall a, R a a.
