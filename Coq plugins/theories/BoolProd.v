

Inductive bool := true : bool | false : bool.


(* We use primitive projections so that the projections of the product are untyped. *)
Set Primitive Projections.

Record prod (A : Type) (B : Type) : Type := pair { fst : A; snd : B }.

Notation "x × y" := (prod x y) (at level 40) : my_scope.
Notation "( x , y )" := (pair _ _ x y) : my_scope.
Arguments pair {_ _} _ _.
Arguments fst {_ _} _.
Arguments snd {_ _} _.
