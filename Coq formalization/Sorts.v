Require Import Compare_dec.
Require Import Lt Le Gt.

(** To deal with variable binding, we use de Bruijn indexes: *)
Definition Vars := nat.

Module withProp.
  Inductive Sorts :=
  | prop : Sorts
  | U : nat -> Sorts.

  Inductive Ax : Sorts -> Sorts -> Prop :=
  | Ax0 : forall i j, i < j -> Ax (U i) (U j)
  | Ax1 : forall i, Ax prop (U i).

  Inductive Rel : Sorts -> Sorts -> Sorts -> Prop :=
  | Rel0 : forall i j, Rel (U i) (U j) (U (max i j))
  | Rel1 : forall i, Rel (U i) prop prop.

  Hint Constructors Ax.
  Hint Constructors Rel.
End withProp.

Module withoutProp.
  Inductive Sorts :=
  | U : nat -> Sorts.

  Inductive Ax : Sorts -> Sorts -> Prop :=
  | Ax0 : forall i j, i < j -> Ax (U i) (U j).

  Inductive Rel : Sorts -> Sorts -> Sorts -> Prop :=
  | Rel0 : forall i j, Rel (U i) (U j) (U (max i j)).

  Hint Constructors Ax.
  Hint Constructors Rel.
End withoutProp.