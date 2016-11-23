Require Import BoolProd Coq.Lists.Streams.

Declare ML Module "mTranslateStream".
Open Scope my_scope.


(* For the internal of the plugin. *)
Definition timesBool := fun Aᵗ => Aᵗ × bool.
Definition pairTrue   := fun (Aᵗ : Type) => (Aᵗ, true).


CoFixpoint id {A : Type} (x : A) : Stream A :=
  Cons x (id x).


(* This translation implements a constructive version of the negation of stream extensionality. *)

(* EqSt is bisimilarity. *)
Implement notStreamExt : forall (A : Type),
    A -> {s1 : Stream A & {s2 : Stream A & EqSt s1 s2 /\ (s1 = s2 -> False)}}
  using timesBool pairTrue.
Proof.
  compute. intros A x. exists (id x, true). exists (id x, false). cbn. split.
  - apply EqSt_reflex.
  - intro H.  apply (f_equal snd) in H; cbn in H. discriminate H.
Defined.


(* ** Some check of the translation on other types. *** *)

Implement f : {P : Prop & {Q : Prop &  ((P -> Q) -> (Q -> P) -> P = Q) -> False}}
                using timesBool pairTrue.
Abort.

Implement foo : forall A B : Type, forall (f g : A -> B), forall x, f x = g x
                using timesBool pairTrue.
Abort.

Implement wqd : forall (A : Type) (B : A -> Prop), forall x, B x
                using timesBool pairTrue.
compute.
Abort.