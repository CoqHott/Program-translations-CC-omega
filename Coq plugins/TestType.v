Require Import BoolProd.

Declare ML Module "mTranslateType".
Open Scope my_scope.


(* For the internal of the plugin. *)
Definition timesBool := fun Aᵗ => Aᵗ × bool.
Definition pairTrue   := fun (Aᵗ : Type) => (Aᵗ, true).


(* This translation negates propositional extensionality. *)

Implement notPropExt : {P : Prop & {Q : Prop &  ((P -> Q) -> (Q -> P) -> P = Q) -> False}}
                         using timesBool pairTrue.
Proof.
  compute. exists (True, true). exists (True, false). cbn.
  intro H. specialize (H (@id True) (@id True)).
  apply (f_equal snd) in H. cbn in H.
  discriminate H.
Defined.


(* ** Some check of the translation on other types. *** *)

Implement a : Type * Type using timesBool pairTrue.
compute.
Abort.

Implement foo : forall A B : Type, forall (f g : A -> B), forall x, f x = g x
                using timesBool pairTrue.
compute.
Abort.

Implement wqd : forall (A : Type) (B : A -> Prop), forall x, B x
                using timesBool pairTrue.
compute.
Abort.