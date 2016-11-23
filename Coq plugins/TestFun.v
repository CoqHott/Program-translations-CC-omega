Require Import BoolProd.

Declare ML Module "mTranslateFun".
Open Scope my_scope.


Tactic Notation "intro'" ident(X) := refine (_, true); intro X.
Tactic Notation "intros'" := repeat (refine (_, true); intro).
Tactic Notation "specialize'" hyp(H) uconstr(t) := apply fst in H; specialize (H t).


(* This translation allow to implement the negation of funext. *)
Implement notFunext :
  (forall (A B : Type) (f g : A -> B), (forall x, f x = g x) -> f = g) -> False.
Proof.
  intro' H.
  specialize' H unit.
  specialize' H unit.
  specialize' H (fun x => x, true).
  specialize' H (fun x => x, false).
  specialize' H (fun x => eq_refl, true).
  apply (f_equal snd) in H; cbn in H.
  discriminate H.
Defined.

(* A more constructive version on inhabited types. *)
Implement notFunext' : forall (A B : Type),
    B -> {f : A -> B & { g : A -> B & ((forall x, f x = g x) -> f = g) -> False}}.
Proof.
  intro' A. intro' B. intro' y.
  pose (f := fun _ : A => y). exists (f, true). exists (f, false).
  intro' H.
  specialize' H (fun x => eq_refl, true).
  apply (f_equal snd) in H; cbn in H.
  discriminate H.
Defined.


Check notFunext'.
Compute notFunext'ᶠ.


Definition notFunext'Nat := notFunext' nat nat.

(* If we want to prove some result about notFunext'Nat we first hae to extend the translation to it. *)
Translate notFunext'Nat.

(* Now we can postulate new principles about notFunext'Nat, always preserving consistency. *)
Implement notFunext'Nat01 : notFunext'Nat 0 = notFunext'Nat 1 -> False.
Proof.
  compute. refine (_, true). intro H.
  pose proof (f_equal (@projT1 _ _) H); cbn in *.
  apply (f_equal fst) in H0; cbn in *.
  assert ((fun _ : nat => 0) 0 = (fun _ : nat => 1) 0).
  change ((fun _ : nat => 0) 0 = (fun _ : nat => 1) 0). rewrite H0. reflexivity.
  discriminate H1.
Defined.



(* ** Some check of the translation on other types. *** *)

Implement f : forall (f : Type -> Type), f Type.
Abort.

Implement foo : forall A B : Type, forall (f g : A -> B), forall x, f x = g x.
Abort.

Implement wqd : forall (A : Type) (B : A -> Prop), forall x, B x.
Abort.

Implement foo : forall (A : Type) (a : A) (p : a = a), p = eq_refl a.
Abort.