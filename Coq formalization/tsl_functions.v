Require Import List.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Le Gt.

Require Sorts PTS PTS_SigmaBool.
Module S := PTS.
Module T := PTS_SigmaBool.
Import T Sorts.withoutProp.


Reserved Notation "M 'ᵗ'" (at level 20).

Fixpoint tsl (t : S.Term) : T.Term :=
  match t with
  | S.Var v => Var v
  | S.Sort s => !s
  | S.Π A B => Σ (Π (A ᵗ) (B ᵗ)) Bool
  | S.λ A M => ⟨λ (A ᵗ) (M ᵗ), true⟩
  | S.App M N => (π1 (M ᵗ)) · (N ᵗ)
  | S.Eq A M N => Eq (A ᵗ) (M ᵗ) (N ᵗ)
  | S.refle M => refle (M ᵗ)
  | S.J A P t1 u t2 p => J (A ᵗ) (P ᵗ) (t1 ᵗ) (u ᵗ) (t2 ᵗ) (p ᵗ)
  end
where " M 'ᵗ'" := (tsl M).


Reserved Notation "Γ 'ᶜ'" (at level 50).

Fixpoint tsl_ctx (Γ : S.Env) : T.Env :=
  match Γ with
  | nil => nil
  | A :: Γ => (A ᵗ) :: (Γ ᶜ)
  end
where "Γ 'ᶜ'" := (tsl_ctx Γ).


Definition tsl_lift M : forall n k, (S.lift_rec n k M) ᵗ = (M ᵗ) ↑ n # k.
  induction M; cbn; intros; auto;
    try (now rewrite ?IHM, ?IHM1, ?IHM2, ?IHM3, ?IHM4, ?IHM5, ?IHM6).
  now destruct (le_gt_dec k v).
Defined.


Definition tsl_var_ctx Γ A v : S.item_lift A Γ v -> A ᵗ ↓ v ⊂ Γ ᶜ.
  induction 1 as [t [H1 H2]]. exists (t ᵗ). split. rewrite H1. apply tsl_lift.
  clear A H1. induction H2. econstructor. econstructor. exact IHitem.
Defined.
Hint Resolve tsl_var_ctx.


Definition tsl_subst M : forall N n, (S.subst_rec N M n) ᵗ = (M ᵗ)[n ← N ᵗ].
  induction M; cbn; intros; auto;
    try (now rewrite ?IHM, ?IHM1, ?IHM2, ?IHM3, ?IHM4, ?IHM5, ?IHM6).
  destruct (lt_eq_lt_dec v n); cbn.
  destruct s. reflexivity. apply tsl_lift. reflexivity.
Defined.


Tactic Notation "trans" := eapply Betas_trans; [eapply Betas_Beta|].

Definition tsl_red M N : S.Beta M N -> M ᵗ →→ N ᵗ.
  induction 1; cbn.
  rewrite tsl_subst. trans; eauto. eauto.
  all: induction IHBeta; eauto 3.
  all: econstructor; eauto. 
Defined.    
Hint Resolve tsl_red.

Definition tsl_conv M N : S.Betac M N -> M ᵗ ≡ N ᵗ.
  induction 1; eauto 2. constructor.
  induction H; eauto.
Defined.
Hint Resolve tsl_conv.

Lemma Bool_s Γ s : Γ ⊣ -> Γ ⊢ Bool : !s.
  intro. destruct s; now constructor.
Defined.
Hint Resolve Bool_s.


Definition tsl_correction :
  (forall Γ M A, S.typ Γ M A -> Γ ᶜ ⊢ M ᵗ : A ᵗ) /\ (forall Γ,  S.wf Γ -> Γ ᶜ ⊣).
Proof.
  unshelve eapply S.typ_induc; cbn; eauto 3.
  - intros Γ A B s s' s'' r _ H _ H0. destruct r.
    pose proof (cΠ (Rel0 _ _) H H0).
    simple refine (let X := cΣ H1 (cBool 0 _) in _). eauto.
    now rewrite PeanoNat.Nat.max_0_r in X.
  - intros Γ A B s s' s'' M r _ H _ H0 _ H1.
    econstructor. eauto.
    constructor. eapply wf_typ. eassumption.
  - intros Γ M N A B t H _ H0. rewrite tsl_subst. econstructor.
    econstructor. eassumption. assumption.
  - intros Γ A P t1 u t2 p s t H t0 H0 t3 H1. rewrite tsl_subst.
    rewrite tsl_subst in H0. econstructor; eassumption.
Defined.

(* Print Assumptions tsl_correction. *)


Definition tsl_consistency : (exists M, S.typ nil M S.empty) -> exists M', nil ⊢ M' : ⊥.
Proof.
  intros [M H]. apply tsl_correction in H. cbn in H.
  exists (π1 (M ᵗ)). eauto.
Defined.
