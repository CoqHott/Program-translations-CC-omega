Require Import List.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Le Gt.

Require Sorts PTS_Prop PTS_Prop_weakened PTS_SigmaBoolProp.
Module S := PTS_Prop.
Module S' := PTS_Prop_weakened.
Module T := PTS_SigmaBoolProp.
Import Sorts.withProp T.

Reserved Notation "M 'ᵗ'" (at level 20).

Fixpoint tsl (t : S.Term) : T.Term :=
  match t with
  | S.Var v => Var v
  | S.Sort s => ⟨Σ !s Bool, true⟩
  | S.Π A B => ⟨Π (π1 (A ᵗ)) (π1 (B ᵗ)), true⟩
  | S.λ A M => λ (π1 (A ᵗ)) (M ᵗ)
  | S.App M N => (M ᵗ) · (N ᵗ)
  end
where " M 'ᵗ'" := (tsl M).


Reserved Notation "Γ 'ᶜ'" (at level 50).

Fixpoint tsl_ctx (Γ : S.Env) : T.Env :=
  match Γ with
  | nil => nil
  | A :: Γ => (π1 (A ᵗ)) :: (Γ ᶜ)
  end
where "Γ 'ᶜ'" := (tsl_ctx Γ).


Definition tsl_lift M : forall n k, (S.lift_rec n k M) ᵗ = (M ᵗ) ↑ n # k.
  induction M; cbn; intros; auto;
    try (now rewrite ?IHM, ?IHM1, ?IHM2, ?IHM3, ?IHM4, ?IHM5, ?IHM6).
  now destruct (le_gt_dec k v).
Defined.

Definition tsl_var_ctx Γ A v : S.item_lift A Γ v -> π1 (A ᵗ) ↓ v ⊂ Γ ᶜ.
  induction 1 as [t [H1 H2]]. exists (π1 (t ᵗ)). split; cbn. rewrite H1.
  apply f_equal. apply tsl_lift.
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
  induction 1; cbn; auto. rewrite tsl_subst. 
  all: try induction IHBeta; eauto 5.
Defined.    
Hint Resolve tsl_red.

Definition tsl_conv M N : S.Betac M N -> M ᵗ ≡ N ᵗ.
  induction 1; eauto 2. constructor.
  induction H; eauto.
Defined.
Hint Resolve tsl_conv.


(* Some helpers *)

Definition next_sort : Sorts -> Sorts.
  destruct 1 as [|i]. exact (U 0). exact (U (S i)).
Defined.

Definition typ_sort {Γ s} : Γ ⊣ -> Γ ⊢ !s : !(next_sort s).
  destruct s; cbn; econstructor; eauto.
Defined.
Hint Resolve typ_sort.

Lemma Bool_next_sort Γ s : Γ ⊣ -> Γ ⊢ Bool : !(next_sort s).
  intro. destruct s; econstructor; eauto.
Defined.
Hint Resolve Bool_next_sort.

Definition helper1 {Γ M A B s} {H : Γ ⊢ A : !s} : Γ ⊢ M : π1 ⟨A, B⟩ -> Γ ⊢ M : A.
  intro. econstructor; try eassumption. auto.
Defined.

Definition helper2 {Γ M A s} {H : Γ ⊢ A : !s}
  : Γ ⊢ M : A -> Γ ⊢ M : π1 ⟨A, true⟩.
  intro. unshelve econstructor; try eassumption. auto.
  pose proof (wf_typ H).
  unshelve econstructor. exact Bool. 
  econstructor; auto.
Defined.

Definition helper3 {Γ s} : Γ ⊣ -> Γ ⊢ Σ !s Bool : !(next_sort s).
  intro. destruct s; cbn. apply (cΣ (i:=0) (j:=0)); eauto.
  simple refine (let X := cΣ (i:=S n) (j:=0) _ _ in _).
  6: rewrite PeanoNat.Nat.max_0_r in X; exact X.
  all: eauto.
Defined.
Hint Resolve helper3.


Definition tsl_correction :
  (forall Γ M A, S.typ Γ M A -> Γ ᶜ ⊢ M ᵗ : π1 (A ᵗ)) /\ (forall Γ,  S.wf Γ -> Γ ᶜ ⊣).
Proof.
  assert ((forall Γ M A, S'.typ Γ M A -> Γ ᶜ ⊢ M ᵗ : π1 (A ᵗ))
          /\ (forall Γ,  S'.wf Γ -> Γ ᶜ ⊣)). {
  simple eapply S'.typ_induc; cbn.
  - intros Γ A v w H i. eauto.
  - intros Γ s s' w H a.
    unshelve eapply helper2. 2: now apply helper3.
    econstructor. destruct a; cbn.
    simple refine (let X := cΣ (i:=j) (j:=0) _ _ in _).
    6: rewrite PeanoNat.Nat.max_0_r in X; exact X.
    eauto. eauto.
    simple refine (let X := cΣ (i:=i) (j:=0) _ _ in _).
    6: rewrite PeanoNat.Nat.max_0_r in X; exact X.
    eauto. eauto. eauto.
  - intros Γ A B s s' s'' r _ H _ H0.
    pose proof (wf_typ H). pose proof (wf_typ H0 : π1 (A ᵗ) :: Γ ᶜ ⊣).
    unshelve eapply helper2. 2: now apply helper3.
    econstructor.
    + econstructor. exact r. all: econstructor; eauto.
    + now constructor.
  - intros Γ A B s s' s'' M r _ H _ H0 _ H1.
    pose proof (wf_typ H). pose proof (wf_typ H0 : π1 (A ᵗ) :: Γ ᶜ ⊣).
    unshelve eapply helper2. 2: econstructor. 2: exact r.
    + econstructor. eauto. 
    + econstructor. eauto. 
    + econstructor. exact r.
      econstructor. eauto. econstructor. eauto.
      assumption.
  - intros Γ M N A B s s' s'' r _ H _ H0 _ H1 _ H2. rewrite tsl_subst.
      pose proof (wf_typ H). pose proof (wf_typ H0 : π1 (A ᵗ) :: Γ ᶜ ⊣).
      assert (Γ ᶜ ⊢ π1 (A ᵗ) : ! s). {
        unshelve eapply helper1 in H.  2: now apply helper3.
        econstructor. exact H. }
      assert (π1 (A ᵗ) :: Γ ᶜ ⊢ π1 (B ᵗ) : ! s'). {
        unshelve eapply helper1 in H0.  2: now apply helper3.
        econstructor. exact H0. }
      simple refine (let X := helper1 H1 in cApp X H2); eauto.
  - intros Γ M A B s b _ H _ H0. pose proof (wf_typ H).
    econstructor. 2: exact H.
    + clear s H H0. induction b; eauto 2. apply Betac_Betas.
      induction H; eauto 2. apply tsl_red in H. induction H; eauto.
    + unshelve eapply helper1 in H0. exact (next_sort s). eauto.
      exact s. econstructor. exact H0.
  - constructor.
  - intros Γ A s t H. pose proof (wf_typ H).
    unshelve eapply helper1 in H. exact (next_sort s). eauto.
    econstructor. econstructor. exact H. }
  split; intros. apply H. now apply S'.weakenedapp_ok.
  apply H. now apply S'.weakenedapp_ok.
Defined.

(* Print Assumptions tsl_correction. *)


Theorem thinning : forall {Γ M T A s}, Γ ⊢ M : T -> Γ ⊢ A : !s -> A::Γ ⊢ M ↑ 1 : T ↑ 1.
Admitted.

Definition tsl_consistency : (exists M, S.typ nil M S.empty) -> exists M', nil ⊢ M' : ⊥.
Proof.
  intros [M H]. apply tsl_correction in H. cbn in H.
  exists (λ !(U 0) (M ᵗ ↑ · ⟨#0, true⟩)). econstructor.
  apply (Rel0 1 0). eauto.
  econstructor. eauto. econstructor. split. 2: eauto. reflexivity.

  simple refine (let H' := Cnv _ H _ in _).
  exact (Π (Σ !(U 0) Bool) (π1 # 0)). exact (U 1).
  econstructor. trans. eauto.
  apply Betas_Beta. eauto.
  econstructor. apply (Rel0 1 0).
  apply (cΣ (i:=1) (j:=0)); eauto.
  econstructor. econstructor. eauto.
  econstructor. split. 2: eauto. cbn. reflexivity.
  clearbody H'.
  simple refine (let H'' := thinning H' _ in _).
  exact !(U 0). exact (U 1). eauto.
  simple refine (let H''' := cApp H'' _ in _).
  exact ⟨ # 0, true ⟩. econstructor. econstructor.
  eauto. econstructor. split. 2: eauto. reflexivity. eauto.
  clearbody H'''.
  econstructor. 2: exact H'''.
  cbn. eauto. econstructor. eauto. econstructor. split.
  2: eauto. reflexivity.
Defined.
