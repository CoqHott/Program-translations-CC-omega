Require Import List.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Le Gt.
Require Import Omega.

Require Sorts PTS_Stream PTS_SigmaBoolStream.
Module S := PTS_Stream.
Module T := PTS_SigmaBoolStream.
Import T Sorts.withoutProp.


Reserved Notation "M 'ᵗ'" (at level 20).

Definition S' Aᵗ sᵗ P0ᵗ P1ᵗ :=
  λ (Stream Aᵗ) (λ (Stream (Aᵗ ↑)) ((sᵗ ↑ 2) · ⟨#1, π2 (P0ᵗ ↑ 2)⟩ · ⟨#0, π2 (P1ᵗ ↑ 2)⟩)).
Definition M' Aᵗ sᵗ Mᵗ P0ᵗ P1ᵗ :=
  λ (Stream Aᵗ) (λ (Stream (Aᵗ ↑)) (λ ((sᵗ ↑ 2) · ⟨#1, π2 (P0ᵗ ↑ 2)⟩ · ⟨#0, π2 (P1ᵗ ↑ 2)⟩) ((Mᵗ ↑ 3) · ⟨#2, π2 (P0ᵗ ↑ 3)⟩ · ⟨#1, π2 (P1ᵗ ↑ 3)⟩ · #0))).

Fixpoint tsl (t : S.Term) : T.Term :=
  match t with
  | S.Var v => Var v
  | S.Sort s => !s
  | S.Π A B => Π (A ᵗ) (B ᵗ)
  | S.λ A M => λ (A ᵗ) (M ᵗ)
  | S.App M N => (M ᵗ) · (N ᵗ)
  | S.Eq A M N => Eq (A ᵗ) (M ᵗ) (N ᵗ)
  | S.refle M => refle (M ᵗ)
  | S.J A P t1 u t2 p => J (A ᵗ) (P ᵗ) (t1 ᵗ) (u ᵗ) (t2 ᵗ) (p ᵗ)
  | S.Stream A => Σ (Stream (A ᵗ)) Bool
  | S.hd M => hd (π1 (M ᵗ))
  | S.tl M => ⟨tl (π1 (M ᵗ)), π2 (M ᵗ)⟩
  | S.stream_corec s M0 M1 N => ⟨stream_corec (s ᵗ) (M0 ᵗ) (M1 ᵗ) (N ᵗ), true⟩
  | S.Bisim A M N => Bisim (A ᵗ) (π1 (M ᵗ)) (π1 (N ᵗ))
  | S.hd_b M => hd_b (M ᵗ)
  | S.tl_b M => tl_b (M ᵗ)
  | S.bisim_corec A s M0 M1 P0 P1 N =>
    bisim_corec (A ᵗ) (S' (A ᵗ) (s ᵗ) (P0 ᵗ) (P1 ᵗ)) (M' (A ᵗ) (s ᵗ) (M0 ᵗ) (P0 ᵗ) (P1 ᵗ))
                (M' (A ᵗ) (s ᵗ) (M1 ᵗ) (P0 ᵗ) (P1 ᵗ)) (π1 (P0 ᵗ)) (π1 (P1 ᵗ)) (N ᵗ)
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
    rewrite ?IHM, ?IHM1, ?IHM2, ?IHM3, ?IHM4, ?IHM5, ?IHM6, ?IHM7; trivial.
  now destruct (le_gt_dec k v).
  assert (H0: Stream (M1 ᵗ) ↑ n # k ↑ = Stream (M1 ᵗ) ↑ ↑ n # (S k)). {
    rewrite <- liftP2. reflexivity. omega. }
  unfold S', M'; rewrite !H0.
  match goal with
  | |- bisim_corec _ ?s ?M0 ?M1 _ _ _ = bisim_corec _ ?s' ?M0' ?M1' _ _ _
    => assert (X0 : s = s');
        [|assert (X1: M0 = M0');
          [|assert (X2: M1 = M1'); [|rewrite X0, X1, X2; reflexivity]]]
  end.
  + apply f_equal, f_equal.
    rewrite <- liftP2. apply f_equal2. apply f_equal. rewrite <- liftP2. reflexivity.
    omega. rewrite <- liftP2. reflexivity. all: omega.
  + clear X0. apply f_equal, f_equal.
  match goal with
  | |- λ ?A ?M = λ ?A' ?M' => assert (X0 : A = A');
                              [|assert (X1: M = M'); [|rewrite X0, X1; reflexivity]]
  end.
    * rewrite <- liftP2. apply f_equal2. apply f_equal, f_equal. rewrite <- liftP2.
      reflexivity. omega. rewrite <- liftP2. reflexivity. all: omega.
    * rewrite <- liftP2. apply f_equal2. apply f_equal2. apply f_equal2, f_equal.
      reflexivity. rewrite <- liftP2. reflexivity. omega. rewrite <- liftP2.
      reflexivity. omega. reflexivity. omega.
  + clear X0 X1. apply f_equal, f_equal.
  match goal with
  | |- λ ?A ?M = λ ?A' ?M' => assert (X0 : A = A');
                              [|assert (X1: M = M'); [|rewrite X0, X1; reflexivity]]
  end.
    * rewrite <- liftP2. apply f_equal2, f_equal. apply f_equal. rewrite <- liftP2.
      reflexivity. omega. rewrite <- liftP2. reflexivity. all: omega.
    * rewrite <- liftP2. apply f_equal2, f_equal. apply f_equal2.
      apply f_equal. rewrite <- liftP2. reflexivity. omega. rewrite <- liftP2.
      reflexivity. omega. reflexivity. omega.
Defined.

Definition tsl_var_ctx Γ A v : S.item_lift A Γ v -> A ᵗ ↓ v ⊂ Γ ᶜ.
  induction 1 as [t [H1 H2]]. exists (t ᵗ). split. rewrite H1. apply tsl_lift.
  clear A H1. induction H2. econstructor. econstructor. exact IHitem.
Defined.
Hint Resolve tsl_var_ctx.

Definition tsl_subst M : forall N n, (S.subst_rec N M n) ᵗ = (M ᵗ)[n ← N ᵗ].
  induction M; cbn; intros; auto;
    rewrite ?IHM, ?IHM1, ?IHM2, ?IHM3, ?IHM4, ?IHM5, ?IHM6, ?IHM7; trivial.
  destruct (lt_eq_lt_dec v n); cbn.
  destruct s. reflexivity. apply tsl_lift. reflexivity.
  match goal with
  | |- bisim_corec _ ?s ?M0 ?M1 _ _ _ = bisim_corec _ ?s' ?M0' ?M1' _ _ _
    => assert (X0 : s = s');
        [|assert (X1: M0 = M0');
          [|assert (X2: M1 = M1'); [|rewrite X0, X1, X2; reflexivity]]]
  end.
  - unfold S'. apply f_equal. rewrite <- !substP2; try omega. reflexivity.
  - unfold M'. apply f_equal. rewrite <- !substP2; try omega. reflexivity.
  - unfold M'. apply f_equal. rewrite <- !substP2; try omega. reflexivity.
Defined.

Tactic Notation "trans" := eapply Betas_trans; [eapply Betas_Beta|].


Definition Betas_S' : forall A A' s s' P0 P0' P1 P1',
    A →→ A' -> s →→ s' -> P0 →→ P0' -> P1 →→ P1' -> S' A s P0 P1 →→ S' A' s' P0' P1'.
  intros. unfold S'.
  apply Betas_La. eauto.
  apply Betas_La. eauto.
  apply Betas_App. eapply Betas_App.
  all: eauto.
Defined.

Definition Betac_S' : forall A A' s s' P0 P0' P1 P1',
    A ≡ A' -> s ≡ s' -> P0 ≡ P0' -> P1 ≡ P1' -> S' A s P0 P1 ≡ S' A' s' P0' P1'.
  intros. unfold S'.
  apply Betac_La. auto.
  apply Betac_La. auto. 
  apply Betac_App. apply Betac_App.
  all: auto.
Defined.
Hint Resolve Betas_S' Betac_S'.

Definition Betas_M' : forall A A' s s' M0 M0' P0 P0' P1 P1',
    A →→ A' -> s →→ s' -> M0 →→ M0' -> P0 →→ P0' -> P1 →→ P1'
    -> M' A s M0 P0 P1 →→ M' A' s' M0' P0' P1'.
  intros. unfold M'.
  apply Betas_La. auto.
  apply Betas_La. auto.
  apply Betas_La. auto. 
  apply Betas_App. apply Betas_App.
  all: auto.
  apply Betas_App. apply Betas_App. apply Betas_App.
  all: auto.
Defined.

Definition Betac_M' : forall A A' s s' M0 M0' P0 P0' P1 P1',
    A ≡ A' -> s ≡ s' -> M0 ≡ M0' -> P0 ≡ P0' -> P1 ≡ P1'
    -> M' A s M0 P0 P1 ≡ M' A' s' M0' P0' P1'.
  intros. unfold M'.
  apply Betac_La. auto.
  apply Betac_La. auto.
  apply Betac_La. auto. 
  apply Betac_App. apply Betac_App.
  all: auto.
  apply Betac_App. apply Betac_App. apply Betac_App.
  all: auto.
Defined.
Hint Resolve Betas_M' Betac_M'.

      
Definition tsl_red M N : S.Beta M N -> M ᵗ ≡ N ᵗ.
  induction 1; cbn. 
  { rewrite tsl_subst. eauto. }
  { eauto. }
  { econstructor. trans. eauto. trans; eauto. }
  { econstructor. trans. eauto. unfold M'. trans. eauto.
    cbn. trans. eauto. eauto. }
  { econstructor. trans. eauto. unfold M'.
    trans. eauto. cbn.
    trans. eauto. cbn. trans. eauto. cbn.
    rewrite !substP3; try omega. rewrite !lift0.
    trans; eauto. }
  { eapply Betac_trans. 
    econstructor. apply Betas_Beta. eauto.
    eapply Betac_bisim_corec.
    - eauto.
    - unfold S'. eapply Betac_sym. econstructor.
      eapply Betas_La. eauto.
      eapply Betas_La. eauto.
      eapply Betas_App. eapply Betas_App.
      eauto. econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor.
    - unfold M'. eapply Betac_sym. econstructor.
      eapply Betas_La. eauto.
      eapply Betas_La. eauto.
      eapply Betas_La. eapply Betas_App.
      eapply Betas_App. eauto.
      econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor.
      eapply Betas_App. eapply Betas_App. eapply Betas_App. eauto.
      econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor. eauto.
    - unfold M'. eapply Betac_sym. econstructor.
      eapply Betas_La. eauto.
      eapply Betas_La. eauto.
      eapply Betas_La. eapply Betas_App.
      eapply Betas_App. eauto.
      econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor.
      eapply Betas_App. eapply Betas_App. eapply Betas_App. eauto.
      econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor. eauto.
    - eauto.
    - eauto.
    - unfold M'. econstructor. trans.
      eauto. cbn. trans. eauto. cbn.
      trans. eauto. cbn. rewrite !substP3; try omega.
      rewrite !lift0. eapply Betas_App.
      eapply Betas_App. eapply Betas_App.
      all: eauto. }
  all: auto 4. 
Defined.
Hint Resolve tsl_red.

Definition tsl_conv M N : S.Betac M N -> M ᵗ ≡ N ᵗ.
  induction 1; eauto 2.
  induction H; eauto.
Defined.
Hint Resolve tsl_conv.

Lemma Bool_s Γ s : Γ ⊣ -> Γ ⊢ Bool : !s.
  intro. destruct s; now constructor.
Defined.
Hint Resolve Bool_s.


Definition tsl_correction :
  (forall Γ M A, S.typ Γ M A -> Γ ᶜ ⊢ M ᵗ : A ᵗ) /\ (forall Γ,  S.wf Γ -> Γ ᶜ ⊣).
  unshelve eapply S.typ_induc; cbn; eauto 3.
  - intros Γ M N A B _ H _ H0. rewrite tsl_subst. eauto.
  - intros Γ A P t1 u t2 p s _ H _ H0 _ H1. rewrite tsl_subst.
    rewrite tsl_subst in H0. econstructor; eassumption.
  - intros Γ A i _ H.
    simple refine (let X := cΣ (i:=i) (j:=0) _ _ in _).
    6: rewrite PeanoNat.Nat.max_0_r in X; exact X.
    eauto. eauto.
  - intros Γ M A _ H. econstructor. eauto. cbn. exact (cπ2 H).
  - intros Γ s M0 M1 N A i _ H _ H0 _ H1 _ H2. econstructor.
    rewrite tsl_lift in H0, H1. econstructor; eassumption.
    cbn; constructor. exact (wf_typ H).
  - intros Γ A M N i _ H _ H0 _ H1. econstructor; eauto.
  - intros Γ A M N1 N2 i _ H _ H0 _ H1 _ H2.
    econstructor. 2: refine (ctl_b H2); eauto.
    apply Betac_sym. econstructor. trans. eauto. econstructor. eauto.
    econstructor. eassumption.
    { unshelve econstructor. exact Bool. econstructor. eauto. exact (cπ2 H0). }
    { unshelve econstructor. exact Bool. econstructor. eauto. exact (cπ2 H1). }
  - intros Γ s M0 M1 P0 P1 N A i _ H _ H0 _ H1 _ H2 _ H3 _ H4 _ H5.
    pose proof (cStream H).
    pose proof (thinning H6 H6); cbn in *.
    pose proof (thinning H7 H7); cbn in *.
    rewrite !tsl_lift in *. rewrite !lift_lift in *; cbn in *.
    assert (HS' : Γ ᶜ ⊢ S' (A ᵗ) (s ᵗ) (P0 ᵗ) (P1 ᵗ)
            : Stream (A ᵗ) ⇒ Stream (A ᵗ) ⇒ ! (U i)). {
      econstructor. 2: eassumption. constructor. cbn.
      econstructor. eauto. eauto. cbn. eauto. cbn.
      econstructor. 2: eassumption. constructor. cbn. eauto.
      eapply (cApp (A := Σ (Stream (A ᵗ ↑ ↑)) Bool) (B := !(U i))).
      * rewrite <- !(lift_lift _ 1 1).
        refine (@thinning _ ((s ᵗ) ↑ · ⟨ # 0, π2 (P0 ᵗ) ↑ ⟩)
                          (Π (Σ (Stream (A ᵗ) ↑) Bool) ! (U i)) _ _ _ H7).
        pose proof (thinning H0 H6); cbn in *.
        simple refine (let X := cApp H9 _ in _); cbn in *.
        exact ⟨ # 0, π2 (P0 ᵗ) ↑ ⟩.
        ++ econstructor. econstructor. eauto. econstructor. split.
           2: econstructor. reflexivity. eapply (cπ2 (B:=Bool)).
           exact (thinning H1 H6).
        ++ clearbody X. rewrite liftP3 in X. cbn in X.
           rewrite substP3 in X. exact X. all: omega.
      * econstructor. econstructor. eauto. econstructor. split.
        2: econstructor. reflexivity. eapply (cπ2 (B:=Bool)).
        rewrite <- (lift_lift _ 1 1).
        eapply  (thinning (thinning H2 H6) H7). }
    assert (HEq : Stream (A ᵗ) ↑ :: Stream (A ᵗ) :: Γ ᶜ ⊢ Eq (A ᵗ) ↑ 2 (hd # 1) (hd # 0)
            : ! (U (S i))). {
      econstructor.
      pose proof (thinning (thinning H H6) H7).
      rewrite !lift_lift in H9; exact H9.
      econstructor. econstructor. eauto.
      econstructor. split. 2: eauto. reflexivity.
      econstructor. econstructor. eauto.
      econstructor. split. 2: eauto.
      cbn; rewrite lift_lift; reflexivity. }
    assert (HH0:  Stream (A ᵗ) ↑ :: Stream (A ᵗ) :: Γ ᶜ ⊢ (S' (A ᵗ) (s ᵗ) (P0 ᵗ) (P1 ᵗ)) ↑ 2 · # 1 · # 0 : ! (U i)). {
      pose proof (thinning (thinning HS' H6) H7).
      rewrite !lift_lift in H9; cbn in H9.
      simple refine (let X := cApp H9 _ in _).
      exact #1.
      econstructor. eauto. econstructor. split.
      2: eauto. reflexivity.
      clearbody X. clear H9. cbn in X.
      rewrite !liftP3 in X; try omega; cbn in X.
      rewrite !substP3 in X; try omega; cbn in X.
      simple refine (let X' := cApp X _ in _).
      exact #0.
      econstructor. eauto. econstructor. split.
      2: eauto. cbn; rewrite lift_lift; reflexivity.
      clearbody X'. clear X. cbn in X'.
      cbn. rewrite !liftP3; try omega. exact X'. }
    assert (HH1:  Stream (A ᵗ) ↑ :: Stream (A ᵗ) :: Γ ᶜ ⊢ (S' (A ᵗ) (s ᵗ) (P0 ᵗ) (P1 ᵗ)) ↑ 2 · # 1 · # 0 ⇒ Eq (A ᵗ) ↑ 2 (hd # 1) (hd # 0) : ! (U (S i))). {
      econstructor. 2: exact HH0.
      pose proof (Rel0 i (S i)). rewrite Max.max_r in H9; try omega.
      eassumption.
      refine (thinning HEq _).
      clear H1 H2 H3 H4 HEq.
      pose proof (thinning (thinning HS' H6) H7).
      simple refine (let X := cApp H1 _ in _).
      exact #1.
      econstructor. eauto. econstructor. split.
      2: eauto. cbn; rewrite lift_lift; reflexivity.
      clearbody X. clear H1. cbn in X.
      rewrite !liftP3 in X; try omega; cbn in X.
      rewrite !substP3 in X; try omega; cbn in X.
      simple refine (let X' := cApp X _ in _).
      exact #0.
      econstructor. eauto. econstructor. split.
      2: eauto. cbn; rewrite lift_lift; reflexivity.
      clearbody X'. clear X. cbn in X'.
      cbn. rewrite !liftP3; try omega. exact X'. }
    assert (HH : Stream (A ᵗ) ↑ :: Stream (A ᵗ) :: Γ ᶜ ⊢ (s ᵗ) ↑ 2 · ⟨ # 1, π2 (P0 ᵗ) ↑ 2 ⟩ · ⟨ # 0, π2 (P1 ᵗ) ↑ 2 ⟩ : ! (U i)). {
      clear H3 H4 H5.
      pose proof (thinning H0 H6).
      pose proof (thinning H3 H7). clear H0 H3.
      rewrite !lift_lift in H4; cbn in H4.
      rewrite liftP3 in H4; try omega; cbn in H4.
      simple refine (let X := cApp H4 _ in _).
      ++ exact ⟨ # 1, π2 (P0 ᵗ) ↑ 2 ⟩.
      ++ econstructor. econstructor. eauto.
         econstructor. split. 2: econstructor; econstructor.
         reflexivity.
         cbn. pose proof (thinning (thinning H1 H6) H7).
         rewrite !lift_lift in H0; cbn in H0.
         exact (cπ2 H0).
      ++ clearbody X. clear H4.
         simple refine (let X' := cApp X _ in X').
         cbn. econstructor. econstructor. eauto.
         econstructor. split. 2: econstructor; econstructor.
         cbn. rewrite substP3. now rewrite lift_lift.
         all: try omega.
         cbn. pose proof (thinning (thinning H2 H6) H7).
         rewrite !lift_lift in H0; cbn in H0.
         exact (cπ2 H0). }

    econstructor.
    + exact HS'.

    + (* Γ ᶜ ⊢ M' (A ᵗ) (s ᵗ) (M0 ᵗ) (P0 ᵗ) (P1 ᵗ)
   : Π (Stream (A ᵗ))
       (Π (Stream (A ᵗ) ↑)
          ((S' (A ᵗ) (s ᵗ) (P0 ᵗ) (P1 ᵗ)) ↑ 2 · # 1 · # 0 ⇒ Eq (A ᵗ) ↑ 2 (hd # 1) (hd # 0))) *)
      econstructor. econstructor. eassumption.
      { econstructor. econstructor. eassumption.
        exact HH1. }
      econstructor. econstructor. eassumption. exact HH1.
      econstructor.
      * apply Betac_sym, Betac_Betas. unfold S'; cbn.
        trans. eauto. cbn. rewrite !liftP3. all: try omega.
        cbn. rewrite !substP3. all: try omega.
        trans. eauto. cbn. rewrite !substP3. all: try omega.
        econstructor.
      * econstructor. econstructor. exact HH.
        -- econstructor.
           ++ simple refine (let X := thinning (thinning (thinning H H6) H7) _ in _).
              4: rewrite !lift_lift in X; exact X.
              2: exact HH.
           ++ econstructor. econstructor. eauto.
              econstructor. split. 2: eauto.
              reflexivity.
           ++ econstructor. econstructor. eauto.
              econstructor. split. 2: eauto.
              cbn; rewrite lift_lift; reflexivity.
        -- clear H4 H5. 
           pose proof (thinning (thinning (thinning H3 H6) H7) HH).
           rewrite !lift_lift in H4; cbn in H4.
           rewrite !liftP3 in H4; try omega; cbn in H4.
           simple refine (let X := cApp H4 _ in _).
           ++ exact ⟨ # 2, π2 (P0 ᵗ) ↑ 3 ⟩.
           ++ econstructor. econstructor. eauto.
              econstructor. split. 2: eauto. reflexivity.
              cbn. pose proof (thinning (thinning (thinning H1 H6) H7) HH).
              rewrite !lift_lift in H5; cbn in H5.
              exact (cπ2 H5). 
           ++ clearbody X. clear H4. 
              simple refine (let X' := cApp X _ in _).
              ** exact ⟨ # 1, π2 (P1 ᵗ) ↑ 3 ⟩.
              ** cbn. econstructor. econstructor. eauto.
                 econstructor. split. 2: eauto. 
                 cbn. rewrite substP3. now rewrite lift_lift.
                 all: try omega.
                 cbn. pose proof (thinning(thinning (thinning H2 H6) H7) HH).
                 rewrite !lift_lift in H4; cbn in H4.
                 exact (cπ2 H4). 
              ** clearbody X'; cbn in X'.
                 rewrite !lift_lift in X'; cbn in X'.
                 rewrite !substP3 in X'; try omega; cbn in X'.
                 simple refine (let X'' := cApp X' _ in _).
                 exact #0.
                 econstructor. eauto. econstructor. split. 2: eauto.
                 cbn. rewrite !lift_lift; reflexivity.
                 clearbody X''. cbn in X''.
                 rewrite !substP3 in X''; try omega. clear X X'.
                 econstructor. 2: exact X''.
                 --- constructor. trans. eauto.
                     constructor. eauto.
                 --- econstructor.
                     pose proof (thinning (thinning (thinning H H6) H7) HH).
                     rewrite !lift_lift in H4; exact H4.
                     econstructor. econstructor. eauto.
                     econstructor. split. 2: eauto. reflexivity.
                     econstructor. econstructor. eauto.
                     econstructor. split. 2: eauto.
                     cbn; rewrite lift_lift; reflexivity.
      * exact HH1.

    + assert (HH2: Stream (A ᵗ) ↑ :: Stream (A ᵗ) :: Γ ᶜ ⊢ (S' (A ᵗ) (s ᵗ) (P0 ᵗ) (P1 ᵗ)) ↑ 2 · # 1 · # 0 ⇒ (S' (A ᵗ) (s ᵗ) (P0 ᵗ) (P1 ᵗ)) ↑ 2 · tl # 1 · tl # 0 : ! (U i)). {
        econstructor. pose proof (Rel0 i i).
        rewrite Max.max_r in H9; try omega. eassumption.
        exact HH0. simple refine (thinning (T := !(U i)) _ HH0).
        pose proof (thinning (thinning HS' H6) H7).
        rewrite !lift_lift in H9; cbn in H9.
        simple refine (let X := cApp H9 _ in _).
        exact (tl #1). econstructor.
        econstructor. eauto. econstructor. split.
        2: eauto. reflexivity.
        clearbody X. clear H9. cbn in X.
        rewrite !liftP3 in X; try omega; cbn in X.
        rewrite !substP3 in X; try omega; cbn in X.
        simple refine (let X' := cApp X _ in _).
        exact (tl #0). econstructor.
        econstructor. eauto. econstructor. split.
        2: eauto. cbn; rewrite lift_lift; reflexivity.
        clearbody X'. clear X. cbn in X'.
        cbn. rewrite !liftP3; try omega. exact X'. }
      assert (HH':  Stream (A ᵗ) ↑ :: Stream (A ᵗ) :: Γ ᶜ ⊢ (s ᵗ) ↑ 2 · ⟨ tl # 1, π2 (P0 ᵗ) ↑ 2 ⟩ · ⟨ tl # 0, π2 (P1 ᵗ) ↑ 2 ⟩ : ! (U i)). {
        clear H3 H4 H5.
        pose proof (thinning H0 H6).
        pose proof (thinning H3 H7). clear H0 H3.
        rewrite !lift_lift in H4; cbn in H4.
        rewrite liftP3 in H4; try omega; cbn in H4.
        simple refine (let X := cApp H4 _ in _).
        ++ exact ⟨ tl # 1, π2 (P0 ᵗ) ↑ 2 ⟩.
        ++ econstructor. econstructor. econstructor. eauto.
           econstructor. split. 2: econstructor; econstructor.
           reflexivity.
           cbn. pose proof (thinning (thinning H1 H6) H7).
           rewrite !lift_lift in H0; cbn in H0.
           exact (cπ2 H0).
        ++ clearbody X. clear H4.
           simple refine (let X' := cApp X _ in X').
           cbn. econstructor. econstructor. econstructor. eauto.
           econstructor. split. 2: econstructor; econstructor.
           cbn. rewrite substP3. now rewrite lift_lift.
           all: try omega.
           cbn. pose proof (thinning (thinning H2 H6) H7).
           rewrite !lift_lift in H0; cbn in H0.
           exact (cπ2 H0). }
     
      econstructor. econstructor. eassumption.
      { econstructor. econstructor. eassumption.
        exact HH2. }
      econstructor. econstructor. eassumption. exact HH2.
      econstructor.
      * apply Betac_sym, Betac_Betas. unfold S'; cbn.
        trans. eauto. cbn. rewrite !liftP3;  try omega.
        cbn. rewrite !substP3;  try omega.
        trans. eauto. cbn. rewrite !substP3; try omega.
        trans. eauto. cbn. rewrite !substP3; try omega.
        trans. eauto. cbn. rewrite !substP3; try omega.
        econstructor.
      * econstructor. econstructor. exact HH.
        -- pose proof (thinning HH' HH).
           cbn in H9; rewrite !lift_lift in H9; cbn in H9. exact H9.
        -- clear H3 H5. 
           pose proof (thinning (thinning (thinning H4 H6) H7) HH).
           rewrite !lift_lift in H3; cbn in H3.
           rewrite !liftP3 in H3; try omega; cbn in H3.
           simple refine (let X := cApp H3 _ in _).
           ++ exact ⟨ # 2, π2 (P0 ᵗ) ↑ 3 ⟩.
           ++ econstructor. econstructor. eauto.
              econstructor. split. 2: eauto. reflexivity.
              cbn. pose proof (thinning (thinning (thinning H1 H6) H7) HH).
              rewrite !lift_lift in H5; cbn in H5.
              exact (cπ2 H5). 
           ++ clearbody X. clear H4. 
              simple refine (let X' := cApp X _ in _).
              ** exact ⟨ # 1, π2 (P1 ᵗ) ↑ 3 ⟩.
              ** cbn. econstructor. econstructor. eauto.
                 econstructor. split. 2: eauto. 
                 cbn. rewrite substP3. now rewrite lift_lift.
                 all: try omega.
                 cbn. pose proof (thinning(thinning (thinning H2 H6) H7) HH).
                 rewrite !lift_lift in H4; cbn in H4.
                 exact (cπ2 H4). 
              ** clearbody X'; cbn in X'.
                 rewrite !lift_lift in X'; cbn in X'.
                 rewrite !substP3 in X'; try omega; cbn in X'.
                 simple refine (let X'' := cApp X' _ in _).
                 exact #0.
                 econstructor. eauto. econstructor. split. 2: eauto.
                 cbn. rewrite !lift_lift; reflexivity.
                 clearbody X''. cbn in X''.
                 rewrite !substP3 in X''; try omega. clear X X'.
                 econstructor. 2: exact X''.
                 --- constructor. trans. eauto.
                     trans. eauto. trans. eauto. constructor.
                     eauto.
                 --- pose proof (thinning HH' HH).
                     cbn in H4; rewrite !lift_lift in H4; cbn in H4. exact H4.
      * exact HH2.

    + econstructor. 2: eassumption.
      * apply Betac_sym, Betac_Betas. unfold S'.
        trans. eauto. cbn. trans. eauto. cbn.
        rewrite !substP3. all: try omega. rewrite !lift0.
        trans. econstructor. eapply Beta_App2. econstructor. eauto.
      * clear HEq HH0 HH1 HH H3 H4.
        unshelve eapply (cApp (B := !(U i)) _ _).
        3: exact (cπ1 H2).
        pose proof (cApp HS' (cπ1 H1)). cbn in H3.
        rewrite substP3 in H3. now rewrite lift0 in H3.
        all: omega.
Defined.

Print Assumptions tsl_correction.


Definition tsl_consistency : (exists M, S.typ nil M S.empty) -> exists M', nil ⊢ M' : ⊥.
Proof.
  intros [M H]. apply tsl_correction in H. cbn in H.
  exists (M ᵗ). eauto.
Defined.
