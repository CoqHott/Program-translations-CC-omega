Require Import Peano_dec Compare_dec Lt Le Gt.
Require Import Plus Minus Bool List.
Require Import Sorts PTS_Prop.
Import withProp.

Set Implicit Arguments.

(* Weakened system (but equivalent) *)
Inductive wf : Env -> Prop :=
| wf_nil   : nil ⊣
| wf_cons : forall Γ A s, Γ ⊢ A : !s -> A::Γ ⊣
where "Γ ⊣" := (wf Γ) : UT_scope
with
typ : Env -> Term -> Term -> Prop :=
| cVar  : forall Γ A v, Γ ⊣ -> A ↓ v  ⊂ Γ -> Γ ⊢ #v : A
| cSort : forall Γ s s', Γ ⊣ -> Ax s s' -> Γ  ⊢ !s : !s'
| cΠ   : forall Γ A B s s' s'', Rel s s' s'' -> Γ ⊢ A : !s -> A::Γ ⊢ B : !s' -> Γ ⊢  Π  A B : !s''
| cλ   : forall Γ A B s s' s'' M, Rel s s' s'' -> Γ ⊢ A : !s -> A::Γ ⊢ B : !s' -> A::Γ ⊢ M : B
                                                                                     -> Γ ⊢ λ A M : Π  A B
| cApp  : forall Γ M N A B s s' s'', Rel s s' s'' -> Γ ⊢ A : !s -> A::Γ ⊢ B : !s'
                                                                       -> Γ ⊢ M : Π A B -> Γ ⊢ N : A -> Γ ⊢ M · N : B[←N]
(* | cApp  : forall Γ M N A B s, Γ ⊢ Π A B : !s -> Γ ⊢ M : Π A B -> Γ ⊢ N : A -> Γ ⊢ M · N : B[←N] *)
| Cnv   : forall Γ M A B s, A ≡ B  -> Γ ⊢ M : A -> Γ ⊢ B : !s -> Γ ⊢ M : B
where "Γ ⊢ t : T" := (typ Γ t T) : UT_scope.

Hint Constructors wf typ.
Open Scope UT_scope.

Scheme typ_ind' := Induction for typ Sort Prop
                   with wf_ind' := Induction for wf Sort Prop.
Combined Scheme typ_induc from typ_ind', wf_ind'.

Lemma wf_typ : forall Γ t T, Γ ⊢ t : T -> Γ ⊣.
induction 1; eauto.
Qed.

Hint Resolve wf_typ.



Lemma inv_lift : forall M N n m , M ↑ n # m = N ↑ n # m -> M = N.
intros M; induction M; destruct N; intros;
simpl in *; try (discriminate || intuition); (try (destruct (le_gt_dec m v) ; discriminate)).
destruct (le_gt_dec m v); destruct (le_gt_dec m v0) ; injection H; intros; subst; intuition.
apply plus_reg_l in H0; rewrite H0; trivial. 
elim (lt_irrefl m). apply le_lt_trans with v. trivial. induction n; intuition.
elim (lt_irrefl v0). apply lt_le_trans with m. induction n; intuition. trivial.
injection H; intros; rewrite (IHM1 N1 n m H1); rewrite (IHM2 N2 n _ H0); reflexivity.
injection H; intros; rewrite (IHM1 N1 n m H1); rewrite (IHM2 N2 n (S m) H0); reflexivity.
injection H; intros; rewrite (IHM1 N1 n m H1); rewrite (IHM2 N2 n _ H0); reflexivity.
Qed.

Lemma lift_rec0 : forall M n, M ↑ 0 # n = M.
induction M; intros; simpl.
destruct (le_gt_dec n v); reflexivity.
reflexivity.
rewrite IHM1; rewrite IHM2; reflexivity.
rewrite IHM1; rewrite IHM2; reflexivity.
rewrite IHM1; rewrite IHM2; reflexivity. 
Qed.

Lemma lift0 : forall M, M ↑ 0 = M .
intros; apply lift_rec0.
Qed.

Lemma liftP1 : forall M i j  k, (M ↑ j # i) ↑ k # (j+i) = M ↑ (j+k) # i.
intros M; induction M; intros;simpl.
destruct (le_gt_dec i v); simpl.
destruct (le_gt_dec (j+i) (j+v)); simpl. 
rewrite plus_assoc. replace (k+j) with (j+k) by (apply plus_comm).  trivial. 
apply plus_gt_reg_l in g. elim (lt_irrefl v).
apply lt_le_trans with i; intuition.
simpl; destruct (le_gt_dec (j+i)); intuition.
elim (lt_irrefl v).
apply lt_le_trans with i; intuition. induction j; intuition.
reflexivity.
rewrite IHM1; rewrite <-IHM2 ;replace (j+S i) with (S(j+i)) by intuition; reflexivity.
rewrite IHM1; rewrite <- IHM2 ;replace (j+S i) with (S(j+i)) by intuition; reflexivity.
rewrite IHM1;rewrite IHM2;reflexivity.
Qed.

Lemma liftP2: forall M i j k n, i <= n ->
  (M ↑ j # i) ↑ k # (j+n) = (M ↑ k # n) ↑ j # i.
intro M; induction M; intros; simpl.
destruct (le_gt_dec i v); destruct (le_gt_dec n v).
simpl.
destruct le_gt_dec. destruct le_gt_dec.
rewrite 2! plus_assoc. replace (k+j) with (j+k) by (apply plus_comm).  trivial. 
elim (lt_irrefl v). apply lt_le_trans with i. induction k; intuition. trivial.
apply plus_gt_reg_l in g. elim (lt_irrefl v).
apply lt_le_trans with n; intuition.
simpl.
destruct le_gt_dec. apply plus_le_reg_l in l0. elim (lt_irrefl v).
apply lt_le_trans with n; intuition. destruct le_gt_dec. trivial.
elim (lt_irrefl v). apply lt_le_trans with i; intuition.
simpl. destruct le_gt_dec. elim (lt_irrefl n). apply lt_le_trans with i.
apply le_lt_trans with v; intuition. trivial. elim (lt_irrefl v).
apply lt_le_trans with n. apply lt_le_trans with i; intuition. trivial.
simpl. destruct le_gt_dec. elim (lt_irrefl v). apply lt_le_trans with n.
intuition. induction j; intuition. destruct le_gt_dec. elim (lt_irrefl i).
apply le_lt_trans with v; intuition. trivial.
trivial.

rewrite IHM1; intuition.
replace (S(j+n)) with (j+S n) by intuition.
rewrite (IHM2 (S i) j k (S n)); intuition.
rewrite IHM1; intuition.
replace (S(j+n)) with (j+S n) by intuition.
rewrite (IHM2 (S i) j k (S n) ); intuition.
rewrite IHM1; intuition;  rewrite IHM2; intuition;  reflexivity.
Qed.

Lemma liftP3 : forall M i k j n , i <= k -> k <= (i+n) ->
  (M ↑ n # i) ↑ j # k = M ↑ (j+n) # i.
intro M; induction M; intros; simpl.
destruct (le_gt_dec i v); simpl.
destruct (le_gt_dec k (n+v)); intuition.
elim (lt_irrefl (i+n)). apply lt_le_trans with k.
apply le_lt_trans with (n+v). rewrite plus_comm. intuition. intuition. trivial.
destruct (le_gt_dec k v); intuition. elim (lt_irrefl k).
apply lt_le_trans with i.  apply le_lt_trans with v. trivial. intuition. trivial.
reflexivity.
rewrite IHM1; intuition;rewrite IHM2; intuition. change (S i + n) with (S (i+n)). intuition.
rewrite IHM1; intuition; rewrite IHM2; intuition. change (S i + n) with (S (i+n)). intuition.
rewrite IHM1; intuition;rewrite IHM2; intuition.
Qed.


Lemma lift_lift : forall M n m, (M ↑ m) ↑ n  = M↑ (n+m).
intros.
apply liftP3; intuition.
Qed.

Lemma substP1: forall M N i j k , 
  ( M [ j ← N] ) ↑ k # (j+i) = (M ↑ k # (S (j+i))) [ j ← (N ↑ k # i ) ].
intros M; induction M; intros.
simpl (#v [j ← N] ↑ k # (j+i)).
change (#v ↑ k # (S (j+i))) with  (if le_gt_dec (S (j+i)) v then #(k+v) else #v).
destruct (lt_eq_lt_dec v j) as [[] | ].
destruct (le_gt_dec (S (j+i)) v).
elim (lt_irrefl v). apply lt_le_trans with j; intuition.
apply le_trans with (S (j+i)); intuition.
simpl.
destruct (le_gt_dec (j+i) v).
elim (lt_irrefl v). apply lt_le_trans with j; intuition. apply le_trans with (j+i); intuition.
destruct (lt_eq_lt_dec v j) as [[] | ]. trivial.
subst. elim (lt_irrefl j);trivial.
elim (lt_irrefl j); apply lt_trans with v; trivial.
destruct (le_gt_dec (S(j+i)) v). subst.
elim (lt_irrefl j). apply lt_le_trans with (S (j+i)). intuition. trivial.
simpl. destruct (lt_eq_lt_dec v j) as [[] | ].
subst. elim (lt_irrefl j); trivial.
apply liftP2; intuition.
subst. elim (lt_irrefl j); trivial.
destruct (le_gt_dec (S (j+i)) v).
simpl.
destruct (le_gt_dec (j+i) (v-1)). destruct (lt_eq_lt_dec (k+v) j) as [[] | ].
elim (lt_irrefl j). apply lt_le_trans with v. trivial. induction k; intuition.
subst. elim (lt_irrefl v). apply lt_le_trans with (S(k+v+i)). intuition. trivial.
destruct v. apply lt_n_O in l; elim l. rewrite <- 2! pred_of_minus. replace (k+ S v) with (S (k+v)) by intuition.
simpl. trivial.
elim (lt_irrefl v). apply lt_le_trans with (S (j+i)). destruct v. apply lt_n_O in l; elim l. 
rewrite <- pred_of_minus in g. simpl in g. intuition. trivial.
simpl.
destruct (le_gt_dec (j+i) (v-1)). destruct (lt_eq_lt_dec v j) as [[] | ].
elim (lt_irrefl j); apply lt_trans with v; trivial.
subst. elim (lt_irrefl j); trivial.
elim (lt_irrefl v). apply lt_le_trans with (S (j+i)). intuition. 
destruct v. apply lt_n_O in l; elim l. rewrite <- pred_of_minus in l0. simpl in l0. intuition.
destruct (lt_eq_lt_dec) as [[] | ]. elim (lt_irrefl j); apply lt_trans with v; trivial.
subst. elim (lt_irrefl j); trivial. trivial.
simpl; trivial.
simpl; rewrite IHM1; intuition.
replace (S(S(j+i))) with (S((S j)+i)) by intuition.
rewrite <- (IHM2 N i (S j)  k ); intuition.
simpl; rewrite IHM1; intuition.
replace (S(S(j+i))) with ((S ((S j)+i))) by intuition.
rewrite <- (IHM2 N i (S j)  k ); intuition.
simpl; rewrite IHM1; intuition; rewrite IHM2; intuition.
Qed.

Lemma substP2: forall M N i j n, i <= n ->
  (M ↑ j # i ) [ j+n ← N ] = ( M [ n ← N]) ↑ j # i .
intro M; induction M; intros; simpl.
destruct (le_gt_dec i v); destruct (lt_eq_lt_dec v n) as [[] | ].
simpl.
destruct (le_gt_dec i v).  destruct (lt_eq_lt_dec (j+v) (j+n)) as [[] | ].
reflexivity.
apply plus_reg_l in e. subst. elim (lt_irrefl n); trivial.
apply plus_lt_reg_l in l2. elim (lt_asym v n); trivial.
elim (lt_irrefl i). apply le_lt_trans with v; intuition. subst.
simpl.
destruct (lt_eq_lt_dec (j+n) (j+n)) as [[] | ].
apply lt_irrefl in l0; elim l0.
symmetry.
apply liftP3; intuition.
apply lt_irrefl in l0; elim l0.
simpl.
destruct (le_gt_dec i (v-1)). destruct (lt_eq_lt_dec (j+v) (j+n))as [[] | ].
apply plus_lt_reg_l in l2. elim (lt_asym  v n ); trivial.
apply plus_reg_l in e; subst. elim (lt_irrefl n); trivial.
destruct v. apply lt_n_O in l0; elim l0. rewrite <- 2! pred_of_minus. replace (j+ S v) with (S (j+v)) by intuition.
simpl. trivial.
unfold gt in g. unfold lt in g. rewrite <- pred_of_minus in g. 
rewrite <- (S_pred  v n l0) in g.
elim (lt_irrefl n). apply lt_le_trans with v; trivial. apply le_trans with i; trivial.
simpl. 
destruct (le_gt_dec i v).  elim (lt_irrefl i). apply le_lt_trans with v; trivial.
destruct (lt_eq_lt_dec v (j+n)) as [[] | ]. reflexivity.
subst. elim (lt_irrefl n). apply le_lt_trans with (j+n); intuition. 
elim (lt_irrefl n). apply lt_trans with v.  apply le_lt_trans with (j+n); intuition. trivial.
simpl. subst. 
elim (lt_irrefl n). apply lt_le_trans with i; intuition.
simpl. elim (lt_irrefl n). apply lt_le_trans with v; intuition.
apply le_trans with i; intuition.
trivial.

rewrite IHM1; intuition;
rewrite <- (IHM2 N (S i) j (S n)); intuition.
replace (S(j+n)) with (j+(S n)) by intuition.
reflexivity.
rewrite IHM1; intuition;
rewrite <- (IHM2 N (S i) j (S n)); intuition.
replace (S(j+n)) with (j+(S n)) by intuition.
reflexivity.
rewrite IHM1; intuition;rewrite IHM2; intuition.
Qed.


Lemma substP3: forall M N i  k n, i <= k -> k <= i+n ->
  (M↑ (S n) # i) [ k← N] = M ↑ n # i.
intro M; induction M; intros; simpl.
destruct (le_gt_dec i v).
unfold subst_rec.
destruct (lt_eq_lt_dec (S(n+v)) k) as [[] | ].
elim (lt_irrefl (i+n)). apply lt_le_trans with k; intuition.
apply le_lt_trans with (v+n). intuition. rewrite plus_comm; intuition.
subst. replace (i+n) with (n+i) in H0 by (apply plus_comm) . replace (S (n+v)) with (n + S v) in H0 by intuition. 
apply plus_le_reg_l in H0. elim (lt_irrefl i). apply le_lt_trans with v; intuition.
simpl. rewrite <- minus_n_O. trivial.
simpl. destruct (lt_eq_lt_dec v k) as [[] | ].
reflexivity. subst. elim (lt_irrefl i). apply le_lt_trans with k; intuition.
elim (lt_irrefl k). apply lt_trans with v; trivial. apply lt_le_trans with i; intuition.

reflexivity.
rewrite IHM1; intuition; rewrite <- (IHM2 N (S i) (S k) n); intuition.
change (S i + n) with (S (i+n)). intuition.
rewrite IHM1; intuition; rewrite <- (IHM2 N (S i) (S k) n); intuition.
change (S i + n) with (S (i+n)). intuition.
rewrite IHM1; intuition;rewrite IHM2; intuition.
Qed.

Lemma substP4: forall M N P i j, 
   (M [ i← N]) [i+j ← P] = (M [S(i+j) ← P]) [i← N[j← P]].
intro M; induction M; intros; simpl.
destruct (lt_eq_lt_dec v i) as [[] | ] ; destruct (lt_eq_lt_dec v (S(i+j))) as [[] | ].
simpl.
destruct (lt_eq_lt_dec v (i+j)) as [[] | ]. destruct (lt_eq_lt_dec v i) as [[] | ].
trivial.
subst. apply lt_irrefl in l; elim l. elim ( lt_asym v i); trivial.
subst. rewrite plus_comm in l. elim (lt_irrefl i). induction j; simpl in *; intuition.
elim (lt_irrefl i). apply le_lt_trans with v;intuition. rewrite plus_comm in l1; intuition.  induction j; simpl in *; intuition.
subst. elim (lt_irrefl i). apply lt_trans with (S (i+j)); intuition.
elim (lt_irrefl i). apply lt_trans with (S (i+j)); intuition. apply lt_trans with v; trivial.
simpl. subst. destruct (lt_eq_lt_dec i i) as [[] | ].
elim (lt_irrefl i); trivial. apply substP2; intuition.
elim (lt_irrefl i); trivial.
subst v. rewrite plus_comm in e0. apply succ_plus_discr in e0. elim e0.
subst. elim (lt_irrefl i). apply le_lt_trans with (i+j); intuition.
simpl.
destruct (lt_eq_lt_dec (v-1) (i+j)) as  [[] | ]. destruct (lt_eq_lt_dec v i) as [[] | ].
elim (lt_asym v i); trivial. subst. elim (lt_irrefl i); trivial.
trivial. rewrite <- e in l0. rewrite <- pred_of_minus in l0.
rewrite <- (S_pred  v i l) in l0. elim (lt_irrefl v); trivial.
apply lt_n_S in l1. elim (lt_irrefl v).
apply lt_trans with (S(i+j)); trivial.
rewrite <- pred_of_minus in l1. rewrite <- (S_pred  v i l) in l1. trivial. 
subst. simpl. rewrite <- minus_n_O.
destruct (lt_eq_lt_dec (i+j) (i+j)) as [[] | ].
elim (lt_irrefl (i+j)) ; trivial.
symmetry. apply substP3; intuition.
elim (lt_irrefl (i+j)) ; trivial.
simpl.
destruct (lt_eq_lt_dec (v-1) (i+j)) as  [[] | ].
elim (lt_irrefl v). apply lt_trans with (S (i+j)) ;trivial.
apply lt_n_S in l1. rewrite <- pred_of_minus in l1. rewrite <- (S_pred v i l) in l1. trivial.
apply eq_S in e. rewrite <- pred_of_minus in e. rewrite <- (S_pred v i l) in e.
subst. elim (lt_irrefl (S(i+j))); trivial.
destruct (lt_eq_lt_dec (v-1) i) as [[] | ].
elim (lt_irrefl v). apply le_lt_trans with i; trivial. destruct v. apply lt_n_O in l; elim l.
rewrite <- pred_of_minus in l2. simpl in l2. trivial.
destruct v. elim (lt_n_O i); trivial. rewrite <- pred_of_minus in e. simpl in e. subst.
rewrite <- pred_of_minus in l1. simpl in l1. elim (lt_irrefl i).
apply le_lt_trans with (i+j); intuition.
trivial.
trivial.
rewrite IHM1; replace (S(S(i+j))) with (S((S i)+ j)) by intuition;
  rewrite <- (IHM2 N P (S i)); replace (S(i+j)) with ((S i)+ j) by intuition; intuition.
rewrite IHM1; replace (S(S(i+j))) with (S((S i)+j)) by intuition;
  rewrite <- (IHM2 N P (S i)); replace (S(i+j)) with ((S i)+ j) by intuition; intuition.
rewrite IHM1; rewrite IHM2; intuition.
Qed.

Lemma subst_travers : 
 forall  M N P n, (M [← N]) [n ← P] = (M [n+1 ← P])[← N[n← P]].
intros.
rewrite plus_comm. change n with (O+n). apply substP4.
Qed.

(** Tool function usefull when eta-conversion is used, but this is not the case
here. *)
Lemma expand_term_with_subst : forall M n, (M ↑ 1 # (S n)) [ n ← #0 ] = M.
induction M; intros.
unfold lift_rec.
destruct (le_gt_dec (S n) v). unfold subst_rec.
destruct (lt_eq_lt_dec (1+v) n) as [[] | ].
apply le_not_lt in l. elim l. intuition.
elim (lt_irrefl v). apply lt_le_trans with (S (S v)). intuition. subst; trivial.
change (1+v) with (S v). destruct v; simpl; trivial.
simpl.
destruct (lt_eq_lt_dec v n) as [[] | ].
trivial.
simpl; subst; trivial.
rewrite <- plus_n_O. trivial.
elim (lt_irrefl n). apply lt_le_trans with v; intuition.
simpl; trivial.
simpl. rewrite IHM1. rewrite IHM2. reflexivity.
simpl. rewrite IHM1. rewrite IHM2. reflexivity.
simpl. rewrite IHM1. rewrite IHM2. reflexivity.
Qed.

Lemma fun_item: forall T (A B:T)(Γ:list T)(n:nat), 
  A ↓ n ∈ Γ -> B ↓ n ∈ Γ -> A = B.
intros T A B  Γ n;revert T A B Γ. 
induction n; intros.
inversion H; inversion H0.
rewrite <- H2 in H1; injection H1; trivial.
inversion H; inversion H0; subst.
injection H5; intros; subst.
apply IHn with (Γ:=Γ0); trivial.
Qed.


Inductive trunc (A:Type) : nat->list A ->list A->Prop :=
     trunc_O: forall (Γ:list A) , (trunc O Γ Γ)
   | trunc_S: forall (k:nat)(Γ Γ':list A)(x:A), trunc k Γ Γ' 
                -> trunc (S k) (cons x Γ) Γ'.

Hint Constructors trunc.

Lemma item_trunc: forall (T:Type) (n:nat) (Γ:list T) (t:T), 
  t ↓ n ∈ Γ -> exists Γ' , trunc (S n) Γ Γ'.
intros T n; induction n; intros.
inversion H.
exists Γ0.
apply trunc_S; apply trunc_O.
inversion H; subst.
destruct (IHn Γ0 t H2).
exists x.
apply trunc_S.
apply H0.
Qed.

(** This type describe how do we add an element in an environment: no type
checking is done, this is just the mecanic way to do it. *)
Inductive ins_in_env (Γ:Env ) (d1:Term): nat->Env -> Env  ->Prop :=
  | ins_O: ins_in_env Γ d1 O Γ (d1::Γ)
  | ins_S: forall (n:nat)(Δ Δ':Env )(d:Term), (ins_in_env Γ d1 n Δ Δ')
    -> ins_in_env Γ d1 (S n) (d::Δ) ( (d ↑ 1 # n)::Δ' ).

Hint Constructors ins_in_env.


(** Some lemmas about inserting a new element. They explain how
 terms in the environment are lifted according to their original position
 and the position of insertion. *)
Lemma ins_item_ge: forall (d':Term) (n:nat) (Γ Δ Δ':Env), 
  ins_in_env Γ d' n Δ Δ' -> 
  forall (v:nat), n<=v -> 
 forall (d:Term),  d ↓ v ∈ Δ  -> d ↓ (S v) ∈ Δ'.
induction n; intros.
inversion H; subst.
apply item_tl. exact H1.
inversion H; subst.
apply item_tl.
destruct v.
elim (le_Sn_O n H0).
apply IHn with (Γ:=Γ) (Δ:=Δ0).
trivial.
apply le_S_n ; trivial.
inversion H1.
exact H4.
Qed.

(* begin hide *)
Lemma gt_O: forall v, ~ 0 > v.
intros; intro.
unfold gt in H. apply lt_n_O in H; trivial.
Qed.
(* end hide *)

Lemma ins_item_lt: forall (d':Term)(n:nat)(Γ Δ Δ':Env),
 ins_in_env Γ d' n Δ Δ' ->
 forall (v:nat), n > v ->
 forall (d:Term), d ↓ v ∈ Δ -> (d ↑ 1 # (n-S v)) ↓ v ∈ Δ' .
induction n; intros.
elim (gt_O H0).
inversion H; subst.
destruct v.
inversion H1; subst.
replace (S n -1) with n by intuition.
apply item_hd.
apply item_tl.
replace (S n - S (S v)) with (n -S v) by intuition.
apply IHn with (Γ:=Γ) (Δ:=Δ0).
exact H3.
intuition.
inversion H1.
exact H4.
Qed.

(** Properties of the item_lift notation.*)
Lemma ins_item_lift_lt: forall  (d':Term)(n:nat)(Γ Δ Δ':Env ),
 ins_in_env Γ d' n Δ Δ' ->
 forall (v:nat),  n>v ->
 forall (t:Term), t ↓ v ⊂ Δ  -> (t ↑ 1 # n) ↓ v ⊂ Δ'.
intros.
destruct H1 as [u [ P Q]].
rewrite P.
exists (u ↑ 1 # (n - S v) ); split.
replace n with ( S v + (n -  S v))  by intuition .
rewrite liftP2.
replace (S v+(n-S v)-S v) with (n-S v) by intuition.
reflexivity.
intuition.
clear t P.
inversion H; subst.
elim (gt_O H0).
inversion Q; subst.
replace (S n0 -1) with n0 by intuition.
apply item_hd.
apply item_tl.
replace (S n0 - S (S n)) with (n0 -S n) by intuition.
apply ins_item_lt with d' Γ Δ0; trivial.
intuition.
Qed.


(** This type describe how do we do substitution inside a context.
As previously, no type checking is done at this point.*)

Inductive sub_in_env (Γ : Env) (t T:Term):
  nat -> Env -> Env -> Prop :=
    | sub_O :  sub_in_env Γ t T 0 (T :: Γ) Γ
    | sub_S :
        forall Δ Δ' n  B,
        sub_in_env Γ t T n Δ Δ' ->
        sub_in_env Γ t T (S n) (B :: Δ) ( B [n← t]  :: Δ').

Hint Constructors sub_in_env.


(** Some ins / subst related facts: what happens to term when we do
 a substitution in a context.*)
Lemma nth_sub_sup :
   forall n Γ Δ Δ' t T,
   sub_in_env Γ t T n Δ Δ' ->
   forall v : nat, n <= v -> 
   forall d , d ↓ (S v) ∈ Δ -> d ↓ v ∈ Δ'.
intros n Γ Δ Δ' t T H; induction H; intros.
inversion H0; subst. trivial.
inversion H1; subst.
destruct v.
elim (le_Sn_O n H0).
apply item_tl.
apply le_S_n in H0.
apply IHsub_in_env; trivial.
Qed.

Lemma nth_sub_eq :
   forall t T n Γ Δ Δ',
   sub_in_env Γ t T n Δ Δ' -> 
  forall d , d↓ n ∈ Δ -> T = d.
intros  t T n Γ Δ Δ' H; induction H; intros.
inversion H; trivial.
inversion H0; subst.
apply IHsub_in_env; trivial.
Qed.

Lemma nth_sub_inf :
   forall t T n Γ Δ Δ',
   sub_in_env Γ t T n Δ Δ' ->
   forall v : nat,
   n > v ->
   forall d , d ↓ v ∈ Δ ->  ( d [n - S v ← t] )↓ v ∈ Δ' .
intros t T n Γ Δ Δ' H; induction H; intros.
elim (gt_O  H).
destruct v.
inversion H1; subst.
replace (S n -1) with n by intuition.
apply item_hd.
replace (S n - S (S v)) with (n - S v) by intuition.
inversion H1; subst.
apply item_tl.
apply gt_S_n in H0.
apply IHsub_in_env; trivial.
Qed.

Lemma nth_sub_item_inf :
   forall t T n g e f , sub_in_env g t T n e f ->
   forall v : nat, n > v ->
   forall u , item_lift u e v -> item_lift (subst_rec t u n) f v.
intros.
destruct H1 as [y [K L]].
exists (subst_rec t y (n-S v)); split.
rewrite K; clear u K.
pattern n at 1 .
replace n with (S v + ( n - S v)) by intuition.
apply substP2; intuition.
apply nth_sub_inf with T g  e; trivial.
Qed.

(** Facts about [Betas] and [Betac]: Congruence. *)
Lemma Betac_refl : forall M, M ≡ M.
intros; constructor; constructor.
Qed.

Hint Resolve Betac_refl.

Lemma Betas_App : forall M M' N N',M →→ M' -> N →→ N' -> M · N →→ M' · N'.
assert (forall a b c, b →→ c ->  a·b →→ a·c).
induction 1; eauto.
assert (forall a b c, b→→c -> b· a →→ c· a).
induction 1; eauto.
intros; eauto.
Qed.

Hint Resolve Betas_App.

Lemma Betac_App : forall M M' N N' , M ≡ M' -> N ≡ N' -> M · N ≡ M' · N'.
assert (forall a b c, b ≡ c ->  a· b ≡ a· c).
induction 1; eauto.
assert (forall a b c , b ≡ c -> b·a ≡ c·a).
induction 1; eauto.
eauto.
Qed.

Hint Resolve Betac_App.

Lemma Betas_La : forall A A' M M', A →→ A' -> M →→ M' -> λ A M →→ λ A' M'.
assert (forall a b c , a →→ b -> λ c  a →→ λ c  b).
induction 1; eauto.
assert (forall a b c, a →→ b -> λ a c →→ λ b c).
induction 1; eauto.
eauto.
Qed.


Hint Resolve Betas_La.

Lemma Betac_La: forall A A' M M', A ≡ A' -> M ≡ M' -> λ A M ≡ λ A' M'.
assert (forall a b c, a ≡ b -> λ c  a ≡ λ c b).
induction 1; eauto.
assert (forall a b c, a ≡ b -> λ a c ≡ λ b c).
induction 1; eauto.
eauto.
Qed.

Hint Resolve Betac_La.

Lemma Betas_Pi : forall A A' B B', A →→ A' -> B →→ B' -> Π A B →→ Π A' B'.
assert (forall a b c , a →→ b -> Π  c  a →→ Π c  b).
induction 1; eauto.
assert (forall a b c, a →→ b -> Π a  c →→ Π b  c).
induction 1; eauto.
eauto.
Qed.

Hint Resolve Betas_Pi.

Lemma Betac_Pi : forall A A' B B', A ≡ A' -> B ≡ B' -> Π A B ≡ Π A' B'.
assert (forall a b c , a ≡ b -> Π c  a ≡ Π c  b).
induction 1; eauto.
assert (forall a b c, a ≡ b -> Π a  c ≡ Π b  c).
induction 1; eauto.
eauto.
Qed.

Hint Resolve Betac_Pi.


Lemma Beta_beta : forall M N P n,  M → N ->  M[n←P] → N[n←P] .
intros.
generalize n.
induction H; intros; simpl; intuition.
rewrite (subst_travers).
replace (n0+1) with (S n0).
constructor.
rewrite plus_comm. trivial.
Qed.

(** Some "inversion" lemmas : 
 - a variable/sort cannot reduce at all
 - a pi/lam can only reduce to another pi/lam
 - ...
*)
Lemma Betas_V : forall x N, #x →→ N -> N = #x.
intros. remember #x as X; induction H; trivial.
subst; inversion H.
transitivity N. apply IHBetas2. rewrite <- HeqX; intuition. intuition.
Qed.


Lemma Betas_S : forall s N, !s →→ N -> N = !s.
intros. remember !s as S; induction H; trivial.
subst; inversion H.
transitivity N. apply IHBetas2. rewrite <- HeqS; intuition. intuition.
Qed.


Lemma Betas_Pi_inv : forall A B N, Π A  B →→ N -> 
  exists C, exists D, N = Π C D /\ A →→ C /\ B →→ D.
intros.
remember (Π A  B) as P. revert A B HeqP; induction H; intros; subst; eauto.
inversion H; subst; clear H.
exists A'; exists B; intuition.
exists A; exists B'; intuition.
destruct (IHBetas1 A B) as (C' & D' & ?); intuition.
destruct (IHBetas2 C' D') as (C'' & D'' &?); intuition.
exists C''; exists D''; eauto.
Qed.


(** Lift properties.*)
Lemma Beta_lift: forall M N  n m, M → N -> M ↑ n # m → N ↑ n # m .
intros.
generalize n m; clear n m.
induction H; intros; simpl; eauto.
change m with (0+m).
rewrite substP1.
constructor.
Qed.


Lemma Betas_lift : forall M N n m , M →→ N -> M ↑ n # m →→ N ↑ n # m .
intros.
induction H.
constructor.
constructor; apply Beta_lift; intuition.
apply Betas_trans with (N:= N ↑ n # m ); intuition.
Qed.



Lemma Betac_lift : forall M N n m, M ≡ N -> M ↑ n # m ≡ N ↑ n # m .
intros.
induction H.
constructor.
apply Betas_lift; trivial.
apply Betac_sym; trivial.
apply Betac_trans with (N ↑ n # m); trivial.
Qed.

Hint Resolve Beta_lift Betas_lift Betac_lift.


(** Subst properties.*)
Lemma Betas_subst : forall M P P' n, P →→ P' -> M [n←P] →→ M[n← P']. 
induction M; intros; simpl; eauto.
destruct (lt_eq_lt_dec v n); intuition.
Qed.

Hint Resolve Betas_subst.

Lemma Betas_subst2 : forall M N P n, M →→ N -> M [n← P] →→ N [n ← P].
induction 1; eauto.
constructor. apply Beta_beta; intuition.
Qed.


Hint Resolve Betas_subst2.

Lemma Betac_subst : forall M P P' n, P ≡ P' -> M[n←P] ≡ M [n←P'].
induction M; simpl; intros; intuition.
destruct (lt_eq_lt_dec v n); intuition.
Qed.

Lemma Betac_subst2 : forall M N P n, 
  M ≡ N -> M[n←P] ≡ N[n← P] .
induction 1; eauto.
Qed.

Hint Resolve Betac_subst Betac_subst2.


Theorem weakening: (forall Δ M T, Δ ⊢ M : T -> forall Γ A s n Δ', ins_in_env Γ A n Δ Δ' ->   Γ ⊢ A : !s ->
                 Δ' ⊢ M ↑ 1 # n : T ↑ 1 # n ) /\
(forall Γ, Γ ⊣ -> forall Δ Γ' n A , ins_in_env Δ A n Γ Γ' -> forall s, Δ ⊢ A : !s -> Γ' ⊣).
apply typ_induc; simpl in *; intros.
(*2*)
destruct (le_gt_dec n v).
constructor. eapply H; eauto. destruct i as (AA & ?& ?). exists AA; split. rewrite H2.
change (S (S v)) with (1+ S v). rewrite liftP3; simpl; intuition. eapply ins_item_ge. apply H0. trivial. trivial.
constructor. eapply H; eauto.  eapply ins_item_lift_lt. apply H0. trivial. trivial.
(*1*)
eauto.
(*3*)
econstructor. apply r. eauto. eapply H0. constructor; apply H1. apply H2.
(*4*)
econstructor. apply r. eapply H; eauto. eapply H0; eauto. eapply H1; eauto.
(*5*)
change n with (0+n). rewrite substP1. simpl.
econstructor. exact r. 3: eapply H1; eauto. eauto. eauto. eapply H2; eauto.
(*6*)
apply Cnv with (A↑ 1 # n) s; intuition.
eapply H; eauto. eapply H0; eauto.
(* wf *)
inversion H; subst; clear H.
apply wf_cons with s; trivial.
(**)
inversion  H0; subst; clear H0.
apply wf_cons with s0; trivial.
apply wf_cons with s; trivial. change !s with !s ↑ 1 # n0.
eapply H.  apply H6. apply H1.
Qed.


Theorem thinning :
   forall Γ M T A s,
      Γ ⊢ M : T ->
   Γ ⊢ A : !s ->
   A::Γ ⊢ M ↑ 1 : T ↑ 1.
intros.
destruct weakening.
eapply H1. apply H. constructor. apply H0.
Qed.

Theorem thinning_n : forall n Δ Δ',
   trunc n Δ Δ' ->
   forall M T , Δ' ⊢ M : T  -> Δ ⊣ ->
               Δ ⊢ M ↑ n : T ↑ n.
intro n; induction n; intros.
inversion H; subst; clear H.
rewrite 2! lift0; trivial.
inversion H; subst; clear H.
change (S n) with (1+n).
replace (M ↑ (1+n)) with ((M ↑ n )↑ 1) by (apply lift_lift).
replace (T ↑ (1+n)) with ((T ↑ n) ↑ 1) by (apply lift_lift).
inversion H1; subst; clear H1.
apply thinning with s; trivial.
eapply IHn. apply H3. trivial. eauto.
Qed.


(** Substitution Property: if a judgment is valid and we replace a variable by a
  well-typed term of the same type, it will remain valid.*)
(* begin hide *)
Lemma sub_trunc : forall Δ a A n Γ Γ', sub_in_env Δ a A n Γ Γ' -> trunc n Γ' Δ.
induction 1.
apply trunc_O.
apply trunc_S. trivial.
Qed.
(* end hide *)

Theorem substitution : (forall Γ M T , Γ  ⊢ M : T  -> forall Δ P A, Δ  ⊢ P : A ->
 forall Γ' n , sub_in_env Δ P A n Γ Γ' -> Γ ⊣  -> Γ' ⊢ M [ n ←P ]  : T [ n ←P ] ) /\
                       (forall Γ ,  Γ ⊣ -> forall Δ P A n Γ' , Δ ⊢ P : A ->
  sub_in_env  Δ P A n Γ Γ' ->  Γ' ⊣).
apply typ_induc; simpl; intros.
(*2*)
destruct lt_eq_lt_dec as [ [] | ].
constructor. eapply H; eauto. eapply nth_sub_item_inf. apply H1. intuition. trivial.
destruct i as (AA & ?& ?). subst. rewrite substP3; intuition.
rewrite <- (nth_sub_eq H1 H4). eapply thinning_n. eapply sub_trunc. apply H1. trivial.
eapply H; eauto. constructor. eapply H; eauto. destruct i as (AA & ? &?). subst.
rewrite substP3; intuition. exists AA; split. replace (S (v-1)) with v. trivial.
rewrite minus_Sn_m. intuition. destruct v. apply lt_n_O in l; elim l. intuition.
eapply nth_sub_sup. apply H1. destruct v. apply lt_n_O in l; elim l. simpl. rewrite <- minus_n_O.
intuition. rewrite <- pred_of_minus. rewrite <- (S_pred v n l). trivial.
(*1*)
eauto.
(*4*)
econstructor. apply r. eapply H; eauto. eapply H0; eauto.
(*5*)
econstructor. apply r. eapply H; eauto. eapply H0; eauto. eapply H1; eauto.
(*6*)
rewrite subst_travers. econstructor. exact r. 
3: replace (n+1) with (S n) by (rewrite plus_comm; trivial). 3: eapply H1; eauto.
eauto.
replace (n+1) with (S n) by (rewrite plus_comm; trivial). eapply H0; eauto.
replace (n+1) with (S n) by (rewrite plus_comm; trivial). eapply H2; eauto.
(*7*)
econstructor.  apply Betac_subst2. apply b. eapply H; eauto. eapply H0; eauto.
(* wf *)
inversion H0.
inversion H1; subst; clear H1. eauto.
econstructor. eapply H. apply H0. trivial. eauto.
Qed.

(** Well-formation of contexts: if a context is valid, every term inside
  is well-typed by a sort.*)
Lemma wf_item : forall Γ A n, A ↓ n ∈ Γ ->
   forall  Γ', Γ ⊣ ->  trunc (S n) Γ Γ' -> exists s, Γ' ⊢ A : !s.
induction 1; intros.
inversion H0; subst; clear H0.
inversion H5; subst; clear H5.
inversion H; subst.
exists s; trivial.
inversion H1; subst; clear H1.
inversion H0; subst.
apply IHitem; trivial. eauto.
Qed.

Lemma wf_item_lift : forall Γ A n ,Γ ⊣  -> A ↓ n ⊂ Γ ->
  exists s,  Γ ⊢ A  : !s.
intros.
destruct H0 as (u & ? & ?).
subst.
assert (exists Γ' , trunc (S n) Γ Γ') by (apply item_trunc with u; trivial).
destruct H0 as (Γ' & ?).
destruct (@wf_item Γ u n H1 Γ' H H0) as (t &  ?).
exists t. change !t with (!t ↑(S n)).
eapply thinning_n. apply H0. trivial. trivial.
Qed.

Lemma gen_pi : forall Γ A B T, Γ ⊢ Π A B : T -> exists s1, exists s2, exists s3,
                                  T ≡ !s3 /\ Rel s1 s2 s3 /\ Γ ⊢ A : !s1  /\ A::Γ ⊢ B : !s2 .
  intros. remember (Π A B) as P. revert A B HeqP.
  induction H; intros; subst; try discriminate.
  clear IHtyp1 IHtyp2. injection HeqP; intros; subst; clear HeqP.
  exists s; exists s'; exists s''; intuition.
  destruct (IHtyp1 A0 B0) as (a & b & c & ? & ? & ? &  ?); trivial.
  exists a; exists b; exists c; split.
  eauto. intuition.
Qed.

(** Type Correction: if a judgment is valid, the type is either welltyped
  itself, or syntacticaly a sort. This distinction comes from the fact
  that we abstracted the typing of sorts with [Ax] and that they may be some
  untyped sorts (also called top-sorts).*)
Theorem TypeCorrect : forall Γ M T, Γ ⊢ M : T  ->
 (exists s, T = !s) \/ (exists s, Γ ⊢ T : !s).
intros; induction H.
(*2*)
apply wf_item_lift in H0. right; trivial. trivial.
(*1*)
left; exists s'; reflexivity.
(*4*)
left; exists s''; trivial.
(*5*)
right; exists s''; apply cΠ with s s'; trivial.
(*6*)
destruct IHtyp3. destruct H4; discriminate. destruct H4 as (u & ?).
apply gen_pi in H4 as (s1 & s2 & s3 & h); decompose [and] h; clear h.
right; exists s2.
change (!s2) with (!s2 [← N]). eapply substitution. apply H8. apply H3. constructor.
eauto.
(*8*)
right; exists s; trivial.
Qed.



(* Theorem TypeCorrect : forall Γ M T, Γ ⊢ M : T  -> exists s, Γ ⊢ T : !s. *)
(*   intros; induction H; eauto. *)
(*   - induction H0. induction H0. rewrite H0; clear H0. induction H1. *)
(*   - destruct H0. exists (U (S j)); eauto. exists (U (S i)); eauto. *)
(*   - pose proof (wf_typ H0). destruct H. *)
(*     exists (U (S (max i j))); eauto.  *)
(*     exists (U 0); eauto. *)
(*   - exists s'. admit. *)

    (* (*1*) *)
    (* left; exists t; reflexivity. *)
    (* (*2*) *)
    (* apply wf_item_lift in H0. right; trivial. trivial. *)
    (* (*4*) *)
    (* left; exists u; trivial. *)
    (* (*5*) *)
    (* right; exists s3; apply cPi with s1 s2; trivial. *)
    (* (*6*) *)
    (* destruct IHtyp1. destruct H1; discriminate. destruct H1 as (u & ?). *)
    (* apply gen_pi in H1 as (s1 & s2 & s3 & h); decompose [and] h; clear h. *)
    (* right; exists s2. *)
    (* change (!s2) with (!s2 [← N]). eapply substitution. apply H5. apply H0. constructor. *)
    (* eauto. *)
    (* (*8*) *)
    (* right; exists s; trivial. *)
(* Admitted.   *)



Lemma weakenedapp_ok :
  (forall Γ M A, PTS_Prop.typ Γ M A -> Γ ⊢ M : A) /\ (forall Γ, PTS_Prop.wf Γ -> Γ ⊣).
  unshelve eapply PTS_Prop.typ_induc; eauto 2.
  intros Γ M N A B _ H _ H0.
  pose proof (TypeCorrect H). pose proof (TypeCorrect H0).
  destruct H1 as [[s H1]|[s H1]]. discriminate. apply gen_pi in H1.
  destruct H1 as [s1 [s2 [s3 [H1 [H1' [H3 H4]]]]]].
  refine (cApp _ _ _ H H0); eauto.
Defined.

(* Print Assumptions weakenedapp_ok. *)