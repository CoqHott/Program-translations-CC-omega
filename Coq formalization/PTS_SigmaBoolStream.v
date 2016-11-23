Require Import List.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Le Gt.
Require Import Sorts. Import withoutProp.

(** * Term definition for PTS and de Bruijn manipulation . *)
(** * Usual Term syntax .*)

(** Term syntax:*)
Inductive Term : Set :=
| Var : Vars -> Term
| Sort : Sorts -> Term
| Π : Term -> Term -> Term
| λ : Term -> Term -> Term
| App : Term -> Term -> Term
| Σ : Term -> Term -> Term
| Pair : Term -> Term -> Term
| π1 : Term -> Term
| π2 : Term -> Term
| Bool : Term
| true : Term
| false : Term
| If : forall (P true' false' b : Term), Term
| Eq : forall (A M N : Term), Term
| refle : Term -> Term
| J : forall (A P M1 N M2 p : Term), Term
| Stream : Term -> Term
| hd : Term -> Term
| tl : Term -> Term
| stream_corec : forall (S M0 M1 N : Term), Term
| Bisim : Term -> Term -> Term -> Term
| hd_b : Term -> Term
| tl_b : Term -> Term
| bisim_corec : forall (A S M0 M1 P0 P1 N : Term), Term
.

Notation "# v" := (Var v) (at level 1) : UT_scope.
Notation "! s" := (Sort s) (at level 1) : UT_scope.
Notation "x · y" := (App x y) (at level 15, left associativity) : UT_scope.
Notation "⟨ A , B ⟩" := (Pair A B) (at level 4) : UT_scope.
Delimit Scope UT_scope with UT. 
Open Scope UT_scope.


Reserved Notation " t ↑ x # n " (at level 5, x at level 0, left associativity).


(** In order to deal with variable bindings and captures, we need a lift
function to deal with free and bounded variables.
[M ↑ n # k recursivly add [n] to all variables that are
 above [k] in [M]. *)
Fixpoint lift_rec (n:nat) (k:nat) (T:Term) {struct T}
  := match T with
     | # x =>  if le_gt_dec k x then Var (n+x) else Var x
     | ! s => !s
     | M · N =>  App (M ↑ n # k) (N ↑ n # k)
     | Π  A B => Π  (A ↑ n # k) (B ↑ n # (S k))
     | λ A M => λ (A ↑ n # k) (M ↑ n # (S k)) 
     | Σ A B => Σ (A ↑ n # k) (B ↑ n # (S k))
     | ⟨ M , N ⟩ => ⟨ (M ↑ n # k) , (N ↑ n # k) ⟩
     | π1 M => π1 (M ↑ n # k)
     | π2 M => π2 (M ↑ n # k)
     | Bool => Bool
     | true => true
     | false => false
     | If P M N b => If (P ↑ n # (S k)) (M ↑ n # k) (N ↑ n # k) (b ↑ n # k)
     | Eq A t1 t2 => Eq (A ↑ n # k) (t1 ↑ n # k) (t2 ↑ n # k)
     | refle t => refle (t ↑ n # k)
     | J A P t1 u t2 p => J (A ↑ n # k) (P ↑ n # (S k)) (t1 ↑ n # k)
                           (u ↑ n # k) (t2 ↑ n # k) (p ↑ n # k)
     | Stream A => Stream (A ↑ n # k)
     | hd M => hd (M ↑ n # k)
     | tl M => tl (M ↑ n # k)
     | stream_corec s M0 M1 N => stream_corec (s ↑ n # k) (M0 ↑ n # k)
                                             (M1 ↑ n # k) (N ↑ n # k)
     | Bisim A M N => Bisim (A ↑ n # k) (M ↑ n # k) (N ↑ n # k)
     | hd_b M => hd_b (M ↑ n # k)
     | tl_b M => tl_b (M ↑ n # k)
     | bisim_corec A s M0 M1 P0 P1 N => bisim_corec (A ↑ n # k) (s ↑ n # k) (M0 ↑ n # k)
                                                   (M1 ↑ n # k) (P0 ↑ n # k) (P1 ↑ n # k)
                                                   (N ↑ n # k)
     end  
where "t ↑ n # k" := (lift_rec n k t) : UT_scope.

Notation " t ↑ n " := (lift_rec n 0 t) (at level 5, n at level 0, left associativity) : UT_scope.
Notation " t ↑ " := (lift_rec 1 0 t) (at level 5, left associativity) : UT_scope.

(** We will consider the usual implicit substitution without variable capture
(this is where the lift operator comes in handy).
  [ M [ n ← N ] ] replace the variable [n] in [M] by the term [N].
 *)
Reserved Notation "t [ x ← u ]" (at level 5, x at level 0, left associativity).

Fixpoint subst_rec u t n {struct t} :=
  match t with
  | # x => match (lt_eq_lt_dec x n) with
          | inleft (left _) => # x (* x < n *)
          | inleft (right _) => u ↑ n  (* x = n *)
          | inright _ => # (x - 1) (* x > n *)
          end
  | ! s => ! s
  | M · N => (M [ n ← u ]) · ( N [ n ← u ]) 
  | Π  A B => Π ( A [ n ← u ] ) (B [ S n ← u ]) 
  | λ  A M => λ (A [ n ← u ]) (M [ S n ← u ]) 
  | Σ  A B => Σ ( A [ n ← u ] ) (B [ S n ← u ]) 
  | ⟨ M , N ⟩ => ⟨ (M [ n ← u ]) , (N [ n ← u ]) ⟩
  | π1 M => π1 (M [ n ← u ])
  | π2 M => π2 (M [ n ← u ])
  | Bool => Bool
  | true => true
  | false => false
  | If P M N b => If (P [ S n ← u ]) (M [ n ← u ]) (N [ n ← u ]) (b [ n ← u ])
  | Eq A t1 t2 => Eq (A [ n ← u ]) (t1 [ n ← u ]) (t2 [ n ← u ])
  | refle t => refle (t [ n ← u ])
  | J A P t1 u t2 p => J (A [ n ← u ]) (P [ S n ← u ]) (t1 [ n ← u ])
                        (u [ n ← u ]) (t2 [ n ← u ]) (p [ n ← u ])
  | Stream A => Stream (A [ n ← u ])
  | hd M => hd (M [ n ← u ])
  | tl M => tl (M [ n ← u ])
  | stream_corec s M0 M1 N => stream_corec (s [ n ← u ]) (M0 [ n ← u ])
                                          (M1 [ n ← u ]) (N [ n ← u ])
  | Bisim A M N => Bisim (A [ n ← u ]) (M [ n ← u ]) (N [ n ← u ])
  | hd_b M => hd_b (M [ n ← u ])
  | tl_b M => tl_b (M [ n ← u ])
  | bisim_corec A s M0 M1 P0 P1 N => bisim_corec (A [ n ← u ]) (s [ n ← u ]) (M0 [ n ← u ]) (M1 [ n ← u ])
                                              (P0 [ n ← u ]) (P1 [ n ← u ]) (N [ n ← u ])
  end
where " t [ n ← u ] " := (subst_rec u t n) : UT_scope.

Notation " t [ ← u ] " := (subst_rec u t 0) (at level 5) : UT_scope.
  
(** Since we use de Bruijn indexes, Environment (or Context) are
simply lists of terms:  Γ(x:A) is encoded as  [A::Γ]. *)

Definition Env := list Term.

Set Implicit Arguments.

Inductive item (A:Type) (x:A): list A -> nat -> Prop :=
| item_hd: forall Γ :list A, (item x (cons x Γ) O)
| item_tl: forall (Γ:list A)(n:nat)(y:A), item x Γ n -> item x (cons y Γ) (S n).

Hint Constructors item.

(** In the list [Γ], the [n]th item is syntacticaly [x]. *)
Notation " x ↓ n ∈ Γ " := (item x Γ n) (at level 80, no associativity) : UT_scope.

(** In the list [Γ], [t] is  [n]th element correctly lifted according to [Γ]:
e.g.: if t ↓ n ⊂ Γ and we insert something in Γ, then 
we can still speak about t without think of the lift hidden by the insertion. *)

Definition item_lift (t:Term) (Γ:Env) (n:nat) :=
  exists u ,  t= u ↑ (S n) /\  u ↓ n ∈ Γ .

Hint Unfold item_lift.
Notation " t ↓ n ⊂ Γ " := (item_lift t Γ n) (at level 80, no associativity): UT_scope.

(** ** Usual Beta-reduction:
 - one step
 - multi step (reflexive, transitive closure)
 - converesion (reflexive, symetric, transitive closure)
 *)
Reserved Notation " A → B " (at level 80).

Inductive Beta : Term -> Term -> Prop :=
| Beta_head  : forall A M N, (λ A M) · N → M [← N]
| Beta_eq    : forall A P M N, J A P M N M (refle M) → N
| Beta_prod1 : forall M N, π1 ⟨M, N⟩ → M
| Beta_prod2 : forall M N, π2 ⟨M, N⟩ → N
| Beta_prod_eta : forall M, ⟨π1 M, π2 M⟩ → M
| Beta_Bool1 : forall A M N , If A true M N → M
| Beta_Bool2 : forall A M N , If A false M N → N
| Beta_hd_corec : forall s M0 M1 N, hd (stream_corec s M0 M1 N) → M0 · N
| Beta_tl_corec : forall s M0 M1 N, tl (stream_corec s M0 M1 N) → stream_corec s M0 M1 (M1 · N)
| Beta_hd_b_corec : forall A s M0 M1 P0 P1 N, hd_b (bisim_corec A s M0 M1 P0 P1 N) → M0 · P0 · P1 · N
| Beta_tl_b_corec : forall A s M0 M1 P0 P1 N, tl_b (bisim_corec A s M0 M1 P0 P1 N) → bisim_corec A s M0 M1 (tl P0) (tl P1) (M1 · P0 · P1 · N)
(* | Beta_tl_b_corec : forall A s M0 M1 P0 P1 N, tl_b (bisim_corec A s M0 M1 P0 P1 N) → bisim_corec A (λ (Stream A) (λ (Stream A ↑) (s ↑ 2 · (tl #1) · (tl #0))))  M0 M1 (tl P0) (tl P1) (M1 · P0 · P1 · N) *)
(* Congruence rules *)
| Beta_Π1    : forall A A' B , A → A' -> Π A B → Π A' B
| Beta_Π2    : forall A B  B', B → B' -> Π A B → Π A  B'
| Beta_λ1    : forall A A' M , A → A' -> λ A M → λ A' M
| Beta_λ2    : forall A M  M', M → M' -> λ A M → λ A  M'
| Beta_App1  : forall M M' N , M → M' -> M · N  → M' · N
| Beta_App2  : forall M N  N', N → N' -> M · N  → M · N'
| Beta_Eq1   : forall A A' M N, A → A' -> Eq A M N → Eq A' M N
| Beta_Eq2   : forall A M M' N, M → M' -> Eq A M N → Eq A M' N
| Beta_Eq3   : forall A M N N', N → N' -> Eq A M N → Eq A M N'
| Beta_refle : forall M M' , M → M' -> refle M  → refle M'
| Beta_J1     : forall A A' P M1 N M2 p, A → A' -> J A P M1 N M2 p → J A' P M1 N M2 p
| Beta_J2     : forall A P P' M1 N M2 p, P → P' -> J A P M1 N M2 p → J A P' M1 N M2 p
| Beta_J3     : forall A P M1 M1' N M2 p, M1 → M1' -> J A P M1 N M2 p → J A P M1' N M2 p
| Beta_J4     : forall A P M1 N N' M2 p, N → N' -> J A P M1 N M2 p → J A P M1 N' M2 p
| Beta_J5     : forall A P M1 N M2 M2' p, M2 → M2' -> J A P M1 N M2 p → J A P M1 N M2' p
| Beta_J6     : forall A P M1 N M2 p p', p → p' -> J A P M1 N M2 p → J A P M1 N M2 p'
| Beta_Σ1    : forall A A' B , A → A' -> Σ A B → Σ A' B
| Beta_Σ2    : forall A B  B', B → B' -> Σ A B → Σ A  B'
| Beta_Pair1 : forall M M' N, M → M' -> ⟨ M , N ⟩  → ⟨ M' , N ⟩
| Beta_Pair2 : forall M N N', N → N' -> ⟨ M , N ⟩  → ⟨ M , N' ⟩
| Beta_π1    : forall M M', M → M' -> π1 M  → π1 M'
| Beta_π2    : forall M M', M → M' -> π2 M  → π2 M'
| Beta_If1   : forall A A' b M N, A → A' -> If A b M N → If A' b M N
| Beta_If2   : forall A b b' M N, b → b' -> If A b M N → If A b' M N
| Beta_If3   : forall A b M M' N, M → M' -> If A b M N → If A b M' N
| Beta_If4   : forall A b M N N', N → N' -> If A b M N → If A b M N'
| Beta_Stream : forall A A', A → A' -> Stream A → Stream A'
| Beta_hd    : forall M M', M → M' -> hd M  → hd M'
| Beta_tl    : forall M M', M → M' -> tl M  → tl M'
| Beta_stream_corec1 : forall s s' M0 M1 N, s → s' -> stream_corec s M0 M1 N → stream_corec s' M0 M1 N
| Beta_stream_corec2 : forall s M0 M0' M1 N, M0 → M0' -> stream_corec s M0 M1 N → stream_corec s M0' M1 N
| Beta_stream_corec3 : forall s M0 M1 M1' N, M1 → M1' -> stream_corec s M0 M1 N → stream_corec s M0 M1' N
| Beta_stream_corec4 : forall s M0 M1 N N', N → N' -> stream_corec s M0 M1 N → stream_corec s M0 M1 N'
| Beta_Bisim1 : forall A A' M N, A → A' -> Bisim A M N → Bisim A' M N
| Beta_Bisim2 : forall A M M' N, M → M' -> Bisim A M N → Bisim A M' N
| Beta_Bisim3 : forall A M N N', N → N' -> Bisim A M N → Bisim A M N'
| Beta_hd_b    : forall M M', M → M' -> hd_b M  → hd_b M'
| Beta_tl_b    : forall M M', M → M' -> tl_b M  → tl_b M'
| Beta_bisim_corec0 : forall A A' s M0 M1 P0 P1 N, A → A' -> bisim_corec A s M0 M1 P0 P1 N → bisim_corec A' s M0 M1 P0 P1 N
| Beta_bisim_corec1 : forall A s s' M0 M1 P0 P1 N, s → s' -> bisim_corec A s M0 M1 P0 P1 N → bisim_corec A s' M0 M1 P0 P1 N
| Beta_bisim_corec2 : forall A s M0 M0' M1 P0 P1 N, M0 → M0' -> bisim_corec A s M0 M1 P0 P1 N → bisim_corec A s M0' M1 P0 P1 N
| Beta_bisim_corec3 : forall A s M0 M1 M1' P0 P1 N, M1 → M1' -> bisim_corec A s M0 M1 P0 P1 N → bisim_corec A s M0 M1' P0 P1 N
| Beta_bisim_corec4 : forall A s M0 M1 P0 P0' P1 N, P0 → P0' -> bisim_corec A s M0 M1 P0 P1 N → bisim_corec A s M0 M1 P0' P1 N
| Beta_bisim_corec5 : forall A s M0 M1 P0 P1 P1' N, P1 → P1' -> bisim_corec A s M0 M1 P0 P1 N → bisim_corec A s M0 M1 P0 P1' N
| Beta_bisim_corec6 : forall A s M0 M1 P0 P1 N N', N → N' -> bisim_corec A s M0 M1 P0 P1 N → bisim_corec A s M0 M1 P0 P1 N'
where "M → N" := (Beta M N) : UT_scope.
  
Reserved Notation " A →→ B " (at level 80).

Inductive Betas : Term -> Term -> Prop :=
| Betas_refl  : forall M    , M →→ M
| Betas_Beta  : forall M N  , M → N  -> M →→ N
| Betas_trans : forall M N P, M →→ N -> N →→ P -> M →→ P
where  " A →→ B " := (Betas A B) : UT_scope.

Reserved Notation " A ≡ B " (at level 80).

Inductive Betac : Term -> Term -> Prop :=
| Betac_Betas : forall M N  , M →→ N -> M ≡ N
| Betac_sym   : forall M N  , M ≡ N  -> N ≡ M
| Betac_trans : forall M N P, M ≡ N  -> N ≡ P -> M ≡ P
where " A ≡ B " := (Betac A B)  : UT_scope.

Hint Constructors Beta.
Hint Constructors Betas.
Hint Constructors Betac.


(** Typing judgements:*)
Reserved Notation "Γ ⊢ t : T" (at level 80, t, T at level 30, no associativity) .
Reserved Notation "Γ ⊣ " (at level 80, no associativity).

Notation "A ⇒ B" := (Π A (B ↑)) (at level 20, right associativity).
Definition empty := Π !(U 0) #0.
Notation "⊥" := empty.

Inductive wf : Env -> Prop :=
| wf_nil   : nil ⊣
| wf_cons : forall Γ A s, Γ ⊢ A : !s -> A::Γ ⊣
where "Γ ⊣" := (wf Γ) : UT_scope
with
typ : Env -> Term -> Term -> Prop :=
| cVar  : forall Γ A v, Γ ⊣ -> A ↓ v  ⊂ Γ -> Γ ⊢ #v : A
| cSort : forall Γ s s', Γ ⊣ -> Ax s s' -> Γ  ⊢ !s : !s'
| cΠ   : forall Γ A B s s' s''  , Rel s s' s'' -> Γ ⊢ A : !s -> A::Γ ⊢ B : !s' -> Γ ⊢  Π  A B : !s''
| cλ   : forall Γ A B s s' s'' M, Rel s s' s'' -> Γ ⊢ A : !s -> A::Γ ⊢ B : !s' -> A::Γ ⊢ M : B
               -> Γ ⊢ λ A M : Π  A B
| cApp  : forall Γ M N A B , Γ ⊢ M : Π A B -> Γ ⊢ N : A -> Γ ⊢ M · N : B[←N]
| cΣ : forall Γ A B i j, Γ ⊢ A : !(U i) -> A::Γ ⊢ B : !(U j) -> Γ ⊢ Σ A B : !(U (max i j))
| cPair : forall Γ M N A B, Γ ⊢ M : A -> Γ ⊢ N : B [←M] -> Γ ⊢ ⟨M,N⟩ : Σ A B
| cπ1 : forall Γ M A B, Γ ⊢ M : Σ A B -> Γ ⊢ π1 M : A
| cπ2 : forall Γ M A B, Γ ⊢ M : Σ A B -> Γ ⊢ π2 M : B[← π1 M]
| cBool : forall Γ i, Γ ⊣ -> Γ ⊢ Bool : !(U i)
| cTrue : forall Γ, Γ ⊣ -> Γ ⊢ true : Bool
| cFalse : forall Γ, Γ ⊣ -> Γ ⊢ false : Bool
| cIf : forall Γ P M N b s, Bool :: Γ ⊢ P : !s -> Γ ⊢ M : P[←true] -> Γ ⊢ N : P[←false]
                                   -> Γ ⊢ b : Bool -> Γ ⊢ (If P b M N) : P[←b]
| cEq : forall Γ A t1 t2 s, Γ ⊢ A : !s -> Γ ⊢ t1 : A -> Γ ⊢ t2 : A -> Γ ⊢ Eq A t1 t2 : !s
| crefle : forall Γ t A, Γ ⊢ t : A -> Γ ⊢ refle t : Eq A t t
| cJ : forall Γ A P t1 u t2 p s, A :: Γ ⊢ P : !s -> Γ ⊢ u : P[←t1] -> Γ ⊢ p : Eq A t1 t2
                                -> Γ ⊢ J A P t1 u t2 p : P[←t2]
| cStream : forall Γ A i, Γ ⊢ A : !(U i) -> Γ ⊢ Stream A : !(U i)
| chd : forall Γ M A, Γ ⊢ M : Stream A -> Γ ⊢ hd M : A
| ctl : forall Γ M A, Γ ⊢ M : Stream A -> Γ ⊢ tl M : Stream A
| cstream_corec : forall Γ s M0 M1 N A i, Γ ⊢ s : !(U i) -> Γ ⊢ M0 : s ⇒ A -> Γ ⊢ M1 : s ⇒ s
                                -> Γ ⊢ N : s -> Γ ⊢ stream_corec s M0 M1 N : Stream A
| cBisim : forall Γ A M N i, Γ ⊢ A : !(U i) -> Γ ⊢ M : Stream A -> Γ ⊢ N : Stream A
                                -> Γ ⊢ Bisim A M N : !(U i)
| chd_b : forall Γ A M N1 N2, Γ ⊢ M : Bisim A N1 N2 -> Γ ⊢ hd_b M : Eq A (hd N1) (hd N2)
| ctl_b : forall Γ A M N1 N2,
        Γ ⊢ M : Bisim A N1 N2 -> Γ ⊢ tl_b M : Bisim A (tl N1) (tl N2)
| cbisim_corec : forall Γ s M0 M1 P0 P1 N A i,
        Γ ⊢ s : Stream A ⇒ Stream A ⇒ !(U i)
       -> Γ ⊢ M0 : Π (Stream A) (Π (Stream (A ↑)) ((s ↑ 2) · #1 · #0 ⇒ Eq (A ↑ 2) (hd #1) (hd #0)))
       -> Γ ⊢ M1 : Π (Stream A) (Π (Stream (A ↑)) ((s ↑ 2) · #1 · #0 ⇒ (s ↑ 2) · (tl #1) · (tl #0)))
       -> Γ ⊢ N : s · P0 · P1 -> Γ ⊢ bisim_corec A s M0 M1 P0 P1 N : Bisim A P0 P1
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


Lemma lift_rec0 : forall M n, M ↑ 0 # n = M.
  induction M; intros; simpl; try reflexivity.
  destruct (le_gt_dec n v); reflexivity.
  all: rewrite ?IHM, ?IHM1, ?IHM2, ?IHM3, ?IHM4, ?IHM5, ?IHM6, ?IHM7;
    try reflexivity.
Qed.

Lemma lift0 : forall M, M ↑ 0 = M .
intros; apply lift_rec0.
Qed.

Lemma liftP1 : forall M i j  k, (M ↑ j # i) ↑ k # (j+i) = M ↑ (j+k) # i.
Admitted.
Lemma liftP2: forall M i j k n, i <= n ->
  (M ↑ j # i) ↑ k # (j+n) = (M ↑ k # n) ↑ j # i.
Admitted.
Lemma liftP3 : forall M i k j n , i <= k -> k <= (i+n) ->
                             (M ↑ n # i) ↑ j # k = M ↑ (j+n) # i.
Admitted.

Lemma lift_lift : forall M n m, (M ↑ m) ↑ n  = M↑ (n+m).
intros.
apply liftP3; intuition.
Qed.

Lemma substP1: forall M N i j k , 
  ( M [ j ← N] ) ↑ k # (j+i) = (M ↑ k # (S (j+i))) [ j ← (N ↑ k # i ) ].
Admitted.
Lemma substP2: forall M N i j n, i <= n ->
  (M ↑ j # i ) [ j+n ← N ] = ( M [ n ← N]) ↑ j # i .
Admitted.
Lemma substP3: forall M N i  k n, i <= k -> k <= i+n ->
  (M↑ (S n) # i) [ k← N] = M ↑ n # i.
Admitted.
Lemma substP4: forall M N P i j, 
   (M [ i← N]) [i+j ← P] = (M [S(i+j) ← P]) [i← N[j← P]].
Admitted.
Theorem thinning : forall {Γ M T A s}, Γ ⊢ M : T -> Γ ⊢ A : !s -> A::Γ ⊢ M ↑ 1 : T ↑ 1.
Admitted.

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

Lemma Betas_Σ : forall A A' B B', A →→ A' -> B →→ B' -> Σ A B →→ Σ A' B'.
assert (forall a b c , a →→ b -> Σ  c  a →→ Σ c  b).
induction 1; eauto.
assert (forall a b c, a →→ b -> Σ a  c →→ Σ b  c).
induction 1; eauto.
eauto.
Qed.
Hint Resolve Betas_Σ.


Lemma Betac_Σ : forall A A' B B', A ≡ A' -> B ≡ B' -> Σ A B ≡ Σ A' B'.
assert (forall a b c , a ≡ b -> Σ  c  a ≡ Σ c  b).
induction 1; eauto.
assert (forall a b c, a ≡ b -> Σ a  c ≡ Σ b  c).
induction 1; eauto.
eauto.
Qed.
Hint Resolve Betac_Σ.


Lemma Betas_Pair : forall M M' N N', M →→ M' -> N →→ N' -> ⟨M, N⟩ →→ ⟨M', N'⟩.
assert (forall a b c, b →→ c ->  ⟨a, b⟩ →→ ⟨a, c⟩).
induction 1; eauto.
assert (forall a b c, b→→c -> ⟨b, a⟩ →→ ⟨c, a⟩).
induction 1; eauto.
intros; eauto.
Qed.
Hint Resolve Betas_Pair.

Lemma Betac_Pair : forall M M' N N', M ≡ M' -> N ≡ N' -> ⟨M, N⟩ ≡ ⟨M', N'⟩.
assert (forall a b c, b ≡ c ->  ⟨a, b⟩ ≡ ⟨a, c⟩).
induction 1; eauto.
assert (forall a b c, b≡c -> ⟨b, a⟩ ≡ ⟨c, a⟩).
induction 1; eauto.
intros; eauto.
Qed.
Hint Resolve Betac_Pair.
     
Lemma Betas_π1 : forall M M', M →→ M' -> π1 M →→ π1 M'.
induction 1; eauto.
Qed.
Hint Resolve Betas_π1.

Lemma Betac_π1 : forall M M', M ≡ M' -> π1 M ≡ π1 M'.
induction 1; eauto.
Qed.
Hint Resolve Betac_π1.
     
Lemma Betas_π2 : forall M M', M →→ M' -> π2 M →→ π2 M'.
induction 1; eauto.
Qed.
Hint Resolve Betas_π2.

Lemma Betac_π2 : forall M M', M ≡ M' -> π2 M ≡ π2 M'.
induction 1; eauto.
Qed.
Hint Resolve Betac_π2.

(* TODO: If *)

Lemma Betas_Eq : forall A A' M M' N N', A →→ A' -> M →→ M' -> N →→ N' -> Eq A M N →→ Eq A' M' N'.
assert (forall a b c d, b →→ c ->  Eq a d b →→ Eq a d c).
induction 1; eauto.
assert (forall a b c d, b →→ c ->  Eq a b d →→ Eq a c d).
induction 1; eauto.
assert (forall a b c d, b →→ c ->  Eq b d a →→ Eq c d a).
induction 1; eauto.
intros; eauto 6.
Qed.
Hint Resolve Betas_Eq.


Lemma Betac_Eq : forall A A' M M' N N', A ≡ A' -> M ≡ M' -> N ≡ N' -> Eq A M N ≡ Eq A' M' N'.
assert (forall a b c d, b ≡ c ->  Eq a d b ≡ Eq a d c).
induction 1; eauto.
assert (forall a b c d, b ≡ c ->  Eq a b d ≡ Eq a c d).
induction 1; eauto.
assert (forall a b c d, b ≡ c ->  Eq b d a ≡ Eq c d a).
induction 1; eauto.
intros; eauto 6.
Qed.
Hint Resolve Betac_Eq.


Lemma Betas_J : forall A A' P P' M1 M1' N N' M2 M2' p p',
    A →→ A' -> P →→ P' -> M1 →→ M1' -> N →→ N' -> M2 →→ M2' -> p →→ p'
    -> J A P M1 N M2 p →→ J A' P' M1' N' M2' p'.
  assert (forall a b c d e f x, a →→ x -> J a b c d e f →→ J x b c d e f).
  induction 1; eauto.
  assert (forall a b c d e f x, b →→ x -> J a b c d e f →→ J a x c d e f).
  induction 1; eauto.
  assert (forall a b c d e f x, c →→ x -> J a b c d e f →→ J a b x d e f).
  induction 1; eauto.
  assert (forall a b c d e f x, d →→ x -> J a b c d e f →→ J a b c x e f).
  induction 1; eauto.
  assert (forall a b c d e f x, e →→ x -> J a b c d e f →→ J a b c d x f).
  induction 1; eauto.
  assert (forall a b c d e f x, f →→ x -> J a b c d e f →→ J a b c d e x).
  induction 1; eauto.
  intros.
  eapply Betas_trans. eapply H; eassumption.
  eapply Betas_trans. eapply H0; eassumption.
  eapply Betas_trans. eapply H1; eassumption.
  eapply Betas_trans. eapply H2; eassumption.
  eapply Betas_trans. eapply H3; eassumption.
  eapply H4; eassumption.
Defined.
Hint Resolve Betas_J.

Lemma Betac_J : forall A A' P P' M1 M1' N N' M2 M2' p p',
    A ≡ A' -> P ≡ P' -> M1 ≡ M1' -> N ≡ N' -> M2 ≡ M2' -> p ≡ p'
    -> J A P M1 N M2 p ≡ J A' P' M1' N' M2' p'.
  assert (forall a b c d e f x, a ≡ x -> J a b c d e f ≡ J x b c d e f).
  induction 1; eauto.
  assert (forall a b c d e f x, b ≡ x -> J a b c d e f ≡ J a x c d e f).
  induction 1; eauto.
  assert (forall a b c d e f x, c ≡ x -> J a b c d e f ≡ J a b x d e f).
  induction 1; eauto.
  assert (forall a b c d e f x, d ≡ x -> J a b c d e f ≡ J a b c x e f).
  induction 1; eauto.
  assert (forall a b c d e f x, e ≡ x -> J a b c d e f ≡ J a b c d x f).
  induction 1; eauto.
  assert (forall a b c d e f x, f ≡ x -> J a b c d e f ≡ J a b c d e x).
  induction 1; eauto.
  intros.
  eapply Betac_trans. eapply H; eassumption.
  eapply Betac_trans. eapply H0; eassumption.
  eapply Betac_trans. eapply H1; eassumption.
  eapply Betac_trans. eapply H2; eassumption.
  eapply Betac_trans. eapply H3; eassumption.
  eapply H4; eassumption.
Defined.
Hint Resolve Betac_J.


Lemma Betas_refle : forall M M', M →→ M' -> refle M →→ refle M'.
induction 1; eauto.
Qed.
Hint Resolve Betas_refle.

Lemma Betac_refle : forall M M', M ≡ M' -> refle M ≡ refle M'.
induction 1; eauto.
Qed.
Hint Resolve Betac_refle.

Lemma Betas_Stream A A' : A →→ A' -> Stream A →→ Stream A'.
  induction 1; eauto.
Defined.
Hint Resolve Betas_Stream.

Lemma Betac_Stream A A' : A ≡ A' -> Stream A ≡ Stream A'.
induction 1; eauto.
Qed.
Hint Resolve Betac_Stream.

Lemma Betas_hd : forall M M', M →→ M' -> hd M →→ hd M'.
induction 1; eauto.
Qed.
Hint Resolve Betas_hd.

Lemma Betac_hd : forall M M', M ≡ M' -> hd M ≡ hd M'.
induction 1; eauto.
Qed.
Hint Resolve Betac_hd.

Lemma Betas_tl : forall M M', M →→ M' -> tl M →→ tl M'.
induction 1; eauto.
Qed.
Hint Resolve Betas_tl.

Lemma Betac_tl : forall M M', M ≡ M' -> tl M ≡ tl M'.
induction 1; eauto.
Qed.
Hint Resolve Betac_tl.

Lemma Betas_stream_corec : forall S S' M0 M0' M1 M1' N N',
    S →→ S' -> M0 →→ M0' -> M1 →→ M1' -> N →→ N'
    -> stream_corec S M0 M1 N →→ stream_corec S' M0' M1' N'.
  assert (forall a b c d x, a →→ x -> stream_corec a b c d →→ stream_corec x b c d).
  induction 1; eauto.
  assert (forall a b c d x, b →→ x -> stream_corec a b c d →→ stream_corec a x c d).
  induction 1; eauto.
  assert (forall a b c d x, c →→ x -> stream_corec a b c d →→ stream_corec a b x d).
  induction 1; eauto.
  assert (forall a b c d x, d →→ x -> stream_corec a b c d →→ stream_corec a b c x).
  induction 1; eauto.
  intros.
  eapply Betas_trans. eapply H; eassumption.
  eapply Betas_trans. eapply H0; eassumption.
  eapply Betas_trans. eapply H1; eassumption.
  eapply H2; eassumption.
Defined.
Hint Resolve Betas_stream_corec.

Lemma Betac_stream_corec : forall S S' M0 M0' M1 M1' N N',
    S ≡ S' -> M0 ≡ M0' -> M1 ≡ M1' -> N ≡ N'
    -> stream_corec S M0 M1 N ≡ stream_corec S' M0' M1' N'.
  assert (forall a b c d x, a ≡ x -> stream_corec a b c d ≡ stream_corec x b c d).
  induction 1; eauto.
  assert (forall a b c d x, b ≡ x -> stream_corec a b c d ≡ stream_corec a x c d).
  induction 1; eauto.
  assert (forall a b c d x, c ≡ x -> stream_corec a b c d ≡ stream_corec a b x d).
  induction 1; eauto.
  assert (forall a b c d x, d ≡ x -> stream_corec a b c d ≡ stream_corec a b c x).
  induction 1; eauto.
  intros.
  eapply Betac_trans. eapply H; eassumption.
  eapply Betac_trans. eapply H0; eassumption.
  eapply Betac_trans. eapply H1; eassumption.
  eapply H2; eassumption.
Defined.
Hint Resolve Betac_stream_corec.


Lemma Betas_Bisim : forall A A' M M' N N', A →→ A' -> M →→ M' -> N →→ N' -> Bisim A M N →→ Bisim A' M' N'.
  assert (forall a b c d, b →→ c ->  Bisim a d b →→ Bisim a d c).
  induction 1; eauto.
  assert (forall a b c d, b →→ c ->  Bisim a b d →→ Bisim a c d).
  induction 1; eauto.
  assert (forall a b c d, b →→ c ->  Bisim b d a →→ Bisim c d a).
  induction 1; eauto.
  intros.
  eapply Betas_trans. eapply H; eassumption.
  eapply Betas_trans. eapply H0; eassumption.
  eapply H1; eassumption.
Qed.
Hint Resolve Betas_Bisim.


Lemma Betac_Bisim : forall A A' M M' N N', A ≡ A' -> M ≡ M' -> N ≡ N' -> Bisim A M N ≡ Bisim A' M' N'.
  assert (forall a b c d, b ≡ c ->  Bisim a d b ≡ Bisim a d c).
  induction 1; eauto.
  assert (forall a b c d, b ≡ c ->  Bisim a b d ≡ Bisim a c d).
  induction 1; eauto.
  assert (forall a b c d, b ≡ c ->  Bisim b d a ≡ Bisim c d a).
  induction 1; eauto.
  intros.
  eapply Betac_trans. eapply H; eassumption.
  eapply Betac_trans. eapply H0; eassumption.
  eapply H1; eassumption.
Qed.
Hint Resolve Betac_Bisim.


Lemma Betas_hd_b : forall M M', M →→ M' -> hd_b M →→ hd_b M'.
induction 1; eauto.
Qed.
Hint Resolve Betas_hd_b.

Lemma Betac_hd_b : forall M M', M ≡ M' -> hd_b M ≡ hd_b M'.
induction 1; eauto.
Qed.
Hint Resolve Betac_hd_b.
     
Lemma Betas_tl_b : forall M M', M →→ M' -> tl_b M →→ tl_b M'.
induction 1; eauto.
Qed.
Hint Resolve Betas_tl_b.

Lemma Betac_tl_b : forall M M', M ≡ M' -> tl_b M ≡ tl_b M'.
induction 1; eauto.
Qed.
Hint Resolve Betac_tl_b.

Lemma Betas_bisim_corec A A' s s' M0 M0' M1 M1' P0 P0' P1 P1' N N' :
  A →→ A' -> s →→ s' -> M0 →→ M0' -> M1 →→ M1'-> P0 →→ P0' -> P1 →→ P1' -> N →→ N' ->
  bisim_corec A s M0 M1 P0 P1 N →→ bisim_corec A' s' M0' M1' P0' P1' N'.
  assert (forall a b c d e f g x, a →→ x -> bisim_corec a b c d e f g →→ bisim_corec x b c d e f g).
  induction 1; eauto.
  assert (forall a b c d e f g x, b →→ x -> bisim_corec a b c d e f g →→ bisim_corec a x c d e f g).
  induction 1; eauto.
  assert (forall a b c d e f g x, c →→ x -> bisim_corec a b c d e f g →→ bisim_corec a b x d e f g).
  induction 1; eauto.
  assert (forall a b c d e f g x, d →→ x -> bisim_corec a b c d e f g →→ bisim_corec a b c x e f g).
  induction 1; eauto.
  assert (forall a b c d e f g x, e →→ x -> bisim_corec a b c d e f g →→ bisim_corec a b c d x f g).
  induction 1; eauto.
  assert (forall a b c d e f g x, f →→ x -> bisim_corec a b c d e f g →→ bisim_corec a b c d e x g).
  induction 1; eauto.
  assert (forall a b c d e f g x, g →→ x -> bisim_corec a b c d e f g →→ bisim_corec a b c d e f x).
  induction 1; eauto.
  intros.
  eapply Betas_trans. eapply H; eassumption.
  eapply Betas_trans. eapply H0; eassumption.
  eapply Betas_trans. eapply H1; eassumption.
  eapply Betas_trans. eapply H2; eassumption.
  eapply Betas_trans. eapply H3; eassumption.
  eapply Betas_trans. eapply H4; eassumption.
  eapply H5; eassumption.
Defined.
Hint Resolve Betas_bisim_corec.

Lemma Betac_bisim_corec A A' s s' M0 M0' M1 M1' P0 P0' P1 P1' N N' :
  A ≡ A' -> s ≡ s' -> M0 ≡ M0' -> M1 ≡ M1'-> P0 ≡ P0' -> P1 ≡ P1' -> N ≡ N' ->
  bisim_corec A s M0 M1 P0 P1 N ≡ bisim_corec A' s' M0' M1' P0' P1' N'.
  assert (forall a b c d e f g x, a ≡ x -> bisim_corec a b c d e f g ≡ bisim_corec x b c d e f g).
  induction 1; eauto.
  assert (forall a b c d e f g x, b ≡ x -> bisim_corec a b c d e f g ≡ bisim_corec a x c d e f g).
  induction 1; eauto.
  assert (forall a b c d e f g x, c ≡ x -> bisim_corec a b c d e f g ≡ bisim_corec a b x d e f g).
  induction 1; eauto.
  assert (forall a b c d e f g x, d ≡ x -> bisim_corec a b c d e f g ≡ bisim_corec a b c x e f g).
  induction 1; eauto.
  assert (forall a b c d e f g x, e ≡ x -> bisim_corec a b c d e f g ≡ bisim_corec a b c d x f g).
  induction 1; eauto.
  assert (forall a b c d e f g x, f ≡ x -> bisim_corec a b c d e f g ≡ bisim_corec a b c d e x g).
  induction 1; eauto.
  assert (forall a b c d e f g x, g ≡ x -> bisim_corec a b c d e f g ≡ bisim_corec a b c d e f x).
  induction 1; eauto.
  intros.
  eapply Betac_trans. eapply H; eassumption.
  eapply Betac_trans. eapply H0; eassumption.
  eapply Betac_trans. eapply H1; eassumption.
  eapply Betac_trans. eapply H2; eassumption.
  eapply Betac_trans. eapply H3; eassumption.
  eapply Betac_trans. eapply H4; eassumption.
  eapply H5; eassumption.
Defined.
Hint Resolve Betac_bisim_corec.


(* (** Lift properties.*) *)
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

