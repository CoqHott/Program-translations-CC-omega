Require Import List.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Le Gt.
Require Import Sorts. Import withProp.

(** * Term definition for PTS and de Bruijn manipulation . *)
(** * Usual Term syntax .*)

(** Term syntax:*)
Inductive Term : Set :=
| Var : Vars -> Term
| Sort : Sorts -> Term
| Π : Term -> Term -> Term
| λ : Term -> Term -> Term
| App : Term -> Term -> Term
.

Notation "# v" := (Var v) (at level 1) : UT_scope.
Notation "! s" := (Sort s) (at level 1) : UT_scope.
Notation "x · y" := (App x y) (at level 15, left associativity) : UT_scope.
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
(* Congruence rules *)
| Beta_Π1    : forall A A' B , A → A' -> Π A B → Π A' B
| Beta_Π2    : forall A B  B', B → B' -> Π A B → Π A  B'
| Beta_λ1    : forall A A' M , A → A' -> λ A M → λ A' M
| Beta_λ2    : forall A M  M', M → M' -> λ A M → λ A  M'
| Beta_App1  : forall M M' N , M → M' -> M · N  → M' · N
| Beta_App2  : forall M N  N', N → N' -> M · N  → M · N'
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