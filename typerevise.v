Set Warnings "-notation-overridden,-parsing". 
From Coq Require Import Arith.Arith.
Require Import maps.
Require Import imp.
Require Import smallstep2.
Hint Constructors multi.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tzero : tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tiszero : tm -> tm.

Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue ttrue
  | bv_false : bvalue tfalse.
Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tzero
  | nv_succ : forall t, nvalue t -> nvalue (tsucc t).
Definition value (t:tm) := bvalue t \/ nvalue t.
Hint Constructors nvalue bvalue.
Hint Unfold value.
Hint Unfold update.

Reserved Notation "t1 '-->' t2" (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) --> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (tif t1 t2 t3) --> (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 --> t1' ->
      (tsucc t1) --> (tsucc t1')
  | ST_PredZero :
      (tpred tzero) --> tzero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) --> t1
  | ST_Pred : forall t1 t1',
      t1 --> t1' ->
      (tpred t1) --> (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) --> ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) --> tfalse
  | ST_Iszero : forall t1 t1',
      t1 --> t1' ->
      (tiszero t1) --> (tiszero t1')

where "t1 '-->' t2" := (step t1 t2).
Hint Constructors step.

Notation step_normal_form := (normal_form step).
Definition stuck (t:tm) : Prop :=
  step_normal_form t /\ ~ value t.
Hint Unfold stuck.

Example some_term_is_stuck :
  exists t, stuck t.
Proof.
exists (tsucc ttrue).
unfold stuck.
split. 
- unfold step_normal_form. unfold not.
intros. inversion H. inversion H0.
inversion H2.
- unfold not. intros.
inversion H. inversion H0.
inversion H0. inversion H2.
Qed.

Lemma tsucc_is_val : forall t,
  nvalue (tsucc t) -> nvalue t.
Proof.
intros.
inversion H. apply H1.
Qed.

Lemma nval_is_val: forall t,
nvalue t -> value t.
Proof with eauto.
intros. induction H.
- auto. 
- auto.
Qed. 


Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
intros. unfold step_normal_form.
unfold not. intros.
inversion H; clear H.  
- inversion H1. subst.
inversion H0. inversion H. subst.
inversion H0. inversion H.
- induction H1 ; subst. 
  + inversion H0. inversion H.
  + apply IHnvalue. 
    inversion H0. inversion H. 
    exists t1'. apply H3.
Qed.  
    
Theorem step_deterministic:
  deterministic step.
Proof with eauto.
unfold deterministic.
intros. generalize dependent y2.  
induction H; intros.
- inversion H0; subst. reflexivity.
inversion H4.
- inversion H0; subst. reflexivity.
inversion H4.
- inversion H0. rewrite <- H2 in H.
inversion H. rewrite <- H2 in H.
inversion H.  rewrite IHstep with t1'0.
reflexivity. apply H5.
- inversion H0. rewrite IHstep with t1'0.
reflexivity. apply H2.
- inversion H0. reflexivity.
  inversion H1.
- apply nval_is_val in H. apply value_is_nf in H.
 inversion H0. 
  + reflexivity.
   
Admitted.

Inductive ty : Type :=
  | TBool : ty
  | TNat : ty.

Reserved Notation "'|-' t 'in' T" (at level 40).
Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       |- ttrue in TBool
  | T_False :
       |- tfalse in TBool
  | T_If : forall t1 t2 t3 T,
       |- t1 in TBool ->
       |- t2 in T ->
       |- t3 in T ->
       |- tif t1 t2 t3 in T
  | T_Zero :
       |- tzero in TNat
  | T_Succ : forall t1,
       |- t1 in TNat ->
       |- tsucc t1 in TNat
  | T_Pred : forall t1,
       |- t1 in TNat ->
       |- tpred t1 in TNat
   (* | T_Pred_Succ : forall t1,
       |- t1 in TNat ->
       |- tpred(tsucc t1) in TNat  *)
  | T_Iszero : forall t1,
       |- t1 in TNat ->
       |- tiszero t1 in TBool


where "'|-' t 'in' T" := (has_type t T).
Hint Constructors has_type.
Hint Constructors step.

Example has_type_1 :
  |- tif tfalse tzero (tsucc tzero) in TNat.
Proof.
apply T_If.
auto. auto.
apply T_Succ. auto.
Qed.

Example has_type_not :
  ~ (|- tif tfalse tzero ttrue in TBool).
Proof.
unfold not.
intros. inversion H.
inversion H5.
Qed.

Example succ_hastype_nat__hastype_nat : forall t,
  |- tsucc t in TNat ->
  |- t in TNat.
Proof.
intros t. intros.
inversion H. apply H1.
Qed.

Lemma bool_canonical : forall t,
  |- t in TBool -> value t -> bvalue t.
Proof. 
  intros t HT [Hb | Hn].
  - assumption.
  - induction Hn; inversion HT; auto.
Qed.

Lemma nat_canonical : forall t,
|- t in TNat -> value t -> nvalue t.
Proof.
intros t HT [Hb | Hn].
  - induction Hb; inversion HT; auto.
  - assumption.
Qed.


Theorem progress : forall t T,
  |- t in T ->
  value t \/ exists t', t --> t'.
Proof with auto.
intros. induction H.
- left. auto.
- left. auto.
- right. destruct IHhas_type1 as [A | B].
assert (G: bvalue t1).
{ apply bool_canonical. apply H.
apply A. }
inversion G. exists t2. 
apply ST_IfTrue. exists t3.
apply ST_IfFalse.
inversion B.
exists (tif x t2 t3).
apply ST_If. apply H2.
- left. auto.
- destruct IHhas_type as [A | B].
assert (G: nvalue t1).
{ apply nat_canonical. apply H.
apply A. } clear A.
left. auto.
right. inversion B.
exists (tsucc x).
apply ST_Succ. apply H0.
- destruct IHhas_type as [A | B].
assert (G: nvalue t1).
apply nat_canonical. apply H.
apply A. right. inversion G.
exists tzero. apply ST_PredZero.
exists t. apply ST_PredSucc. 
apply H0. 
right. inversion B. exists (tpred x).
apply ST_Pred. apply H0.
- destruct IHhas_type as [A | B].
assert (G: nvalue t1).
apply nat_canonical. apply H.
apply A. right. inversion G.
exists ttrue. apply ST_IszeroZero.
exists tfalse. apply ST_IszeroSucc.
apply H0. right. inversion B. 
exists (tiszero x). apply ST_Iszero.
apply H0.
Qed.

Theorem preservation : forall t t' T,
  |- t in T ->
  t --> t' ->
  |- t' in T.
Proof.
intros.
generalize dependent t'. 
induction H.
- intros. inversion H0.
- intros. inversion H0.
- intros. inversion H2.
  rewrite <- H3. apply H0.
  rewrite <- H3. apply H1.
  apply T_If. apply IHhas_type1; assumption.
  assumption. assumption.
- intros. inversion H0.
- intros. inversion H0. apply T_Succ.
  apply IHhas_type. apply H2.
- intros. inversion H0.  
  auto. inversion H2.
  auto. rewrite <- H1 in IHhas_type.
Admitted.
  
  
Theorem preservation' : forall t t' T,
  |- t in T ->
  t --> t' ->
  |- t' in T.
Proof with eauto.
intros. generalize dependent T.
induction H0; intros.
- inversion H. apply H5.
- inversion H. apply H6.
- inversion H. apply T_If.
  apply IHstep. apply H4.
  apply H6. apply H7.
- inversion H. apply T_Succ.
  apply IHstep. apply H2.
- inversion H. auto.
- inversion H0. inversion H2.
  apply H5.
- inversion H. apply T_Pred.
  apply IHstep. apply H2.
- inversion H. auto. 
- inversion H0. auto.
- inversion H. apply T_Iszero.
  apply IHstep. apply H2.
Qed.

Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

(* Definition stuck (t:tm) : Prop :=
  step_normal_form t /\ ~ value t.
Hint Unfold stuck.
 *)
(* forall t T,
  |- t in T ->
  value t \/ exists t', t --> t'. *)
(* forall t t' T,
  |- t in T ->
  t --> t' ->
  |- t' in T.
 *)
Corollary soundness : forall t t' T,
  |- t in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
intros t t' T HT P.
induction P.
- intros [R S].
destruct (progress x T HT). auto.
unfold step_normal_form in R. auto.
- apply IHP. 
  apply (preservation x y T HT H).
Qed.


Corollary soundness' : forall t t' T,
  |- t in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
intros. induction H0. (* (x-->x and x-->z) *)
- unfold not. intros.
  unfold stuck in H0.  
  destruct (progress x T H).
  destruct H0  as [A B]. auto.
  destruct H0  as [A B].
  unfold step_normal_form in A. auto.
- apply IHmulti. 
  apply (preservation x y T H H0).
Qed.

Theorem subject_expansion : 
exists t, exists t', exists T,
  t --> t' /\ |- t' in T /\ ~ |- t in T.
Proof with eauto.
apply ex_intro with (tif tfalse tzero ttrue).
exists ttrue. exists TBool. split.
apply ST_IfFalse. split. auto.
unfold not. intros. inversion H. 
inversion H5.
Qed.
 














  
  


 




