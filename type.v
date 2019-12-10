Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Arith.Arith.
Require Import maps.
Require Import imp.
Require Import smallstep.

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

Reserved Notation "t1 '==>' t2" (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 ==> t1' ->
      (tsucc t1) ==> (tsucc t1')
  | ST_PredZero :
      (tpred tzero) ==> tzero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) ==> t1
  | ST_Pred : forall t1 t1',
      t1 ==> t1' ->
      (tpred t1) ==> (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) ==> ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) ==> tfalse
  | ST_Iszero : forall t1 t1',
      t1 ==> t1' ->
      (tiszero t1) ==> (tiszero t1')

where "t1 '==>' t2" := (step t1 t2).
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
- unfold normal_form, not. intros.
inversion H. inversion H0. inversion H2.
- unfold not. intros. inversion H.
inversion H0. inversion H0. inversion H2.
Qed.

Lemma value_is_nf' : forall t,
  value t -> step_normal_form t.
Proof.
intros.
unfold step_normal_form, not.
intros. inversion H; clear H.
- inversion H1; subst.
  + inversion H0. inversion H.
  + inversion H0. inversion H.
- induction H1; subst.
  + inversion H0. inversion H.
  + apply IHnvalue. inversion H0.  
inversion H. exists t1'. assumption.
Qed.

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
  | T_Iszero : forall t1,
       |- t1 in TNat ->
       |- tiszero t1 in TBool

where "'|-' t 'in' T" := (has_type t T).
Hint Constructors has_type.

Example has_type_1 :
  |- tif tfalse tzero (tsucc tzero) in TNat.
Proof.
apply T_If.
apply T_False.
apply T_Zero.

apply T_Succ.
apply T_Zero.
Qed.

Example has_type_not :
  ~ (|- tif tfalse tzero ttrue in TBool).
Proof.
intros c. solve_by_inverts 2. Qed.

Example succ_hastype_nat__hastype_nat : forall t,
  |- tsucc t in TNat ->
  |- t in TNat.
Proof.
intros.
inversion H.
assumption.
Qed.

Lemma bool_canonical : forall t,
  |- t in TBool -> value t -> bvalue t.
Proof.
intros.
inversion H0. auto.
induction H1; inversion H.
Qed.

Lemma nat_canonical : forall t,
  |- t in TNat -> value t -> nvalue t.
Proof.
intros t HT HV.
inversion HV.
inversion H; subst; inversion HT.
assumption.
Qed. 



Theorem progress : forall t T,
  |- t in T ->
  value t \/ exists t', t ==> t'.
Proof with auto.
intros t T HT.
  induction HT...
- (* T_If *)
    right. inversion IHHT1; 
clear IHHT1.
  + apply (bool_canonical t1 HT1) in H.
    inversion H; subst; clear H.
      * exists t2. apply ST_IfTrue.
      * exists t3. apply ST_IfFalse.
  + inversion H as [t1' H1].
  exists (tif t1' t2 t3). auto.
- right. inversion IHHT; clear IHHT.
  + apply (nat_canonical t1 HT) in H.
    inversion H; subst; clear H.
    *
Admitted.



Definition 
manual_grade_for_finish_progress_informal : 
option (prod nat string) := None.

Theorem preservation : forall t t' T,
  |- t in T ->
  t ==> t' ->
  |- t' in T.
Proof.
Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT; intros t' HE;
  try solve_by_invert.
Admitted.

Definition multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  |- t in T ->
  t ==>* t' ->
  ~(stuck t').
Proof.
intros t t' T HT P.
induction P ; intros [R S].
destruct (progress x T HT); auto.
apply IHP. apply (preservation x y T HT H).
  unfold stuck. split. auto. auto. Qed.

Module NormalizePlayground.
Import smallstep.
Example step_example1 :
  (P (C 3) (P (C 3) (C 4)))
  ==>* (C 10).
Proof.
  apply multi_step with (P (C 3) (C 7)).
    apply ST_Plus2.
      apply v_const.
      apply ST_PlusConstConst.
  apply multi_step with (C 10).
    apply ST_PlusConstConst.
  apply multi_refl.
Qed.

Hint Constructors step value.
Example step_example1' :
  (P (C 3) (P (C 3) (C 4)))
  ==>* (C 10).
Proof.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  apply multi_refl.
Qed.

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.
Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | (instantiate; simpl)]);
  apply multi_refl.

Example step_example1'' :
  (P (C 3) (P (C 3) (C 4)))
  ==>* (C 10).
Proof.
  normalize.
Qed.

Example step_example1''' : exists e',
  (P (C 3) (P (C 3) (C 4)))
  ==>* e'.
Proof.
  eapply ex_intro. eapply multi_step. auto.
  simpl. eapply multi_step. auto. simpl.
  apply multi_refl.
 Qed.


Theorem normalize_ex : exists e',
  (P (C 3) (P (C 2) (C 1)))
  ==>* e'.
Proof.
eapply ex_intro. eapply multi_step. auto.
  simpl. eapply multi_step. auto. simpl.
  apply multi_refl.
 Qed.

Theorem normalize_ex' : exists e',
  (P (C 3) (P (C 2) (C 1)))
  ==>* e'.
Proof.
eapply ex_intro.
apply multi_step with (P (C 3) (C 3)).
apply ST_Plus2.
apply v_const.
apply ST_PlusConstConst.
apply multi_step with (C 6).
apply ST_PlusConstConst.
apply multi_refl.
Qed.

End NormalizePlayground.
Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.
Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | (instantiate; simpl)]);
  apply multi_refl.

Definition manual_grade_for_subject_expansion : option (prod nat string) := None.
Definition manual_grade_for_variation1 : option (prod nat string) := None.
Definition manual_grade_for_variation2 : option (prod nat string) := None.
Definition manual_grade_for_remove_predzero : option (prod nat string) := None.
Definition manual_grade_for_prog_pres_bigstep : option (prod nat string) := None.






