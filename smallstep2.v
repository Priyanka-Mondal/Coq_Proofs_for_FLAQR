Set Warnings "-notation-overridden,-parsing". 
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations. 
Require Import maps. 
Require Import imp.
Require Import rel.

Inductive tm : Type :=
  | C : nat -> tm 
  | P : tm -> tm -> tm. 

Fixpoint evalF (t:tm) : nat :=
match t with
| C n => n
| P n1 n2 => evalF n1 + evalF n2
end.

Reserved Notation " t '==>' n " 
(at level 50, left associativity).

Inductive eval : tm -> nat-> Prop :=
| E_Const : forall n,
  C n ==> n
| E_Plus : forall t1 t2 n1 n2,
  t1 ==> n1 ->
  t2 ==> n2 ->
  P t1 t2 ==> (n1+n2)
where "t '==>' n " := (eval t n).

Module SimpleArith1.

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
       P (C n1) (C n2) --> C(n1+n2)
  | ST_Plus1 : forall t1 t2 t1',
       t1 --> t1' ->
       P t1 t2 --> P t1' t2
  | ST_Plus2 : forall n1 t2 t2',
       t2 --> t2' ->
       P (C n1) t2 --> P (C n1) t2'
where " t '-->' t' " := (step t t').
(* small step version of evalF
 *)

Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
      -->
      P
        (C 0)
        (P
          (C 2)
          (C (0 + 3))).
Proof.
apply ST_Plus2.
apply ST_Plus2.
apply ST_PlusConstConst.
Qed.

End SimpleArith1.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.
Module SimpleArith2.
Import SimpleArith1.

Theorem step_deterministic:
  deterministic step.
Proof.
unfold deterministic.
intros.
generalize dependent y2.
induction H; intros.
(* - rewrite <- H1 in H. *)
(* rewrite <- H0 in H. *)
- inversion H0. reflexivity.
inversion H3.
inversion H3.
- inversion H0.
  rewrite <- H2 in H.
  inversion H.
  rewrite IHstep with t1'0.
  reflexivity.
  apply H4.
  rewrite <- H1 in H.
  inversion H.
- inversion H0.
  rewrite <- H3 in H.
  inversion H.
  inversion H4. 
  rewrite IHstep with t2'0.
  reflexivity.
  apply H4.
Qed.

End SimpleArith2.

(* Ltac solve_by_invert :=
  solve_by_inverts 1.
Module SimpleArith3.
Import SimpleArith1.
Theorem step_deterministic_alt: deterministic step.
Proof.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
    inversion Hy2; subst; try solve_by_invert.
  - (* ST_PlusConstConst *) reflexivity.
  - (* ST_Plus1 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
  - (* ST_Plus2 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.
End SimpleArith3. *)
Inductive value : tm -> Prop :=
 | v_const  : forall n, value (C n).

Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
          P (C n1) (C n2)
      --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 --> t1' ->
        P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 -> (* <--- n.b. *)
        t2 --> t2' ->
        P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

Theorem step_deterministic :
  deterministic step.
Proof.
unfold deterministic.
intros.
generalize dependent y2.
induction H; intros.
- inversion H0. reflexivity.
inversion H3. inversion H4.
- inversion H0. 
  + rewrite <- H2 in H. inversion H.
  + rewrite IHstep with t1'0.
    reflexivity. apply H4. 
  + inversion H3.
    rewrite <- H6 in H.
    inversion H. 
- inversion H1.
  + rewrite <- H4 in H0.
    inversion H0.
  + inversion H. rewrite <- H6 in H5.
    inversion H5.
  + rewrite IHstep with t2'0.
    reflexivity.
    apply H6.
Qed.

Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
Proof.
intros.
induction t.
- left. apply v_const.
- right. 
  destruct IHt1 as [val1|[t1' imp1]].
  destruct IHt2 as [val2|[t2' imp2]].
  inversion val1.
  inversion val2.
  exists (C(n+n0)).
  apply ST_PlusConstConst.
  inversion val1. 
  exists (P (C n) t2').
  apply ST_Plus2. 
  apply v_const.
  apply imp2.
  destruct IHt2 as [val2| [t2' imp2]].
  + exists (P t1' t2).
  apply ST_Plus1. apply imp1.
  + exists (P t1' t2).
    apply ST_Plus1.
    apply imp1.
Qed.
 
(*  let's begin by giving a name to 
terms that cannot make progress. 
We'll call them normal forms.
 *)

Definition normal_form {X : Type} 
(R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

(* Note that this definition 
specifies what it is to be a 
normal form for an arbitrary 
relation R over an arbitrary 
set X, not just for the particular 
single-step reduction relation over 
terms that we are interested in at the moment. 
 *)

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
intros.
unfold normal_form.
unfold not.
intros.
inversion H.
rewrite <- H1 in H0.
inversion H0.
inversion H2.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof.
unfold normal_form.
intros t H.
assert (G : value t \/ 
exists t', t --> t').
{ apply strong_progress. }
destruct G.
apply H0.
exfalso.
unfold not in H.
apply H. apply H0.
Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split. apply nf_is_value. apply value_is_nf.
Qed.

Module Temp1.
Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_funny : forall t1 n2,
                value (P t1 (C n2)).

Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
unfold normal_form.
unfold not.
exists (P (C 1) (C 2)).
split.
apply v_funny.
intros.
apply H.
exists (C (1+2)).
apply ST_PlusConstConst.
Qed.
End Temp1.
Module Temp2.
Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_Funny : forall n,
      C n --> P (C n) (C 0) (* <--- NEW *)
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists v, value v /\ 
~normal_form step v.
Proof.
unfold normal_form.
unfold not. 
exists (C 2).
split.
apply v_const.
intros.
apply H.
exists (P (C 2) (C 0)).
apply ST_Funny.
Qed.

End Temp2.

Module Temp3.
Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).
Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2

  where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  exists t, ~value t /\ normal_form step t.
Proof.
unfold normal_form.
unfold not.
exists (P (C 1) (P (C 2) (C 3))).
split.
intros.
inversion H.
intros.
inversion H.
inversion H0.
inversion H4.
Qed.

End Temp3.

Module Temp4.
Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.
Inductive value : tm -> Prop :=
  | v_tru : value tru
  | v_fls : value fls.

Reserved Notation 
" t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3

where " t '-->' t' " := (step t t').

Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
Proof.
intros.
induction t.
- left. apply v_tru.
- left. apply v_fls.
- right. destruct IHt1 as [A | B].
  inversion A. exists t2. 
  apply ST_IfTrue.
  exists t3. apply ST_IfFalse.
  inversion B.
  exists (test x t2 t3).
  apply ST_If. apply H.
Qed.
 
Theorem step_deterministic :
  deterministic step.
Proof. 
unfold deterministic.
intros. generalize dependent y2.
induction H.
- intros y2 tt. inversion tt.
reflexivity. inversion H3.
- intros. inversion H0.
reflexivity. inversion H4. 
- intros. inversion H0. 
rewrite <- H2 in H.
inversion H.
rewrite <- H2 in H.
inversion H.
rewrite IHstep with t1'0.
reflexivity.
apply H5.
Qed.

Module Temp5.

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3
  | ST_Same : forall t1 t2,
      test t1 t2 t2 --> t2

  where " t '-->' t' " := (step t t').

(* Theorem step_deterministic :
  deterministic step.
Proof.
unfold deterministic.
intros.
generalize dependent y2.
induction H. 
- intros. inversion H0.
  reflexivity. inversion H4.
  reflexivity.
- intros. inversion H0.
  reflexivity. inversion H4.
  reflexivity.
- intros. inversion H0.
  + rewrite <- H2 in H. inversion H. 
  + rewrite <- H2 in H. inversion H.
  +  rewrite IHstep with t1'0. reflexivity.
  apply H5.
  + assert (G : test t1 t2 t3 --> test t1' t2 t3).
  { apply ST_If. apply H. }
     
    inversion G. rewrite H4 in H5.
    rewrite H1 in H5.
    rewrite <- H5.
    reflexivity. 
    rewrite H4 in H5.
    rewrite H1 in H5.
    rewrite <- H5.
    reflexivity.
    
     
   rewrite H4 in two.
   rewrite H1 in two.
   
  
 subst. 
clear H. clear IHstep.
    rewrite <- H4 in H1.
  rewrite <- H1 in H0.
  rewrite <- H4 in H0.
  
  rewrite <- H3 in H0.
  rewrite <- H2 in H0.
  apply ST_Same in H0. 
  
 *)
   

End Temp5.
End Temp4.

Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation " t '==>*' t' " := 
(multi step t t') (at level 40).

Theorem multi_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> (multi R) x y.
Proof.
intros.
apply multi_step with y.
apply H.
apply multi_refl.
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y ->
      multi R y z ->
      multi R x z.
Proof.
intros.
induction H.
apply H0.
apply multi_step with y.
apply H.
apply IHmulti.
apply H0.
Qed.

Lemma test_multistep_1:
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
   ==>*
      C ((0 + 3) + (2 + 4)).
Proof.  
apply multi_step with
            (P (C (0 + 3))
               (P (C 2) (C 4))).
apply ST_Plus1. 
apply ST_PlusConstConst.
apply multi_step with 
(P (C (0 + 3)) (C (2 + 4))).
apply ST_Plus2.
apply v_const.
apply ST_PlusConstConst.
apply multi_R.
apply ST_PlusConstConst.
Qed.

Definition step_normal_form := normal_form step.
Definition normal_form_of (t t' : tm) :=
  (t ==>* t' /\ step_normal_form t').

Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
unfold deterministic.
unfold normal_form_of.
intros x y1 y2 H1 H2.
inversion H1 as [P11 P12]; clear H1.
inversion H2 as [P21 P22]; clear H2.
generalize dependent y2.
induction P11; intros.
Admitted.

Definition normalizing {X : Type} 
(R : relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'.

Lemma multistep_congr_1 : forall t1 t1' t2,
     t1 ==>* t1' ->
     P t1 t2 ==>* P t1' t2.
Proof.
intros.
induction H.
apply multi_refl.
apply multi_trans with (P y t2).
apply multi_R.
apply ST_Plus1.
apply H.
apply IHmulti.
Qed.

Lemma multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 ==>* t2' ->
     P t1 t2 ==>* P t1 t2'.
Proof.
intros.
induction H0.
apply multi_refl.
apply multi_trans with (P t1 y).
apply multi_R.
apply ST_Plus2.
apply H.
apply H0.
apply IHmulti.
Qed.

Theorem step_normalizing :
  normalizing step.
Proof.
unfold normalizing.
intros.
induction t.
- exists (C n).
split. apply multi_refl.
apply nf_same_as_value.
apply v_const.
- destruct IHt1 as 
[t1' [Hsteps1 Hnormal1]].
destruct IHt2 as 
[t2' [Hsteps2 Hnormal2]].
rewrite nf_same_as_value in Hnormal1.
rewrite nf_same_as_value in Hnormal2.
inversion Hnormal1.
inversion Hnormal2.
exists (C(n+n0)).
split.
apply multi_trans with (P t1' t2).
apply multistep_congr_1.
apply Hsteps1.
apply multi_trans with (P t1' t2').
apply multistep_congr_2.
apply Hnormal1.
apply Hsteps2.
rewrite <- H.
rewrite <- H0.
apply multi_R.
apply ST_PlusConstConst.
apply nf_same_as_value.
apply v_const.
Qed.

Theorem eval__multistep : forall t n,
  t ==> n -> t ==>* C n.
Proof.
intros t n.
intros.
induction H.
- apply multi_refl.
- apply multi_trans with (P (C n1) t2).
apply multistep_congr_1.
apply IHeval1.
apply multi_trans with (P (C n1) (C n2)).
apply multistep_congr_2.
apply v_const.
apply IHeval2.
apply multi_R.
apply ST_PlusConstConst.
Qed.

Lemma step__eval : forall t t' n,
     t --> t' ->
     t' ==> n ->
     t ==> n.
(*t ==> n -> t ==>* C n.*)
Proof.
intros t t' n Hs. 
generalize dependent n.
induction Hs.
- intros. inversion H.
  apply E_Plus.
  apply E_Const.
  apply E_Const.
- intros. inversion H.
  apply E_Plus.
  apply IHHs.
  apply H2. apply H4.
- intros. inversion H0.
  apply E_Plus.
  apply H3.
  apply IHHs.
  apply H5.
Qed.

Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, 
t' = C n /\ t ==> n.
Proof. 
intros.
unfold normal_form_of in H.
destruct H as [I SN].
unfold step_normal_form in SN.
rewrite nf_same_as_value in SN.
inversion SN.
exists n.
split. reflexivity.
induction I.
- rewrite <- H.
apply E_Const.
- apply step__eval with y.
apply H0. apply IHI.
apply SN. apply H.
Qed.

(* Fixpoint evalF (t:tm) : nat :=
match t with
| C n => n
| P n1 n2 => evalF n1 + evalF n2
end. *)

(* Inductive eval : tm -> nat-> Prop :=
| E_Const : forall n,
  C n ==> n
| E_Plus : forall t1 t2 n1 n2,
  t1 ==> n1 ->
  t2 ==> n2 ->
  P t1 t2 ==> (n1+n2) *)

Theorem evalF_eval_1 : forall t n,
  t ==> n -> evalF t = n.
Proof.
intros t n E.
induction E.
- simpl. reflexivity.
- rewrite <- IHE1. 
  rewrite <- IHE2.
  simpl. reflexivity.
Qed.

Theorem evalF_eval_2 : forall t n,
  evalF t = n -> t ==> n.
Proof.
intros. induction H. 
induction t. simpl.
  apply E_Const.
  simpl. apply E_Plus. 
  apply IHt1. apply IHt2.
Qed.

Theorem evalF_eval : forall t n,
  evalF t = n <-> t ==> n.
Proof.
intros.
split.
apply evalF_eval_2.
apply evalF_eval_1.
Qed.

Module Combined.
Inductive tm : Type :=
  | C : nat -> tm
  | P : tm -> tm -> tm
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.
Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_tru : value tru
  | v_fls : value fls.
Reserved Notation " t '-->' t' " (at level 40).


Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'
  | ST_IfTrue : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3

  where " t '-->' t' " := (step t t').

Theorem step_deterministic :
  deterministic step. 
Proof.
unfold deterministic.
intros x y1 y2.
intros.
generalize dependent y2.
induction H; intros.
- inversion H0. reflexivity.
  inversion H3. inversion H4.
- inversion H0. rewrite <- H2 in H.
  inversion H. rewrite IHstep with t1'0.
  reflexivity. apply H4.  
  inversion H3. rewrite <- H6 in H.
  inversion H. rewrite <- H6 in H.
  inversion H. rewrite <- H6 in H.
  inversion H.  
- inversion H1. 
  rewrite <- H4 in H0.
  inversion H0.
  rewrite H3.
  inversion H. rewrite <- H6 in H5.
  inversion H5. rewrite <- H6 in H5.
  inversion H5. rewrite <- H6 in H5.
  inversion H5. rewrite IHstep with t2'0.
  reflexivity. apply H6.
-  inversion H0.  reflexivity. 
   inversion H4. 
- inversion H0. reflexivity. 
  inversion H4. 
- inversion H0.
  rewrite <- H2 in H. inversion H.
  rewrite <- H2 in H. inversion H.
  rewrite IHstep with t1'0. 
  reflexivity. apply H5.
Qed. 

Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
Proof.
intros.
induction t.
- left. apply v_const.
- right. destruct IHt1 as [A1|A2].
  inversion A1. destruct IHt2 as [B1|B2].
  inversion B1. exists (C(n+n0)).
  apply ST_PlusConstConst.
(* No strong progress I think.*)
Admitted. 

End Combined.

Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).
Reserved Notation " t '/' st '-->a' t' "
                  (at level 40, st at level 39).
Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Id : forall st i,
      AId i / st -->a ANum (st i)
  | AS_Plus1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (APlus a1 a2) / st -->a (APlus a1' a2)
  | AS_Plus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (APlus v1 a2) / st -->a (APlus v1 a2')
  | AS_Plus : forall st n1 n2,
      APlus (ANum n1) (ANum n2) / st -->a
 ANum (n1 + n2)
  | AS_Minus1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (AMinus a1 a2) / st -->a (AMinus a1' a2)
  | AS_Minus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (AMinus v1 a2) / st -->a (AMinus v1 a2')
  | AS_Minus : forall st n1 n2,
      (AMinus (ANum n1) (ANum n2)) / st -->a (ANum (minus n1 n2))
  | AS_Mult1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (AMult a1 a2) / st -->a (AMult a1' a2)
  | AS_Mult2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (AMult v1 a2) / st -->a (AMult v1 a2')
  | AS_Mult : forall st n1 n2,
      (AMult (ANum n1) (ANum n2)) / st -->a (ANum (mult n1 n2))

    where " t '/' st '-->a' t' " := (astep st t t').

Reserved Notation " t '/' st '-->b' t' "
                  (at level 40, st at level 39).
Inductive bstep : state -> bexp -> bexp -> Prop :=
| BS_Eq1 : forall st a1 a1' a2,
    a1 / st -->a a1' ->
    (BEq a1 a2) / st -->b (BEq a1' a2)
| BS_Eq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    (BEq v1 a2) / st -->b (BEq v1 a2')
| BS_Eq : forall st n1 n2,
    (BEq (ANum n1) (ANum n2)) / st -->b
    (if (n1 =? n2) then BTrue else BFalse)
| BS_LtEq1 : forall st a1 a1' a2,
    a1 / st -->a a1' ->
    (BLe a1 a2) / st -->b (BLe a1' a2)
| BS_LtEq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    (BLe v1 a2) / st -->b (BLe v1 a2')
| BS_LtEq : forall st n1 n2,
    (BLe (ANum n1) (ANum n2)) / st -->b
             (if (n1 <=? n2) then BTrue else BFalse)
| BS_NotStep : forall st b1 b1',
    b1 / st -->b b1' ->
    (BNot b1) / st -->b (BNot b1')
| BS_NotTrue : forall st,
    (BNot BTrue) / st -->b BFalse
| BS_NotFalse : forall st,
    (BNot BFalse) / st -->b BTrue
| BS_AndTrueStep : forall st b2 b2',
    b2 / st -->b b2' ->
    (BAnd BTrue b2) / st -->b (BAnd BTrue b2')
| BS_AndStep : forall st b1 b1' b2,
    b1 / st -->b b1' ->
    (BAnd b1 b2) / st -->b (BAnd b1' b2)
| BS_AndTrueTrue : forall st,
    (BAnd BTrue BTrue) / st -->b BTrue
| BS_AndTrueFalse : forall st,
    (BAnd BTrue BFalse) / st -->b BFalse
| BS_AndFalse : forall st b2,
    (BAnd BFalse b2) / st -->b BFalse

where " t '/' st '-->b' t' " := (bstep st t t').

Definition empty_st := fun (_ : string) => 0.

Definition extend_st a x (st : state) :=
  (fun (a' : string) => if beq_string a a' then x
                     else st a).

Notation "a '!->' x" := (extend_st a x empty_st) (at level 100).

Notation "a '!->' x ';' s" := (extend_st a x s)
                              (at level 100, x at next level, right associativity).

Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).
Open Scope aexp_scope.
Open Scope bexp_scope.
Open Scope com_scope.
Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st i a a',
      a / st -->a a' ->
      (i ::= a) / st --> (i ::= a') / st
  | CS_Ass : forall st i n,
      (i ::= (ANum n)) / st --> SKIP / (i!->n;st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      (c1 ;; c2) / st --> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st --> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b / st -->b b' ->
      IFB b THEN c1 ELSE c2 FI / st
      -->
      (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_IfTrue : forall st c1 c2,
      IFB BTrue THEN c1 ELSE c2 FI / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      IFB BFalse THEN c1 ELSE c2 FI / st --> c2 / st
  | CS_While : forall st b c1,
      WHILE b DO c1 END / st
      -->
      (IFB b THEN c1;; WHILE b DO c1 END ELSE SKIP FI) / st
  where " t '/' st '-->' t' '/' st' " 
:= (cstep (t,st) (t',st')).

Close Scope aexp_scope.
Close Scope bexp_scope.
Close Scope com_scope.

Module CImp.
Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CPar : com -> com -> com. (* <--- NEW *)
Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (CIf b c1 c2) (at level 80, right associativity).
Notation "'PAR' c1 'WITH' c2 'END'" :=
  (CPar c1 c2) (at level 80, right associativity).

Inductive cstep : (com * state) -> (com * state) -> Prop :=
    (* Old part *)
  | CS_AssStep : forall st i a a',
      a / st -->a a' ->
      (i ::= a) / st --> (i ::= a') / st
  | CS_Ass : forall st i n,
      (i ::= (ANum n)) / st --> SKIP / (i!->n;st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      (c1 ;; c2) / st --> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st --> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b /st -->b b' ->
          (TEST b THEN c1 ELSE c2 FI) / st
      --> (TEST b' THEN c1 ELSE c2 FI) / st
  | CS_IfTrue : forall st c1 c2,
      (TEST BTrue THEN c1 ELSE c2 FI) / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      (TEST BFalse THEN c1 ELSE c2 FI) / st --> c2 / st
  | CS_While : forall st b c1,
          (WHILE b DO c1 END) / st
      --> (TEST b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI) / st
    (* New part: *)
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st --> c1' / st' ->
      (PAR c1 WITH c2 END) / st --> (PAR c1' WITH c2 END) / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st --> c2' / st' ->
      (PAR c1 WITH c2 END) / st --> (PAR c1 WITH c2' END) / st'
  | CS_ParDone : forall st,
      (PAR SKIP WITH SKIP END) / st --> SKIP / st
  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Definition cmultistep := multi cstep.
Notation " t '/' st '-->*' t' '/' st' " :=
   (multi cstep (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).

Definition par_loop : com :=
  PAR
    Y ::= 1
  WITH
    WHILE Y = 0 DO
      X ::= X + 1
    END
  END.



Example par_loop_example_0:
  exists st',
       par_loop / empty_st -->* SKIP / st'
    /\ st' X = 0.
Proof.
eapply ex_intro.
split.
- unfold par_loop.
eapply multi_step.
apply CS_Par1.
apply CS_Ass.
eapply multi_step.
apply CS_Par2.
apply CS_While.
eapply multi_step.
apply CS_Par2.
apply CS_IfStep.
apply BS_Eq1.
apply AS_Id.
eapply multi_step.
apply CS_Par2.
apply CS_IfStep.
apply BS_Eq.
simpl. 
eapply multi_step.
apply CS_Par2.
apply CS_IfFalse.
eapply multi_step.
apply CS_ParDone.
eapply multi_refl.  
- reflexivity.
Qed.

Example par_loop_example_2:
  exists st',
       par_loop / empty_st -->* SKIP / st'
    /\ st' X = 2.
(* Proof.
  eapply ex_intro. split.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.
   
   *) 
Proof.
eapply ex_intro.
split.
- unfold par_loop.
eapply multi_step.
apply CS_Par2.
apply CS_While.
eapply multi_step.
apply CS_Par2.
apply CS_IfStep.
apply BS_Eq1.
apply AS_Id.
eapply multi_step.
apply CS_Par2.
apply CS_IfStep.
apply BS_Eq. simpl.
eapply multi_step. 
apply CS_Par2.
apply CS_IfTrue.
eapply multi_step.
apply CS_Par2.
apply CS_SeqStep.
apply CS_AssStep.
apply AS_Plus1.
apply AS_Id.
eapply multi_step.

apply CS_Par2.
apply CS_SeqStep.
apply CS_AssStep.
apply AS_Plus.
eapply multi_step.
apply CS_Par2.
apply CS_SeqStep.
Admitted.

Lemma par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st -->* 
par_loop / (X !-> S n ; st).
Proof.
intros. inversion H as [H1 H2].  subst.
eapply multi_step. apply CS_Par2.
apply CS_While. eapply multi_step.
apply CS_Par2. apply CS_IfStep.
apply BS_Eq1.  apply AS_Id.
eapply multi_step. apply CS_Par2.
apply CS_IfStep. apply BS_Eq.
rewrite H2. simpl. eapply multi_step. 
apply CS_Par2. apply CS_IfTrue.
eapply multi_step. apply CS_Par2.
apply CS_SeqStep. apply CS_AssStep.
apply AS_Plus1. apply AS_Id.
eapply multi_step. apply CS_Par2. 
apply CS_SeqStep. apply CS_AssStep. 
apply AS_Plus. eapply multi_step. 
apply CS_Par2. apply CS_SeqStep.
apply CS_Ass. eapply multi_step. 
apply CS_Par2. apply CS_SeqFinish.
rewrite plus_comm. simpl.
fold par_loop. apply multi_refl.
Qed.

Lemma st_0: forall n m  X Y st,
 st Y = 0 /\ st X = n 
-> (X!->m; st) Y = 0.
Proof.
Admitted.

Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st -->* par_loop / st' /\ 
    st' X = n /\ st' Y = 0.
Proof.
induction n.
- intros. exists st.
split. apply multi_refl.
apply H.
-intros. 
assert(exists st' : state,
        par_loop / st -->* par_loop / st' 
/\ st' X = n /\ st' Y = 0).
apply IHn.
apply H. inversion H0.
exists (X !-> S n ; x).
split; inversion H1 as [H2 H3].
eapply multi_trans.
apply H2.
eapply par_body_n__Sn.
apply H3.
split. reflexivity.
inversion H3. 
Admitted.

(* 
Definition par_loop : com :=
  PAR
    Y ::= 1
  WITH
    WHILE Y = 0 DO
      X ::= X + 1
    END
  END. *)

Theorem par_loop_any_X:
  forall n, exists st',
    par_loop / empty_st -->* SKIP / st'
    /\ st' X = n.
Proof.
induction n.
- eapply ex_intro.
  unfold par_loop. split.
  eapply multi_step.
apply CS_Par1.
apply CS_Ass.
eapply multi_step.
apply CS_Par2. apply CS_While. 
eapply multi_step. apply CS_Par2.
apply CS_IfStep.
apply BS_Eq1. apply AS_Id.
eapply multi_step. apply CS_Par2.
apply CS_IfStep. apply BS_Eq.
eapply multi_step.
simpl. apply CS_Par2. apply CS_IfFalse.
eapply multi_step.
apply CS_ParDone.
apply multi_refl.
reflexivity.
- eapply ex_intro. unfold par_loop.
 split.

Admitted.
End CImp.

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.

Definition stack := list nat.
Definition prog := list sinstr.
Inductive stack_step : state -> prog * stack -> prog * stack -> Prop :=
  | SS_Push : forall st stk n p',
    stack_step st (SPush n :: p', stk) (p', n :: stk)
  | SS_Load : forall st stk i p',
    stack_step st (SLoad i :: p', stk) (p', st i :: stk)
  | SS_Plus : forall st stk n m p',
    stack_step st (SPlus :: p', n::m::stk) (p', (m+n)::stk)
  | SS_Minus : forall st stk n m p',
    stack_step st (SMinus :: p', n::m::stk) (p', (m-n)::stk)
  | SS_Mult : forall st stk n m p',
    stack_step st (SMult :: p', n::m::stk) (p', (m*n)::stk).

Theorem stack_step_deterministic : forall st,
  deterministic (stack_step st).
Proof.
intros.
unfold deterministic.
intros.
generalize dependent y2.
induction H; intros.
- inversion H0. reflexivity.
- inversion H0. reflexivity.
- inversion H0. reflexivity.
- inversion H0. reflexivity.
- inversion H0. reflexivity.
Qed.

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [(SPush n)]
  | AId x => [(SLoad x)]
  | APlus a1 a2 => (s_compile a1)++(s_compile a2)++[SPlus]
  | AMinus a1 a2 => (s_compile a1)++(s_compile a2)++[SMinus]
  | AMult a1 a2 => (s_compile a1)++(s_compile a2)++[SMult]
  end.


Definition stack_multistep st := 
multi (stack_step st).








 


















