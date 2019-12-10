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

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P a1 a2 => evalF a1 + evalF a2
  end.

Reserved Notation " t '\\' n " 
(at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n \\ n
  | E_Plus : forall t1 t2 n1 n2,
      t1 \\ n1 ->
      t2 \\ n2 ->
      P t1 t2 \\ (n1 + n2)

  where " t '\\' n " := (eval t n).

Module SimpleArith1.

Reserved Notation " t '==>' t' " 
(at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) ==> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 ==> t1' ->
      P t1 t2 ==> P t1' t2
  | ST_Plus2 : forall n1 t2 t2',
      t2 ==> t2' ->
      P (C n1) t2 ==> P (C n1) t2'

  where " t '==>' t' " := (step t t').

Example test_step_1 :
      P(P (C 0)(C 3))(P (C 2) (C 4))
      ==>P(C (0 + 3))(P (C 2) (C 4)).
Proof.
apply ST_Plus1.
apply ST_PlusConstConst.
Qed.

Example test_step_2 :
P (C 0) (P (C 2) (P (C 0) (C 3)))
==> P (C 0) (P (C 2) (C (0 + 3))).
Proof.
apply ST_Plus2.
simpl.
apply ST_Plus2. 
apply ST_PlusConstConst.
Qed.
End SimpleArith1.

Definition deterministic {X: Type} 
(R: relation X) :=
  forall x y1 y2 : X, R x y1 
-> R x y2 -> y1 = y2.

Module SimpleArith2.
Import SimpleArith1.
Theorem step_deterministic:
deterministic step.
Proof.
unfold deterministic.
intros x y1 y2 Hy1 Hy2.
generalize dependent y2.
induction Hy1. intros y2 Hy2.
Admitted.

End SimpleArith2.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ => 
  match type of T with Prop =>
    solve [ 
      inversion H; 
      match n with S (S (?n')) => 
subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

Module SimpleArith3.
Import SimpleArith1.
Theorem step_deterministic_alt: 
deterministic step.
Proof.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
    inversion Hy2; subst; 
try solve_by_invert.
  - (* ST_PlusConstConst *) reflexivity.
  - (* ST_Plus1 *)
    apply IHHy1 in H2. 
rewrite H2. reflexivity.
  - (* ST_Plus2 *)
    apply IHHy1 in H2. 
rewrite H2. reflexivity.
Qed.
End SimpleArith3.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

Reserved Notation " t '==>' t' " 
(at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
          P (C n1) (C n2)
      ==> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 ==> t1' ->
        P t1 t2 ==> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 -> (* <----- n.b. *)
        t2 ==> t2' ->
        P v1 t2 ==> P v1 t2'

  where " t '==>' t' " := (step t t').

Theorem step_deterministic :
  deterministic step.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem strong_progress : forall t,
  value t \/ (exists t', t ==> t').
Proof.
intros.
induction t.
- left. apply v_const.
- right. inversion IHt1.
  + inversion IHt2. inversion H0.
Admitted.

Definition normal_form {X:Type}
 (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
unfold normal_form.
intros.
unfold not.
inversion H.
intros c.
inversion c.
inversion H1.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof.
unfold normal_form.
intros t H.
assert ( G: value t 
\/ exists t', t==>t').
{ apply strong_progress. }
inversion G.
+ assumption.
+ exfalso. apply H. assumption.
Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
split.
apply nf_is_value.
apply value_is_nf.
Qed.

(** some good exercises are left **)

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
assumption.
apply multi_refl.
Qed.

Theorem multi_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      multi R x y ->
      multi R y z ->
      multi R x z.
Proof.
intros X R x y z H1 H2.
induction H1.
assumption. 
apply multi_step with y.
assumption. apply IHmulti. apply H2.
Qed.

Lemma test_multistep_1:
P(P (C 0) (C 3))(P (C 2) (C 4))==>*C ((0 + 3) + (2 + 4)).
Proof.
apply multi_step with (P (C (0 + 3))
               (P (C 2) (C 4))).
apply ST_Plus1.
apply ST_PlusConstConst.
apply multi_step with (P (C (0 + 3))
                (C (2 + 4))).
apply ST_Plus2.
apply v_const.
apply ST_PlusConstConst.
apply multi_step with (C (0 + 3 + (2 + 4))).
apply ST_PlusConstConst.
apply multi_refl.
Qed.

Lemma test_multistep_1':
P(P (C 0) (C 3))(P (C 2) (C 4))
==>* C ((0 + 3) + (2 + 4)).
Proof.
eapply multi_step.
apply ST_Plus1. apply ST_PlusConstConst.
  eapply multi_step. apply ST_Plus2. apply v_const.
  apply ST_PlusConstConst.
  eapply multi_step. apply ST_PlusConstConst.
  apply multi_refl. Qed.

Lemma test_multistep_2:
  C 3 ==>* C 3.
Proof.
apply multi_refl.
Qed.

Lemma test_multistep_3:
      P (C 0) (C 3)
   ==>*
      P (C 0) (C 3).
Proof.
apply multi_refl.
Qed.

Lemma test_multistep_4:
P(C 0)(P(C 2) (P (C 0) (C 3)))
  ==>*P(C 0)(C (2 + (0 + 3))).
Proof.
apply multi_step with (P(C 0)(P(C 2)(C (0 + 3)))).
apply ST_Plus2.
apply v_const.
apply ST_Plus2.
apply v_const.
apply ST_PlusConstConst.
apply multi_step with (P(C 0)(C (2 + (0 + 3)))).
apply ST_Plus2.
apply v_const.
apply ST_PlusConstConst.
apply multi_refl.
Qed.

Definition step_normal_form := normal_form step.
Definition normal_form_of (t t' : tm) :=
  (t ==>* t' /\ step_normal_form t').

Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
unfold deterministic.
unfold normal_form_of.
intros.
inversion H as [P1 P2]. clear H.
- inversion H0 as [P3 P4]. clear H0.
generalize dependent y2.
Admitted.

Definition normalizing {X:Type} (R:relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'.

Lemma multistep_congr_1 : forall t1 t1' t2,
     t1 ==>* t1' ->
     P t1 t2 ==>* P t1' t2.
Proof.
intros. induction H .
apply multi_refl.
apply multi_step with (P y t2).
apply ST_Plus1. apply H.
assumption.
Qed.

Lemma multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 ==>* t2' ->
     P t1 t2 ==>* P t1 t2'.
Proof.
intros.
induction H0.
- apply multi_refl.
- apply multi_step with (P t1 y).
apply ST_Plus2.
apply H. apply H0. apply IHmulti.
Qed.

Theorem step_normalizing :
  normalizing step.
Proof.
unfold normalizing.
induction t.
- exists (C n).
split. apply multi_refl.  
apply nf_same_as_value. apply v_const.
- destruct IHt1 as [t1' [H11 H12]].
  destruct IHt2 as [t2' [H21 H22]].
rewrite nf_same_as_value in H12.
rewrite nf_same_as_value in H22.
inversion H12 as [n1 H]. 
inversion H22 as [n2 H'].
Admitted.

Theorem eval__multistep : forall t n,
  t \\ n -> t ==>* C n.
Proof.
intros.
  induction H. constructor.
  eapply multi_trans.
  assert(P t1 t2 ==>* P (C n1) t2).
    apply multistep_congr_1; assumption.
    apply H1.
  eapply multi_trans.
    apply multistep_congr_2. constructor.
    apply IHeval2.
  econstructor; constructor.
  Qed.

Definition manual_grade_for_eval__multistep_inf : option (prod nat string) := None.

Lemma step__eval : forall t t' n,
     t ==> t' ->
     t' \\ n ->
     t \\ n.
Proof.
intros t t' n Hs. generalize dependent n.
induction Hs.
- intros. inversion H; subst. 
constructor. constructor. constructor.
- intros. inversion H; subst. 
constructor. apply IHHs. assumption.
assumption.
- intros. inversion H0; subst.
constructor. assumption. apply IHHs.
assumption.
Qed.

Theorem multistep__eval : forall t t',
  normal_form_of t t' -> 
  exists n, t' = C n /\ t \\ n.
Proof.
intros. unfold normal_form_of in H.
inversion H.
induction H0.
- assert (value x).
 + apply nf_is_value. apply H1.
 + inversion H0.  exists n. split.
reflexivity. constructor.
- assert(exists n : nat, z = C n /\ y \\ n).
apply IHmulti. split.
assumption. assumption. assumption.
inversion H3 as [n [H6 H7]].
exists n. split. assumption.
eapply step__eval. apply H0. 
apply H7.
Qed.

Theorem evalF_eval : forall t n,
  evalF t = n <-> t \\ n.
Proof.
intros.
split. generalize dependent n.
-  induction t.
 + intros. subst. 
constructor.
 + intros. simpl in H. rewrite <-H.
constructor.
 apply IHt1. reflexivity.
apply IHt2. reflexivity.
- intros. induction H.
constructor. simpl.
subst. reflexivity.
Qed.

Module Combined.
Inductive tm : Type :=
  | C : nat -> tm
  | P : tm -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm.
Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_true : value ttrue
  | v_false : value tfalse.
Reserved Notation " t '==>' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) ==> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 ==> t1' ->
      P t1 t2 ==> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 ==> t2' ->
      P v1 t2 ==> P v1 t2'
  | ST_IfTrue : forall t1 t2,
      tif ttrue t1 t2 ==> t1
  | ST_IfFalse : forall t1 t2,
      tif tfalse t1 t2 ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      tif t1 t2 t3 ==> tif t1' t2 t3

  where " t '==>' t' " := (step t t'). 

End Combined.
Definition manual_grade_for_combined_properties : option (prod nat string) := None.

Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).

Reserved Notation " t '/' st '==>a' t' "
                  (at level 40, st at level 39).
Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Id : forall st i,
      AId i / st ==>a ANum (st i)
  | AS_Plus : forall st n1 n2,
      APlus (ANum n1) (ANum n2) / st ==>a ANum (n1 + n2)
  | AS_Plus1 : forall st a1 a1' a2,
      a1 / st ==>a a1' ->
      (APlus a1 a2) / st ==>a (APlus a1' a2)
  | AS_Plus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ==>a a2' ->
      (APlus v1 a2) / st ==>a (APlus v1 a2')
  | AS_Minus : forall st n1 n2,
      (AMinus (ANum n1) (ANum n2)) / st ==>a (ANum (minus n1 n2))
  | AS_Minus1 : forall st a1 a1' a2,
      a1 / st ==>a a1' ->
      (AMinus a1 a2) / st ==>a (AMinus a1' a2)
  | AS_Minus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ==>a a2' ->
      (AMinus v1 a2) / st ==>a (AMinus v1 a2')
  | AS_Mult : forall st n1 n2,
      (AMult (ANum n1) (ANum n2)) / st ==>a (ANum (mult n1 n2))
  | AS_Mult1 : forall st a1 a1' a2,
      a1 / st ==>a a1' ->
      (AMult a1 a2) / st ==>a (AMult a1' a2)
  | AS_Mult2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ==>a a2' ->
      (AMult v1 a2) / st ==>a (AMult v1 a2')

    where " t '/' st '==>a' t' " := (astep st t t').
Reserved Notation " t '/' st '==>b' t' "
                  (at level 40, st at level 39).
Inductive bstep : state -> bexp -> bexp -> Prop :=
| BS_Eq : forall st n1 n2,
    (BEq (ANum n1) (ANum n2)) / st ==>b
    (if (beq_nat n1 n2) then BTrue else BFalse)
| BS_Eq1 : forall st a1 a1' a2,
    a1 / st ==>a a1' ->
    (BEq a1 a2) / st ==>b (BEq a1' a2)
| BS_Eq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st ==>a a2' ->
    (BEq v1 a2) / st ==>b (BEq v1 a2')
| BS_LtEq : forall st n1 n2,
    (BLe (ANum n1) (ANum n2)) / st ==>b
             (if (leb n1 n2) then BTrue else BFalse)
| BS_LtEq1 : forall st a1 a1' a2,
    a1 / st ==>a a1' ->
    (BLe a1 a2) / st ==>b (BLe a1' a2)
| BS_LtEq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st ==>a a2' ->
    (BLe v1 a2) / st ==>b (BLe v1 a2')
| BS_NotTrue : forall st,
    (BNot BTrue) / st ==>b BFalse
| BS_NotFalse : forall st,
    (BNot BFalse) / st ==>b BTrue
| BS_NotStep : forall st b1 b1',
    b1 / st ==>b b1' ->
    (BNot b1) / st ==>b (BNot b1')
| BS_AndTrueTrue : forall st,
    (BAnd BTrue BTrue) / st ==>b BTrue
| BS_AndTrueFalse : forall st,
    (BAnd BTrue BFalse) / st ==>b BFalse
| BS_AndFalse : forall st b2,
    (BAnd BFalse b2) / st ==>b BFalse
| BS_AndTrueStep : forall st b2 b2',
    b2 / st ==>b b2' ->
    (BAnd BTrue b2) / st ==>b (BAnd BTrue b2')
| BS_AndStep : forall st b1 b1' b2,
    b1 / st ==>b b1' ->
    (BAnd b1 b2) / st ==>b (BAnd b1' b2)

where " t '/' st '==>b' t' " := (bstep st t t').

Reserved Notation " t '/' st '==>' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).
Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st i a a',
      a / st ==>a a' ->
      (i ::= a) / st ==> (i ::= a') / st
  | CS_Ass : forall st i n,
      (i ::= (ANum n)) / st ==> SKIP / (st & { i --> n })
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st ==> c1' / st' ->
      (c1 ;; c2) / st ==> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st ==> c2 / st
  | CS_IfTrue : forall st c1 c2,
      IFB BTrue THEN c1 ELSE c2 FI / st ==> c1 / st
  | CS_IfFalse : forall st c1 c2,
      IFB BFalse THEN c1 ELSE c2 FI / st ==> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b / st ==>b b' ->
          IFB b THEN c1 ELSE c2 FI / st 
      ==> (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_While : forall st b c1,
          (WHILE b DO c1 END) / st
      ==> (IFB b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI) / st

  where " t '/' st '==>' t' '/' st' " := (cstep (t,st) (t',st')).

Module CImp.
Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  (* New: *)
  | CPar : com -> com -> com.
Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (CIf b c1 c2) (at level 80, right associativity).
Notation "'PAR' c1 'WITH' c2 'END'" :=
  (CPar c1 c2) (at level 80, right associativity).
Inductive cstep : (com * state) -> (com * state) -> Prop :=
    (* Old part *)
  | CS_AssStep : forall st i a a',
      a / st ==>a a' ->
      (i ::= a) / st ==> (i ::= a') / st
  | CS_Ass : forall st i n,
      (i ::= (ANum n)) / st ==> SKIP / st & { i --> n }
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st ==> c1' / st' ->
      (c1 ;; c2) / st ==> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st ==> c2 / st
  | CS_IfTrue : forall st c1 c2,
      (IFB BTrue THEN c1 ELSE c2 FI) / st ==> c1 / st
  | CS_IfFalse : forall st c1 c2,
      (IFB BFalse THEN c1 ELSE c2 FI) / st ==> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b /st ==>b b' ->
          (IFB b THEN c1 ELSE c2 FI) / st 
      ==> (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_While : forall st b c1,
          (WHILE b DO c1 END) / st 
      ==> (IFB b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI) / st
    (* New part: *)
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st ==> c1' / st' ->
      (PAR c1 WITH c2 END) / st ==> (PAR c1' WITH c2 END) / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st ==> c2' / st' ->
      (PAR c1 WITH c2 END) / st ==> (PAR c1 WITH c2' END) / st'
  | CS_ParDone : forall st,
      (PAR SKIP WITH SKIP END) / st ==> SKIP / st
  where " t '/' st '==>' t' '/' st' " := (cstep (t,st) (t',st')).
Definition cmultistep := multi cstep.
Notation " t '/' st '==>*' t' '/' st' " :=
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
       par_loop / { --> 0 } ==>* SKIP / st'
    /\ st' X = 0.
Proof.
eapply ex_intro. split.
eapply multi_step. apply CS_Par1.
apply CS_Ass. eapply multi_step.
apply CS_Par2. apply CS_While.
eapply multi_step. eapply CS_Par2.
apply CS_IfStep. apply BS_Eq1.
apply AS_Id. eapply multi_step.
apply CS_Par2. apply CS_IfStep.
apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity. Qed.

Example par_loop_example_2:
  exists st',
       par_loop / { --> 0 } ==>* SKIP / st'
    /\ st' X = 2.
Proof.
Admitted.

Theorem par_loop_any_X:
  forall n, exists st',
    par_loop / { --> 0 } ==>* SKIP / st'
    /\ st' X = n.
Proof.
Admitted.

End CImp.




















































