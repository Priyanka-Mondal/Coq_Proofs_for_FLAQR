Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Require Import maps.
Require Import imp.

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st:state),
    aeval st a1 = aeval st a2.
Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st:state),
    beval st b1 = beval st b2.

Theorem aequiv_example:
  aequiv (X - X) 0.
Proof.
  intros st. simpl. omega.
Qed.

Theorem bequiv_example:
  bequiv (X - X = 0) true.
Proof.
intros st. unfold beval. rewrite aequiv_example. reflexivity.
Qed.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st \\ st') <-> (c2 / st \\ st').

Theorem skip_left: forall c,
  cequiv
     (SKIP;; c)
     c.
Proof.
intros c st st'. split; intros H.
- inversion H; subst. inversion H2; subst. apply H5.
- apply E_Seq with st. apply E_Skip. apply H.
Qed.

Theorem skip_right: forall c,
  cequiv
    (c ;; SKIP)
    c.
Proof.
intros c st st'. unfold iff. split.
-  intros. inversion H; subst. inversion H5; subst. apply H2.
- intros. apply E_Seq with st'. apply H. apply E_Skip.
Qed.

Theorem IFB_true_simple: forall c1 c2,
  cequiv
    (IFB BTrue THEN c1 ELSE c2 FI)
    c1.
Proof.
intros c1 c2. unfold cequiv.
intros st st'. split; intros.
-  inversion H; subst. assumption. inversion H5.
- apply E_IfTrue. simpl. reflexivity. assumption.
Qed.

Theorem IFB_true: forall b c1 c2,
     bequiv b BTrue ->
     cequiv
       (IFB b THEN c1 ELSE c2 FI)
       c1.
Proof.
intros b c1 c2. intros H. 
unfold cequiv. intros st st'.
split.
- intros. inversion H0; subst. 
  + assumption.
  + unfold bequiv in H. simpl in H. rewrite H in H6. 
    inversion H6.
- apply E_IfTrue. unfold bequiv in H. simpl in H. apply H.
Qed.

Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse ->
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c2.
Proof.
intros.
unfold cequiv. intros. split.
- intros. inversion H0; subst. unfold bequiv in H. simpl in H.
rewrite H in H6. inversion H6. assumption.
- intros. apply E_IfFalse. unfold bequiv in H. simpl in H.
 apply H. assumption.
Qed.

Lemma negm : forall b,
 negb b = true -> b = false.
Proof.
Admitted.

Lemma nego : forall b,
 negb b = false -> b = true.
Proof.
Admitted.

Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
intros. unfold cequiv.
intros st st'. split.
- intros. inversion H; subst. 
  + apply E_IfFalse. simpl. rewrite H5. reflexivity. assumption.
  + apply E_IfTrue. simpl. rewrite H5. reflexivity. assumption.
- intros. inversion H; subst. 
  + apply E_IfFalse. simpl in H5. apply negm in H5.
rewrite H5. reflexivity. assumption.
  + apply E_IfTrue. simpl in H5. apply nego in H5. 
rewrite H5. reflexivity. assumption.
Qed.

Theorem WHILE_false : forall b c,
  bequiv b BFalse ->
  cequiv
    (WHILE b DO c END)
    SKIP.
Proof.
intros.
unfold cequiv.
intros. split.
- intros. inversion H0; subst. apply E_Skip.
unfold bequiv in H. simpl in H. rewrite H in H3. inversion H3.
- intros. inversion H0; subst. apply  E_WhileFalse.
unfold bequiv in H. simpl in H. apply H.
Qed.

Lemma WHILE_true_nonterm : forall b c st st',
  bequiv b BTrue ->
  ~( (WHILE b DO c END) / st \\ st' ).
Proof.
  (* WORKED IN CLASS *)
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw eqn:Heqcw.
  induction H;
  (* Most rules don't apply; we rule them out by inversion: *)
  inversion Heqcw; subst; clear Heqcw.
  (* The two interesting cases are the ones for WHILE loops: *)
  - (* E_WhileFalse *) (* contradictory -- b is always true! *)
    unfold bequiv in Hb.
    (* rewrite is able to instantiate the quantifier in st *)
    rewrite Hb in H. inversion H.
  - (* E_WhileTrue *) (* immediate from the IH *)
    apply IHceval2. reflexivity. Qed.

Theorem WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).
Proof.
  intros. split. 
- intros.
  apply WHILE_true_nonterm in H0. inversion H0. try assumption.
- intros. apply WHILE_true_nonterm in H0. inversion H0.  try
assumption. try constructor. 
Qed.

Theorem loop_unrolling: forall b c,
  cequiv
    (WHILE b DO c END)
    (IFB b THEN (c ;; WHILE b DO c END) ELSE SKIP FI).
Proof.
intros. split. 
- intros. inversion H; subst. apply E_IfFalse. 
assumption. apply E_Skip. apply E_IfTrue. apply H2.
apply E_Seq with (st' := st'0). assumption. assumption.
- intros. inversion H; subst. inversion H6; subst.
apply E_WhileTrue with (st' := st'0). assumption.
assumption. assumption. 
inversion H6; subst. apply E_WhileFalse. assumption.
Qed.

Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
intros.
split.
-  intros.
inversion H; subst. inversion H2; subst. 
apply E_Seq with (c2:= c2;; c3) (st':=st'1).
assumption. apply E_Seq with (st' := st'0).
assumption. assumption.
- intros. inversion H; subst. inversion H5; subst.
apply E_Seq with (c1:= c1;; c2) (st' := st'1).
apply E_Seq with (st':= st'0). assumption. 
assumption. assumption. 
Qed.

Theorem identity_assignment : forall (X:string),
  cequiv
    (X ::= X)
    SKIP.
Proof.
intros.
split.
- intros. inversion H; subst. simpl. simpl in H.
replace (st & {X --> st X}) with st.
apply E_Skip. apply functional_extensionality. intros.
rewrite t_update_same. reflexivity.
- intro. replace st' with (st' & { X --> aeval st' X }).
 + inversion H; subst. apply E_Ass. reflexivity.
 + apply functional_extensionality. intros. rewrite t_update_same.
reflexivity.
Qed.

Theorem assign_aequiv : forall (X:string) e,
  aequiv X e ->
  cequiv SKIP (X ::= e).
Proof.
intros.
split; intro.
-  
Admitted.

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof.
intros a st. reflexivity.
Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
aequiv a1 a2 -> aequiv a2 a1.
Proof.
intros. intros st. symmetry. apply H.
Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity. Qed.

Lemma refl_bequiv : forall (b : bexp), bequiv b b.
intros b st. reflexivity. 
Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
unfold bequiv. intros. symmetry in H. rewrite H.
reflexivity.
Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3. 
Proof.
unfold bequiv. intros. rewrite H. symmetry in H0. 
rewrite H0. reflexivity.
Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof.
intros c st. split. intros. assumption. intros. assumption.
Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
intros c1 c2. intros. unfold cequiv in H.
symmetry in H. unfold cequiv. assumption.
Qed.

Lemma iff_trans : forall (P1 P2 P3 : Prop),
  (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
intros. rewrite H. symmetry in H0. rewrite H0.
reflexivity.
Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
intros c1 c2 c3. unfold cequiv. intros. 
apply iff_trans with (c2 / st \\ st').
apply H. apply H0.
Qed.

Theorem CAss_congruence : forall i a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss i a1) (CAss i a1').
Proof.
intros.
split ; intros.
- inversion H0; subst. apply E_Ass.
unfold aequiv in H. rewrite H. reflexivity.
-inversion H0; subst. apply E_Ass. unfold aequiv in H. rewrite H.
reflexivity. Qed.
Lemma PimpP : forall P,
P-> P.
Proof.
Admitted.

Theorem CWhile_congruence : forall b1 b1' c1 c1',
  bequiv b1 b1' -> cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
(** unfold bequiv,cequiv.
  intros b1 b1' c1 c1' Hb1e Hc1e st st'.
  split; intros Hce.
- remember (WHILE b1 DO c1 END) as cwhile
eqn:Heqcwhile.
induction Hce; inversion Heqcwhile; subst.
  + apply E_WhileFalse. rewrite <- Hb1e. apply H.
  +   apply E_WhileTrue with (st' := st'). 
  * rewrite <- Hb1e. apply H.  * apply (Hc1e st st'). apply Hce1.
  * apply IHHce2. reflexivity.
- remember (WHILE b1' DO c1' END) as c'while
      eqn:Heqc'while.
induction Hce; inversion Heqc'while; subst.
  + (* E_WhileFalse *)
      apply E_WhileFalse. rewrite -> Hb1e. apply H.
    + (* E_WhileTrue *)
      apply E_WhileTrue with (st' := st').
      * (* show loop runs *) rewrite -> Hb1e. apply H.
      * (* body execution *)
        apply (Hc1e st st'). apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity.
Qed.**)
Admitted.

Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof.
intros.
unfold cequiv in H.
unfold cequiv in H0.
unfold cequiv. split.
- intros. inversion H1; subst.
apply E_Seq with st'0. apply H. apply H4. 
apply H0. apply H7.
- intros. inversion H1; subst. 
apply E_Seq with st'0. apply H. apply H4.
apply H0. apply H7.
Qed.

Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI)
         (IFB b' THEN c1' ELSE c2' FI).
Proof.
 unfold cequiv. unfold bequiv. intros. split; intros.
inversion H2; subst. 
- apply E_IfTrue. rewrite <- H.
apply H8. apply H0. apply H9. 
- apply E_IfFalse. rewrite <- H. apply H8.
apply H1. apply H9. 
- inversion H2; subst. 
  + apply E_IfTrue. rewrite H.
apply H8. apply H0. apply H9.
  + apply E_IfFalse. rewrite H.
apply H8. apply H1. apply H9.
Qed.

Example congruence_example:
  cequiv
    (* Program 1: *)
    (X ::= 0;;
     IFB X = 0
     THEN
       Y ::= 0
     ELSE
       Y ::= 42
     FI)
    (* Program 2: *)
    (X ::= 0;;
     IFB X = 0
     THEN
       Y ::= X - X (* <--- changed here *)
     ELSE
       Y ::= 42
     FI).
Proof.
apply CSeq_congruence.
- apply refl_cequiv.
- apply CIf_congruence.
  + apply refl_bequiv.
  + apply CAss_congruence. unfold aequiv. simpl.
symmetry. apply minus_diag.
  + apply refl_cequiv.
Qed.

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
 forall (a : aexp),
    aequiv a (atrans a).
Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
 forall (b : bexp),
    bequiv b (btrans b).
Definition ctrans_sound (ctrans : com -> com) : Prop :=
 forall (c : com),
    cequiv c (ctrans c).

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId i => AId i
  | APlus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => APlus a1' a2'
    end
  | AMinus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => AMinus a1' a2'
    end
  | AMult a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => AMult a1' a2'
    end
  end.
(* needed for parsing the examples below *)
Local Open Scope aexp_scope.
Local Open Scope bexp_scope.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if beq_nat n1 n2 then BTrue else BFalse
      | (a1', a2') =>
          BEq a1' a2'
      end
  | BLe a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if leb n1 n2 then BTrue else BFalse
      | (a1', a2') =>
          BLe a1' a2'
      end
  | BNot b1 =>
      match (fold_constants_bexp b1) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b1' => BNot b1'
      end
  | BAnd b1 b2 =>
      match (fold_constants_bexp b1, fold_constants_bexp b2) with
      | (BTrue, BTrue) => BTrue
      | (BTrue, BFalse) => BFalse
      | (BFalse, BTrue) => BFalse
      | (BFalse, BFalse) => BFalse
      | (b1', b2') => BAnd b1' b2'
      end
  end.

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP =>
      SKIP
  | i ::= a =>
      CAss i (fold_constants_aexp a)
  | c1 ;; c2 =>
      (fold_constants_com c1) ;; (fold_constants_com c2)
  | IFB b THEN c1 ELSE c2 FI =>
      match fold_constants_bexp b with
      | BTrue => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => IFB b' THEN fold_constants_com c1
                     ELSE fold_constants_com c2 FI
      end
  | WHILE b DO c END =>
      match fold_constants_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
(**unfold atrans_sound. intros a. unfold aequiv. intros st.
induction a; simpl; try reflexivity;
try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2); 
rewrite IHa1; rewrite IHa2; reflexivity). **)
Admitted.

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
induction b ; try reflexivity.
rename a into a1. rename a0 into a2. simpl.
Admitted.

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
- apply refl_cequiv.
- apply CAss_congruence. apply fold_constants_aexp_sound.
- apply CSeq_congruence. assumption. assumption.
- Admitted.

Fixpoint optimize_0plus (e:aexp) : aexp :=
      match e with
      | ANum n =>
          ANum n
      | AId i => AId i
      | APlus (ANum 0) e2 =>
          optimize_0plus e2
      | APlus e1 e2 =>
          APlus (optimize_0plus e1) (optimize_0plus e2)
      | AMinus e1 e2 =>
          AMinus (optimize_0plus e1) (optimize_0plus e2)
      | AMult e1 e2 =>
          AMult (optimize_0plus e1) (optimize_0plus e2)
      end.

Fixpoint subst_aexp (i : string) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | AId i' =>
      if beq_string i i' then u else AId i'
  | APlus a1 a2 =>
      APlus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMinus a1 a2 =>
      AMinus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMult a1 a2 =>
      AMult (subst_aexp i u a1) (subst_aexp i u a2)
  end.

Definition subst_equiv_property := forall i1 i2 a1 a2,
  cequiv (i1 ::= a1;; i2 ::= a2)
         (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).

Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
Admitted.
(** unfold subst_equiv_property.
intros C.
remember (X ::= X + 1;; Y ::= X) as c1.
remember (X ::= X + 1;;
            Y ::= X+1) as c2.
assert (cequiv c1 c2) by (subst; apply C).
remember {X --> 1 ; Y --> 1} as st1.
remember {X --> 1 ; Y --> 2} as st2.
assert (H1: c1 / { --> 0 } \\ st1);
assert (H2: c2 / { --> 0 } \\ st2);
try (subst;
       apply E_Seq with (st' := {X --> 1});
       apply E_Ass; reflexivity).
  apply H in H1.
assert (Hcontra: st1 = st2)
    by (apply (ceval_deterministic c2 { --> 0 }); assumption).
  assert (Hcontra': st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. inversion Hcontra'. Qed.
**)

Theorem inequiv_exercise:
  ~ cequiv (WHILE BTrue DO SKIP END) SKIP.
Proof.
unfold not. intros contra. 
unfold cequiv in contra. 
assert (H: forall st, SKIP / st \\ st). apply E_Skip.
Admitted.

(** Skipped HAVOC : Extended Exercise: Nondeterministic Imp**)


































