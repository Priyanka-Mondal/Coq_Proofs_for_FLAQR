Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import imp.
Require Import maps.

Definition Assertion := state -> Prop.

Module ExAssertions.
Definition as1 : Assertion := fun st => st X = 3.
Definition as2 : Assertion := fun st => st X <= st Y.
Definition as3 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition as4 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition as5 : Assertion := fun st => True.
Definition as6 : Assertion := fun st => False.
(* FILL IN HERE *)
End ExAssertions.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.
Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
     c / st \\ st' ->
     P st ->
     Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H. 
Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~(P st)) ->
  {{P}} c {{Q}}.
Proof.
intros P Q c H.
unfold hoare_triple.
intros st st' Heval HP. unfold not in H.
apply H in HP. inversion HP.
Qed.

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (st & { X --> aeval st a }).
Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof.
intros Q X a. unfold hoare_triple.
intros st st'. intros H1 H2.
inversion H1. subst.
unfold assn_sub in H2.
assumption. Qed.

Example assn_sub_example :
  {{(fun st => st X < 5) [X |-> X+1]}}
  (X ::= X+1)
  {{fun st => st X < 5}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_asgn. Qed.

Local Close Scope aexp_scope.

Theorem hoare_asgn_fwd :
  forall m a P,
  {{fun st => P st /\ st X = m}}
    X ::= a
  {{fun st => P (st & { X --> m })
            /\ st X =
 aeval (st & { X --> m }) a }}.
Proof.
(* FILL IN HERE *) Admitted.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
intros P P' Q c.
intros H1 H2.
unfold hoare_triple.
intros st st' H3 H4.
apply (H1 st st').
assumption.
apply H2. assumption. 
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
intros P Q Q' c.
intros H1 H2.
intros st st' H3 H4.
apply H2.
apply (H1 st st').
assumption. assumption.
Qed.

Example hoare_asgn_example1 :
  {{fun st => True}} (X ::= 1) {{fun st => st X = 1}}.
Proof.
eapply hoare_consequence_pre.
    (** with (P' := (fun st => st X = 1) [X |-> 1]). **)
apply hoare_asgn.
intros st H. unfold assn_sub. unfold t_update.
simpl. reflexivity.
Qed.

Example assn_sub_example2 :
  {{(fun st => st X < 4)}}
  (X ::= X+1)
  {{fun st => st X < 5}}.
Proof.
apply hoare_consequence_pre with
(P' := (fun st => st X < 5)[X|-> X+1]).
apply hoare_asgn. intros st H.
unfold assn_sub, t_update. 
simpl. omega. Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
intros. unfold hoare_triple.
intros.
unfold hoare_triple in H.
apply H1.
apply (H st st').
assumption.
apply H0.
assumption.
Qed.

Lemma silly2_fixed :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP .
  eapply HQ. apply H.
Qed.

Lemma silly2_eassumption : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. 
  eapply HQ. eassumption.
Qed.

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
unfold hoare_triple.
intros.  inversion H; subst.
apply H0.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
unfold hoare_triple. intros.
inversion H1; subst.
apply ( H st'0 st').
assumption.
apply (H0 st st'0).
assumption.
assumption.
Qed.

Example hoare_asgn_example3 : forall a n,
  {{fun st => aeval st a = n}}
  (X ::= a;; SKIP)
  {{fun st => st X = n}}.
Proof.
intros. eapply hoare_seq.
apply hoare_skip.
eapply hoare_consequence_pre.
eapply hoare_asgn.
intros st H. subst.
reflexivity.
Qed.

Example hoare_asgn_example4 :
  {{fun st => True}} (X ::= 1;; Y ::= 2)
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
eapply hoare_seq.
eapply hoare_asgn.
eapply hoare_consequence_pre.
eapply hoare_asgn.
intros st T. unfold assn_sub, t_update.
simpl. split;
reflexivity.
Qed.

Definition swap_program : com :=
  (Z ::= AId X ;; X ::= AId Y;; Y ::= AId Z).

Theorem swap_exercise :
  {{fun st => st X <= st Y}}
  swap_program
  {{fun st => st Y <= st X}}.
Proof.
unfold swap_program.
eapply hoare_seq.
eapply hoare_seq.
eapply hoare_asgn.
eapply hoare_asgn.
eapply hoare_consequence_pre.
eapply hoare_asgn.
intros st T. unfold assn_sub, t_update.
simpl. assumption.
Qed.

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
intros.
unfold bassn. assumption.
Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
intros b st Hf c.
unfold bassn in c. rewrite Hf in c.
inversion c.
Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
unfold hoare_triple.
intros.
inversion H1; subst.
- apply (H st st'). assumption.
split. assumption. unfold bassn. assumption.
- apply (H0 st st'). assumption. split.
assumption. apply bexp_eval_false.
assumption.
Qed.

Example if_example :
    {{fun st => True}}
  IFB X = 0
    THEN Y ::= 2
    ELSE Y ::= X + 1
  FI
    {{fun st => st X <= st Y}}.
Proof.
eapply hoare_if.
- eapply hoare_consequence_pre.
apply hoare_asgn.
unfold assn_sub, t_update, assert_implies. simpl.
intros st [_T]. apply beq_nat_true in H. simpl in H.
rewrite H. omega.
- eapply hoare_consequence_pre.
apply hoare_asgn.
unfold assn_sub, t_update, assert_implies. simpl.
intros st _. omega.
Qed.

Theorem if_minus_plus :
  {{fun st => True}}
  IFB X <= Y
    THEN Z ::= Y - X
    ELSE Y ::= X + Z
  FI
  {{fun st => st Y = st X + st Z}}.
Proof.
eapply hoare_if.
- eapply hoare_consequence_pre. 
eapply hoare_asgn.
unfold assn_sub, t_update, assert_implies.
simpl. intros s [_T].  inversion H.
Admitted.

Module If1.
Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'IF1' b 'THEN' c 'FI'" :=
  (CIf1 b c) (at level 80, right associativity).

Reserved Notation "c1 '/' st '\\' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st \\ st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : string),
            aeval st a1 = n -> (X ::= a1) / st \\ st & { X --> n }
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
            c1 / st \\ st' -> c2 / st' \\ st'' -> (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
               beval st b1 = true ->
               c1 / st \\ st' -> (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
                beval st b1 = false ->
                c2 / st \\ st' -> (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileFalse : forall (b1 : bexp) (st : state) (c1 : com),
                 beval st b1 = false -> (WHILE b1 DO c1 END) / st \\ st
  | E_WhileTrue : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
                  beval st b1 = true ->
                  c1 / st \\ st' ->
                  (WHILE b1 DO c1 END) / st' \\ st'' ->
                  (WHILE b1 DO c1 END) / st \\ st''
(* FILL IN HERE *)

  where "c1 '/' st '\\' st'" := (ceval c1 st st').

Definition hoare_triple1 (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
       c / st \\ st' ->
       P st ->
       Q st'.
Notation "{{ P }} c {{ Q }}" := (hoare_triple1 P c Q)
                                  (at level 90, c at next level)
                                  : hoare_spec_scope.

Lemma hoare_if1_good :
  {{ fun st => st X + st Y = st Z }}
  IF1 !(Y = 0) THEN
    X ::= X + Y
  FI
  {{ fun st => st X = st Z }}.
Proof. (* FILL IN HERE *) Admitted.
End If1.

Theorem hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
intros P b c Hhoare st st' He HP.
remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); 
subst; clear Heqwcom.
  - (* E_WhileFalse *)
    split. assumption. apply bexp_eval_false. assumption.
  - (* E_WhileTrue *)
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.

Lemma nottrue : forall P,
(P = false) = (P <> true).
Proof.
Admitted.

Example while_example :
    {{fun st => st X <= 3}}
  WHILE X <= 2
  DO X ::= X + 1 END
    {{fun st => st X = 3}}.
Proof.
eapply hoare_consequence_post.
eapply hoare_while.
- eapply hoare_consequence_pre. eapply hoare_asgn.
unfold bassn, assn_sub, t_update, assert_implies. 
simpl.
intros st [H1 H2]. apply leb_complete in H2.
omega.
- unfold assn_sub, t_update, assert_implies.
intros st.
replace (~ bassn (X <= 2) st) with (beval st (X<=2) = false).
intros [H1 H2]. simpl in H2. 
apply leb_iff_conv in H2. omega.
simpl. unfold bassn. simpl.
replace ((st X <=? 2) <> true) with ((st X <=? 2) = false).
reflexivity.
remember (st X <=? 2) as P.
apply nottrue.
Qed.

Theorem always_loop_hoare : forall P Q,
  {{P}} WHILE true DO SKIP END {{Q}}.
Proof.
intros.
apply hoare_consequence_pre 
with (P' := fun st : state => True).
  eapply hoare_consequence_post.
apply hoare_while.
- apply hoare_post_true. intros st. apply I.
- simpl. intros st. intros [T B]. 
exfalso. apply B. unfold bassn. simpl. reflexivity.
- intros st H. constructor.
Qed.

Module RepeatExercise.
Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
  (CRepeat e1 b2) (at level 80, right associativity).

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      ceval st SKIP st
  | E_Ass : forall st a1 n X,
      aeval st a1 = n ->
      ceval st (X ::= a1) (st & { X --> n })
  | E_Seq : forall c1 c2 st st' st'',
      ceval st c1 st' ->
      ceval st' c2 st'' ->
      ceval st (c1 ;; c2) st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      ceval st c2 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_WhileFalse : forall b1 st c1,
      beval st b1 = false ->
      ceval st (WHILE b1 DO c1 END) st
  | E_WhileTrue : forall st st' st'' b1 c1,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st' (WHILE b1 DO c1 END) st'' ->
      ceval st (WHILE b1 DO c1 END) st''
  | E_RepeatFalse : forall st st' b1 c1,
      beval st b1 = false -> 
      ceval st c1 st' ->
      ceval st' (REPEAT c1 UNTIL b1 END) st' ->
      ceval st (REPEAT c1 UNTIL b1 END) st'
  | E_RepeatTrue : forall st st' st'' b1 c1,
      beval st b1 = true -> 
      ceval st c1 st' ->
      ceval st' (REPEAT c1 UNTIL b1 END) st'' ->
      ceval st (REPEAT c1 UNTIL b1 END) st''
.

Notation "c1 '/' st '\\' st'" := (ceval st c1 st')
                                 (at level 40, st at level 39).
Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion)
                        : Prop :=
  forall st st', (c / st \\ st') -> P st -> Q st'.
Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level).

Definition ex1_repeat :=
  REPEAT
    X ::= 1;;
    Y ::= Y + 1
  UNTIL X = 1 END.

Theorem ex1_repeat_works :
  ex1_repeat / { --> 0 } \\ { X --> 1 ; Y --> 1 }.
Proof.
unfold ex1_repeat.
Admitted.

End RepeatExercise.
(** havoc exercise **)