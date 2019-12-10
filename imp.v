Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Import ListNotations.
Require Import maps.

(**Module AExp.
Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.
Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. simpl.
reflexivity. Qed.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2 => leb (aeval a1) (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus (ANum 0) e2 =>
      optimize_0plus e2
  | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
intros. induction a.
- simpl. reflexivity.
- destruct a1.
 + destruct n.
   * simpl. apply IHa2.
   * simpl. rewrite IHa2. trivial.
 + simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. trivial.
 + simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. trivial.
 + simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. trivial.
- simpl. rewrite IHa1. rewrite IHa2. trivial.
- simpl. rewrite IHa1. rewrite IHa2. trivial.
Qed.

Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof. try reflexivity. (* this just does reflexivity *) Qed.
Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* just reflexivity would have failed *)
  apply HP. (* we can still finish the proof in some other way *)
Qed.

Lemma foo : forall n, leb 0 n = true.
Proof.
  intros.
  destruct n.
    (* Leaves two subgoals, which are discharged identically...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.

Lemma foo' : forall n, leb 0 n = true.
Proof.
  intros.
  (* destruct the current goal *)
  destruct n;
  (* then simpl each resulting subgoal *)
  simpl;
  (* and do reflexivity on each resulting subgoal *)
  reflexivity.
Qed.

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  - (* ANum *) reflexivity.
  - (* APlus *)
    destruct a1;try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
repeat simpl.
repeat (try (left; reflexivity); right).
Qed.

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1 => BNot (optimize_0plus_b b1)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.

Theorem optimize_0plus_b_sound:
  forall e, beval (optimize_0plus_b e) = beval e.
Proof.
  intro e.
  induction e;
    try reflexivity;
    try (simpl; rewrite 2 optimize_0plus_sound; reflexivity).
    simpl. rewrite IHe. reflexivity.
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

Theorem optimize_0plus_b_sound' : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
Admitted.

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.

Module aevalR_first_try.
Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n: nat),
      aevalR (ANum n) n
  | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus: forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).
Notation "e '\\' n"
         := (aevalR e n)
            (at level 50, left associativity)
         : type_scope.
End aevalR_first_try.

Reserved Notation "e '\\' n" (at level 50, left associativity).
Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)

  where "e '\\' n" := (aevalR e n) : type_scope.



Fixpoint ble_nat ( n1 n2 : nat) : bool :=
match n1 with
| O => match n2 with 
     | O => true 
     | S n2' => true
     end
| S n1' => match n2 with
    | O => false 
    | S n2' => ble_nat n1' n2'
    end
end.

Reserved Notation "e '||' n" (at level 50, left associativity).

Inductive bevalR : bexp -> bool -> Prop :=
| E_BTrue : BTrue || true
| E_BFalse : BFalse || false
| E_BEq : forall a1 a2 n1 n2, 
aevalR a1 n1 -> aevalR a2 n2 -> BEq a1 a2 || beq_nat n1 n2
| E_BLe : forall a1 a2 n1 n2, 
aevalR a1 n1 -> aevalR a2 n2 -> BLe a1 a2 || ble_nat n1 n2
| E_BNot : forall b p, b || p -> BNot b || negb p
| E_BAnd : forall b1 b2 p1 p2,
b1 || p1 -> b2 || p2 -> BAnd b1 b2 || andb p1 p2

where "e '||' n" := (bevalR e n) : type_scope.

Theorem aeval_iff_aevalR : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
split.
- intros. induction H;simpl.
  +  trivial.
  + rewrite IHaevalR1. rewrite IHaevalR2. trivial. 
  + rewrite IHaevalR1. rewrite IHaevalR2. trivial.
  + rewrite IHaevalR1. rewrite IHaevalR2. trivial. 
- intros. generalize dependent n. induction a;
  simpl; intros; subst.
  + apply E_ANum.
  + apply E_APlus. apply IHa1. reflexivity. apply IHa2. reflexivity.
  + apply E_AMinus. apply IHa1. reflexivity. 
    apply IHa2. reflexivity. 
  + apply E_AMult. apply IHa1. reflexivity. apply IHa2. reflexivity.
Qed.

Lemma beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
intros.
split.
- intros. induction H;simpl.
  + reflexivity.
  + reflexivity.
  + induction H; simpl; induction H0; simpl;
try (reflexivity). generalize dependent n.
Admitted.
**)
Definition state := total_map nat.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : string -> aexp (* <----- NEW *)
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Definition bool_to_bexp (b: bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope aexp_scope with aexp.
Infix "+" := APlus : aexp_scope.
Infix "-" := AMinus : aexp_scope.
Infix "*" := AMult : aexp_scope.
Bind Scope bexp_scope with bexp.
Infix "<=" := BLe : bexp_scope.
Infix "=" := BEq : bexp_scope.
Infix "&&" := BAnd : bexp_scope.
Notation "'!' b" := (BNot b) (at level 60) : bexp_scope.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x (* <----- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => leb (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Notation "{ a !-> x }" := 
  (t_update { !-> 0 } a x) (at level 0).
Notation "{ a !-> x ; b !-> y }" := 
  (t_update ({ a !-> x }) b y) (at level 0).
Notation "{ a !-> x ; b !-> y ; c !-> z }" := 
  (t_update ({ a !-> x ; b !-> y }) c z) (at level 0).
Notation "{ a !-> x ; b !-> y ; c !-> z ; d !-> t }" := 
    (t_update ({ a !-> x ; b !-> y ; c !-> z }) d t) (at level 0).
Notation "{ a !-> x ; b !-> y ; c !-> z ; d !-> t ; e !-> u }" :=
  (t_update ({ a !-> x ; b !-> y ; c !-> z ; d !-> t }) e u) (at level 0).
Notation "{ a !-> x ; b !-> y ; c !-> z ; d !-> t ; e !-> u ; f !-> v }" :=
  (t_update ({ a !-> x ; b !-> y ; c !-> z ; d !-> t ; e !-> u }) f v) (at level 0).

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Bind Scope com_scope with com.
Notation "'SKIP'" :=
   CSkip : com_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : com_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : com_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : com_scope.
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : com_scope.

Open Scope com_scope.

Definition fact_in_coq : com :=
  Z ::= X;;
  Y ::= 1;;
  WHILE ! (Z = 0) DO
    Y ::= Y * Z;;
    Z ::= Z - 1 
  END.

Definition plus2 : com :=
  X ::= X + 2.
Definition XtimesYinZ : com :=
  Z ::= X * Y.
Definition subtract_slowly_body : com :=
  Z ::= Z - 1 ;;
  X ::= X - 1.

Definition subtract_slowly : com :=
  WHILE ! (X = 0) DO
    subtract_slowly_body
  END.
Definition subtract_3_from_5_slowly : com :=
  X ::= 3 ;;
  Z ::= 5 ;;
  subtract_slowly.

Definition loop : com :=
  WHILE true DO
    SKIP
  END.

Fixpoint ceval_fun_no_while (st : state) (c : com)
                          : state :=
  match c with
    | SKIP =>
        st
    | x ::= a1 =>
        st & { x !-> (aeval st a1) }
    | c1 ;; c2 =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | WHILE b DO c END =>
        st (* bogus *)
  end.

Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st \\ st
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st \\ st & { x !-> n }
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st \\ st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      c / st \\ st' ->
      (WHILE b DO c END) / st' \\ st'' ->
      (WHILE b DO c END) / st \\ st''

  where "c1 '/' st '\\' st'" := (ceval c1 st st').

Example ceval_example1:
    (X ::= 2;;
     IFB X <= 1
       THEN Y ::= 3
       ELSE Z ::= 4
     FI)
   / { !-> 0 } \\ { X !-> 2 ; Z !-> 4 }.
Proof.
apply E_Seq with { X !-> 2 }.
  -
    apply E_Ass. reflexivity.
  -
    apply E_IfFalse. simpl.
      reflexivity.
      apply E_Ass. simpl. reflexivity. Qed.

Example ceval_example2:
  (X ::= 0;; Y ::= 1;; Z ::= 2) / { !-> 0 } \\
  { X !-> 0 ; Y !-> 1 ; Z !-> 2 }.
Proof.
apply E_Seq with { X !-> 0}.
apply E_Ass. reflexivity.
apply E_Seq with { X !-> 0;Y !-> 1}.
apply E_Ass. reflexivity.
apply E_Ass. reflexivity.
Qed.

Theorem plus2_spec : forall st n st',
  st X = n ->
  plus2 / st \\ st' ->
  st' X = (n + 2).
Proof.
  intros st n st' HX Heval.
inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq. Qed.

Definition empty_st := fun (_ : string) => 0.
(** do the advanced exercise **)













