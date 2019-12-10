Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import maps.
Require Import imp.
Require Import hoare.


Definition reduce_to_zero' : com :=
  WHILE !(X = 0) DO
    X ::= X - 1
  END.

Theorem reduce_to_zero_correct' :
  {{fun st => True}}
  reduce_to_zero'
  {{fun st => st X = 0}}.
Proof.
unfold reduce_to_zero'.
eapply hoare_consequence_post.
- apply hoare_while.
eapply hoare_consequence_pre.
apply hoare_asgn.
unfold bassn, assn_sub, t_update, assert_implies.
intros st [T bv]. apply I.
-  unfold bassn, assn_sub, t_update, assert_implies. 
intros st [T bv]. rewrite not_true_iff_false in bv.
simpl in bv. rewrite negb_false_iff in bv.
apply beq_nat_true in bv.
assumption.
Qed.

Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

Lemma parity_ge_2 : forall x,
  2 <= x ->
  parity (x - 2) = parity x.
Proof.
intros.
induction x.
- simpl. reflexivity.
- destruct x. inversion H. inversion H1.
simpl. rewrite <- minus_n_O. reflexivity.
Qed.

Lemma parity_lt_2 : forall x,
  ~ 2 <= x ->
  parity (x) = x.
Proof.
intros.
induction x.
- simpl. reflexivity.
- destruct x. reflexivity.
  exfalso. apply H. omega.
Qed.

Fixpoint ble_nat (n m : nat) : bool :=
match n with
| O => match m with
  | O => false
  | S _ => true
  end
| S n' => match m with 
  | O => true 
  | S m' => ble_nat n' m'
  end
end.

Theorem ble_nat_true : forall n m,
    ble_nat n m = true -> n <= m.
Proof.
  (* FILL IN HERE *) Admitted.

Notation " n <= m" :=
  (ble_nat n m) (at level 70).

Theorem parity_correct : forall m,
    {{ fun st => st X = m }}
  WHILE 2 <= X DO
    X ::= X - 2
  END
    {{ fun st => st X = parity m }}.
Proof.
intros.
apply hoare_consequence_pre with (fun st => parity (st X) = parity m).
eapply hoare_consequence_post.
- apply hoare_while. 
eapply hoare_consequence_pre. apply hoare_asgn.
  unfold assn_sub.
 intros st [M BV]. simpl. rewrite <- M.
apply parity_ge_2. unfold bassn in BV.
unfold beval in BV. unfold aeval in BV.
apply ble_nat_true. rewrite <- BV.
Admitted.

Lemma lemma1 : forall x y,
    (x=0 \/ y=0) -> min x y = 0.
Proof.
Admitted.
  Lemma lemma2 : forall x y,
    min (x-1) (y-1) = (min x y) - 1.
Proof.
Admitted.

Definition is_wp P c Q :=
  {{P}} c {{Q}} /\
  forall P', {{P'}} c {{Q}} -> (P' ->> P).

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
  split.
  -
    apply hoare_asgn.
  -
    unfold hoare_triple, assn_sub.
    intros  P' Hhoare st HP'.
Admitted.

Theorem hoare_asgn_weakest' : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
unfold is_wp.
intros.
split.
- apply hoare_asgn.
- intros  P' H st HP'.
Admitted.

































