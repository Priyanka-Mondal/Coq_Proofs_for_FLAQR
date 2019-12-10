Set Warnings "-notation-overridden,-parsing".
Require Export indprop.
Require Import Coq.omega.Omega.

Definition relation (X: Type) := X -> X -> Prop.

Print le.

Check le : nat -> nat -> Prop.
Check le : relation nat.

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Inductive next_nat (n : nat) : nat -> Prop :=
           nn : next_nat n (S n).

Check next_nat : relation nat.
Theorem next_nat_partial_function :
   partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity. 
Qed.

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
unfold not.
unfold partial_function.
intros.
assert (0 = 1) as Nonsense.
 {
    apply H with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n.
 } 
  inversion Nonsense. 
Qed.

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.
Theorem le_reflexive :
  reflexive le.
Proof.
unfold reflexive.
intros.
apply le_n.
Qed.

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).
Theorem le_trans :
  transitive le.
Proof.
unfold transitive.
intros.
induction H0.
assumption.
apply le_S. 
apply IHle.
assumption.
Qed.

Theorem lt_trans:
  transitive lt.
Proof.
unfold transitive.
unfold lt.
intros.
apply le_S in H.
apply le_trans with 
(a := (S a)) (b := (S b)) (c := c).
assumption. assumption.
Qed.

Theorem lt_trans' :
  transitive lt.
Proof.
unfold lt. unfold transitive.
intros n m o Hnm Hmo.
induction Hmo as [| m' Hm'o].
Admitted.

Theorem le_Sn_le : forall n m, 
S n <= m -> n <= m.
Proof.
intros.
apply le_trans with (S n).
- apply le_S. apply le_n.
- assumption.
Qed.

Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
intros.
inversion H.
- apply le_n.
- apply le_Sn_le in H2.
assumption.
Qed.

Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
induction n.
- intros H.
inversion H.
- unfold not in IHn.
intros H. apply le_S_n in H.
apply IHn in H.
assumption.
Qed.

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
unfold not.
unfold symmetric.
intros.
assert (1<=0) as A.
- apply H. apply le_S. apply le_n.
- inversion A.
Qed.

Definition antisymmetric 
{X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Lemma Sn_eq_n : forall n m,
 n =  m -> S n = S m.
Proof.
Admitted.

Theorem le_antisymmetric :
  antisymmetric le.
Proof.
intros a b.
generalize dependent a.
induction b.
- intros. inversion H.
reflexivity.
- intros a. intros H H1.
destruct a.
+ inversion H1.
+ apply le_S_n in H1.
apply le_S_n in H.
apply Sn_eq_n.
apply IHb.
assumption. assumption.
Qed.

Lemma le_lt: forall n m,
n <= m -> n < S m.
Proof.
Admitted.

Lemma lt_le : forall n m,
n < S m -> n <= m.
Proof.
Admitted.

Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
intros n m p Hnm Hmp1.
  unfold lt in Hnm.
  assert (S n <= S p).
  apply le_trans with m.
  assumption.
  assumption.
  apply le_S_n.
  assumption.
Qed.

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).
(** order is patial order **)

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
split.
- unfold reflexive. intros. apply le_n.
- split.
  +  unfold antisymmetric. intros.
     apply le_antisymmetric.
     assumption. assumption.
  +  apply le_trans.
Qed.

Inductive clos_refl_trans 
{A: Type} (R: relation A) : relation A :=
    | rt_step : forall x y, R x y -> clos_refl_trans R x y
    | rt_refl : forall x, clos_refl_trans R x x
    | rt_trans : forall x y z,
          clos_refl_trans R x y ->
          clos_refl_trans R y z ->
          clos_refl_trans R x z.

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
split.
- intros. induction H.
 + apply rt_refl.
 + apply rt_trans with m.
   apply IHle. apply rt_step. apply nn.
- intros. induction H. 
 + inversion H. apply le_S. apply le_n.
 + apply le_n.
 + apply le_trans with y.
   assumption. assumption.
Qed.

Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A) :
      R x y -> clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.

Lemma rsc_R : forall (X:Type) 
(R:relation X) (x y : X),
       R x y -> clos_refl_trans_1n R x y.
Proof.
intros.
apply rt1n_trans with y.
assumption.
apply rt1n_refl.
Qed.

Lemma rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y ->
      clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.
Proof.
intros X R x y z.
replace (clos_refl_trans_1n R y z -> clos_refl_trans_1n R x z)
with (R x y).
intros.
Admitted.

Theorem rtc_rsc_coincide :
        forall (X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
Admitted.

















