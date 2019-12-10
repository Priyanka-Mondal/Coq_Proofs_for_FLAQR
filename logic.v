Set Warnings "-notation-overridden,-parsing".
Require Export tactics. 

Definition plus_fact : Prop := 2 + 2 = 14.
Check plus_fact.

(**Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity. Qed. 
reflexivity does not work**)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.

Definition injective {A B :Type } (f : A -> B) :=
  forall x y : A, eq (f x) (f y) -> eq x y.
Check @injective.
Check eq.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
intros. split. apply H. apply H0. Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  destruct n.
  - intros m H. destruct m.
    + simpl in H. split. reflexivity. reflexivity.
    + simpl in H. split. reflexivity. inversion H.
 - intros m H. destruct m.
   + split. inversion H. reflexivity.
   + split. inversion H. inversion H.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
intros n m [HA HB].
rewrite HA. rewrite HB.
simpl. reflexivity. 
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
intros n m H.
assert (A : n = 0 /\ m = 0).
{ apply and_exercise. apply H. }
destruct A as [Ha Hb].
rewrite Ha. simpl. reflexivity.
Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
intros P Q [HP HQ].
apply HQ.
Qed.

Lemma and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
intros P Q [HP HQ].
split.
apply HQ. apply HP.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split. split. apply HP. apply HQ. apply HR.
Qed.

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
intros n m.
intros [Hn | Hm].
- rewrite Hn. simpl. reflexivity.
- rewrite Hm. rewrite <- mult_n_O. reflexivity.
Qed.

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
intros [| n].
- left. reflexivity.
- right. reflexivity.
Qed.

Module MyNot.
Definition not (P:Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.
Check not.
(* ===> Prop -> Prop *)
End MyNot.
Check not.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P xyz.
  destruct xyz. Qed.

Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
intros P notP.
Admitted.

Theorem zero_not_one : ~(0 = 1).
Proof.
intros c. inversion c. Qed.
Theorem zero_not_one' : 0 <> 1.
Proof.
intros H. inversion H.
Qed.

Theorem not_False :
  ~ False.
Proof.
unfold not. intros H. apply H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
intros P Q.
intros c.
destruct c.
unfold not in H0. 
apply H0 in H.
destruct H. Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
intros P.
intros C.
unfold not.
intros D. apply D. apply C. Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
unfold not.
intros P Q. intros PQ Qf p.
apply Qf. apply PQ. apply p.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
unfold not.
intros P.
intros [Hp Pf]. apply Pf. apply Hp.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
intros b. intros H. unfold not in H.
destruct b. 
- apply ex_falso_quodlibet. apply H. reflexivity.
- reflexivity.
Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

Module MyIff.
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.
End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
intros P Q.
unfold iff.
intros [L R].
split.
apply R.
apply L.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
intros b.
unfold iff.
split.
apply not_true_is_false.
intros bf.
rewrite bf.
unfold not.
intros bf'. inversion bf'.
Qed.

Lemma or_commut : forall A B : Prop,
A \/ B -> B \/ A.
Proof.
intros A B.
intros [l | r].
right. apply l. left.  apply r.
Qed.


Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
intros P Q R.
split.
- intros [l|r]. split. apply or_intro . apply l. apply or_intro.
apply l. split. right. apply r. right. apply r.
- intros [l r]. inversion l as [ p | q]. left. apply p. 
  inversion r as [pp | rr]. left. apply pp. right. 
  apply and_intro. apply q. apply rr.
Qed.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
intros.
unfold iff.
split.
- intros. 
destruct n in H.
+ destruct m.
  { simpl in H. right. apply H. }
  { left. inversion H.  
Admitted.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
intros.
unfold iff.
split.
- intros. inversion H as [p | [q | r]]. left. left. apply p.
  left. right. apply q. right. apply r.
- intros. inversion H as [[p|q]|r]. left. apply p. right. left. 
  apply q. right. right. apply r.
Qed.

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
Admitted.

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* WORKED IN CLASS *)
  intros n [m Hm]. (* note implicit destruct here *)
  exists (2 + m).
  apply Hm. Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
intros.
unfold not. intros.
inversion H0. 
apply H1.
apply H.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
intros.
split.
- intros. destruct H. destruct H. left.
Admitted.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros. apply H.
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
intros.
split.
- induction l as [ | h t IH]. intros.
simpl in H. simpl. inversion H. intros. simpl in H. inversion H.

Admitted.

Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
intros. split.
- intros. induction l.
  + simpl. simpl in H. right. apply H.
  + simpl. simpl in H. inversion H. left. left. apply H0. 
    apply IHl in H0. inversion H0. left. right. apply H1. 
    right. apply H1.
- intros. induction l.
  + simpl in H. simpl. inversion H. 
  apply ex_falso_quodlibet. apply H0. apply H0.
  + simpl. 
  simpl in H. apply or_assoc in H. inversion H. left. 
  apply H0. apply IHl in H0.
  right. apply H0.
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop)
: nat -> Prop :=
fun n => if (evenb n) then Peven n else Podd n.

Theorem combine_odd_even_intro : 
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
intros po pe n.
unfold oddb. intros h1 h2.
induction n.
- unfold combine_odd_even. apply h2. reflexivity.
- unfold combine_odd_even. destruct evenb.
 + apply h2. reflexivity.
 + apply h1. reflexivity.
Qed.

Lemma plus_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  assert (H : y + z = z + y).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Lemma plus_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm .
  rewrite (plus_comm z y).
  reflexivity.
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
intros n ns . intros.
Admitted.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
Admitted.










































