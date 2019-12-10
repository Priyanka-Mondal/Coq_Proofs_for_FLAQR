Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Export Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.

Definition beq_string x y :=
  if string_dec x y then true else false.

Theorem beq_string_refl : forall s, true = beq_string s s.
Proof.
intros. unfold beq_string.
destruct (string_dec s s).
- reflexivity.
- destruct n. reflexivity.
Qed.

Theorem beq_string_eql : forall s, 
beq_string s s = true.
Proof.
intros. unfold beq_string.
destruct (string_dec s s).
- reflexivity.
- destruct n. reflexivity.
Qed.

Theorem beq_string_true_iff : forall x y : string,
  beq_string x y = true <-> x = y.
Proof.
intros.
unfold iff.
split. 
- intros. unfold beq_string in H. destruct (string_dec x y) in H.
  + apply e.
  + inversion H.
- intros. rewrite H. symmetry. apply beq_string_refl. 
Qed.

Theorem false_beq_string : forall x y : string,
   x <> y -> beq_string x y = false.
Proof.
Admitted.

Theorem beq_string_false_iff : forall x y : string,
  beq_string x y = false
  <-> x <> y.
Proof.
intros.
unfold iff. 
split.
- intros.
unfold beq_string in H. destruct (string_dec x y).
 + inversion H.
 + apply n.
- apply false_beq_string. 
Qed.

(** starting of total maps **)

Definition total_map (A:Type) := string -> A.
(** function that can be used to look up strings, yielding As.**)
Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A:Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if beq_string x x' then v else m x'.

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

Notation "{ !-> d }" := (t_empty d) (at level 0).

Notation "m '&' { a !-> x }" :=
  (t_update m a x) (at level 20).
Notation "m '&' { a !-> x ; b !-> y }" :=
  (t_update (m & { a !-> x }) b y) (at level 20).
Notation "m '&' { a !-> x ; b !-> y ; c !-> z }" :=
  (t_update (m & { a !-> x ; b !-> y }) c z) (at level 20).
Notation "m '&' { a !-> x ; b !-> y ; c !-> z ; d !-> t }" :=
    (t_update (m & { a !-> x ; b !-> y ; c !-> z }) d t) (at level 20).
Notation "m '&' { a !-> x ; b !-> y ; c !-> z ; d !-> t ; e !-> u }" :=
    (t_update (m & { a !-> x ; b !-> y ; c !-> z ; d !-> t }) e u) (at level 20).
Notation "m '&' { a !-> x ; b !-> y ; c !-> z ; d !-> t ; e !-> u ; f !-> v }" :=
    (t_update (m & { a !-> x ; b !-> y ; c !-> z ; d !-> t ; e !-> u }) f v) (at level 20).

Definition examplemap' :=
  { !-> false } & { "foo" !-> true ; "bar" !-> true }.

Lemma t_apply_empty: forall 
(A:Type) (x: string) (v: A), { !-> v } x = v.
Proof.
intros.
unfold t_empty.
reflexivity.
Qed.

Lemma t_update_eq : forall A (m: total_map A) x v,
  (m & {x !-> v}) x = v.
Proof.
intros.
unfold t_update.
replace (beq_string x x) with true.
- reflexivity.
- rewrite beq_string_eql. reflexivity.
Qed.

Theorem t_update_neq : forall (X:Type) v x1 x2
                         (m : total_map X),
  x1 <> x2 ->
  (m & {x1 !-> v}) x2 = m x2.
Proof.
intros.
unfold t_update.
replace (beq_string x1 x2) with false.
- reflexivity.
- rewrite false_beq_string.
  reflexivity. apply H.
Qed.

(** Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    t_update (t_update m x v1) x v2
  = t_update m x v2.
Proof.
  intros A m v1 v2 x.
  unfold t_update.
  extensionality x'.
  remember (beq_string x x') as e; induction e.
  trivial. trivial. **)


Lemma t_update_shadow' : forall A (m: total_map A) v1 v2 x,
    m & {x !-> v1 ; x !-> v2} = m & {x !-> v2}.
Proof.
intros.
unfold t_update.
extensionality x'.
induction (beq_string x x').
- reflexivity.
- reflexivity.
Qed.


Lemma beq_stringP : forall x y, 
reflect (x = y) (beq_string x y).
Proof.
Admitted.

Lemma beq_equal : forall x x',
 beq_string x x' = true -> x = x'.
Proof.
Admitted.

Theorem t_update_same : forall X x (m : total_map X),
    m & { x !-> m x } = m.
Proof.
intros.
unfold t_update.
extensionality x'.
remember (beq_string x x') as h. 
induction h.
- symmetry in Heqh. apply beq_equal in Heqh. 
rewrite Heqh. reflexivity.
- trivial.
Qed.

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 <> x1 ->
  m & { x2 !-> v2 ; x1 !-> v1 }
  = m & { x1 !-> v1 ; x2 !-> v2 }.
Proof.
intros.
unfold t_update.
extensionality x'.
remember (beq_string x1 x') as h1. 
induction h1.
- symmetry in Heqh1. apply beq_equal in Heqh1.
symmetry in Heqh1. rewrite Heqh1. 
remember (beq_string x2 x1) as h2.
 apply false_beq_string in H.
symmetry in Heqh2. rewrite H in Heqh2. 
symmetry in Heqh2.
rewrite Heqh2 . trivial.
- trivial.
Qed.

Definition partial_map (A:Type)
 := total_map (option A).
Definition empty {A:Type} : partial_map A :=
  t_empty None. 

Definition update {A:Type} (m : partial_map A)
           (x : string) (v : A) :=
  m & { x !-> (Some v) }.

Notation "m '&' {{ a !-> x }}" :=
  (update m a x) (at level 20).
Notation "m '&' {{ a !-> x ; b !-> y }}" :=
  (update (m & {{ a !-> x }}) b y) (at level 20).
Notation "m '&' {{ a !-> x ; b !-> y ; c !-> z }}" :=
  (update (m & {{ a !-> x ; b !-> y }}) c z) (at level 20).
Notation "m '&' {{ a !-> x ; b !-> y ; c !-> z ; d !-> t }}" :=
    (update (m & {{ a !-> x ; b !-> y ; c !-> z }}) d t) (at level 20).
Notation "m '&' {{ a !-> x ; b !-> y ; c !-> z ; d !-> t ; e !-> u }}" :=
    (update (m & {{ a !-> x ; b !-> y ; c !-> z ; d !-> t }}) e u) (at level 20).
Notation "m '&' {{ a !-> x ; b !-> y ; c !-> z ; d !-> t ; e !-> u ; f !-> v }}" :=
    (update (m & {{ a !-> x ; b !-> y ; c !-> z ; d !-> t ; e !-> u }}) f v) (at level 20).

Lemma apply_empty : forall (A: Type) (x: string),
 @empty A x = None.
Proof.
intros.
unfold empty. rewrite t_apply_empty.
trivial. Qed.

Lemma update_eq : forall A (m: partial_map A) x v,
    (m & {{ x !-> v }}) x = Some v.
Proof.
intros.
unfold update. apply t_update_eq. Qed.

Theorem update_neq : forall (X:Type) v x1 x2
                       (m : partial_map X),
  x2 <> x1 ->
  (m & {{ x2 !-> v }}) x1 = m x1.
Proof.
intros.
unfold update. apply t_update_neq. apply H. Qed.


























































