Set Warnings "-notation-overridden,-parsing".
Require Import maps.
Require Import typerevise.
Require Import stlc.
Require Import smallstep2.
Module STLCProp.
Import STLC.

Lemma canonical_forms_bool : forall t,
  empty |- t in TBool ->
  value t ->
  (t = ttrue) \/ (t = tfalse).
Proof.
intros t HT HVal.
inversion HVal ; intros; subst.
try inversion HT. auto. auto.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t in (TArrow T1 T2) ->
  value t ->
  exists x u, t = tabs x T1 u.
Proof.
intros.
inversion H0; intros; subst;
try inversion H; subst; auto.
exists x0. exists t0. reflexivity.
Qed.

Theorem progress : forall t T,
  empty |- t in T ->
  value t \/ exists t', t --> t'.
Proof with eauto.
intros t T Ht. 
remember (@empty ty) as Gamma.
induction Ht; subst Gamma...
- inversion H.
- right. destruct IHHt1...
 + destruct IHHt2...
   * assert (exists x0 t0, 
t1 = tabs x0 T11 t0).
eapply canonical_forms_fun; eauto.
destruct H1 as [x0 [t0 Heq]]. subst.
    exists ([x0:=t2]t0)...
   * inversion H0 as [t2' Hstp]. 
exists (tapp t1 t2')...
    + (* t1 steps *)
      inversion H as [t1' Hstp]. 
exists (tapp t1' t2)...
  - (* T_If *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct (canonical_forms_bool t1); subst; eauto.
    + (* t1 also steps *)
      inversion H as [t1' Hstp]. exists (tif t1' t2 t3)...
Qed.

(* start from free occurences *)

Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tapp t1 t2)
  | afi_abs : forall x y T11 t12,
      y <> x ->
      appears_free_in x t12 ->
      appears_free_in x (tabs y T11 t12)
  | afi_if1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (tif t1 t2 t3)
  | afi_if2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (tif t1 t2 t3)
  | afi_if3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (tif t1 t2 t3).
Hint Constructors appears_free_in.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

Definition manual_grade_for_afi : option (prod nat string) := None.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t in T ->
   exists T', Gamma x = Some T'.
Proof.
intros x t T Gamma H H0. 
generalize dependent Gamma.
  generalize dependent T.
  induction H;
  intros; 
try solve 
[inversion H0; eauto].
  - (* afi_abs *)
    inversion H1; subst.
    apply IHappears_free_in in H7.
    rewrite update_neq in H7; 
assumption.
Qed.









