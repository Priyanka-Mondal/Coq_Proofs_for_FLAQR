Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations. 
Require Import maps.
Require Import smallstep2.
Require Import typerevise. 
Require Import stlc.

Module STLCProp.
Import STLC.

Lemma canonical_forms_bool : forall t,
  empty |- t in TBool ->
  value t ->
  (t = ttrue) \/ (t = tfalse).
Proof.
intros. inversion H0.
- subst. inversion H.
- left. reflexivity.
- right. reflexivity.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t in (TArrow T1 T2) ->
  value t ->
  exists x u, t = tabs x T1 u.
Proof.
intros. inversion H0.
- subst. inversion H.
exists x0. exists t0.
reflexivity.
- subst. inversion H.
- subst. inversion H.
Qed.

Theorem progress : forall t T,
  empty |- t in T ->
  value t \/ exists t', t --> t'.
Proof.
intros.
remember (@empty ty) as Gamma. 
induction H; subst ...
- inversion H.
- left. apply v_abs.
- right. destruct IHhas_type1. reflexivity.
  + destruct IHhas_type2. reflexivity.
assert (exists x0 t, t1 = tabs x0 T11 t). 
eapply canonical_forms_fun. eapply H.
apply H1. destruct H3 as [x00 [t0 Heq]].
  exists (subst x00 t2 t0). rewrite  Heq. 
  apply ST_AppAbs.
  apply H2. inversion H2.
  exists (tapp t1 x0). apply ST_App2.
  apply H1. apply H3. 
 + inversion H1. exists (tapp x0 t2).
   apply ST_App1. apply H2.
- left. apply v_true.
- left. apply v_false.
- destruct IHhas_type1 as [v |I].
 + reflexivity.
 + destruct (canonical_forms_bool t1).
   apply H. apply v. right. subst. 
   exists t2.
   apply ST_IfTrue.
   subst. right. exists t3. apply ST_IfFalse.
 + right. inversion I. exists (tif x0 t2 t3).
   apply ST_If. apply H2.
Qed.

Theorem progress' : forall t T,
     empty |- t in T ->
     value t \/ exists t', t --> t'.
Proof.
  intros t. induction t; intros T Ht; auto.
  + left. inversion Ht. subst. inversion H1.
  + right. inversion Ht. subst.
    assert (H22: empty |- t1 in TArrow T11 T).
    apply H2.  
    apply IHt1 in H2. destruct H2 as [A|B].
    apply IHt2 in H4. destruct H4 as [C|D].
    assert (exists x t, t1 = tabs x T11 t). 
eapply canonical_forms_fun. eapply H22.
apply A. destruct H as [x [t Heq]].
subst. exists (subst x t2 t).
    apply ST_AppAbs. apply C.
inversion D. exists (tapp t1 x0).
apply ST_App2. apply A. apply H. 
inversion B. exists (tapp x0 t2).
apply ST_App1. apply H.
 + right. inversion Ht. subst. 
   assert (H33: empty |- t1 in TBool).
   apply H3. 
   apply IHt1 in H3. 
   destruct H3 as [A|B].
   destruct (canonical_forms_bool t1).
   apply H33. apply A. subst.
   exists t2. apply ST_IfTrue.
   subst. exists t3. apply ST_IfFalse.
   inversion B. exists (tif x0 t2 t3).
   apply ST_If. apply H.
Qed.

Inductive appears_free_in : 
string -> tm -> Prop :=
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

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t in T ->
   exists T', Gamma x = Some T'.
Proof.
intros. generalize dependent Gamma. 
generalize dependent T.
induction H;intros.
- inversion H0. subst. exists T. apply H2.
- inversion H0. subst. 
  apply IHappears_free_in in H4. 
  apply H4.
- inversion H0. subst. 
  apply IHappears_free_in in H6. 
  apply H6.
- inversion H1. subst. 
  apply IHappears_free_in in H7. 
    rewrite update_neq in H7.
  apply H7. apply H.
- inversion H0. subst. 
  apply IHappears_free_in in H5.
  apply H5.
- inversion H0. subst. 
  apply IHappears_free_in in H7.
  apply H7.
- inversion H0. subst. 
  apply IHappears_free_in in H8.
  apply H8.
Qed.

(* Corollary typable_empty__closed : forall t T,
    empty |- t in T ->
    closed t.
Proof.
intros. unfold closed; intros.  
inversion H. 
- inversion H0.
- subst.  inversion H0.
  +  
   rewrite update_neq in H4.  *)



















