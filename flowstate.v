Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations. 
Require Import rel.
Require Import maps.
Require Import smallstep2.
Require Import typerevise. 
Require Import stlc.


Module Flow.
(* no polumophism for now  *)
(*and no pc also*)
(*no assume and where*)
(*no sealed term *)
(* | tproj : nat -> tm -> tm -> tm
  | Prodty : ty -> ty -> ty
   pair : tm -> tm -> tm
 *)

Inductive pr : Type :=
  | prin : string -> pr
  | bot: pr
  | top : pr  
  | confpr : pr -> pr
  | integpr : pr -> pr
  | andpr : pr -> pr -> pr
  | orpr : pr -> pr -> pr
  | joinpr : pr -> pr -> pr
  | meetpr : pr -> pr -> pr. 

Inductive ty : Type :=
  | Unit
  | Fail (f: ty)
  | Sumty : ty -> ty -> ty
  | Functy : ty -> ty -> ty
  | Says: pr -> pr -> ty -> ty.

Inductive tm : Type :=
  | var : string -> tm
  | unit : tm
  | fail : tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  | inj : nat -> tm -> tm
  | eta : pr -> pr -> tm -> tm
  | case : tm -> string-> tm -> tm -> tm 
  | bind  : string -> tm -> tm -> tm
  | run   : tm -> pr -> tm
  | ret   : tm -> pr -> tm
  | compEnd : tm -> tm -> tm 
  | select :  pr -> pr -> tm -> tm -> tm.

Inductive config : Type :=
  | conf : tm -> pr -> config.

Open Scope string_scope.
Definition x := "x".
Definition y := "y".
Definition z := "z".
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.
 
Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (abs x T t)
  | v_unit :
      value (unit)
  | v_fail :
      value fail
  | v_inj: forall n v,
      (value v) -> value (inj n v)
  | eta_val: forall v l j,
      (value v) -> value (eta l j v).
Hint Constructors value.

Reserved Notation 
"'[' x ':=' s ']' t" (at level 40).
Fixpoint subst (x:string) 
(s:tm) (t:tm) : tm :=
  match t with
  | var x' =>
      if beq_string x x' then s else t
  | fail => fail
  | unit => 
       unit
  | abs x' T t1 =>
      abs x' T 
     (if beq_string x x' then t1 else
     ([x:=s] t1))
  | app t1 t2 =>
      app ([x:=s] t1) ([x:=s] t2)
  | inj n t1 => inj n ([x:=s] t1)
  | eta l j t1 => eta l j ([x:=s] t1)
  | case t1 x' t2 t3 => 
      (if beq_string x x' then case t1 x' t2 t3
      else
      case ([x:=s] t1) x' ([x:=s] t2) ([x:=s] t3))
  | bind x' t1 t2 =>  
        if beq_string x x' then t else 
        bind x' ([x := s] t1) ([x := s] t2)
  | run t1 p => run ([x := s] t1) p
  | ret t1 p => ret ([x := s] t1) p
  | compEnd t1 t2 => compEnd ([x:=s] t1) ([x:=s] t2)
  | select p1 p2 t1 t2 => 
       select  p1 p2 ([x:=s] t1) ([x:=s] t2) 
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Inductive substi (s:tm) (x:string) : tm -> tm -> Prop :=
  | s_var1 :
      substi s x (var x) s
  | s_var2 : forall x', x <> x' ->  
      substi s x (var x') (var x')
  | s_fail : substi s x fail fail
  | s_unit : substi s x unit unit
  | s_abs1 : forall T t1 t1', t1 = abs x T t1' -> 
              substi s x (abs x T t1') t1
  | s_abs2 : forall x' T t1 t1', x<>x'->
    substi s x t1 t1' ->
    substi s x (abs x' T t1) (abs x' T t1')
  | s_app : forall t1 t1' t2 t2', 
       substi s x t1' t1 ->  substi s x t2' t2 ->
         substi s x (app t1' t2') (app t1 t2)
  | s_inj  : forall n t1 t1', 
        substi s x t1 t1' -> 
        substi s x (inj n t1) (inj n t1')
  | s_eta : forall l j t1 t1',
       substi s x t1 t1' ->
       substi s x (eta l j t1) (eta l j t1')
  | s_case1 :  forall t1 t2 t3,
     substi s x (case t1 x t2 t3) (case t1 x t2 t3)
  | s_case2 :  forall x' t1 t2 t3 t1' t2' t3',
     x <> x' ->
     substi s x t1 t1' -> substi s x t2 t2' 
     -> substi s x t3 t3' ->
     substi s x (case t1 x' t2 t3) (case t1' x' t2' t3')
  | s_bind1 : forall t1 t2,
       substi s x (bind x t1 t2) (bind x t1 t2)
  | s_bind2 : forall x' t1 t2 t1' t2',
      x<>x' -> substi s x t1 t1' -> 
      substi s x t2 t2' ->
      substi s x (bind x' t1 t2) (bind x' t1' t2') 
  | s_run : forall t1 t1' p,
      substi s x t1 t1' ->
      substi s x (run t1 p) (run t1' p)
  | s_ret : forall t1 t1' p,
      substi s x t1 t1' ->
      substi s x (ret t1 p) (ret t1' p)
  | s_compEnd : forall t1 t1' t2 t2',
      substi s x t1 t1' -> substi s x t2 t2' ->
      substi s x (compEnd t1 t2) (compEnd t1' t2')
  | s_select: forall p1 p2 t1 t1' t2 t2' ,
      substi s x t1 t1' -> substi s x t2 t2' ->
      substi s x (select p1 p2 t1 t2) 
                 (select p1 p2 t1' t2').

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
intros. inversion H.
Qed.

Theorem substi_correct : forall s x t t',
  [x:=s]t = t' <-> substi s x t t'.
Proof.
intros. split.
- generalize dependent t'. induction t; intros.
  + simpl in H. unfold beq_string in H.
    destruct (string_dec x0 s0) in H.
   * rewrite <- e, H. apply s_var1.
   * rewrite <- H. apply s_var2. apply n.
  + subst. simpl. apply s_unit.
  + subst. simpl. apply s_fail.
  + simpl in H.  subst. apply s_app.
    apply IHt1. reflexivity.
    apply IHt2. reflexivity.
  + simpl in H. unfold beq_string in H.
    destruct (string_dec x0 s0) in H.
    subst. apply s_abs1. reflexivity.
    subst. apply s_abs2. apply n.
    apply IHt. reflexivity.
  + simpl in H. subst. apply s_inj.
    apply IHt. reflexivity.
  + simpl in H. subst. apply s_eta.
    apply IHt. reflexivity.
  + simpl in H. unfold beq_string in H.
    destruct (string_dec x0 s0) in H.
    subst. apply s_case1. subst. 
    apply s_case2. apply n.
    apply IHt1. reflexivity.
    apply IHt2. reflexivity.
    apply IHt3. reflexivity.
  + simpl in H. unfold beq_string in H.
    destruct (string_dec x0 s0) in H.
    subst. apply s_bind1. subst.
    apply s_bind2. apply n.
    apply IHt1. reflexivity.
    apply IHt2. reflexivity.
  + simpl in H. subst. apply s_run. 
    apply IHt. reflexivity.
  + simpl in H. subst. apply s_ret. 
    apply IHt. reflexivity.
  + simpl in H. subst. apply s_compEnd.
    apply IHt1. reflexivity.
    apply IHt2. reflexivity.
  + simpl in H. subst. apply s_select.
    apply IHt1. reflexivity. 
    apply IHt2. reflexivity.
- generalize dependent t'. induction t; intros.
  + inversion H. subst. simpl. unfold beq_string.
    destruct (string_dec s0 s0). reflexivity.
    apply ex_falso_quodlibet. apply n.
    reflexivity. simpl. unfold beq_string.
    destruct (string_dec x0 s0). 
    apply ex_falso_quodlibet. rewrite e in H1.
    apply H1. reflexivity. reflexivity.
  + simpl. inversion H. reflexivity.
  + simpl. inversion H. reflexivity.
  + inversion H. subst. simpl. 
    apply IHt1 in H2. apply IHt2 in H4.
   subst. reflexivity.
  + inversion H. subst. simpl.
   unfold beq_string. 
   destruct (string_dec s0 s0). 
   reflexivity.
   apply ex_falso_quodlibet. apply n.
   reflexivity. subst. apply IHt in H5.
   rewrite <- H5. simpl. 
   unfold beq_string. 
   destruct (string_dec x0 s0).
   apply ex_falso_quodlibet. apply H4. apply e.
   reflexivity.
  + simpl. inversion H. 
    apply IHt in H3. subst. reflexivity.
  + simpl. inversion H. subst.  apply IHt in H4.
    subst. reflexivity.
  + simpl. inversion H. unfold beq_string.
    destruct (string_dec s0 s0). reflexivity.
    apply ex_falso_quodlibet. apply n. 
    reflexivity. unfold beq_string.
    destruct (string_dec x0 s0). rewrite e in H4.
    apply ex_falso_quodlibet. apply H4.
    reflexivity. apply IHt1 in H6. 
    apply IHt2 in H7. apply IHt3 in H8.
    subst. reflexivity.
  + simpl. inversion H. unfold beq_string.
    destruct (string_dec s0 s0). reflexivity.
    apply ex_falso_quodlibet. apply n.
    reflexivity. unfold beq_string.
    destruct (string_dec x0 s0). 
    rewrite e in H3. apply ex_falso_quodlibet.
    apply H3. reflexivity.
    apply IHt1 in H5. apply IHt2 in H6.
    subst. reflexivity.
  + simpl. inversion H. apply IHt in H3.
    subst. reflexivity.
  + simpl. inversion H. apply IHt in H3.
    subst. reflexivity.
  + simpl. inversion H. apply IHt1 in H2.
    apply IHt2 in H4. subst. reflexivity.
  + simpl. inversion H. apply IHt1 in H5.
    apply IHt2 in H6. subst. reflexivity.
Qed.


Reserved Notation " t '==>' n " 
(at level 50, left associativity).

Inductive floweval : tm ->tm ->Prop :=
  | E_Inj1 : forall t1 v,
        t1 ==> v ->
        inj 1 t1 ==> inj 1 v
  | E_Inj2 : forall t2 v,
        t2 ==> v ->
        inj 2 t2 ==> inj 2 v 
  | E_Eta : forall l j t1 v,
       t1 ==> v ->
       eta l j t1 ==> eta l j v
  | E_App : forall x T t2 v2 t12,
         t2 ==> v2 ->
         (app (abs x T t12) t2) ==> [x:=v2]t12
  | E_Case1 : forall t1 x v t2 t3,
       t1 ==> inj 1 v -> 
      case t1 x t2 t3 ==> [x:=v] t2
  | E_Case2 : forall t1 x v t2 t3,
       t1 ==> inj 2 v -> 
      case t1 x t2 t3 ==> [x:=v] t3
  | E_Bind1 : forall t1 t2 x v1 v l j,
       t1 ==> v1 -> 
       value v -> v1 = eta l j v ->
       bind x t1 t2 ==> [x:=v]t2
  | E_Run : forall t1 p t1' c v,
      value v ->
      ret t1 c ==> ret v c ->
      run t1 p ==> run t1' p
  | E_Ret : forall t1 p v,
      t1 ==> v ->
      ret t1 p ==> ret v p
  | E_CompEnd1 : forall t1 t2 l1 l2 j1 j2 v1 v2 v,
      t1 ==> v1 -> t2 ==> v2 ->
      v1 = eta l1 j1 v -> v2 = eta l2 j2 v ->
      compEnd t1 t2 ==> eta (andpr l1 l2 ) (andpr j1 j2) v
  | E_Select1 : forall v t1 t2 v1 p1 p2 l j,
      t1 ==> v1 -> t2 ==> fail -> 
      v1 = eta l j v  ->
      select p1 p2 t1 t2 ==> eta p1 p2 v
  | E_Select2 : forall v t1 t2 v2 p1 p2 l j,
      t1 ==> fail -> t2 ==> v2 -> v2 = eta l j v ->
      select p1 p2 t1 t2 ==> eta p1 p2 v
where "t1 '==>' t2" := (floweval t1 t2).

Reserved Notation 
"t1 '-->' t2" (at level 40).
(* ,  c1 at level 0,
t2 at level 40, c2 at level 12). 
 *)
Inductive flowstep : config -> config ->Prop :=
  | ST_Inj1 : forall t1 t1' c,
        conf t1 c  --> conf t1'  c ->
        conf (inj 1 t1)  c --> conf (inj 1 t1')  c
  | ST_Inj2 : forall t2 t2' c,
        conf t2  c --> conf t2'  c ->
        conf (inj 2 t2)  c --> conf (inj 2 t2')  c
  | ST_Eta : forall l j t1 t1' c,
       conf t1 c --> conf t1' c ->
       conf (eta l j t1) c --> conf (eta l j t1') c
  | ST_AppAbs : forall x T t12 v2 c,
         value v2 ->
         conf (app (abs x T t12) v2) c --> conf ([x := v2]t12)  c
  | ST_App1 : forall t1 t1' t2 c,
         conf t1 c --> conf t1' c ->
         conf (app t1 t2) c--> conf (app t1' t2) c
  | ST_App2 : forall v1 t2 t2' c,
         value v1 ->
         conf t2 c --> conf t2' c ->
         conf (app v1 t2) c --> conf (app v1 t2') c
  | ST_Case1 : forall t1 x v t2 t3 c,
       (value v) -> t1 = inj 1 v ->
      conf (case t1 x t2 t3) c --> conf ([x:=v] t2) c
  | ST_Case2 : forall t1 x v t2 t3 c,
       (value v) -> t1 = inj 2 v ->
      conf (case t1 x t2 t3) c --> conf ([x:=v] t3) c
  | ST_Case : forall t1 t1' x t2 t3 c,
      conf t1 c--> conf t1' c ->
      conf (case t1 x t2 t3) c --> conf (case t1' x t2 t3) c
  | ST_Bind1 : forall t1 t1' t2 x c,
       conf t1 c --> conf t1' c ->
       conf (bind x t1 t2) c --> conf (bind x t1' t2) c
  | ST_Bind2 : forall t1 t2 v x l j c,
       value t1 -> t1 = eta l j v ->
       conf (bind x t1 t2) c --> conf ([x:=v] t2) c
  | ST_Run1 : forall t1 p c,
      conf (run t1 p) c --> conf (ret t1 c) p
  (* | ST_Run2 : forall p c v,
      value v ->
      conf (run v p) c --> conf v c *)
  | ST_Ret1 : forall t1 p t1' c,
      conf t1 p --> conf t1' p ->
      conf (ret t1 c) p --> conf (ret t1' c) p
  | ST_Ret2 : forall p v c,
      value v ->
      conf (ret v c) p --> conf v c
  | ST_CompEnd1 : forall t1 t1' t2 c,
      conf t1 c --> conf t1' c ->
      conf (compEnd t1 t2) c --> conf (compEnd t1' t2) c
  | ST_CompEnd2 : forall v t2 t2' c,
      value v -> conf t2 c --> conf t2' c -> 
      conf (compEnd v t2) c --> conf (compEnd v t2') c
  | ST_Select1 : forall t1 t1' t2 p1 p2 c,
      conf t1 c --> conf t1' c ->
      conf (select p1 p2 t1 t2) c --> 
      conf (select p1 p2 t1' t2) c
  | ST_Select2 : forall v t2 t2' p1 p2 c,
      value v -> conf t2 c --> conf t2' c -> 
      conf (select p1 p2 v t2) c 
      --> conf (select p1 p2 v t2') c
where "t1 '-->' t2 " := (flowstep t1 t2).


Hint Constructors flowstep.
Notation multistep := (multi flowstep).
Notation "t1 -->*' t2" := 
(multistep t1 t2) (at level 110).


Lemma val_nostep : forall v c,
value v -> ~ exists t, conf v c --> conf t c.
Proof. 
intros. unfold not.
intros. induction H.
 - inversion H0; subst. inversion H.
- inversion H0; subst; inversion H.
- inversion H0; subst. inversion H.
- apply IHvalue. inversion H0. inversion H1.
subst. exists t1'. apply H3. subst. exists t2'.
apply H3.
- apply IHvalue. inversion H0. inversion H1.
subst. exists t1'. apply H3.
Qed.

Lemma inj_same_val:  forall n v1 v2,
inj n v1 = inj n v2 -> v1 = v2.
Proof.
intros. inversion H. reflexivity.
Qed.
 
(* Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.
 *)
Lemma same_term: forall t t' c,
conf t c = conf t' c -> t = t'.
Proof.
intros.
inversion H. reflexivity.
Qed.


Theorem step_deterministic:
  deterministic flowstep.
Proof.
unfold deterministic.
intros. generalize dependent y2.
induction H; intros. 
- inversion H0. subst.
apply IHflowstep in H4. 
apply same_term in H4. subst. reflexivity. 
- inversion H0. subst. 
  apply IHflowstep in H4. subst. 
apply same_term in H4. subst. reflexivity.
- inversion H0. subst. apply IHflowstep in H6.
apply same_term in H6. subst. reflexivity.
- inversion H0. 
  + reflexivity.
  + subst. inversion H5.
  + subst. 
 assert (G: ~ exists t, conf v2 c --> conf t c).
      { apply val_nostep. apply H. }
     unfold not in G. 
     apply ex_falso_quodlibet.
     apply G. exists t2'. apply H6. 
- inversion H0. 
  + subst. inversion H.
  + subst. apply IHflowstep in H5.
  apply same_term in H5. subst. reflexivity.
  + subst. assert (G: ~ exists t, conf t1 c --> conf t c).
      { apply val_nostep. apply H5. }
     unfold not in G. 
     apply ex_falso_quodlibet.
     apply G. exists t1'. apply H.
- inversion H1. 
   + subst. assert (G: ~ exists t, conf t2 c --> conf t c).
      { apply val_nostep. apply H6. }
     unfold not in G. 
     apply ex_falso_quodlibet.
     apply G. exists t2'. apply H0.
  + subst. assert (G: ~ exists t, conf v1 c --> conf t c).
      { apply val_nostep. apply H. }
     unfold not in G. 
     apply ex_falso_quodlibet.
     apply G. exists t1'. apply H6.
  + subst. apply IHflowstep in H7. 
    apply same_term in H7. subst. reflexivity.
- inversion H1.
   + subst. apply inj_same_val in H9.
     rewrite H9. reflexivity.
   + subst. inversion H9.
   + subst. 
   assert (G: ~ exists t, conf (inj 1 v) c --> conf t c).
      { apply val_nostep. apply v_inj. apply H. }
     unfold not in G. 
     apply ex_falso_quodlibet.
     apply G. exists t1'. apply H8.
- inversion H1. 
  + subst. inversion H9.
  + subst. apply inj_same_val in H9. rewrite H9.
    reflexivity.
  + subst. assert (G: ~ exists t, conf (inj 2 v) c --> conf t c).
      { apply val_nostep. apply v_inj. apply H. }
     unfold not in G. 
     apply ex_falso_quodlibet.
     apply G. exists t1'. apply H8.
- inversion H0. 
  + subst. 
    assert (G: ~ exists t, conf (inj 1 v) c --> conf t c).
      { apply val_nostep. apply v_inj. apply H7. }
     unfold not in G. 
     apply ex_falso_quodlibet.
     apply G. exists t1'. apply H.
  + subst. assert (G: ~ exists t, conf (inj 2 v) c --> conf t c).
      { apply val_nostep. apply v_inj. apply H7. }
     unfold not in G. 
     apply ex_falso_quodlibet.
     apply G. exists t1'. apply H.
  + subst. apply IHflowstep in H7. 
apply same_term in H7. subst. reflexivity.
- inversion H0. 
  + subst. apply IHflowstep in H6. apply same_term in H6.
    subst. reflexivity.
  + subst. assert (G: ~ exists t, conf (eta l j v) c --> conf t c).
      { apply val_nostep. apply H6. }
     unfold not in G. 
     apply ex_falso_quodlibet.
     apply G. exists t1'. apply H.
- inversion H1. 
  + subst. 
  assert (G: ~ exists t, conf (eta l j v) c --> conf t c).
      { apply val_nostep. apply H. }
     unfold not in G. 
     apply ex_falso_quodlibet.
     apply G. exists t1'. apply H7.
  + subst. inversion H8. reflexivity.
- inversion H0. 
  + subst. reflexivity.
- inversion H0. 
  + subst. apply IHflowstep in H5.
  apply same_term in H5. subst. reflexivity.
  + subst. assert (G: ~ exists t, conf t1 p --> conf t p).
      { apply val_nostep. apply H5. }
     unfold not in G. 
     apply ex_falso_quodlibet.
     apply G. exists t1'. apply H.
- inversion H0. 
  + subst. assert (G: ~ exists t, conf v p --> conf t p).
      { apply val_nostep. apply H. }
     unfold not in G. 
     apply ex_falso_quodlibet.
     apply G. exists t1'. apply H5.
  + reflexivity.
- inversion H0.
  + subst. apply IHflowstep in H5. apply same_term in H5.
    subst. reflexivity.
  + subst. assert (G: ~ exists t, conf t1 c --> conf t c).
      { apply val_nostep. apply H5. }
     unfold not in G. 
     apply ex_falso_quodlibet.
     apply G. exists t1'. apply H.
- inversion H1. 
  + subst. assert (G: ~ exists t, conf v c --> conf t c).
      { apply val_nostep. apply H. }
     unfold not in G. 
     apply ex_falso_quodlibet.
     apply G. exists t1'. apply H6.
   + subst. apply IHflowstep in H7. apply same_term in H7. subst.
     reflexivity.
- inversion H0. 
  + subst. apply IHflowstep in H7. apply same_term in H7.
    subst. reflexivity.
  + subst. assert (G: ~ exists t, conf t1 c --> conf t c).
      { apply val_nostep. apply H7. }
     unfold not in G. 
     apply ex_falso_quodlibet.
     apply G. exists t1'. apply H.
- inversion H1. 
  + subst. assert (G: ~ exists t, conf v c --> conf t c).
      { apply val_nostep. apply H. }
     unfold not in G. 
     apply ex_falso_quodlibet.
     apply G. exists t1'. apply H8.
   + subst. apply IHflowstep in H9. apply same_term in H9.
     subst. reflexivity. 
Qed.

Inductive pt : Type :=
  | prpr : pr -> pt
  | tyty : ty -> pt.


Fixpoint J (t: ty) : pr :=
  match t with
   | Unit => bot
   | Fail f => bot
   | Sumty  t1 t2 => joinpr (J t1) (J t2)
   | Functy t1 t2 => joinpr (J t1) (J t2) 
   | Says l j t => j
  end.

Definition flowsto_map (A:Type) := pr -> A.
Definition flow_empty {A:Type} (v : A) : flowsto_map A :=
  (fun _ => v).
Definition partial_flow_map (A:Type) := 
flowsto_map (option A).
Definition fempty {A:Type} : partial_flow_map A :=
  flow_empty None.

Definition del := partial_flow_map pt.

Reserved Notation "D '|-' p1 'F' p2"  (at level 40). 
Inductive flowsto : del -> pr -> pt -> Prop :=
  | F_true : forall D p1 p2,
      D p1 = Some p2 -> flowsto D p1 p2
  | F_Ty : forall D p1 t1 l j t,
     t1 = Says l j t -> flowsto D p1 (prpr l) -> 
     flowsto D p1 (tyty t1)
 where "D '|-' p1 'F' p2" := (flowsto D p1 p2).


Definition context := partial_map ty.

Inductive has_type : 
context -> del -> tm -> ty -> Prop :=
  | T_Var : forall G D x T,
      G x = Some T ->
      has_type G D (var x) T.

      (*  Gamma ; D |- var x in T  *)
  | T_Unit : forall Gamma D,
       (has_type Gamma D unit Unit) 
     (*  Gamma ; D |- unit in Unit  *)
  | T_Fail : forall Gamma D f,
       (has_type Gamma D fail (Fail f)) 
  | T_Abs : forall Gamma D x T11 T12 t12,
 (has_type (t_update Gamma x T11) D t12 T12) ->
 ( has_type Gamma D (abs x T11 t12) 
(Functy T11 T12))
  | T_Inj : forall Gamma D n T1 T2 t1,
     (has_type Gamma D t1 T1) \/
     (has_type Gamma D t1 T2) ->
     (has_type Gamma D (inj n t1) (Sumty T1 T2))
  | T_App : forall T11 T12 Gamma D t1 t2,
     (has_type Gamma D t1 (Functy T11 T12)) ->
     (has_type Gamma D t2 T11) ->
     (has_type Gamma D (app t1 t2) T12)
  | T_Eta : forall Gamma D l j t1 T,
     (has_type Gamma D t1 T) -> (flowsto D (J T) (prpr l)) ->
     (has_type Gamma D (eta l j t1) (Says l j T))
  | T_Case : forall t1 x t2 t3 T T1 T2 Gamma D,
       (has_type Gamma D t1 (Sumty T1 T2)) ->
       (has_type (t_update Gamma x T1) D t2 T) ->
       (has_type (t_update Gamma x T2) D t3 T) ->
       (has_type Gamma D (case t1 x t2 t3) T)
  | T_Bind : forall x t1 t2 l j  T1 T2 Gamma D,
      (has_type Gamma D t1 (Says l j T1)) ->
      (has_type (t_update Gamma x T1) D t2 T2) ->
       flowsto D j (prpr (J T2)) ->  
       flowsto D l (tyty T2)  ->
      (has_type Gamma D (bind x t1 t2) T2) 
  | T_run : forall Gamma D t1 p T1,
     (has_type Gamma D t1 T1) ->
     (has_type Gamma D (run t1 p) T1)
  | T_ret : forall Gamma D t1 p T1,
     (has_type Gamma D t1 T1) ->
     (has_type Gamma D (ret t1 p) T1)
  | T_CompEnd : forall Gamma D t1 t2 T j1 j2 l1 l2 l j ,
     has_type Gamma D t1 (Says l1 j1 T) ->
     has_type Gamma D t2 (Says l2 j2 T)->
     l = andpr l1 l2 ->
     j = andpr j1 j2 ->
     has_type Gamma D (compEnd t1 t2) (Says l j T)
  | T_Select : forall Gamma D t1 t2 p1 p2 T j1 j2 l1 l2 ,
     has_type Gamma D t1 (Says l1 j1 T) ->
     has_type Gamma D t2 (Says l2 j2 T) ->
     p1 = orpr l1 l2 -> 
     p2 = joinpr j1 j2 ->
     has_type Gamma D (select p1 p2 t1 t2) (Says p1 p2 T).

(*where "Gamma ';' D '|-' t 'in' T" 
:= (has_type Gamma D t T). *)


 
  
Hint Constructors has_type. 

Lemma canonical_forms_unit : forall t,
  has_type t_empty fempty t Unit ->
  value t -> t = unit.
Proof.
intros. inversion H0;subst.
- inversion H.
- reflexivity.
- inversion H.
- inversion H.
- inversion H.
Qed. 

Lemma canonical_forms_fail : forall t,
  empty ; fempty |- t in Fail ->
  value t -> t = fail.
Proof.
intros. inversion H0;subst.
- inversion H.
- inversion H.
- reflexivity.
- inversion H.
- inversion H.
Qed.

Lemma canonical_forms_inj : forall t T1 T2,
  empty ; fempty |- t in  Sumty T1 T2->
  value t -> exists n v, (value v /\ t = inj n v).
Proof.
intros. inversion H0;subst.
- inversion H.
- inversion H.
- inversion H.
- exists n, v. split. apply H1. reflexivity.
- inversion H.
Qed.

Lemma canonical_forms_eta : forall t T l j,
  empty ; fempty |- t in  Says l j T->
  value t -> exists v, (value v /\ t = eta l j v).
Proof.
intros. inversion H0;subst.
- inversion H.
- inversion H.
- inversion H.
- inversion H.
- exists v. split. apply H1.
inversion H. reflexivity.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty ; fempty |- t in (Functy T1 T2) ->
  value t ->
  exists x u, t = abs x T1 u.
Proof.
intros. inversion H0; subst.
- inversion H. subst. exists x0,t0.
reflexivity.
- inversion H.
- inversion H.
- inversion H.
- inversion H.
Qed.




big_step 
val_nostep    
Types (not complete yet)
progress
preservation
l protects t proof

(* 
Theorem pc_reduction : 
forall t G D c pc pcm T,
  has_type G D c pc t T -> flowsto D pcm pc ->
  actsfor D c pcm ->
  has_type G D c pcm t T.
Proof.
intros.  
(* generalize dependent pc'. *)
induction H.
- apply T_Var. apply H. 
apply H1.
- apply T_Unit. apply H1.
- apply T_Fail. apply H1.
- apply T_Abs with c'. 
apply H. apply H1.
- apply T_Inj1. 
apply IHhas_type.
apply H0. apply H1. apply H1.
- apply T_Inj2. 
apply IHhas_type.
apply H0. apply H1. apply H1.
- apply T_App with T11 pc'.
apply IHhas_type1. apply H0.
apply H1. apply IHhas_type2.
apply H0. apply H1. apply H1.
apply transitive_flowsto with pc0.
apply H0. apply H4.
- apply T_Eta. 
apply IHhas_type.
apply H0. apply H1. apply H2. apply H1.
- apply T_Case with T1 T2. 
apply IHhas_type1. apply H0. apply H1.
apply IHhas_type2. apply H0. apply H1.
apply IHhas_type3. apply H0. apply H1.
apply H1.
- apply T_Bind with l j T1. 
apply IHhas_type1. apply H0. apply H1.
apply l j *)

(* Lemma run_pc_reduction :
forall c c' pc pc' t G D T,
 flowsto D pc' pc ->
actsfor D c pc' -> has_type G D c pc (run t c') T
-> has_type G D c pc' (run t c') T.
Proof.
intros. induction H1; subst.
- apply T_Var. apply H1. apply H0.
- apply T_Unit. apply H0.
- apply T_Fail. apply H0.
- apply T_Abs with c'0. apply H1.
apply H0. 
- apply T_Inj1. apply IHhas_type.
apply H. apply H0. apply H0.
- apply T_Inj2. apply IHhas_type.
apply H. apply H0. apply H0.
- apply T_App with T11 pc'0. 
apply IHhas_type1. apply H.
apply H0. apply IHhas_type2.
apply H. apply H0. apply H0.
apply transitive_flowsto with pc0.
apply H. apply H2.
- apply T_Eta. apply IHhas_type. apply H.
apply H0. apply H2. apply H0.
- intros. apply T_Case with T1 T2. 
apply IHhas_type1. apply H. apply H0.
apply IHhas_type2. apply H. apply H0.
apply IHhas_type3. apply H. apply H0.
apply H0. 
- intros. 
assert (E: actsfor D c (joinpr (joinpr l j) pc0)).
{ apply clearance in H1_0. apply H1_0. }
 apply T_Bind with l j T1. 
apply IHhas_type1. apply H. apply H0.
eapply IHhas_type2. eapply flowsto_join.
apply H4. 
apply actsfor_joinr in E. 
destruct E as [E1 E2].
apply actsfor_joinf. apply E1. apply H5.

apply H1. apply H2. apply H5. *)








