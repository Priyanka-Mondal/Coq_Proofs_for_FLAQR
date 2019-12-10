Set Warnings "-notation-overridden,-parsing".
Require Export logic.
Require Coq.omega.Omega.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.
Lemma double_plus : forall n, double n = n + n.
  Proof.
Admitted.

Theorem ev_double : forall n,
  ev (double n).
Proof.
Admitted.
(** intros.
induction n.
-  apply ev_0.
- rewrite double_plus in IHn. unfold double. simpl.
  rewrite plus_comm. simpl. apply ev_SS. apply IHn.
Qed.
**)

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'. Qed.

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
intros. inversion H.
apply H1. Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. inversion H. Qed.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
intros. inversion H. inversion H1. apply H3. Qed.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
intros. inversion H. inversion H1. inversion H3. Qed.

Lemma ev_even_firsttry : forall n,
  ev n -> exists k, n = double k.
Proof.
intros.
inversion H.
- exists 0. reflexivity.
-(** assert (I : exists k', n' = double k' ->
                exists k, (S (S n')) = double k).
    { intros [k' Hk']. rewrite Hk'. exists (S k'). reflexivity. }
   apply I.**)
Admitted.

Lemma doublenum : forall n,
double n = n + n.
Proof.
Admitted.
 

Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.
Admitted.
(** 
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists(S k'). simpl. rewrite plus_comm. simpl. 
    symmetry. rewrite doublenum. reflexivity.
Qed.
**)

Theorem ev_even_iff : forall n,
  ev n <-> exists k, n = double k.
Proof.
intros.
split.
- apply ev_even.
- intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
intros.
induction H as [| n' En' EIHn' ].
- simpl. apply H0.
- apply ev_SS. apply EIHn'.
Qed. 

Theorem ev_ev_ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
intros.
induction H0.
- simpl in H. apply H.
- simpl in H. inversion H.
  + apply IHev. apply H2.
Qed.

Lemma plus00 : forall n m,
m+n = 0 -> m =0 /\ n= 0.
Proof.
Admitted.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
intros n m p Enm Enp.
apply ev_sum with (n:= n+m) (m:= n+p) in Enm.
replace (n+m +(n+p)) with ((n+n)+(m+p)) in Enm.
replace (n+n) with (double n) in Enm.
apply ev_ev_ev with (m:= m+p) in Enm.
apply Enm.
replace (double n+ (m+p)+(m+p)) with (double n + double (m+p)).
apply ev_sum.
apply ev_double.
apply ev_double.
rewrite double_plus with (n:=m+p).
rewrite plus_assoc. reflexivity.
rewrite double_plus. reflexivity.
rewrite <- plus_assoc.
replace (n+(m+p)) with (m+(n+p)).
rewrite plus_assoc.
reflexivity.
rewrite plus_assoc.
rewrite ( plus_comm m n).
rewrite <- plus_assoc. reflexivity.
apply Enp.
Qed.

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n. Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
intros.
inversion H. inversion H2. Qed.

Definition relation (X:Type) := X -> X -> Prop.
Definition reflexive {X:Type} (R: relation X) :=
	forall a : X, R a a.
Definition transitive {X:Type} (R: relation X) :=
forall n m o : X, (R n m) -> (R m o) -> (R n o).

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
intros m n o Hnm Hno.
  induction Hno.
  - apply Hnm.
  - apply le_S. apply IHHno. apply Hnm. Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
intros.
induction n.
- apply le_n.
- apply le_S. apply IHn.
Qed.

Lemma nleSn : forall n,
n<= S n.
Proof.
Admitted.

Lemma nlessSm : forall n m,
n<=m -> n <= S m.
Proof.
Admitted.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros. induction H.
  apply le_n.
  apply le_S. apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
intros. inversion H.
- apply le_n.
- apply le_trans with (n := S n). apply nleSn.
 apply H2. Qed.


Lemma plusO : forall n,
n+0 = n.
Proof.
Admitted.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
intros.
induction b.
- rewrite plusO. apply le_n.
- rewrite plus_comm. simpl. apply le_S.
rewrite plus_comm. apply IHb.
Qed.

Definition lt (n m:nat) := le (S n) m.
Notation "m < n" := (lt m n).

Lemma O_lt_n : forall n,
  0 < n.
Proof.
Admitted.
Lemma lessS : forall n m,
 n <= m ->  n <= S m.
Proof.
Admitted.

Lemma nleqn : forall n,
n<= n.
Proof.
Admitted.
Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
unfold lt.
Admitted.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
intros.
inversion H.
- unfold lt. apply le_S. apply nleqn.
- unfold lt. apply le_S. apply lessS in H0. apply H0.
Qed.

Inductive reg_exp {T : Type} : Type :=
| EmptySet : reg_exp
| EmptyStr : reg_exp
| Char : T -> reg_exp
| App : reg_exp -> reg_exp -> reg_exp
| Union : reg_exp -> reg_exp -> reg_exp
| Star : reg_exp -> reg_exp.

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar : forall x, exp_match [x] (Char x)
| MApp : forall s1 re1 s2 re2,
           exp_match s1 re1 ->
           exp_match s2 re2 ->
           exp_match (s1 ++ s2) (App re1 re2)
| MUnionL : forall s1 re1 re2,
              exp_match s1 re1 ->
              exp_match s1 (Union re1 re2)
| MUnionR : forall re1 s2 re2,
              exp_match s2 re2 ->
              exp_match s2 (Union re1 re2)
| MStar0 : forall re, exp_match [] (Star re)
| MStarApp : forall s1 s2 re,
               exp_match s1 re ->
               exp_match s2 (Star re) ->
               exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
apply (MApp [1] _ [2]).
- apply MChar.
- apply MChar.
Qed.

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

Fixpoint reg_exp_of_list {T: Type} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
simpl. apply ( MApp [1]). apply MChar. apply ( MApp [2]).
apply MChar. apply ( MApp [3]). apply MChar. apply MEmpty.
Qed.

Lemma MStar1 :
  forall T s (re : @reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
intros.
rewrite <- (app_nil_r T s).
apply (MStarApp s [] re).
apply H. apply MStar0.
Qed.

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
intros.
induction s.
- unfold not.
intros.
inversion H.
Admitted.

Lemma MUnion' : forall T (s : list T) (re1 re2 : @reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
intros.
inversion H.
- apply MUnionL. apply H0.
- apply MUnionR. apply H0.
Qed.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
intros.
Admitted.

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
intros.
unfold iff.
split.
- intros. 
Admitted.

Fixpoint re_chars {T} (re : reg_exp) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.
Lemma equalrelist : forall T (s : list T) (re : reg_exp),
 s =~ re -> s = (re_chars re).
Proof.
Admitted.

Theorem in_re_match : forall T (s : list T) (re : reg_exp) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
(**intros. apply equalrelist in H. rewrite <- H. apply H0.**)
intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *)
    apply Hin.
  - (* MChar *)
    apply Hin.
  - simpl. rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
- (* MStarApp *)
    simpl. rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.



 








































































 