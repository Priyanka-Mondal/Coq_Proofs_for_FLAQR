Set Warnings "-notation-overridden,-parsing".
Require Export list.

Inductive list (X:Type) :Type :=
| nil : list X
| cons : X -> list X -> list X.

Fixpoint equal (n1 n2 : nat) : bool :=
match n1 with
| O => match n2 with
      | O => true
      | _ => false
      end
| S n1' => match n2 with 
          | O => false
          | S n2' => equal n1' n2'
          end
end.

Fixpoint repeat (X: Type) (x: X) (t: nat) : list X :=
match t with 
| O => nil X
| S t' => cons X x (repeat X x t')
end.

Arguments nil {X}.
Arguments cons {X} _ _.

Fixpoint repeat' {X : Type} (x : X) (t : nat) : list X :=
  match t with
  | 0 => nil
  | S t' => cons x (repeat' x t')
  end.

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
match l with
| nil => l
| cons h t => app (rev t) (cons h nil)
end.

Fixpoint length {X : Type} (l : list X) : nat :=
match l with
| nil => O
| cons h t => S (length t)
end.

Example test_rev1 :
  length (cons 1 (cons 2 nil)) = S(S O).
Proof. reflexivity. Qed.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity). 

Theorem nil_app : forall X:Type, forall l:list X, 
  app [] l = l.
Proof.
  intros X l.
  simpl.
  reflexivity.
Qed.

Theorem appl : forall X:Type, forall h:X , forall t:list X, 
  h::t = [h] ++ t.
Proof.
  intros X h t.
  induction t as [ |h1 t1 IH].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
 

Theorem app_nil_r : forall (X:Type), forall l:list X,
  app l [] = l.
Proof.
intros X l.
simpl.
induction l as [| h t IH].
- simpl. reflexivity.
- rewrite appl. simpl. rewrite appl. rewrite IH. simpl. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
intros A l m n.
induction l as [| h t IH].
- simpl. reflexivity.
- simpl. rewrite IH. reflexivity.
Qed.


Inductive option (X:Type) : Type :=
| Some : X -> option X
| None : option X.

Arguments Some {X} _.
Arguments None {X}.

Definition hd_error {X : Type} (l : list X) : option X :=
match l with
| [] => None
| h :: t => Some h
end.

Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof.
simpl. reflexivity. Qed.

Definition doit3times { X: Type } (f:X->X) (n:X) : X :=
f (f (f n)).

Fixpoint evenb (n : nat) : bool :=
match n with
| O => true
| S O => false
| S (S n') => evenb n'
end.

Compute S O.
Compute ( evenb (S (S O))).

Fixpoint filter {X: Type } (test : X -> bool) (l:list X) : list X :=
match l with 
| [] => []
| h :: t => if test h then h:: (filter test t) else (filter test t)
end.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. simpl. reflexivity. Qed.

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X:=
(filter test l, filter (fun n => negb (test n)) l).

Fixpoint map {X Y:Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Lemma app_map : forall (X Y : Type) (f : X -> Y) (l : list X) (x : X),
   (map f l) ++ [f x] = map f ( l ++ [x]).
Proof.
intros X Y f l x.
induction l as [|h t IH].
-  simpl. reflexivity.
- simpl. rewrite <- IH. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
intros X Y f l.
induction l as [| h t IH].
- simpl. reflexivity.
- simpl. rewrite <- IH. rewrite app_map. reflexivity.
Qed.

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X) : (list Y) :=
match l with 
| [] => []
| h :: t => (f h) ++ (flat_map f t)
end. 

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof.
simpl. reflexivity.
Qed.

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y
  := fold (fun x l' => cons (f x) l') l [].

Theorem fold_map_correct : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f l = fold_map f l.
Proof.
intros X Y f l.
induction l as [| h l IH]. 
- simpl. reflexivity.
- simpl. rewrite IH. reflexivity.
Qed.

Definition fold_length {X: Type} (l: list X) : nat :=
 fold (fun _ n => S n) l 0.

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Check @prod_curry.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
match l with
| [] => None
| a:: l' => if equal n O then Some a else nth_error l' (pred n)
end.

Lemma rev_op : forall l1 l2 : list nat,
 rev(l1 ++ l2 ) = rev l2 ++ rev l1.
Proof.
intros l1 l2.
induction l1 as [| h t IH].
- simpl. rewrite app_nil_r. reflexivity.
- simpl. rewrite IH. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_rev: forall l : list nat,
    rev (rev l) = l.
  Proof.
    intros l.
    induction l as [| h t IH].
    - simpl. reflexivity.
    - simpl. rewrite rev_op. rewrite IH. simpl. reflexivity.
Qed.












