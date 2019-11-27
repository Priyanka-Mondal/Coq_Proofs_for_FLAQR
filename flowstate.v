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


Module Flow.
(* no polumophism for now  *)
(*and no pc also*)
(*no assume and where*)
(*no sealed term *)

Inductive ty : Type :=
  | Unit : ty
  | Sumty : ty -> ty -> ty
  | Prodty : ty -> ty -> ty
  | Functy : ty -> ty -> ty
  | Says: ty -> ty -> ty.

Inductive pr : Type :=
  | prin : string -> pr
  | top : nat -> pr  (* 0 *)
  | bot : nat -> pr  (* 1 *)
  | confpr : pr -> pr
  | integpr : pr -> pr
  | andpr : pr -> pr -> pr
  | orpr : pr -> pr -> pr
  | joinpr : pr -> pr -> pr
  | meetpr : pr -> pr -> pr.

Inductive tm : Type :=
  | tvar : string -> tm
  | tapp : tm -> tm -> tm
  | tabs : string -> ty -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tcase : tm -> tm -> tm -> tm
  | tproj : nat -> tm -> tm -> tm
  | bind  : tm -> tm -> tm -> tm
  | run   : tm -> pr -> tm
  | ret   : tm -> pr -> tm
  | compEnd : tm -> tm -> tm 
  | select :  pr -> pr -> tm -> tm -> tm.










