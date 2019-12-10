(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Ltac2.Init.

Ltac2 @ external type : constr -> constr := "ltac2" "constr_type".
(** Return the type of a term *)

Ltac2 @ external equal : constr -> constr -> bool := "ltac2" "constr_equal".
(** Strict syntactic equality: only up to α-conversion and evar expansion *)

Module Unsafe.

(** Low-level access to kernel terms. Use with care! *)

Ltac2 Type case.

Ltac2 Type kind := [
| Rel (int)
| Var (ident)
| Meta (meta)
| Evar (evar, constr array)
| Sort (sort)
| Cast (constr, cast, constr)
| Prod (ident option, constr, constr)
| Lambda (ident option, constr, constr)
| LetIn (ident option, constr, constr, constr)
| App (constr, constr array)
| Constant (constant, instance)
| Ind (inductive, instance)
| Constructor (constructor, instance)
| Case (case, constr, constr, constr array)
| Fix (int array, int, ident option array, constr array, constr array)
| CoFix (int, ident option array, constr array, constr array)
| Proj (projection, constr)
].

Ltac2 @ external kind : constr -> kind := "ltac2" "constr_kind".

Ltac2 @ external make : kind -> constr := "ltac2" "constr_make".

Ltac2 @ external check : constr -> constr result := "ltac2" "constr_check".
(** Checks that a constr generated by unsafe means is indeed safe in the
    current environment, and returns it, or the error otherwise. Panics if
    not focussed. *)

Ltac2 @ external substnl : constr list -> int -> constr -> constr := "ltac2" "constr_substnl".
(** [substnl [r₁;...;rₙ] k c] substitutes in parallel [Rel(k+1); ...; Rel(k+n)] with
    [r₁;...;rₙ] in [c]. *)

Ltac2 @ external closenl : ident list -> int -> constr -> constr := "ltac2" "constr_closenl".
(** [closenl [x₁;...;xₙ] k c] abstracts over variables [x₁;...;xₙ] and replaces them with
    [Rel(k); ...; Rel(k+n-1)] in [c]. If two names are identical, the one of least index is kept. *)

End Unsafe.

Ltac2 @ external in_context : ident -> constr -> (unit -> unit) -> constr := "ltac2" "constr_in_context".
(** On a focussed goal [Γ ⊢ A], [in_context id c tac] evaluates [tac] in a
    focussed goal [Γ, id : c ⊢ ?X] and returns [fun (id : c) => t] where [t] is
    the proof built by the tactic. *)