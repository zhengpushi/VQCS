(*
  file:     Raux.v
  author:   Zhengpu Shi
  purpose:  
  1. add more operations and properties for Real Numbers. 
*)

Require Import Reals.
Open Scope R_scope.

(** Comparison of two Real Numbers *)

(** r1 =? r2 *)
Definition R_beq (r1 r2 : R) : bool :=
  if Req_EM_T r1 r2 then true else false.

Infix "=?" := (R_beq) : R_scope.

(** r1 <=? r2 *)
Definition R_ble (r1 r2 : R) : bool :=
  if Rle_lt_dec r1 r2 then true else false.
Infix "<=?" := (R_ble) : R_scope.

(** r1 <=? r2 *)
Definition R_blt (r1 r2 : R) : bool :=
  if Rlt_le_dec r1 r2 then true else false.
Infix "<?" := (R_ble) : R_scope.


Lemma R_beq_refl : forall r, R_beq r r = true.
Proof. intros. unfold R_beq. destruct (Req_EM_T r r); auto. Qed.