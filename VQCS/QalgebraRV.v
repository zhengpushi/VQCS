(*
  Copyright 2024 ***
  This file is part of VQCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Algebra of Quantities on R vector type
  author    : ***
  date      : 2024.06
*)

From FinMatrix Require Export MatrixR.
Require Import SI.
Import SI_Accepted SI_Prefix.

Require Export QalgebraR.

Declare Scope QuRV_scope.
Delimit Scope QuRV_scope with QRV.

Open Scope Unit_scope.
Open Scope Quantity_scope.
Open Scope QuR_scope.
Open Scope QuRV_scope.


(* ######################################################################### *)
(** * Algebraic operations for quantities of vector type over R *)

Definition QuRV n := @Quantity (vec n).
Definition u2qRV {n} (x : vec n) (u : Unit) : QuRV n := u2q x u.

Definition vec2q {n} (x : vec n) : QuRV n := a2q x.
Coercion vec2q : vec >-> QuRV.

(* Check @l2v 3 [1;2;3] : QuRV 3. *)

Definition qcvtbleRV {n} (q1 q2 : QuRV n) := qcvtble q1 q2.
Definition q2qnRV {n} (q : QuRV n) (nref : Nunit) : QuRV n := q2qn vscal q nref.
Definition q2quRV {n} (q : QuRV n) (uref : Unit) : QuRV n := q2qu vscal q uref.
Definition q2qRV {n} (q qref : QuRV n) : QuRV n := q2q vscal q qref.

Definition qaddRV {n} (q1 q2 : QuRV n) : QuRV n := qadd vadd q1 q2.
Definition qaddlRV {n} (q1 q2 : QuRV n) : QuRV n := qaddl vscal vadd q1 q2.
Definition qaddrRV {n} (q1 q2 : QuRV n) : QuRV n := qaddr vscal vadd q1 q2.
Definition qoppRV {n} (q : QuRV n) : QuRV n := qopp vopp q.
Definition qsubRV {n} (q1 q2 : QuRV n) : QuRV n := qsub vadd vopp q1 q2.
Definition qsublRV {n} (q1 q2 : QuRV n) : QuRV n := qsubl vscal vadd vopp q1 q2.
Definition qsubrRV {n} (q1 q2 : QuRV n) : QuRV n := qsubr vscal vadd vopp q1 q2.

Infix "+" := qaddRV : QuRV_scope.
Infix "'+" := qaddlRV : QuRV_scope.
Infix "+'" := qaddrRV : QuRV_scope.
Notation "- q" := (qoppRV q) : QuRV_scope.
Infix "-" := qsubRV : QuRV_scope.
Infix "'-" := qsublRV : QuRV_scope.
Infix "-'" := qsubrRV : QuRV_scope.

(** Automation for quantity equality of R vector type *)
Ltac qeqRV :=
  (* simplify *)
  intros; cbv;
  (* elim Rbool, solve R contracdiction *)
  autoRbool; auto; try lra;
  (* elim Qmake, option, tuple *)
  try match goal with | |- Qmake _ _ = Qmake _ _ => f_equal end;
  try match goal with | |- Some _ = Some _ => f_equal end;
  try match goal with | |- (_, _) = (_, _) => f_equal end;
  (* elim vector *)
  try veq;
  (* elim R *)
  try lra.


(* ######################################################################### *)
(** * Specific operations for quantities of vector type over R *)

(** get component of a vector quantity *)
Definition qnthRV {n} (q : QuRV n) (i : fin n) : QuR :=
  match q with
  | Qmake v n => Qmake (v i) n
  | _ => !!
  end.

Notation "q .[ i ]" := (qnthRV q i) : QuRV_scope.
Notation "q .1" := (q.[#0]) : QuRV_scope.
Notation "q .2" := (q.[#1]) : QuRV_scope.
Notation "q .3" := (q.[#2]) : QuRV_scope.
Notation "q .4" := (q.[#3]) : QuRV_scope.


(** scalar product for a R quantity and a RV quantity *)
Definition qscalRV {n} (k : QuR) (q : QuRV n) : QuRV n := qmul vscal k q.
Infix "s*" := qscalRV : QuRV_scope.


(** dot product for two RV quantities *)
Definition qdotRV {n} (q1 q2 : QuRV n) : QuR :=
  match q1, q2 with
  | Qmake v1 n1, Qmake v2 n2 => Qmake (vdot v1 v2) (nmul n1 n2)
  | _, _ => !!
  end.
Notation "< q1 , q2 >" := (qdotRV q1 q2) : QuRV_scope.


(** cross product for two 3-RV quantities *)
Definition qcrossRV3 (q1 q2 : QuRV 3) : QuRV 3 :=
  match q1, q2 with
  | Qmake v1 n1, Qmake v2 n2 => Qmake (v3cross v1 v2) (nmul n1 n2)
  | _, _ => !!
  end.
Notation "q1 \x q2" := (qcrossRV3 q1 q2) : QuRV_scope.


(* ######################################################################### *)
(** * Examples *)
Section test.

  Section ex1.
    (* t = 5 sec *)
    Let t := u2qR 5 's.

    (* v = [vx;vy;vz] = [1;2;3] m/s *)
    Let v := @u2qRV 3 (l2v [1;2;3]) ('m/'s)%U.

    (* s = v * t *)
    Let s := t s* v.
      
    (* s = [5;10;15] m *)
    Goal s = u2qRV (l2v [5;10;15]) 'm.
    Proof. qeqRV. Qed.

    (* s[1] = 5 m  *)
    Goal s.1 = u2qR 5 'm.
    Proof. qeqRV. Qed.

    (* <v, v> = 14 m^2/s^2 *)
    Goal <v, v> = u2qR 14 (('m/'s)^2)%U.
    Proof. qeqRV. Qed.

    (* [1;0;0] N * [0;1;0] m = [0;0;1] J  (1 J = 1 N.m) *)
    Goal (u2qRV v3i 'N) \x (u2qRV v3j 'm) = u2qRV v3k 'J.
    Proof. qeqRV. Qed.

    (* [1;0;0] + [0;1;0] + 2 * [0;0;1] = [1;1;2] *)
    Goal v3i + v3j + 2 s* v3k = l2v [1;1;2].
    Proof. qeqRV. Qed.
  End ex1.

End test.

