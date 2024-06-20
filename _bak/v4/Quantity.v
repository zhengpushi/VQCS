(*
  file:   Quantity.v
  purpose:
  1. compare two quantity
  
*)

Require Export Raux.
Require Export Unit.
Require Import FunctionalExtensionality.

(** Scope *)
Declare Scope Quantity_scope.
Delimit Scope Quantity_scope with quantity.
Open Scope Quantity_scope.

(** * Quantity, composed by a Real number, and a Unit *)
(* Definition Quantity : Set := (R * Unit)%type.
Definition mkQ r u : Quantity := (r, u).
Definition Qcoef (q : Quantity) : R := let (r,_) := q in r.
Definition Qunit (q : Quantity) : Unit := let (_,u) := q in u. *)

Inductive Quantity : Set :=
  | Qinvalid            (* to represent a invalid result. eg. 'A + 'm *)
  | Qbasic (r : R) (u : Unit).

Definition Qu := Quantity.
Notation "!" := Qinvalid : Quantity_scope.
Notation "r & u" := (Qbasic r u) : Quantity_scope.

Definition R2Quantity (r : R) : Quantity := r & 1.
Coercion R2Quantity : R >-> Quantity.


(** * Comparison for Quantity *)

Definition Quantity_beq (q1 q2 : Quantity) : bool :=
  match q1,q2 with
  | Qinvalid, _ => false
  | _, Qinvalid => false
  | Qbasic r1 u1, Qbasic r2 u2 =>
    andb (R_beq r1 r2) (Unit_beq u1 u2)
  end.

Definition Quantity_eq (q1 q2 : Quantity) : Prop := Quantity_beq q1 q2 = true.

Notation "q1 == q2" := (Quantity_eq q1 q2) : Quantity_scope.

Definition Quantity_cmp (q1 q2 : Quantity) (Rcmp : R -> R -> bool) : bool :=
  match q1,q2 with
  | Qinvalid, _ => false
  | _, Qinvalid => false
  | Qbasic r1 u1, Qbasic r2 u2 =>
    (Rcmp r1 r2) && (Unit_beq u1 u2)
  end.

Definition Quantity_cmpP (q1 q2 : Quantity) (RcmpP : R -> R -> Prop) : Prop :=
  match q1,q2 with
  | Qinvalid, _ => False
  | _, Qinvalid => False
  | Qbasic r1 u1, Qbasic r2 u2 =>
    (RcmpP r1 r2) /\ (ueq u1 u2)
  end.

Notation "q1 < q2" := (Quantity_cmpP q1 q2 Rlt) : Quantity_scope.


(** * Operations for Quantity *)

(** ** Type for Quantity operations *)

Definition Qop1Type := Quantity -> Quantity.
Definition Qop2Type := Quantity -> Quantity -> Quantity.

(** ** Type for Unit operations *)

Definition UnitOp1Type := Unit -> (bool * Unit).
Definition UnitOp2Type := Unit -> Unit -> (bool * Unit).

(** ** Operations for normalized types *)

(** unit op1 (general): normalize *)
Definition unit_op1_general : UnitOp1Type := fun u =>
  let un := unorm u in (true, un).
  
(** unit op1 (inv): normalize, return inv *)
Definition unit_op1_inv : UnitOp1Type := fun u =>
  let un := unorm (/u) in (true, un).

(** unit op2 (plus): normalize, check same, return any one. *)
Definition unit_op2_plus : UnitOp2Type := fun u1 u2 =>
  let u1n := unorm u1 in
  let u2n := unorm u2 in
    if (Unit_beq u1n u2n) then (true, u1n) else (false, u1n).

(** unit op2 (mult): normalize, return multiplication. *)
Definition unit_op2_mult : UnitOp2Type := fun u1 u2 =>
  let u1n := unorm u1 in
  let u2n := unorm u2 in
    (true, unorm (u1n * u2n)).

(** unit op2 (div): normalize, check same, return 1. *)
Definition unit_op2_div : UnitOp2Type := fun u1 u2 =>
  let u1n := unorm u1 in
  let u2n := unorm u2 in
    if (Unit_beq u1n u2n) then (true, ub 1) else (false, u1n).

(** unit op2 (power): normalize, check same, check 1, return 1. *)
Definition unit_op2_power : UnitOp2Type := fun u1 u2 =>
  let u1n := unorm u1 in
  let u2n := unorm u2 in
    if (Unit_beq u1n u2n) then
      if (Unit_beq u1n 1) then (true, ub 1) else (false, u1n)
    else (false, u1n).

(** unary operation of Quantity *)
Definition Qop1 (op_val : R -> R) (op_unit : UnitOp1Type) 
  (q : Quantity) : Quantity :=
  match q with
  | Qinvalid => Qinvalid
  | Qbasic r u =>
    let (b, un) := op_unit u in
      if (negb b) then Qinvalid
      else Qbasic (op_val r) un
  end.

(** binary operation of Quantity *)
Definition Qop2 (op_val : R -> R -> R) (op_unit : UnitOp2Type)
  (q1 q2 : Quantity) : Quantity :=
  match q1,q2 with
  | Qinvalid, _ => Qinvalid
  | _, Qinvalid => Qinvalid
  | Qbasic r1 u1, Qbasic r2 u2 =>
    let (b,un) := op_unit u1 u2 in
      if (negb b) then Qinvalid
      else Qbasic (op_val r1 r2) un
  end.

(** Notation of quantity operation *)

Definition Qadd : Qop2Type := Qop2 Rplus unit_op2_plus.
Definition Qopp : Qop1Type := Qop1 Ropp unit_op1_general.
Definition Qsub : Qop2Type := Qop2 
  (fun r1 r2 => Rplus r1 (Ropp r2)) unit_op2_plus.
Definition Qmul : Qop2Type := Qop2 Rmult unit_op2_mult.
Definition Qinv : Qop1Type := Qop1 Rinv unit_op1_inv.
Definition Qdiv : Qop2Type := Qop2 Rdiv unit_op2_div.
Definition Qpower : Qop2Type := Qop2 Rpower unit_op2_power.

Infix "+" := Qadd : Quantity_scope.
Infix "-" := Qsub : Quantity_scope.
Infix "*" := Qmul : Quantity_scope.
Notation " a ² " := (a * a) (at level 1) : Quantity_scope.
Notation " a ³ " := ((a²) * a) (at level 1) : Quantity_scope.
Notation " a ⁴ " := ((a³) * a) (at level 1) : Quantity_scope.
Infix "/" := Qdiv : Quantity_scope.
Notation "- q" := (Qopp q) : Quantity_scope.
Notation "/ q" := (Qinv q) : Quantity_scope.

Fixpoint Qpow (q : Quantity) (n : nat) : Quantity :=
  match n with
  | O => 1 & 1
  | S O => q
  | S n' => (Qpow q n') * q
  end.

Notation "a ^ n" := (Qpow a n) : Quantity_scope.

Definition Qsin : Qop1Type := Qop1 sin unit_op1_general.
Definition Qcos : Qop1Type := Qop1 cos unit_op1_general.
Definition Qtan : Qop1Type := Qop1 tan unit_op1_general.
Definition Qatan : Qop1Type := Qop1 atan unit_op1_general.
Definition Qacos : Qop1Type := Qop1 acos unit_op1_general.
Definition Qsqrt : Qop1Type := Qop1 sqrt unit_op1_general.

(* 证明单位相同 *)
Global Ltac pfqeq := 
  compute; remember (Req_EM_T _ _) as Hr;auto;
  destruct Hr as [Hn1 | Hn2];auto;
  destruct Hn2;compute;field.

(** Control unfold behavior *)
Global Opaque PI.
Global Opaque Rpower.
Global Opaque sin.
Global Opaque cos.
Global Opaque tan.
Global Opaque atan.
Global Opaque acos.
Global Opaque sqrt.


(** Example *)
Definition q_3s := 3 & 's.
Definition q_2s := 2 & 's.
Definition q_3s' := (1 + 2) & ('s * 'A / 'A * 1 * 1).

Compute Qadd q_3s q_2s.
Compute Qadd q_3s' q_2s.

Lemma q_3s_2s : q_3s + q_2s == q_3s' + q_2s.
Proof.  pfqeq. Qed.


(** * Quantity上的微积分 *)

Declare Scope Qfun_scope.
Delimit Scope Qfun_scope with Qfun.
Open Scope Qfun_scope.

Definition Qfun := Qu -> Qu.

(** 函数的算术运算 *)

Definition Qfadd (f g : Qfun) t := f t + g t.
Definition Qfsub (f g : Qfun) t := f t - g t.
Definition Qfmul (f g : Qfun) t := f t * g t.
Definition Qfdiv (f g : Qfun) t := f t / g t.
Definition Qfcnst (f : Qfun) c t := c * (f t).

Infix "+" := Qfadd : Qfun_scope.
Infix "-" := Qfsub : Qfun_scope.
Infix "*" := Qfmul : Qfun_scope.
Infix "/" := Qfdiv : Qfun_scope.
Infix "*c" := Qfcnst (at level 40, left associativity) : Qfun_scope.

(** 函数算术运算的合法性 *)
Lemma Qfadd_ok : forall (f g : Qfun) t, (f + g) t = (f t + g t)%quantity.
Proof. intros. auto. Qed.

(** 函数加乘运算的结合律和交换律 *)
(* 
  f + g = g + f
  (f + g) + h = f + (g + h) 
*)
Lemma Qfadd_comm : forall (f g : Qfun), f + g = g + f.
Proof. 
  intros. apply functional_extensionality. intros.
  repeat rewrite Qfadd_ok. auto.
  Abort.
