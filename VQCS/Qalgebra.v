(*
  Copyright 2024 Zhengpu Shi
  This file is part of VQCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Algebra of Quantities
  author    : Zhengpu Shi
  date      : 2022.04

  remark    :
  * operations should satisfy the dimension law
    1. q1 {+,-,==,<=,<} q2, only if q1 and q2 have same unit.
    2. {sin,cos,tan,exp,log} q, only if q i dimensionless.
*)

Require Export Quantity.

Generalizable Variable tA Aadd Azero Aopp Amul Aone Ainv.
Generalizable Variable tB Badd Bzero Bopp Bmul Bone Binv.

(* ######################################################################### *)
(** * Basic algebraic operations of quantity *)

(* ======================================================================= *)
(** ** General algebraic operations of quantity *)

(** General unary quantity operation *)
Definition qop1 {tA} (f : tA -> tA) (q : @Quantity tA) : @Quantity tA :=
  match q with
  | Qmake v n => Qmake (f v) n
  | _ => !!
  end.

(** General binary quantity operation on same unit *)
Definition qop2 {tA} (f : tA -> tA -> tA) (q1 q2 : @Quantity tA) : @Quantity tA :=
  match q1, q2 with
  | Qmake v1 n1, Qmake v2 n2 => if neqb n1 n2 then Qmake (f v1 v2)%A n1 else !!
  | _, _ => !!
  end.

(** General binary quantity operation on convertible untis, adopting the unit of 
    the left operand q1 *)
Definition qop2l {tA} (ARmul : R -> tA -> tA) (f : tA -> tA -> tA)
  (q1 q2 : @Quantity tA) : @Quantity tA :=
  if qcvtbleb q1 q2 then qop2 f q1 (q2q ARmul q2 q1) else !!.

(** General binary quantity operation on convertible untis, adopting the unit of 
    the right operand q2 *)
Definition qop2r {tA} (ARmul : R -> tA -> tA) (f : tA -> tA -> tA)
  (q1 q2 : @Quantity tA) : @Quantity tA :=
  if qcvtbleb q1 q2 then qop2 f (q2q ARmul q1 q2) q2 else !!.

(** General unary quantity operation, on which the quantity is dimensionless *)
Definition qdim0op1 {tA} (f : tA -> tA) (q : @Quantity tA) : @Quantity tA :=
  match q with
  | Qmake v n => if ndim1b n then Qmake (f v) n else !!
  | _ => !!
  end.

(** General binary quantity operation, on which the quantity is dimensionless *)
Definition qdim0op2 {tA} (f : tA -> tA -> tA) (q1 q2 : @Quantity tA)
  : @Quantity tA :=
  match q1, q2 with
  | Qmake v1 n1, Qmake v2 n2 =>
      if ndim1b n1 && ndim1b n2 then Qmake (f v1 v2) n1 else !!
  | _, _ => !!
  end.


(* ======================================================================= *)
(** ** Specific algebraic operations of quantity *)

(** Quantity addition/opposition/subtraction *)
Section qadd_qopp_qsub.
  Context {tA} (ARmul : R -> tA -> tA) (Aadd : tA -> tA -> tA) (Aopp : tA -> tA).

  (** Quantity addition using same unit *)
  Definition qadd (q1 q2 : Quantity) : Quantity := qop2 Aadd q1 q2.
  Infix "+" := qadd : Quantity_scope.

  (** Quantity addition using the unit of the left operand q1 *)
  Definition qaddl (q1 q2 : Quantity) : Quantity := qop2l ARmul Aadd q1 q2.
  Infix "'+" := qaddl : Quantity_scope.

  (** Quantity addition using the unit of the right operand q1 *)
  Definition qaddr (q1 q2 : Quantity) : Quantity := qop2r ARmul Aadd q1 q2.
  Infix "+'" := qaddr : Quantity_scope.

  (** Quantity opposition *)
  Definition qopp (q : Quantity) : Quantity := qop1 Aopp q.
  Notation "- q" := (qopp q) : Quantity_scope.

  (** Quantity subtraction using same unit  *)
  Definition qsub (q1 q2 : Quantity) : Quantity := q1 + - q2.
  Infix "-" := qsub : Quantity_scope.

  (** Quantity subtraction using the unit of the left operand q1 *)
  Definition qsubl (q1 q2 : Quantity) : Quantity := q1 '+ - q2.
  Infix "'-" := qsubl : Quantity_scope.
  
  (** Quantity subtraction using the unit of the right operand q1 *)
  Definition qsubr (q1 q2 : Quantity) : Quantity := q1 +' - q2.
  Infix "-'" := qsubr : Quantity_scope.
  
  Context `{HASGroup : ASGroup _ Aadd}.

  (** [qadd] is associative. *)
  Lemma qadd_assoc (q1 q2 q3 : Quantity) : (q1 + q2) + q3 = q1 + (q2 + q3).
  Proof.
    unfold qadd, qop2.
    destruct q1 as [v1 n1|], q2 as [v2 n2|], q3 as [v3 n3|]; try easy.
    - bdestruct (neqb n1 n2); subst; auto.
      + bdestruct (neqb n2 n3); subst; auto. rewrite neqb_refl. f_equal. asgroup.
      + bdestruct (neqb n2 n3); subst; auto. apply neqb_false_iff in H.
        rewrite H. auto.
    - bdestruct (neqb n1 n2); subst; auto.
  Qed.

  (** [qadd] is commutative. *)
  Lemma qadd_comm (q1 q2 : Quantity) : q1 + q2 = q2 + q1.
  Proof.
    unfold qadd, qop2. destruct q1 as [v1 n1|], q2 as [v2 n2|]; try easy.
    rewrite neqb_comm. bdestruct (neqb n2 n1); subst; auto. f_equal. asgroup.
  Qed.

  (** [qadd] left with !! equal to !!. *)
  Lemma qadd_qinvalid_l (q : Quantity) : !! + q = !!.
  Proof. auto. Qed.

  (** [qadd] right with !! equal to !!. *)
  Lemma qadd_qinvalid_r (q : Quantity) : q + !! = !!.
  Proof. rewrite qadd_comm. auto. Qed.


  Context `{HGroup : Group _ Aadd Azero Aopp}.

End qadd_qopp_qsub.


(** Quantity inversion *)
Section qinv.
  Context {A} (Ainv : A -> A).
  
  (** Quantity inversion *)
  Definition qinv (q : Quantity) : Quantity :=
    match q with
    | Qmake v n => Qmake (Ainv v) (ninv n)
    | _ => !!
    end.
  Notation "/ q" := (qinv q) : Quantity_scope.
End qinv.


(** multiplication or division of two quantities that may have different units.
    For example, scalar multiplication of vectors or matrices *)
Section qmul_qdiv.
  Context {tA tB} (AmulB : tA -> tB -> tB) (Binv : tB -> tB).
  Infix "*" := AmulB : A_scope.
  Notation qinv := (qinv Binv).

  (** Quantity multiplication *)
  Definition qmul (q1 : @Quantity tA) (q2 : @Quantity tB) : @Quantity tB :=
    match q1,q2 with
    | Qmake v1 n1, Qmake v2 n2 => Qmake (v1 * v2)%A (nmul n1 n2)
    | _, _ => !!
    end.
  Infix "*" := qmul : Quantity_scope.


  (** Power of quantity with an integer numbers *)
  Section qpow.
    Context (ApowerZ : tA -> Z -> tA).
    
    Definition qpow (q : @Quantity tA) (z : Z) : @Quantity tA :=
      match q with
      | Qmake v n => Qmake (ApowerZ v z) (npow n z)
      | !! => !!
      end.
    Notation "q ^ n" := (qpow q n) : Quantity_scope.
    Notation " q ² " := (q ^ 2) : Quantity_scope.
    Notation " q ³ " := (q ^ 3) : Quantity_scope.
    Notation " q ⁴ " := (q ^ 4) : Quantity_scope.
    Notation " q ⁵ " := (q ^ 5) : Quantity_scope.
  End qpow.
  

  (** Quantity division *)
  Definition qdiv (q1 : @Quantity tA) (q2 : @Quantity tB) : @Quantity tB :=
    qmul q1 (qinv q2).
  Infix "/" := qdiv : Quantity_scope.

  (** [qmul] left cancellation law *)
  Lemma qmul_cancel_l q1 q2 q3 : q1 * q2 = q1 * q3 -> q2 = q3.
  Proof.
    intros. unfold qmul in *. destruct q1,q2,q3. inv H.
  Abort.

  (** [qmul] right cancellation law *)
  Lemma qmul_cancel_r q1 q2 q3 : q1 * q3 = q2 * q3 -> q1 = q2.
  Abort.
  
End qmul_qdiv.

(** Properties for qmul with specific element types *)
Section qmul_specific.
  Context `{HASGroup : ASGroup tA Amul}.
  Notation qmul := (qmul Amul).
  Infix "*" := qmul : Quantity_scope.

  (** [qmul] is associative *)
  Lemma qmul_assoc (q1 q2 q3 : Quantity) : (q1 * q2) * q3 = q1 * (q2 * q3).
  Proof.
    unfold qmul. destruct q1 as [v1 n1|], q2 as [v2 n2|], q3 as [v3 n3|]; try easy.
    f_equal. asgroup. apply nmul_assoc.
  Qed.
  
  (** [qmul] is commutative *)
  Lemma qmul_comm (q1 q2 : Quantity) : q1 * q2 = q2 * q1.
  Proof.
    unfold qmul. destruct q1 as [v1 n1|], q2 as [v2 n2|]; try easy.
    f_equal. asgroup. apply nmul_comm.
  Qed.

  Context `{HAMonoid : AMonoid tA Amul Aone}.
  Notation qone := (qone Aone).
  
  (** [qone] is the left identity for multiplication *)
  Lemma qmul_1_l q : qone * q = q.
  Proof.
    unfold qmul. unfold qone. destruct q as [v n|]; auto.
    f_equal. amonoid. apply nmul_1_l.
  Qed.

  Lemma qmul_1_r q : q * qone = q.
  Proof. rewrite qmul_comm. apply qmul_1_l. Qed.

  Instance qmul_Monoid : Monoid qmul qone.
  Proof.
    repeat constructor.
    all: try apply qmul_assoc; try apply qmul_1_l; try apply qmul_1_r;
      try apply qmul_comm.
  Qed.
    
  Instance qmul_AMonoid : AMonoid qmul qone.
  Proof.
    repeat constructor.
    all: try apply qmul_assoc; try apply qmul_1_l; try apply qmul_1_r;
      try apply qmul_comm.
  Qed.

  Context `{HAGroup : AGroup tA Amul Aone Ainv}.
  Notation qinv := (qinv Ainv).

  Lemma qmul_qinv_l : forall q, q <> !! -> qcoef q <> Some 0 -> qinv q * q = qone.
  Proof.
    intros. unfold qmul, qinv, qone. destruct q as [v n|]; auto; try easy.
    f_equal. apply HAGroup.
    apply nmul_ninv_l. cbv in H0. destruct n. simpl. intro. destruct H0.
    rewrite H1. auto.
  Qed.
  
  Instance qmul_Group : Group qmul qone qinv.
  Proof.
    repeat constructor.
    all: try apply qmul_assoc; try apply qmul_1_l; try apply qmul_1_r;
      try apply qmul_comm.
  Abort.
  
End qmul_specific.
