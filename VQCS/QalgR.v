(*
  purpose   : Algebraic of Quantities on type R
  author    : ZhengPu Shi
  date      : 2022.04

*)

Require Export Quantity.
Require Import SI.

Open Scope R_scope.
Open Scope Quantity_scope.

(** Monomorphic functions for current field *)
Notation QmakeU := (QmakeU Rmult).
Notation QvalRef := (QvalRef Rmult).
Notation QvalZero := (@QvalZero _ R0).


(* ##################################################################### *)
(** * Arithmetic of [Quantity R] *)

(** ** Constants *)

(** Identity element of [Quantity R] *)
Definition Qone : Quantity := Qmake 1 Dzero.


(** ** Qadd *)

Definition Qadd (q1 q2 : Quantity) : Quantity :=
  match q1,q2 with
  | Qmake v1 d1, Qmake v2 d2 =>
      if Deqb d1 d2
      then Qmake (v1 + v2) d1
      else !!
  | _, _ => !!
  end.
Infix "+" := Qadd : Quantity_scope.

Lemma Qadd_comm : forall q1 q2 : Quantity, q1 + q2 = q2 + q1.
Proof.
  intros. destruct q1,q2; auto. cbn. rewrite Deqb_comm.
  bdestruct (Deqb d0 d); auto; subst. f_equal; ring.
Qed.

Lemma Qadd_assoc : forall q1 q2 q3 : Quantity, (q1 + q2) + q3 = q1 + (q2 + q3).
Proof.
  intros. destruct q1,q2,q3; auto; cbn.
  - bdestruct (Deqb d d0); auto; subst; simpl.
    + bdestruct (Deqb d0 d1); auto; subst. rewrite Deqb_refl. f_equal; ring.
    + bdestruct (Deqb d0 d1); auto; subst. apply Deqb_false_iff in H. rewrite H; auto.
  - bdestruct (Deqb d d0); auto.
Qed.


(** ** Qopp *)

Definition Qopp (q : Quantity) : Quantity :=
  match q with
  | Qmake v d => Qmake (Ropp v) d
  |  _ => !!
  end.
Notation "- q" := (Qopp q) : Quantity_scope.


(** ** Qsub *)
Definition Qsub (q1 q2 : Quantity) : Quantity := q1 + (-q2).
Infix "-" := Qsub : Quantity_scope.


(** ** Qmul *)
Definition Qmul (q1 q2 : Quantity) : Quantity :=
  match q1,q2 with
  | Qmake v1 d1, Qmake v2 d2 => Qmake (v1*v2) (Dplus d1 d2)
  | _, _ => !!
  end.
Infix "*" := Qmul : Quantity_scope.

Section test.
  Import SI_Accepted.

  Let q1 := QmakeU 1 'hrs.
  Let q2 := QmakeU 30 'min.
  Let q3 := QmakeU 10 'kg.

  Goal (q1 + q2) * q3 = q3 * q2 + q3 * q1.
  Proof. simpl. f_equal. ring. Qed.

End test.

Lemma Qmul_comm : forall q1 q2 : Quantity, q1 * q2 = q2 * q1.
Proof. intros. destruct q1,q2; auto. cbn. rewrite Dplus_comm. f_equal. ring. Qed.

Lemma Qmul_assoc : forall q1 q2 q3 : Quantity, (q1 * q2) * q3 = q1 * (q2 * q3).
Proof. intros. destruct q1,q2,q3; auto. cbn. rewrite Dplus_assoc. f_equal. ring. Qed.

Lemma Qmul_1_l : forall q : Quantity, Qone * q = q.
Proof. intros. destruct q; auto. cbn. f_equal. ring. des_dims1 d. auto. Qed.

Lemma Qmul_1_r : forall q : Quantity, q * Qone = q.
Proof. intros. rewrite Qmul_comm. apply Qmul_1_l. Qed.


(** ** Qinv *)

Definition Qinv (q : Quantity) : Quantity :=
  match q with
  | Qmake v d => Qmake (Rinv v) (Dopp d)
  |  _ => !!
  end.
Notation "/ q" := (Qinv q) : Quantity_scope.

Lemma Qmul_Qinv_l : forall q, q <> !! -> ~QvalZero q -> q * /q = Qone.
Proof.
  intros. destruct q; try easy. cbn in *. unfold Qone.
  rewrite Dplus_Dopp_r. f_equal. field. auto.
Qed.


(** ** Qdiv *)
Definition Qdiv (q1 q2 : Quantity) : Quantity := q1 * (/q2).
Infix "/" := Qdiv : Quantity_scope.


(** ** Integer power *)
Definition QpowZ (q : Quantity) (z : Z) : Quantity :=
  match q with
  | Qmake v d => Qmake (powerRZ v z) (Dcmul z d)
  | _ => !!
  end.

Notation " q ² " := (QpowZ q 2) (at level 1) : Quantity_scope.
Notation " q ³ " := (QpowZ q 3) (at level 1) : Quantity_scope.
Notation " q ⁴ " := (QpowZ q 4) (at level 1) : Quantity_scope.
Notation " q ⁵ " := (QpowZ q 5) (at level 1) : Quantity_scope.
Notation "q ^ n" := (QpowZ q n) : Quantity_scope.


(** Solve Quanity equality *)
Ltac pfqeq :=
  (* simplify *)
  compute;
  (* pairs *)
  f_equal;
  (* equality on R type *)
  try field;
  (* inequality on R type *)
  try lra
(*   repeat match goal with *)
(*   | |- Qmake _ _ = Qmake _ _ => f_equal *)
(*   | |- mkNunit _ _ = mkNunit _ _ => f_equal *)
(*   | |- _ => idtac *)
  (*   end; *)
(*   (* real decision *) *)
(*   repeat destruct (Req_EM_T); auto; try lra; *)
(*   (* sin,cos,sqrt ... *) *)
(*   autorewrite with R in *; auto with R. *)
.


Section test.
  Import SI_Accepted.
  
  (* Add with same Unit *)
  Goal (QmakeU 3 's) + (QmakeU 2 's) = (QmakeU 1 's) + (QmakeU 4 's).
  Proof. pfqeq. Qed.

  (* Add with different Unit *)
  Goal (QmakeU 50 'min) + (QmakeU 600 's) = (QmakeU 1 'hrs).
  Proof. pfqeq. Qed.

  (* Get value by measure it with a Unit *)
  Goal QvalRef (QmakeU 600 's) 'min = Some 10.
  Proof. pfqeq. Qed.

  (* Multiply with same Unit *)
  Goal (QmakeU 3 's) * (QmakeU 2 's) = (QmakeU 6 ('s²)%U).
  Proof. pfqeq. Qed.

  (* Inversion *)
  Goal /(QmakeU 10 'ms) = QmakeU 100 'Hz.
  Proof. pfqeq. Qed.

  (* Divide with different Unit *)
  Goal (QmakeU 100 'm) / (QmakeU 8 ('m/'s)%U) = QmakeU 12.5 's.
  Proof. pfqeq. Qed.

  (* QpowZ *)
  Goal forall q, QpowZ q 4 = q * q² * q.
  Proof.
    intros. destruct q; auto. cbn. f_equal. simpl. ring.
    des_dims1 d. Opaque Z.mul. simpl. repeat (f_equal; try ring).
  Qed.

  (* Use variable instead of constant value *)
  Goal forall distance speed : R,
      speed > 0 ->
      (QmakeU distance 'm) / (QmakeU speed ('m/'s)%U) =
        QmakeU (distance/speed)%R 's.
  Proof. intros. pfqeq. Qed.
End test.


(* ##################################################################### *)
(** * Complex operations of quantities *)


?

(** ** General unary operation of quantity which won't change it's unit *)
Definition Qop1 (q : Quantity) (f : R -> R) : Quantity :=
  match q with
  | Qmake v n => Qmake (f v) n
  | _ => !!
  end.

(** ** Several unary operations of quantity *)
Definition Qsin q := Qop1 q sin.
Definition Qcos q := Qop1 q cos.
Definition Qtan q := Qop1 q tan.
Definition Qatan q := Qop1 q atan.
Definition Qacos q := Qop1 q acos.
Definition Qabs q := Qop1 q Rabs.

Example Qsin_ex1 (r : R) : (Qsin (QmakeU r 'm))² + (Qcos (QmakeU r 'm))² ==
  QmakeU 1 ('m²)%U.
Proof. pfqeq. Qed.



(** ** Square root of quantity *)

(** Note that Qsqrt is correct only when:
1. value of Q is [0,+)
2. coefficient of NUnit of Q is [0,+)
3. dimensions of NUnit of Q is all even
*)
Definition Qsqrt_cond (q : Quantity) : bool :=
  match q with
  | Qmake v n => (0 <=? v)%R && (Nsqrt_cond n)
  | _ => false
  end.

Lemma Qsqrt_cond_true_iff (q : Quantity) : Qsqrt_cond q = true <->
  match q with
  | Qmake v (mkNunit c d) => (0 <= v)%R /\ (0 < c)%R /\ 
    Dsqrt_cond d = true
  | _ => False
  end.
Proof.
  destruct q; try easy.
  destruct n. unfold Qsqrt_cond, Nsqrt_cond in *. simpl.
  rewrite ?andb_true_iff.
  rewrite Rleb_true_iff,Rltb_true_iff. easy.
Qed.
  
Definition Qsqrt (q : Quantity) : Quantity :=
  match q with
  | Qmake v n => Qmake (sqrt v) (Nsqrt n)
  | _ => !!
  end.

Example Qsqrt_ex1 : Qsqrt (QmakeU 4 ('m⁶)%U) = QmakeU 2 ('m³)%U.
Proof. pfqeq. Qed.

(* error example, although got a result, but wrong! *) 
(* Compute Qsqrt (QmakeU 1 (-1)%R * #'s)². *)
Goal (QmakeU 1 (-1)%R * #'s)² = QmakeU 1 ('s*'s)%U.
pfqeq. Qed.

Lemma Qsqrt_Qsqr q : Qsqrt_cond q = true -> Qsqrt (q²) == q.
Proof.
  intros. unfold Qsqrt,Nsqrt in *.
  unfold Qabs,Qop1,Qpow.
  destruct q as [v (c,d)|]; try easy. simpl. 
  rewrite Dsqrt_Dcmul2.
  apply Qsqrt_cond_true_iff in H. do 2 destruct H as [? H].
  apply Qeq_Qmake_bij. split.
  - autorewrite with R; auto.
  - apply Neq_iff_each_eq. simpl. split; auto.
    assert (c * (c * 1) = c * c)%R. { field. } rewrite H2.
    autorewrite with R; auto with R.
Qed.

Lemma Qsqr_Qsqrt q : Qsqrt_cond q = true -> (Qsqrt q)² == q.
Proof.
  intros. unfold Qsqrt,Qsqrt_cond,Qpow in *.
  destruct q as [v (c,d)|]; try easy. simpl in *.
  unfold Nsqrt_cond in *. simpl in *.
  rewrite ?andb_true_iff in H.
  rewrite Rleb_true_iff,Rltb_true_iff in *.
  do 2 destruct H as [? H].
  apply Qeq_Qmake_bij. split.
  - autorewrite with R; auto.
  - apply Neq_iff_each_eq. simpl. split.
    + autorewrite with R; auto with R.
    + rewrite Dcmul2_Dsqrt; auto.
Qed.

(** Register that [Qsqrt] is compatible for [Qeq]. *)
Add Parametric Morphism : Qsqrt
  with signature Qeq ==> Qeq as Qsqrt_Qeq_Qeq_mor.
Proof.
  intros. destruct x,y; try easy.
  apply Qeq_Qmake_bij in H. destruct H. rewrite H.
  apply Qeq_Qmake_bij. rewrite H0. easy.
Qed.

Lemma Qmult_Qsqrt_l q1 q2 : q1 * Qsqrt q2 == Qsqrt (q1 * q1 * q2).
Admitted.

Lemma Qcomps_Qsqrt q1 (H1 : !q1) (H3 : !(Qsqrt q1)) : 
  Qcomps (Qsqrt q1) H3 =
  let '(v1,c1,d1) := Qcomps q1 H1 in
    (sqrt v1, sqrt c1, Dsqrt d1).
Admitted.



(** ** Any power of quantity which the unit of base and exponent both are 1 *)
Definition Qpower (base exp : Quantity) : Quantity :=
  match base,exp with
  | Qmake v1 n1, Qmake v2 n2 =>
    if ((Neqb n1 Nunitone) && (Neqb n2 Nunitone))
    then Qmake (Rpower v1 v2) n1
    else !!
  | _, _ => !!
  end.

