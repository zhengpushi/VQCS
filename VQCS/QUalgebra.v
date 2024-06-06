(*
  purpose   : Algebric of Quantities
  author    : Zhengpu Shi
  date      : 2022.04

*)


Require Export QUantity.


(** * Quantity Arithmetic Operations *)


(* (** ** Automatic for for simplify context and goals contain Dims_xx *)

Hint Rewrite u2n_n2u : QALG.

(* 环境中有两组形如 Dims_eqb ?a ?b = true | false 的表达式，则先构造新的表达式 *)
Ltac tac_dims_gen_exp :=
  match goal with
  (* true,true *)
  | H1 : Dims_eqb ?a ?b = true, 
    H2 : Dims_eqb ?b ?c = true |- _ =>
    assert (Dims_eqb a c = true); [
      rewrite ?Dims_eqb_true_iff,?Dims_eqb_false_iff in *;
      subst; auto|]
  (* true,false *)
  | H1 : Dims_eqb ?a ?b = true, 
    H2 : Dims_eqb ?b ?c = false |- _ =>
    assert (Dims_eqb a c = false); [
      rewrite ?Dims_eqb_true_iff,?Dims_eqb_false_iff in *;
      subst; auto|]
  (* false,true *)
  | H1 : Dims_eqb ?a ?b = false, 
    H2 : Dims_eqb ?b ?c = true |- _ =>
    assert (Dims_eqb a c = false); [
      rewrite ?Dims_eqb_true_iff,?Dims_eqb_false_iff in *;
      subst; auto|]
  end.

(* 环境中有形如 Dims_eqb ?a ?b = true | false 的表达式，则使用它们 *)
Ltac tac_dims_simp :=
  match goal with
  | H1 : Dims_eqb _ _ = true |- _ => rewrite H1
  | H2 : Dims_eqb _ _ = false |- _ => rewrite H2
  end.
 *)



(** ** Quantity addition *)

(** Quantity addition is valid only when they are similar and not valid *)
Definition QUplus' (q1 q2 : Quantity) : Quantity :=
  match q1,q2 with
  | QUmake v1 n1, QUmake v2 n2 =>
    if (n1 =? n2)%NU
    then QUmake (Rplus v1 v2) n1
    else !!
  | _, _ => !!
  end.
  
Definition QUplus (q1 q2 : Quantity) : Quantity :=
  match q1,q2 with
  | QUmake v1 n1, QUmake v2 n2 =>
    match QUconv q2 (n2u n1) with
    | QUmake v2' n2' =>
      QUmake (Rplus v1 v2') n1
    | _ => !!
    end
  | _, _ => !!
  end.
Infix "+" := QUplus : QU_scope.

(* Eval compute in (genQU 1 'min) + (genQU 60 's).
Eval compute in (genQU 1 'rpm) + (genQU 60 'rps).
 *)

(** Register that [QUplus] is compatible for [QUeq]. *)
(* Add Parametric Morphism : QUplus
  with signature QUeq ==> QUeq ==> QUeq as QUplus_QUeq_QUeq_mor.
Proof.
  intros q1 q2 H1 q3 q4 H2. 
  unfold QUeq,QUeqb,QUcmpb,QUplus,Neqb in *.
  destruct q1 as [v1 (c1,d1)|], q2 as [v2 (c2,d2)|], q3 as [v3 (c3,d3)|], 
    q4 as [v4 (c4,d4)|]; try easy. simpl in *.
  rewrite ?andb_true_iff in *.
  destruct H1 as [H1a [H1b H1c]].
  destruct H2 as [H2a [H2b H2c]].
  rewrite ?Reqb_true_iff,?Qeq_bool_iff,?Deqb_true_iff_Deq in *.
  rewrite H1a,H1b,H1c,H2a,H2b,H2c.
  destruct (Qeq_bool c2 c4),(Deqb d2 d4); auto; simpl.
  rewrite <- Qeq_bool_iff in H1b.
  rewrite Reqb_true_refl,Deqb_true_refl,H1b. auto.
Qed. *)

Add Parametric Morphism : QUplus
  with signature QUeq ==> QUeq ==> QUeq as QUplus_QUeq_QUeq_mor.
Proof.
  intros q1 q2 H1 q3 q4 H2. 
  unfold QUeq,QUeqb,QUcmpb,QUplus,Neqb in *.
  destruct q1 as [v1 (c1,d1)|], q2 as [v2 (c2,d2)|], q3 as [v3 (c3,d3)|], 
    q4 as [v4 (c4,d4)|]; try easy. simpl in H1,H2.
  rewrite ?andb_true_iff in *.
  rewrite ?Reqb_true_iff,?Qeq_bool_iff,?Deqb_true_iff_Deq in *.
  destruct H1 as [H1a [H1b H1c]].
  destruct H2 as [H2a [H2b H2c]]. subst.
  unfold QUconv. unfold Uconv.
  destruct ({| Ncoef := c3; Ndims := d4 |} =? 
    {| Ncoef := c1; Ndims := d2 |})%NU eqn:E1.
  - apply Neqb_true_iff_Neq in E1.
    rewrite Neq_iff_each_eq in E1. simpl in E1. destruct E1. subst.
    destruct d2. simpl. rewrite ?Ugetdim_Ucons. simpl.
    rewrite Deqb_true_refl;
    rewrite ?Ugetcoef_Ucons; simpl.
    rewrite ?Ugetcoef_Ucons;
    rewrite ?andb_true_iff. repeat split.
    + apply Reqb_true_iff. rewrite <- H1b. rewrite <- H2b. rewrite H.
      simpl. field.
    + apply Qeq_bool_iff. auto.
    + apply Deqb_true_refl.
  - apply Neqb_false_iff_Nneq in E1.
    apply Nneq_iff_each_neq in E1. simpl in E1. 
    destruct d2,d4; simpl. rewrite ?Ugetdim_Ucons,?Z.add_0_r; simpl.
    destruct E1. 
    + destruct (Deqb _ _) eqn:E4; auto. simpl.
      rewrite ?Ugetcoef_Ucons. 
      rewrite ?andb_true_iff. repeat split.
      * simpl. rewrite H1b,H2b. apply Reqb_true_iff. field.
      * apply Qeq_bool_iff. auto.
      * apply Deqb_true_refl. 
    + apply Deqb_false_iff_Dneq in H. rewrite H. auto.
Qed.


(** [QUplus] is commutative. *)
Lemma QUplus_comm (q1 q2 : Quantity) : q1 + q2 == q2 + q1.
Proof.
  destruct q1 as [v1 n1|], q2 as [v2 n2|]; try easy.
  unfold QUplus. unfold QUconv.
(*   destruct (n simpl.
  rewrite Rplus_comm.
  rewrite Neqb_comm, Rplus_comm.
  destruct (n2 =? n1)%NU eqn:E1; try easy.
  apply Neqb_true_iff_Neq in E1. rewrite E1. easy.
Qed. *)
Admitted.

(** [QUplus] left with !! equal to !!. *)
Lemma QUplus_QUinvalid_l (q : Quantity) : !! + q == !!.
Proof. try easy. Qed.

(** [QUplus] right with !! equal to !!. *)
Lemma QUplus_QUinvalid_r (q : Quantity) : q + !! == !!.
Proof. rewrite QUplus_comm. try easy. Qed.

(** [QUplus] is associative. *)
Lemma QUplus_assoc (q1 q2 q3 : Quantity) :
  (q1 + q2) + q3 == q1 + (q2 + q3).
Proof.
(*   destruct q1 as [v1 n1|], q2 as [v2 n2|], q3 as [v3 n3|]; try easy.
  - unfold QUplus.
    destruct (n1=?n2)%NU eqn:E1, (n2=?n3)%NU eqn:E2; try easy.
    + rewrite E1. apply Neqb_true_iff_Neq in E1. rewrite <- E1 in E2.
      rewrite E2. rewrite Rplus_assoc. easy.
    + assert (n1 =? n3 = false)%NU.
      { apply Neqb_true_iff_Neq in E1. rewrite <- E1 in E2. auto. }
      rewrite H. easy.
    + rewrite E1. easy.
  - rewrite ?QUplus_QUinvalid_l,?QUplus_QUinvalid_r. easy.
Qed. *)
Admitted.



(** ** Quantity opposition *)
Definition QUopp (q : Quantity) : Quantity :=
  match q with
  | QUmake v n => QUmake (Ropp v) n
  | _ => !!
  end.
Notation "- q" := (QUopp q) : QU_scope.

(** Register that [QUopp] is compatible for [QUeq]. *)
Add Parametric Morphism : QUopp
  with signature QUeq ==> QUeq as QUopp_QUeq_mor.
Proof.
  intros q1 q2. unfold QUeq,QUeqb,QUcmpb,Ueqb,QUopp in *.
  destruct q1 as [v1 n1|], q2 as [v2 n2|]; try easy.
  rewrite ?andb_true_iff,?Reqb_true_iff,?NUeqb_true_iff.
  intros [H1 H2]; rewrite H1,H2. split; auto.
Qed.



(** ** Quantity substraction *)
Definition Qsub (q1 q2 : Quantity) : Quantity := QUplus q1 (QUopp q2).
Infix "-" := Qsub : QU_scope.

(* (** Register that [Qsub] is compatible for [QUeq]. *)
Add Parametric Morphism : Qsub
  with signature QUeq ==> QUeq ==> QUeq as Qsub_mor.
Proof.
  intros. unfold Qsub. rewrite H,H0. reflexivity.
Qed. *)



(** ** Quantity multiplication *)
Definition QUmult (q1 q2 : Quantity) : Quantity :=
  match q1,q2 with
  | QUmake v1 n1, QUmake v2 n2 => QUmake (Rmult v1 v2) (Nmult n1 n2)
  | _, _ => !!
  end.
Infix "*" := QUmult : QU_scope.

(** [QUmult] is commutative. *)
Lemma QUmult_comm (q1 q2 : Quantity) : q1 * q2 == q2 * q1.
Proof.
  destruct q1,q2; try easy. unfold QUmult.
  rewrite Rmult_comm, Nmult_comm. easy.
Qed.

(** [QUmult] is associative. *)
Lemma QUmult_assoc (q1 q2 q3 : Quantity) : (q1 * q2) * q3 == q1 * (q2 * q3).
Proof.
  destruct q1,q2,q3; try easy. simpl.
  rewrite Rmult_assoc, Nmult_assoc. easy.
Qed.

Lemma QUmult_1_l q : (genQU 1 #1) * q == q.
Proof.
  destruct q; try easy. unfold QUmult. simpl.
  apply QUeq_QUmake_bij. split; try ring.
  rewrite u2n_Unone. unfold Nmult. destruct n. simpl.
  apply Neq_iff_each_eq. simpl. split; try field.
  destruct Ndims; auto.
Qed.

Lemma QUmult_1_r q : q * (genQU 1 #1) == q.
Proof.
  intros. rewrite QUmult_comm. apply QUmult_1_l.
Qed.

(** Register that [QUmult] is compatible for [QUeq]. *)
Add Parametric Morphism : QUmult
  with signature QUeq ==> QUeq ==> QUeq as QUmult_QUeq_QUeq_mor.
Proof.
  intros q1 q2 H1 q3 q4 H2. 
  unfold QUeq,QUeqb,QUcmpb,QUplus,Neqb in *.
  destruct q1 as [v1 (c1,d1)|], q2 as [v2 (c2,d2)|], q3 as [v3 (c3,d3)|], 
    q4 as [v4 (c4,d4)|]; try easy. simpl in *.
  rewrite ?andb_true_iff in *.
  destruct H1 as [H1a [H1b H1c]].
  destruct H2 as [H2a [H2b H2c]].
  rewrite ?Reqb_true_iff,?Qeq_bool_iff,?Deqb_true_iff_Deq in *.
  rewrite H1a,H1b,H1c,H2a,H2b,H2c.
  repeat split.
Qed.

(** [QUvalue] with [Qmult] and [real2QU] *)
Lemma QUvalue_Qmult_real2QU q r : (QUvalue (q) * r)%R = QUvalue (q * r).
Admitted.

(** [QUmult] cancellation *)
Lemma QUmult_cancel_l q1 q2 q3 : q1 == q2 -> q3 * q1 == q3 * q2.
Admitted.

Lemma QUmult_cancel_r q1 q2 q3 : q1 == q2 -> q1 * q3 == q2 * q3.
Admitted.



(** ** Quantity inversion *)
Definition QUinv (q : Quantity) : Quantity :=
  match q with
  | QUmake v n => QUmake (Rinv v) (Ninv n)
  | _ => !!
  end.
Notation "/ q" := (QUinv q) : QU_scope.

Lemma QUmult_QUinv q (H1 : !q) (H2 : not (QUcoef q == 0)%Q) 
  (H3 : (QUvalue q <> (0%R))) 
  : q * /q == genQU 1 #1.
Proof.
  unfold QUinv. destruct q; try easy.
  destruct n eqn:E1. simpl in *. unfold genQU.
  apply QUeq_QUmake_bij. split.
  - field. auto.
  - unfold Ninv,Nmult. simpl. rewrite Dplus_Dopp_r. rewrite u2n_Unone.
    apply Neq_iff_each_eq. split; simpl; auto. field. auto.
Qed.

Lemma QUmult_QUinv_simpl_mid q1 q2 (H1 : !q1) (H2 : not (QUcoef q1 == 0)%Q) 
  (H3 : QUvalue q1 <> (0%R)) : q1 * q2 * /q1 == q2.
Proof.
  intros.
  rewrite QUmult_assoc. rewrite QUmult_comm. rewrite QUmult_assoc.
  rewrite (QUmult_comm _ q1).
  rewrite (QUmult_QUinv _ H1); auto.
  rewrite QUmult_1_r. easy.
Qed.

(** Register that [QUinv] is compatible for [QUeq]. *)
Add Parametric Morphism : QUinv
  with signature QUeq ==> QUeq as QUinv_QUeq_mor.
Proof.
  intros q1 q2. unfold QUeq,QUeqb,QUcmpb,Ueqb,QUinv in *.
  destruct q1 as [v1 n1|], q2 as [v2 n2|]; try easy.
  rewrite ?andb_true_iff,?Reqb_true_iff,?Neqb_true_iff_Neq.
  intros [H1 H2]. rewrite H1. rewrite H2. easy.
Qed.



(** ** Quantity division *)
Definition QUdiv (q1 q2 : Quantity) : Quantity := QUmult q1 (QUinv q2).
Infix "/" := QUdiv : QU_scope.

(** Register that [QUdiv] is compatible for [QUeq]. *)
Add Parametric Morphism : QUdiv
  with signature QUeq ==> QUeq ==> QUeq as QUdiv_QUeq_QUeq_QUeq_mor.
Proof.
  intros. unfold QUdiv. rewrite H0. rewrite H. easy.
Qed.



(** ** Tactic for solving equality of quantities *)

(** Solve Q1 == Q2 *)
Ltac pfqeq :=
  intros;
  compute;
  (* replace PI_Q *)
  try rewrite <- PI_Q_eq_PI; compute;
  (** solve Req_EM_T *)
  try destruct (Req_EM_T);
  (** solve pair *)
  repeat match goal with
  | |- QUmake _ _ = QUmake _ _ => f_equal
  | |- (_, _) = (_, _) => f_equal
  | |- _ => try field; try lra
  end;
  (* solve extra operations of R *)
  autorewrite with R in *; auto with R 
  .



(** ** Arithmetic Examples *)

(* plus with same Unit *)
Goal (genQU 3 's) + (genQU 2 's) == (genQU 1 's) + (genQU 4 's).
Proof. pfqeq. Qed.

(* plus with different Unit is not supported, need manual convertion *)
Goal (genQU 3600 's) + (genQU 30 'min) == (genQU 90 'min).
Proof. pfqeq. Abort.

(* Notice that, the convertion could manipulate the output unit exactly. *)
Goal (genQU 3600 's) + (QUconv (genQU 30 'min) 's) == (genQU 5400 's). pfqeq. Qed.
Goal (QUconv (genQU 3600 's) 'min) + (genQU 30 'min) == (genQU 90 'min). pfqeq. Qed.
Goal (QUconv (genQU 3600 's) 'hrs) + (QUconv (genQU 30 'min) 'hrs) == (genQU 1.5 'hrs). 
  pfqeq. Qed.

Goal (genQU 3 'kg) + (genQU 1000 'g) == (genQU 4 'kg).
Proof. pfqeq. Abort.

(* multiply with same Unit *)
Goal (genQU 3 's) * (genQU 2 's) == (genQU 6 ('s²)%U).
Proof. pfqeq. Qed.

(* inversion *)
Goal (QUconv (/(genQU 3 'min)) 'Hz) == (genQU (1/180) 'Hz).
Proof. pfqeq. Qed.

(* divide with different Unit *)
Goal (genQU 6000 ('m*'s)%U) / (genQU 3 'm) == (genQU 2000 's).
Proof. pfqeq. Qed.


(** * Complex operations of quantities *)


(** ** Power of quantity with an integer numbers *)
Definition QUpow (q : Quantity) (z : Z) : Quantity :=
  match q with
  | QUmake v n => QUmake (powerRZ v z) (Npow n z)
  | _ => q
  end.
Notation " q ² " := (QUpow q 2) (at level 1) : QU_scope.
Notation " q ³ " := (QUpow q 3) (at level 1) : QU_scope.
Notation " q ⁴ " := (QUpow q 4) (at level 1) : QU_scope.
Notation " q ⁵ " := (QUpow q 5) (at level 1) : QU_scope.
Notation "q ^ n" := (QUpow q n) : QU_scope.

Example QUpow_ex1 : (genQU 4 'm) ^ 4 = genQU 256 ('m² * 'm * 'm)%U.
Proof. pfqeq. Qed.



(** ** General unary operation of quantity which won't change it's unit *)
Definition QUop1 (q : Quantity) (f : R -> R) : Quantity :=
  match q with
  | QUmake v n => QUmake (f v) n
  | _ => !!
  end.

(** ** Several unary operations of quantity *)
Definition QUabs q := QUop1 q Rabs.



(** ** Trigonemetric functions require input unit is 'rad, and output unit is
 1. *)
Definition QUtrig (q : Quantity) (f : R -> R) : Quantity :=
  match QUconv q 'rad with
  | QUmake v _ => QUmake (f v) Nunit_one
  | !! => !!
  end.

Definition QUsin q := QUtrig q sin.
Definition QUcos q := QUtrig q cos.
Definition QUtan q := QUtrig q tan.

#[global]  Opaque sin cos tan.

Example QUsin_ex1 (r : R) :
  let theta := genQU r 'rad in
    (QUsin theta)² + (QUcos theta)² == genQU 1 #1.
Proof. pfqeq. Qed.


(** ** Inverse Trigonemetric functions require input unit is 1 and output unit 
 is 'rad. *)
Definition QUinvtrig (q : Quantity) (f : R -> R) : Quantity :=
  match q with
  | QUmake v n => 
    if (Neqb n Nunit_one) 
    then QUmake (f v) (u2n 'rad)
    else !!
  | !! => !!
  end.

Definition QUasin q := QUinvtrig q asin.
Definition QUacos q := QUinvtrig q acos.
Definition QUatan q := QUinvtrig q atan.



(** ** Square root of quantity *)

(** Note that QUsqrt is correct only when:
1. value of Q is [0,+)
2. coefficient of NUnit of Q is [0,+)
3. dimensions of NUnit of Q is all even
*)
Definition QUsqrt_cond (q : Quantity) : bool :=
  match q with
  | QUmake v n => (0 <=? v)%R && (Nsqrt_cond n)
  | _ => false
  end.

Lemma QUsqrt_cond_true_iff (q : Quantity) : QUsqrt_cond q = true <->
  match q with
  | QUmake v (mkNunit c d) => (0 <= v)%R /\ (0 <= c)%Q /\ Dsqrt_cond d = true
  | _ => False
  end.
Proof.
  destruct q; try easy.
  destruct n. unfold QUsqrt_cond, Nsqrt_cond in *. simpl.
  rewrite ?andb_true_iff.
  rewrite Qle_bool_iff. rewrite Rleb_true_iff. easy.
Qed.
  
Definition QUsqrt (q : Quantity) : Quantity :=
  match q with
  | QUmake v n => QUmake (sqrt v) (Nsqrt n)
  | _ => !!
  end.

Example QUsqrt_ex1 : QUsqrt (genQU 4 ('m⁶)%U) = genQU 2 ('m³)%U.
Proof. pfqeq. Qed.

(* error example, although got a result, but meaningless *) 
(* Compute QUsqrt (genQU 1 (-1)%Q * #'s)². *)
Goal (genQU 1 ((-1)%Q * 's)%U)² = genQU 1 ('s*'s)%U.
compute. f_equal. field. Qed.

Lemma QUsqrt_QUsqr q : QUsqrt_cond q = true -> QUsqrt (q²) == q.
Proof.
  intros. unfold QUsqrt,Nsqrt in *.
  unfold QUabs,QUop1,QUpow.
  destruct q as [v (c,d)|]; try easy. simpl. 
  rewrite Dsqrt_Dcmul2.
  apply QUsqrt_cond_true_iff in H. do 2 destruct H as [? H].
  apply QUeq_QUmake_bij. split.
  - autorewrite with R; auto.
  - apply Neq_iff_each_eq. simpl. split; auto.
    assert (c * (c * 1) == c * c)%Q. { field. } rewrite H2.
    rewrite Qsqrt_sqr; try easy.
Qed.

Lemma QUsqr_QUsqrt q : QUsqrt_cond q = true -> (QUsqrt q)² == q.
Proof.
  intros. unfold QUsqrt,QUsqrt_cond,QUpow in *.
  destruct q as [v (c,d)|]; try easy. simpl in *.
  unfold Nsqrt_cond in *. simpl in *.
  rewrite ?andb_true_iff in H.
  rewrite Rleb_true_iff, Qle_bool_iff in *. do 2 destruct H as [? H].
  apply QUeq_QUmake_bij. split.
  - autorewrite with R; auto.
  - apply Neq_iff_each_eq. simpl. split.
    + rewrite Qmult_1_r. rewrite sqr_Qsqrt; easy.
    + rewrite Dcmul2_Dsqrt; auto.
Qed.

(** Register that [QUsqrt] is compatible for [QUeq]. *)
Add Parametric Morphism : QUsqrt
  with signature QUeq ==> QUeq as QUsqrt_QUeq_QUeq_mor.
Proof.
  intros. destruct x,y; try easy.
  apply QUeq_QUmake_bij in H. destruct H. rewrite H.
  apply QUeq_QUmake_bij. rewrite H0. easy.
Qed.



(** ** Any power of quantity which the unit of base and exponent both are 1 *)
Definition QUpower (base exp : Quantity) : Quantity :=
  match base,exp with
  | QUmake v1 n1, QUmake v2 n2 =>
    if ((Neqb n1 Nunit_one) && (Neqb n2 Nunit_one))
    then QUmake (Rpower v1 v2) n1
    else !!
  | _, _ => !!
  end.

