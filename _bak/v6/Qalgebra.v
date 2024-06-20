(*
  purpose   : Algebric of Units.
  author    : Zhengpu Shi
  date      : 2022.04
  
  remark    :
  1. differences between arithmetic and algebra
  (1). arithmetic means add,sub,mul,div of numbers, prefer calculate directly.
  (2). algebra use numbers and variables sametime, and mainly use laws to 
    deal with the problem, prefer transform, not calculate.
  (3). algebra include power, algorithm and complex numbers too.
  
  2. u1 +/- u2, only if dims(u1) == dims(u2)

*)

(* From MyStdLibExt Require Export RExt. *)

Require Export Unit NUnit SI Uconv.


(** * Quantity: data type for support algebric of [Unit]. *)

Declare Scope Qu_scope.
Delimit Scope Qu_scope with Qu.
Open Scope Qu_scope.


(** ** Definition of Quantity *)

(** A quantity is an option type that contains a unit type, and Qinvalid means 
  an error operation. For example, add with time and length is invalid. *)
Inductive Quantity : Set :=
  | Qumake (u : Unit)
  | Qinvalid.

(* Bind Scope Qu_scope with Quantity. *)

Notation "! q" := (q <> Qinvalid) (at level 0) : Qu_scope.
Notation "!!" := (Qinvalid) (at level 0) : Qu_scope.

(* Coercion that from Unit to Quantity *)
Coercion Qumake : Unit >-> Quantity.

(** Qumake is injective. *)
Lemma Qumake_inj u1 u2 : Qumake u1 = Qumake u2 <-> u1 = u2.
Proof.
  split; intro H; inversion H; auto.
Qed.



(** ** Get numerical value of a quantity *)
Definition Qcoef_opt (q : Quantity) : option R :=
  match q with
  | Qumake u => let (c,d) := u2n u in Some c
  | _ => None
  end.

Definition Qcoef (q : Quantity) (H : !q) : R.
Proof.
  destruct q; try easy. exact (let (c,d) := u2n u in c).
Defined.



(** ** Get Dimensions of a quantity *)
Definition Qdim_opt (q : Quantity) : option Dims :=
  match q with
  | Qumake u  => let (c,d) := u2n u in Some d
  | _ => None
  end.

Definition Qdim (q : Quantity) (H : !q) : Dims.
Proof.
  destruct q; try easy. exact (let (c,d) := u2n u in d).
Defined.



(** ** Get [Unit] of a quantity *)
Definition Qunit (q : Quantity) (H : !q) : Unit.
Proof.
  destruct q; try easy.
Defined.

(** Qunit is equal to a unit created by n2u with Qcoef and Qdim. *)
Lemma Qunit_eq_Qcoef_Qdim (q : Quantity) (H : !q) : 
  Qunit q H == n2u (Qcoef q H, Qdim q H).
Proof.
  destruct q; try easy. unfold Qcoef, Qdim, Qunit.
  destruct (u2n u) eqn:E1. unfold Ueq. rewrite u2n_n2u. auto.
Qed.



(** ** Check if two quantities are similar *)

(** Quantities are similar when they are valid and the units are similar. *)
Definition Qsimb (q1 q2 : Quantity) : bool :=
  match q1, q2 with
  | Qumake u1, Qumake u2 => Usimb u1 u2
  | _, _ => false
  end.

(** Use [Qsimb] can check a Quantity's similar unit. *)
(* Compute Qsimb 'hrs 'min. *)


(** Propersional similar of quantities. *)
Definition Qsim q1 q2 := Qsimb q1 q2 = true.



(** ** Boolean comparison of two quantities *)

Definition Qcmpb (q1 q2 : Quantity) (Rcmpb : R -> R -> bool) : bool :=
  match q1,q2 with
  | Qumake u1, Qumake u2 => Ueqb u1 u2
  | !!, !! => true  (* take care! *)
  | _, _ => false
  end.

(** Equal,Less Than, Less Equal of two quantities *)
Definition Qeqb (q1 q2 : Quantity) : bool := Qcmpb q1 q2 Reqb.
Definition Qltb (q1 q2 : Quantity) : bool := Qcmpb q1 q2 Rltb.
Definition Qleb (q1 q2 : Quantity) : bool := Qcmpb q1 q2 Rleb.

Infix "=?"  := Qeqb : Qu_scope.
Infix "<?"  := Qltb : Qu_scope.
Infix "<=?" := Qleb : Qu_scope.

(** [Qeqb] equal to [Ueqb] when the quantity are valid. *)
Lemma Qeqb_eq_Ueqb u1 u2 : Qeqb (Qumake u1) (Qumake u2) = Ueqb u1 u2.
Proof. auto.
Qed.

(** [Qeqb] is true, it reflexive. *)
Lemma Qeqb_true_refl q : q =? q = true.
Proof.
  destruct q; auto. rewrite Qeqb_eq_Ueqb. apply Ueqb_true_refl.
Qed.

(** [Qeqb] is commutative *)
Lemma Qeqb_comm q1 q2 : (q1 =? q2) = (q2 =? q1).
Proof.
  destruct q1,q2; auto. repeat rewrite Qeqb_eq_Ueqb. apply Ueqb_comm.
Qed.

(** [Qeqb] left with [!!] is true, iff the quantity is !! too. *)
Lemma Qeqb_left_qinvalid_true_iff : forall q, 
  ((!! =? q) = true) -> q = Qinvalid.
Proof.
  intros. destruct q; simpl in *; auto. easy.
Qed.

(** [Qeqb] right with [!!] is true, iff the quantity is !! too. *)
Lemma Qeqb_right_qinvalid_true_iff : forall q, 
  ((q =? !!) = true) -> q = Qinvalid.
Proof.
  intros. destruct q; simpl in *; auto. easy.
Qed.

(** [Qeqb] is true, it is transitive *)
Lemma Qeqb_true_trans q1 q2 q3 : (q1 =? q2 = true) -> (q2 =? q3 = true) ->
  (q1 =? q3 = true).
Proof.
  destruct q1 as [u1|], q2 as [u2|], q3 as [u3|]; auto.
  - repeat rewrite Qeqb_eq_Ueqb. apply Ueqb_true_trans.
  - intros H1 H2.
    apply Qeqb_left_qinvalid_true_iff in H2.
    apply Qeqb_right_qinvalid_true_iff in H1.
    easy.
Qed.

(** [Qeqb] is true, iff coefficient and dimensions all equal. *)
Lemma Qeqb_true_iff_coef_dims q1 q2 : (q1 =? q2 = true) <->
  (Qcoef_opt q1 = Qcoef_opt q2) /\ (Qdim_opt q1 = Qdim_opt q2).
Proof.
  unfold Qcoef_opt, Qdim_opt. destruct q1,q2; try easy.
  unfold Qeqb. unfold Qcmpb. unfold Ueqb.
  destruct (u2n u),(u2n u0).
  rewrite NUeqb_true_iff. split; intro H; inversion H; auto.
  inversion H0; inversion H1. auto.
Qed.

(** ** Propositional comparison of two quantities *)
Definition Qeq (q1 q2 : Quantity) : Prop := q1 =? q2 = true.
Definition Qlt (q1 q2 : Quantity) : Prop := q1 <? q2 = true.
Definition Qle (q1 q2 : Quantity) : Prop := q1 <=? q2 = true.

Infix "==" := Qeq : Qu_scope.
Infix "<>" := (not Qeq) : Qu_scope.
Infix "<" := Qlt : Qu_scope.
Infix "<=" := Qle : Qu_scope.

(** Qeq is an equivalence relation. *)

Lemma Qeq_refl q : q == q.
Proof.
  unfold Qeq. intros. apply Qeqb_true_refl.
Qed.

Lemma Qeq_comm q1 q2 : q1 == q2 -> q2 == q1.
Proof.
  unfold Qeq. intros. rewrite Qeqb_comm. auto.
Qed.

Lemma Qeq_trans q1 q2 q3 : q1 == q2 -> q2 == q3 -> q1 == q3.
Proof.
  unfold Qeq. intros. apply (Qeqb_true_trans q1 q2 q3); auto.
Qed.

Lemma Qeq_equiv : equivalence Quantity Qeq.
Proof.
  intros. refine (Build_equivalence _ _ _ _ _); unfold Qeq.
  - intros x. apply Qeq_refl.
  - intros x1 x2 x3. apply Qeqb_true_trans.
  - intros x1 x2. rewrite Qeqb_comm. auto.
Qed.

(** Example, before registered relation, we can't rewrite. *)
Goal forall (q1 q2 q3 : Quantity), q1 == q2 -> q3 == q2 -> q1 == q3.
intros. (* Fail rewrite H. *) Abort.

(** Register that [Qeq] is equivalence relation. *)
Add Parametric Relation : Quantity Qeq
  reflexivity proved by (equiv_refl _ _ Qeq_equiv)
  symmetry proved by (equiv_sym _ _ Qeq_equiv)
  transitivity proved by (equiv_trans _ _ Qeq_equiv)
  as Qeq_rel.

(** Example, after registered relation, we can rewrite. *)
Goal forall (q1 q2 q3 : Quantity), q1 == q2 -> q3 == q2 -> q1 == q3.
intros. rewrite H. symmetry. auto. Qed.


(** [Qeq] iff [Qunit] of the quantities are equal. *)
Lemma Qeq_iff_Qunit_eq (q1 q2 : Quantity) (H1 : !q1) (H2 : !q2) :
  q1 == q2 <-> (Qunit q1 H1 == Qunit q2 H2)%U.
Proof.
  destruct q1,q2; simpl; try easy.
  unfold Qeq. rewrite Qeqb_eq_Ueqb. unfold Ueq. unfold Ueqb.
  rewrite NUeqb_true_iff. easy.
Qed.

(** [Qeq] iff [Ueq] when the quantity are valid. *)
Lemma Qeq_if_Ueq u1 u2 : Qeq (Qumake u1) (Qumake u2) <-> Ueq u1 u2.
Proof.
  unfold Qeq. rewrite Qeqb_eq_Ueqb. rewrite Ueq_iff_Ueqb. easy.
Qed.




(** * Quantity Arithmetic Operations *)


(** ** Automatic for for simplify context and goals contain Dims_xx *)

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



(** ** Quantity addition *)

(** Quantity addition is valid only when they are similar and not valid *)
Definition Qplus (q1 q2 : Quantity) : Quantity :=
  match q1,q2 with
  | Qumake u1, Qumake u2 =>
    let '(c1, d1) := u2n u1 in
    let '(c2, d2) := u2n u2 in
      if (Dims_eqb d1 d2)
      then Qumake (n2u (Rplus c1 c2, d1))
      else !!
  | _, _ => !!
  end.
Infix "+" := Qplus : Qu_scope.

(** [Qplus] is commutative. *)
Lemma Qplus_comm (q1 q2 : Quantity) : q1 + q2 == q2 + q1.
Proof.
  destruct q1 as [u1|], q2 as [u2|]; try easy.
  unfold Qplus.
  destruct (u2n u1) as (c1,d1), (u2n u2) as (c2,d2).
  rewrite Dims_eqb_comm. rewrite Rplus_comm.
  destruct (Dims_eqb d2 d1) eqn:E3.
  - apply Dims_eqb_true_iff in E3. subst. apply Qeq_refl.
  - apply Qeq_refl.
Qed.

(** [Qplus] left with !! equal to !!. *)
Lemma Qplus_Qinvalid_l (q : Quantity) : !! + q == !!.
Proof. simpl. apply Qeq_refl. Qed.

(** [Qplus] right with !! equal to !!. *)
Lemma Qplus_Qinvalid_r (q : Quantity) : q + !! == !!.
Proof. rewrite Qplus_comm. apply Qplus_Qinvalid_l. Qed.

(** [Qplus] is associative. *)
Lemma Qplus_assoc (q1 q2 q3 : Quantity) :
  (q1 + q2) + q3 == q1 + (q2 + q3).
Proof.
  destruct q1 as [u1|], q2 as [u2|], q3 as [u3|]; try easy;
  unfold Qeq, Qeqb, Qcmpb, Qplus.
  - destruct (u2n u1) as (c1,d1), (u2n u2) as (c2,d2), (u2n u3) as (c3,d3).
    destruct (Dims_eqb d1 d2) eqn:E1, (Dims_eqb d2 d3) eqn:E2; auto.
    + autorewrite with QALG. tac_dims_gen_exp; repeat tac_dims_simp.
      apply Ueqb_n2u_true_iff_coef_dims; split; auto; ring.
    + autorewrite with QALG. tac_dims_gen_exp; repeat tac_dims_simp. auto.
    + autorewrite with QALG. tac_dims_gen_exp; repeat tac_dims_simp. auto.
  - destruct (u2n u1) as (c1,d1), (u2n u2) as (c2,d2).
    destruct (Dims_eqb d1 d2) eqn:E1; auto.
Qed.

(** Example, before registered morphism, we can't rewrite. *)
Goal forall (q1 q2 q3 : Quantity), q1 == q2 -> q1 + q3 == q2 + q3.
intros. (* Fail rewrite H. *) Abort.

(** Register that [Qplus] is compatible for [Qeq]. *)
Add Parametric Morphism : Qplus
  with signature Qeq ==> Qeq ==> Qeq as Qplus_mor.
Proof.
  intros. unfold Qeq,Qeqb,Qcmpb,Ueqb,Qplus in *.
  destruct x, y, x0, y0; try easy.
  destruct (u2n u),(u2n u0),(u2n u1),(u2n u2).
  apply NUeqb_true_iff in H; inversion H.
  apply NUeqb_true_iff in H0; inversion H0.
  subst. destruct (Dims_eqb d0 d2); auto.
  apply Ueqb_true_refl.
Qed.

(** Example, after registered morphism, we can rewrite. *)
Goal forall (q1 q2 q3 : Quantity), q1 == q2 -> q1 + q3 == q2 + q3.
intros. rewrite H. reflexivity. Qed.



(** ** Quantity opposition *)
Definition Qopp (q : Quantity) : Quantity :=
  match q with
  | Qumake u =>
    let '(c, d) := u2n u in n2u (Ropp c, d)
  | _ => !!
  end.
Notation "- q" := (Qopp q) : Qu_scope.

(** Register that [Qopp] is compatible for [Qeq]. *)
Add Parametric Morphism : Qopp
  with signature Qeq ==> Qeq as Qopp_mor.
Proof.
  intros. unfold Qeq,Qeqb,Qcmpb,Ueqb,Qopp in *.
  destruct x, y; try easy.
  destruct (u2n u),(u2n u0).
  apply NUeqb_true_iff in H. inversion H. subst.
  apply Ueqb_true_refl.
Qed.



(** ** Quantity substraction *)
Definition Qsub (q1 q2 : Quantity) : Quantity := Qplus q1 (Qopp q2).
Infix "-" := Qsub : Qu_scope.

(** Register that [Qsub] is compatible for [Qeq]. *)
Add Parametric Morphism : Qsub
  with signature Qeq ==> Qeq ==> Qeq as Qsub_mor.
Proof.
  intros. unfold Qsub. rewrite H,H0. reflexivity.
Qed.



(** ** Quantity multiplication *)
Definition Qmult (q1 q2 : Quantity) : Quantity :=
  match q1,q2 with
  | Qumake u1, Qumake u2 =>
    let '(c1, d1) := u2n u1 in
    let '(c2, d2) := u2n u2 in
      n2u (Rmult c1 c2, Dims_plus d1 d2)
  | _, _ => !!
  end.
Infix "*" := Qmult : Qu_scope.

(** [Qmult] is commutative. *)
Lemma Qmult_comm (q1 q2 : Quantity) : q1 * q2 == q2 * q1.
Proof.
  destruct q1 as [u1|], q2 as [u2|]; try easy.
  unfold Qmult.
  destruct (u2n u1) as (c1,d1), (u2n u2) as (c2,d2).
  rewrite Dims_plus_comm. rewrite Rmult_comm.
  destruct (Dims_eqb d2 d1) eqn:E3.
  - apply Dims_eqb_true_iff in E3. subst. apply Qeq_refl.
  - apply Qeq_refl.
Qed.

(** [Qmult] is associative. *)
Lemma Qmult_assoc (q1 q2 q3 : Quantity) : (q1 * q2) * q3 == q1 * (q2 * q3).
Proof.
  destruct q1 as [u1|], q2 as [u2|], q3 as [u3|]; try easy;
  unfold Qeq, Qeqb, Qcmpb, Qmult.
  destruct (u2n u1) as (c1,d1), (u2n u2) as (c2,d2), (u2n u3) as (c3,d3).
  autorewrite with QALG.
  apply Ueqb_n2u_true_iff_coef_dims; split.
  ring. apply Dims_plus_assoc.
Qed.

(** Register that [Qmult] is compatible for [Qeq]. *)
Add Parametric Morphism : Qmult
  with signature Qeq ==> Qeq ==> Qeq as Qmult_mor.
Proof.
  intros. unfold Qeq,Qeqb,Qcmpb,Ueqb,Qmult in *.
  destruct x, y, x0, y0; try easy.
  destruct (u2n u),(u2n u0),(u2n u1),(u2n u2).
  apply NUeqb_true_iff in H; inversion H.
  apply NUeqb_true_iff in H0; inversion H0.
  subst. 
  apply Ueqb_true_refl.
Qed.

Lemma Qmult_1_l q : 1 * q == q.
Proof.
  intros. unfold Qeq,Qeqb,Qcmpb,Ueqb,Qmult in *.
  destruct q; try easy.
  destruct (u2n u) eqn:E1, (u2n 1) eqn:E2. rewrite u2n_n2u.
  rewrite (u2n_Unone) in E2; inversion E2.
  apply NUeqb_true_iff. f_equal; try ring.
  apply Dims_plus_0_l.
Qed.

Lemma Qmult_1_r q : q * 1 == q.
Proof.
  intros. rewrite Qmult_comm. apply Qmult_1_l.
Qed.



(** ** Quantity inversion *)
Definition Qinv (q : Quantity) : Quantity :=
  match q with
  | Qumake u =>
    let '(c, d) := u2n u in n2u (Rinv c, Dims_opp d)
  | _ => !!
  end.
Notation "/ q" := (Qinv q) : Qu_scope.

(** Register that [Qinv] is compatible for [Qeq]. *)
Add Parametric Morphism : Qinv
  with signature Qeq ==> Qeq as Qinv_mor.
Proof.
  intros. unfold Qeq,Qeqb,Qcmpb,Ueqb,Qinv in *.
  destruct x, y; try easy.
  destruct (u2n u),(u2n u0).
  apply NUeqb_true_iff in H. inversion H. subst.
  apply Ueqb_true_refl.
Qed.

Lemma Qmult_Qinv q (H1 : !q) (H2 : Qcoef q H1 <> 0) : q * /q = 1.
Proof.
  intros. unfold Qeq,Qeqb,Qcmpb,Ueqb,Qmult,Qinv in *.
  destruct q; try easy.
  destruct (u2n u) eqn:E1. rewrite u2n_n2u.
  rewrite Dims_plus_opp_r. compute. rewrite Rinv_r; auto.
  unfold Qcoef in *. simpl in H2.
  rewrite (Ugetcoef_u2n u r d) in H2; auto.
Qed.

Lemma Qmult_Qinv_simpl_mid q1 q2 (H1 : !q1) (H2 : Qcoef q1 H1 <> 0) :
  q1 * q2 * /q1 == q2.
Proof.
  intros.
  rewrite Qmult_assoc. rewrite Qmult_comm. rewrite Qmult_assoc.
  rewrite (Qmult_comm _ q1). rewrite (Qmult_Qinv _ H1); auto.
  rewrite Qmult_1_r. apply Qeq_refl.
Qed.



(** ** Quantity division *)
Definition Qdiv (q1 q2 : Quantity) : Quantity := Qmult q1 (Qinv q2).
Infix "/" := Qdiv : Qu_scope.

(** Register that [Qdiv] is compatible for [Qeq]. *)
Add Parametric Morphism : Qdiv
  with signature Qeq ==> Qeq ==> Qeq as Qdiv_mor.
Proof.
  intros. unfold Qdiv. rewrite H,H0. reflexivity.
Qed.



(** ** Tactic for solving equality of quantities *)

(** Solve Q1 == Q2 *)
Ltac pfqeq :=
  compute;
  destruct Req_EM_T as [H11|H12]; auto;
  destruct H12; try field.



(** ** Arithmetic Examples *)

(* direct compare *)
Goal 1000 * 'g == 1 * 'kg.
Proof. pfqeq. Qed.

(* plus with same Unit *)
Goal (3 * 's) + (2 * 's) == (1*'s) + (4*'s).
Proof. pfqeq. Qed.

(* plus with different Unit *)
Goal (10*'s) + (1*'min) == (70*'s).
Proof. pfqeq. Qed.

Goal (3*'kg) + (1000*'g) == (4*'kg).
Proof. pfqeq. Qed.

(* opposition *)
Goal - (3*'min) == ((-180)%R*'s).
Proof. pfqeq. Qed.

(* multiply with different Unit *)
Goal (3*'km) * (2*'s) == (6000*('m*'s)).
Proof. pfqeq. Qed.

(* inversion *)
Goal /(3*'min) == ((1/180)%R*'Hz).
Proof. pfqeq. Qed.

(* divide with different Unit *)
Goal (6000*('m*'s)) / (3*'m) == (2000*'s).
Proof. pfqeq. Qed.



(** * Complex operations of quantities *)



(** ** Power of quantity with an integer numbers *)
Definition Qpow (q : Quantity) (z : Z) : Quantity :=
  match q with
  | Qumake u => Upow u z
  | _ => q
  end.
Notation " q ² " := (Qpow q 2) (at level 1) : Qu_scope.
Notation " q ³ " := (Qpow q 3) (at level 1) : Qu_scope.
Notation " q ⁴ " := (Qpow q 4) (at level 1) : Qu_scope.
Notation " q ⁵ " := (Qpow q 5) (at level 1) : Qu_scope.
Notation "q ^ n" := (Qpow q n) : Qu_scope.

(** Register that [Qpow] is compatible for [Qeq]. *)
Add Parametric Morphism : Qpow
  with signature Qeq ==> eq ==> Qeq as Qpow_mor.
Proof.
  intros. unfold Qeq,Qeqb,Qcmpb,Ueqb,Qpow in *.
  destruct x, y; try easy.
(*   destruct (u2n u),(u2n u0). *)
  destruct (u2n u)eqn:E1,(u2n u0)eqn:E2.
  apply NUeqb_true_iff in H; inversion H.
  subst. rewrite <- E2 in E1. rewrite (u2n_Upow u u0); auto.
  apply Ueqb_true_refl.
Qed.

Example Qpow_ex1 : (4*'m)⁴ == 256 * 'm² * 'm * 'm.
Proof. pfqeq. Qed.



(** ** General unary operation of quantity which won't change it's unit *)
Definition Qop1 (q : Quantity) (f : R -> R) : Quantity :=
  match q with
  | Qumake u =>
    let '(c, d) := u2n u in n2u (f c, d)
  | _ => !!
  end.

(** Register that [Qop1] is compatible for [Qeq]. *)
Add Parametric Morphism : Qop1
  with signature Qeq ==> eq ==> Qeq as Qop1_mor.
Proof.
  intros. unfold Qeq,Qeqb,Qcmpb,Ueqb,Qop1 in *.
  destruct x, y; try easy.
(*   destruct (u2n u),(u2n u0). *)
  destruct (u2n u)eqn:E1,(u2n u0)eqn:E2.
  repeat rewrite u2n_n2u.
  apply NUeqb_true_iff in H; inversion H. subst.
  apply NUeqb_true_refl.
Qed.



(** ** Several unary operations of quantity *)
Definition Qsin q := Qop1 q sin.
Definition Qcos q := Qop1 q cos.
Definition Qtan q := Qop1 q tan.
Definition Qatan q := Qop1 q atan.
Definition Qacos q := Qop1 q acos.
Definition Qabs q := Qop1 q Rabs.

Example Qsin_ex1 (r : R) : (Qsin (r * 'm))² + (Qcos (r * 'm))² == 'm².
Proof.
  pfqeq.
  rewrite ?Rmult_1_l,?Rmult_1_r.
  repeat rewrite xx_sqr. apply sin2_cos2.
Qed.

Example Qsin_ex3 q1 q2 q3 : q1 == q2 -> Qsin (q1 * q3) == Qsin (q2 * q3).
Proof. intros. unfold Qsin. rewrite H. apply Qeq_refl. Qed.



(** ** Square root of quantity *)

(** A quantity has valid sqrt need two conditions: coefs >= 0, dims is even. *)
Definition Qsqrt_cond (q : Quantity) : bool :=
  match (Qcoef_opt q), (Qdim_opt q) with
  | Some c, Some d => (0 <=? c)%R && Dims_sqrt_cond d
  | _, _ => false
  end.

Lemma Qsqrt_cond_Qbu_false bu : Qsqrt_cond [bu] = false.
Proof.
  destruct bu; compute;
  destruct (Rle_lt_dec); auto.
Qed.

Definition Qsqrt (q : Quantity) : Quantity :=
  match q with
  | Qumake u => match (Unit_sqrt u) with
    | Some u' => u'
    | None => !!
    end
  | _ => !!
  end.

Example Qsqrt_ex1 : Qsqrt (4 * 'm²) == 2 * 'm.
Proof.
  pfqeq. autorewrite with R; auto with R.
Qed.

(** Register that [Qsqrt] is compatible for [Qeq]. *)
Add Parametric Morphism : Qsqrt
  with signature Qeq ==> Qeq as Qsqrt_mor.
Proof.
  intros. unfold Qeq,Qeqb,Qcmpb,Ueqb,Qsqrt,Unit_sqrt in *.
  destruct x, y; try easy.
  destruct (u2n u),(u2n u0).
  apply NUeqb_true_iff in H; inversion H. subst.
  destruct (Dims_sqrt d0); auto.
  apply NUeqb_true_refl.
Qed.

Lemma Qsqrt_Qsqr q : Qsqrt (q²) == Qabs q.
Proof.
  intros. unfold Qeq,Qeqb,Qcmpb,Ueqb,Qsqrt,Unit_sqrt in *.
  unfold Qabs,Qop1,Qpow.
  destruct q; try easy.
  destruct (u2n u) eqn:E1. destruct (u2n u²)%U eqn:E2.
  destruct (Dims_sqrt d0) eqn:E3; auto.
  - repeat rewrite u2n_n2u.
    rewrite (u2n_Upow_rew _ _ r d) in E2; auto; inversion E2.
    rewrite <- H1 in E3.
    assert ((Dims_sqrt (Dims_cmul 2 d)) = Some d).
    apply Dims_sqrt_Dims_cmul_2.
    rewrite E3 in H; inversion H. subst.
    replace (sqrt _) with (Rabs r). apply NUeqb_true_refl.
    replace (r * (r * 1))%R with (r²)%R.
    rewrite sqrt_Rsqr_abs; auto.
    autorewrite with R; auto.
  - rewrite (u2n_Upow_rew _ _ r d) in E2; auto; inversion E2.
    rewrite <- H1 in E3.
    assert ((Dims_sqrt (Dims_cmul 2 d)) = Some d).
    apply Dims_sqrt_Dims_cmul_2. rewrite E3 in H; easy.
Qed.

Lemma Qsqr_Qsqrt q : Qsqrt_cond q = true -> (Qsqrt q)² == Qabs q.
Proof.
  unfold Qeq,Qeqb,Qcmpb,Ueqb,Qsqrt,Unit_sqrt.
  unfold Qsqrt_cond,Qcoef_opt,Qdim_opt.
  destruct q; try easy.
  destruct (u2n u) eqn:E1.
  intros.
  apply andb_true_iff in H; destruct H.
  destruct d as [[[[[[a1 a2] a3] a4] a5] a6] a7].
  destruct Dims_sqrt eqn:E2.
  2: { apply Dims_sqrt_cond_imply_Dims_sqrt_not_None in E2; auto. }
  Admitted. (* I want to re-define Quantity by NUnit, so that I can use equal. *)
  


(** ** Any power of quantity which the unit of base and exponent both are 1 *)
Definition Qpower (base exp : Quantity) : Quantity :=
  match base,exp with
  | Qumake u1, Qumake u2 =>
    let '(c1, d1) := u2n u1 in
    let '(c2, d2) := u2n u2 in
      if ((Dims_eqb d1 Dims_zero) && (Dims_eqb d2 Dims_zero))
      then n2u (Rpower c1 c2, d1)
      else !!
  | _, _ => !!
  end.

Example Qpower_ex1 (r1 r2 : R) : Qpower ($r1) ($r2) == (Rpower r1 r2)%R.
Proof.
  pfqeq.
Qed.

(** Register that [Qpower] is compatible for [Qeq]. *)
Add Parametric Morphism : Qpower
  with signature Qeq ==> Qeq ==> Qeq as Qpower_mor.
Proof.
  intros. unfold Qeq,Qeqb,Qcmpb,Ueqb,Qpower in *.
  destruct x, y, x0, y0; try easy.
  destruct (u2n u),(u2n u0),(u2n u1),(u2n u2).
  apply NUeqb_true_iff in H; inversion H.
  apply NUeqb_true_iff in H0; inversion H0. subst.
  destruct (Dims_eqb d0 Dims_zero), (Dims_eqb d2 Dims_zero); auto.
  destruct (true && true); auto.
  apply NUeqb_true_refl.
Qed.

