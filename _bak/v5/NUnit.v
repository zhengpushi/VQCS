(*
  purpose   : Normalized Unit, semantics of unit.
  author    : Zhengpu Shi
  date      : 2021.05
*)

Require Import ZExt.
Require Export Unit. 


(** * Coefficient of a Unit *)


(** ** Definitions *)

(** Get coefficient of a Unit *)
Fixpoint Ugetcoef (u : Unit) : R :=
  match u with
  | Unone c => c
  | Ubu bu => R1
  | Uinv u1 => Rinv (Ugetcoef u1)
  | Umul u1 u2 => Rmult (Ugetcoef u1) (Ugetcoef u2)
  end.

(* (** Test examples *)
Compute Ugetcoef (kg * m / (s * s)).
Compute Ugetcoef N.
Compute Ugetcoef N'. *)


(** ** Properties *)

(** Get Coefficient of a inversed unit equal to inversion of its coefficient. *)
Lemma Ugetcoef_inv : forall u, Ugetcoef (/ u) = Rinv (Ugetcoef u).
Proof. intros. auto. Qed.

(** Get Coefficient of multiplication by two unit, equal to multiplication of 
 two seperated coefficients *)
Lemma Ugetcoef_mul : forall u1 u2, 
  Ugetcoef (u1 * u2) = Rmult (Ugetcoef u1) (Ugetcoef u2).
Proof. intros. auto. Qed.



(** * Dimensional Exponents (short as dimension) of BasicUnit from the Unit *)


(** ** Definitions *)

(** Get dimension of BasicUnit from the Unit *)
Fixpoint Ugetdim (u : Unit) (b : BasicUnit) : Z :=
  match u with
  | Unone c => 0
  | Ubu bu => if (BasicUnit_eq_dec bu b) then 1 else 0
  | Uinv u1 => Z.opp (Ugetdim u1 b)
  | Umul u1 u2 => Z.add (Ugetdim u1 b) (Ugetdim u2 b)
  end.

(* Test examples *)
(* Compute Ugetdim (kg * m / (s * s)) BUTime. *)
(* Compute Ugetdim ($100*kg) BUMass. *)


(** ** Properties *)

(** Get dimension of BasicUnit b from [b] will return 1 *)
Lemma Ugetdim_1_same : forall b, Ugetdim [b] b = Z.of_nat 1.
Proof. destruct b; simpl; auto. Qed.

(** Get dimension of BasicUnit b from [b'] will return 0 when b <> b' *)
Lemma Ugetdim_1_diff : forall b b', b <> b' -> Ugetdim [b] b' = 0%Z.
Proof. intros. destruct b,b'; simpl; auto; destruct H; auto. Qed.

(** Get dimension of BasicUnit b from u1*u2 equal to (dim b u1) + (dim b u2). *)
Lemma Ugetdim_mul : forall u1 u2 b, 
  Ugetdim (u1 * u2) b = Z.add (Ugetdim u1 b) (Ugetdim u2 b).
Proof. intros. auto. Qed.


(** * Create a Unit by power of BasicUnit with a natural number [n] *)

(** ** Definitions *)

Fixpoint BUpown (b : BasicUnit) (n : nat) : Unit :=
  match n with
  | O => $1
  | S O => [b]
  | S n' => (BUpown b n') * [b]
  end.

(* (** Test examples *)
Compute BUpown BUTime 3.
Compute BUpown BUTime 2.
Compute BUpown BUTime 1.
Compute BUpown BUTime 0. *)


(** ** Properties *)

(** Get coefficient of a Unit created by BUpown, return 1 *)
Lemma Ugetcoef_BUpown : forall (b : BasicUnit) (n : nat),
  Ugetcoef (BUpown b n) = R1.
Proof.
  intros b n. induction n; auto.
  destruct n; auto.
  replace (BUpown b (S (S n))) with (BUpown b (S n) * [b]); auto.
  rewrite Ugetcoef_mul. rewrite IHn. simpl. ring.
Qed.

(** Get dimension of a Unit created by [BUpown b n] with b, return n *)
Lemma Ugetdim_BUpown_same : forall (b : BasicUnit) (n : nat),
  Ugetdim (BUpown b n) b = Z.of_nat n.
Proof.
  induction n; auto. destruct n; auto.
  - replace (BUpown b 1) with [b]; auto. apply Ugetdim_1_same.
  - replace (BUpown b (S (S n))) with
    (BUpown b (S n) * [b]); auto.
    rewrite Ugetdim_mul. rewrite IHn. rewrite Ugetdim_1_same. simpl. f_equal.
    remember (Pos.of_succ_nat n).
    rewrite Pos.add_comm. rewrite Pos.add_1_l. auto.
Qed.

(** Get dimension of a Unit created by [BUpown b1 n] with b2 which b1 <> b2,
 return 0 *)
Lemma Ugetdim_BUpown_diff : forall (b1 b2 : BasicUnit) (n : nat),
  b1 <> b2 -> Ugetdim (BUpown b1 n) b2 = 0%Z.
Proof.
  intros. induction n; auto. destruct n; auto.
  - replace (BUpown b1 1) with [b1]; auto. rewrite Ugetdim_1_diff; auto.
  - replace (BUpown b1 (S (S n))) with
    (BUpown b1 (S n) * [b1]); auto.
    rewrite Ugetdim_mul. rewrite IHn. rewrite Ugetdim_1_diff; auto.
Qed.



(** * Create a Unit by power of BasicUnit with a integer number [dim] *)


(** ** Difinitions *)

Definition BUpowz (b : BasicUnit) (dim : Z) : Unit :=
  match Z_dec 0 dim with  (* {0 < dim} + {0 > dim} + {0 = dim} *)
  | inleft dec2 => match dec2 with
    | left _ => BUpown b (Z.to_nat dim)
    | right _ => / (BUpown b (Z.to_nat (Z.opp dim)))
    end
  | inright _ => $1
  end.

(** Test examples *)
(* Compute BUpowz BUTime 2. *)
(* Compute BUpowz BUTime 1. *)
(* Compute BUpowz BUTime 0. *)
(* Compute BUpowz BUTime (-1). *)
(* Compute BUpowz BUTime (-2). *)


(** ** Properties *)

(** Get coefficient of a Unit created by [BUpowz b dim], return 1 *)
Lemma Ugetcoef_BUpowz : forall (b : BasicUnit) (dim : Z),
  Ugetcoef (BUpowz b dim) = R1.
Proof.
  destruct dim; auto.
  - replace (BUpowz b (Z.pos p))
    with (BUpown b (Z.to_nat (Z.pos p))); auto.
    apply Ugetcoef_BUpown.
  - replace (BUpowz b (Z.neg p))
    with (/ (BUpown b (Z.to_nat (Z.pos p)))); auto.
    rewrite Ugetcoef_inv.
    rewrite Ugetcoef_BUpown. field.
Qed.

(** Get dimension of a Unit created by [BUpowz b dim] with b, return dim *)
Lemma Ugetdim_BUpowz_same : forall (b : BasicUnit) (dim : Z),
  Ugetdim (BUpowz b dim) b = dim.
Proof.
  destruct dim; auto.
  - replace (BUpowz b (Z.pos p))
    with (BUpown b (Z.to_nat (Z.pos p))); auto.
    rewrite Ugetdim_BUpown_same. auto with zarith.
  - replace (BUpowz b (Z.neg p))
    with (/ (BUpown b (Z.to_nat (Z.pos p)))); auto.
    simpl. rewrite Ugetdim_BUpown_same. auto with zarith.
Qed.

(** Get dimension of a Unit created by [BUpowz b1 dim] with b2 where k1 <> k2,
 then return 0 *)
Lemma Ugetdim_BUpowz_diff : forall (b1 b2 : BasicUnit) (dim : Z),
  b1 <> b2 ->
  Ugetdim (BUpowz b1 dim) b2 = 0%Z.
Proof.
  induction dim; auto; intros H.
  - replace (BUpowz b1 (Z.pos p))
    with (BUpown b1 (Z.to_nat (Z.pos p))); auto.
    rewrite Ugetdim_BUpown_diff; auto.
  - replace (BUpowz b1 (Z.neg p))
    with (/ (BUpown b1 (Z.to_nat (Z.pos p)))); auto.
    simpl. rewrite Ugetdim_BUpown_diff; auto.
Qed.



(** * Create a Unit with a base Unit and a power of BasicUnit *)


(** ** Difinitions *)

Definition Ucons (base : Unit) (b : BasicUnit) (dim : Z) : Unit :=
  if (dim =? 0)%Z 
  then base
  else base * (BUpowz b dim).


(** ** Properties *)

(** Get coefficient of a Unit created by [Ucons base b dim], return the 
 coefficient of [base] *)
Lemma Ugetcoef_Ucons : forall (base : Unit) (b : BasicUnit) (dim : Z),
  Ugetcoef (Ucons base b dim) = Ugetcoef base.
Proof.
  unfold Ucons. induction base; intros; simpl.
  - induction dim; simpl; auto.
    + rewrite Ugetcoef_BUpowz. field.
    + rewrite Ugetcoef_BUpown. field.
  - induction dim; simpl; auto.
    + rewrite Ugetcoef_BUpowz. field.
    + rewrite Ugetcoef_BUpown. field.
  - induction dim; simpl; auto.
    + rewrite Ugetcoef_BUpowz. rewrite Rmult_1_r. auto.
    + rewrite Ugetcoef_BUpown. rewrite RMicromega.Rinv_1. auto.
  - induction dim; simpl; auto.
    + rewrite Ugetcoef_BUpowz. rewrite Rmult_1_r. auto.
    + rewrite Ugetcoef_BUpown. rewrite RMicromega.Rinv_1. auto.
Qed.

(** Get dimension of a Unit created by [Ucons base b1 dim] b2 where *)
Lemma Ugetdim_Ucons : forall (base : Unit) (b1 b2 : BasicUnit) (dim : Z),
  Ugetdim (Ucons base b1 dim) b2 = ((Ugetdim base b2) + 
    (if (BasicUnit_beq b1 b2) then dim else 0))%Z.
Proof.
  intros.
  destruct (BasicUnit_beq b1 b2) eqn : E1 ; simpl.
  - apply BasicUnit_beq_eq in E1. subst. 
    unfold Ucons. induction dim; simpl; try ring.
    + rewrite Ugetdim_BUpowz_same. auto.
    + rewrite Ugetdim_BUpown_same. auto with zarith.
  - unfold Ucons. induction dim; simpl; auto with zarith.
    + rewrite Ugetdim_BUpowz_diff; auto.
      apply BasicUnit_beq_neq. auto.
    + rewrite Ugetdim_BUpown_diff; auto.
      apply BasicUnit_beq_neq. auto.
Qed.



(** * Dimensions of a Unit *)


(** ** Difinitions *)

(** These seven components are dimensions of every basic unit *)
Definition Dims := (Z * Z * Z * Z * Z * Z * Z)%type.

(** Boolean equality of NDim *)
Definition Dims_eqb (d1 d2 : Dims) : bool :=
  let '(ds1,dm1,dkg1,dA1,dK1,dmol1,dcd1) := d1 in
  let '(ds2,dm2,dkg2,dA2,dK2,dmol2,dcd2) := d2 in
    Z.eqb ds1 ds2 
    && Z.eqb dm1 dm2 
    && Z.eqb dkg1 dkg2 
    && Z.eqb dA1 dA2 
    && Z.eqb dK1 dK2 
    && Z.eqb dmol1 dmol2 
    && Z.eqb dcd1 dcd2.

(** Plus of two Dims *)
Definition Dims_plus (d1 d2 : Dims) : Dims :=
  let '(ds1,dm1,dkg1,dA1,dK1,dmol1,dcd1) := d1 in
  let '(ds2,dm2,dkg2,dA2,dK2,dmol2,dcd2) := d2 in
    (ds1 + ds2, 
     dm1 + dm2,
     dkg1 + dkg2,
     dA1 + dA2,
     dK1 + dK2,
     dmol1 + dmol2,
     dcd1 + dcd2)%Z.

(** Opposite of a NDim *)
Definition Dims_opp (d1 : Dims) : Dims :=
  let '(ds1,dm1,dkg1,dA1,dK1,dmol1,dcd1) := d1 in
    (-ds1, -dm1,-dkg1, -dA1, -dK1, -dmol1, -dcd1)%Z.

(** Substraction of two Dims *)
Definition Dims_sub' (d1 d2 : Dims) : Dims :=
  let '(ds1,dm1,dkg1,dA1,dK1,dmol1,dcd1) := d1 in
  let '(ds2,dm2,dkg2,dA2,dK2,dmol2,dcd2) := d2 in
    (ds1 - ds2, 
     dm1 - dm2,
     dkg1 - dkg2,
     dA1 - dA2,
     dK1 - dK2,
     dmol1 - dmol2,
     dcd1 - dcd2)%Z.
Definition Dims_sub (d1 d2 : Dims) : Dims :=
  Dims_plus d1 (Dims_opp d2).


(** ** Properties *)

(** d1 <> d2, iff at least one of the corresponding components is not equal *)
Lemma Dims_neq_iff : forall (d1 d2 : Dims),
  d1 <> d2 <->
  let '(ds1,dm1,dkg1,dA1,dK1,dmol1,dcd1) := d1 in
  let '(ds2,dm2,dkg2,dA2,dK2,dmol2,dcd2) := d2 in
    (ds1 <> ds2) \/
    (dm1 <> dm2) \/
    (dkg1 <> dkg2) \/
    (dA1 <> dA2) \/
    (dK1 <> dK2) \/
    (dmol1 <> dmol2) \/
    (dcd1 <> dcd2).
Proof.
  intros d1 d2.
  destruct d1 as [[[[[[ds1 dm1] dkg1] dA1] dK1] dmol1] dcd1].
  destruct d2 as [[[[[[ds2 dm2] dkg2] dA2] dK2] dmol2] dcd2]. 
  split; intros H.
  - assert (not (ds1 = ds2 /\ dm1 = dm2 /\ dkg1 = dkg2 /\ 
    dA1 = dA2 /\ dK1 = dK2 /\ dmol1 = dmol2 /\ dcd1 = dcd2)); try tauto.
    intros H1. repeat (destruct H1 as [?H H1]; subst).
    destruct H. auto.
  - intros H1; inversion H1. subst. repeat destruct H; auto.
Qed.

(** Decidable of Dims equality  *)
Lemma Dims_eq_dec : forall (d1 d2 : Dims), {d1 = d2} + {d1 <> d2}.
Proof.
  intros d1 d2.
  destruct d1 as [[[[[[ds1 dm1] dkg1] dA1] dK1] dmol1] dcd1].
  destruct d2 as [[[[[[ds2 dm2] dkg2] dA2] dK2] dmol2] dcd2]. 
  destruct (Z.eq_dec ds1 ds2); [idtac | right; intros H; inversion H; auto].
  destruct (Z.eq_dec dm1 dm2); [idtac | right; intros H; inversion H; auto].
  destruct (Z.eq_dec dkg1 dkg2); [idtac | right; intros H; inversion H; auto].
  destruct (Z.eq_dec dA1 dA2); [idtac | right; intros H; inversion H; auto].
  destruct (Z.eq_dec dK1 dK2); [idtac | right; intros H; inversion H; auto].
  destruct (Z.eq_dec dmol1 dmol2); [idtac | right; intros H; inversion H; auto].
  destruct (Z.eq_dec dcd1 dcd2); [idtac | right; intros H; inversion H; auto].
  subst. auto.
Qed.

(** Boolean equality of Dims is reflexive *)

Lemma Dims_eqb_refl (d : Dims) : Dims_eqb d d = true.
Proof.
  repeat destruct d as [d ?]. unfold Dims_eqb.
  repeat rewrite andb_true_intro; split; auto; apply Z.eqb_refl.
Qed.

Lemma Dims_eqb_comm (d1 d2 : Dims) : Dims_eqb d1 d2 = Dims_eqb d2 d1.
Proof.
  repeat destruct d1 as [d1 ?],d2 as [d2 ?]. unfold Dims_eqb.
  repeat apply andb_eq_inv; try apply Z.eqb_sym.
Qed.

(** Boolean equality of Dims is transitive *)
Lemma Dims_eqb_trans (d1 d2 d3 : Dims) : Dims_eqb d1 d2 = true ->
  Dims_eqb d2 d3 = true ->
  Dims_eqb d1 d3 = true.
Proof.
  repeat destruct d1 as [d1 ?],d2 as [d2 ?],d3 as [d3 ?]. unfold Dims_eqb.
  intros. apply andb_true_iff7. apply andb_true_iff7 in H,H0.
  repeat rewrite Z.eqb_eq in *.
  repeat match goal with | H: _ /\ _ |- _ => destruct H as [? H] end.
  subst. repeat split; auto.
Qed.

(** Boolean equal of two Dims iff propositonal equal *)
Lemma Dims_eqb_true_iff (d1 d2 : Dims) : Dims_eqb d1 d2 = true <-> d1 = d2.
Proof.
  repeat destruct d1 as [d1 ?].
  repeat destruct d2 as [d2 ?].
  unfold Dims_eqb. split; intros H.
  - repeat (rewrite Bool.andb_true_iff in H; destruct H as [H H1]; 
    apply Z.eqb_eq in H1; subst). apply Z.eqb_eq in H; subst. auto.
  - inversion H. subst. rewrite ?Bool.andb_true_iff. 
    repeat split; try rewrite Z.eqb_eq; auto.
Qed.

(** Boolean not equal of two Dims iff propositonal not equal *)
Lemma Dims_eqb_false_iff (d1 d2 : Dims) : 
  Dims_eqb d1 d2 = false <-> d1 <> d2.
Proof.
  split; intros H.
  - intros H1. apply Dims_eqb_true_iff in H1. rewrite H in H1. lra.
  - repeat destruct d1 as [d1 ?].
    repeat destruct d2 as [d2 ?].
    apply Dims_neq_iff in H. unfold Dims_eqb.
    repeat (destruct H; try (apply Z.eqb_neq in H; rewrite H; 
      rewrite ?andb_false_l,?andb_false_r; auto)).
Qed.

(** Dims_plus is commutative *)
Lemma Dims_plus_comm : forall (d1 d2 : Dims),
  Dims_plus d1 d2 = Dims_plus d2 d1.
Proof.
  intros. destruct d1,d2. repeat destruct p,p0. simpl. 
  repeat (f_equal; try ring).
Qed.

(** Dims_plus is associative *)
Lemma Dims_plus_assoc : forall (d1 d2 d3 : Dims),
  Dims_plus (Dims_plus d1 d2) d3 = Dims_plus d1 (Dims_plus d2 d3).
Proof.
  intros. destruct d1,d2,d3. repeat destruct p,p0,p1. simpl.
  repeat (f_equal; try ring).
Qed.



(** * Normalized Unit, which is the semantics of a Unit *)


(** ** Definitions *)

(** A normalized unit is a pair of coefficient and dimensions *) 
Definition NUnit : Set := R * Dims.

(** Boolean Equality of two NUnits *)
Definition NUeqb (nu1 nu2 : NUnit) : bool :=
  let '(coef1, dim1) := nu1 in
  let '(coef2, dim2) := nu2 in
     (coef1 =? coef2)%R && Dims_eqb dim1 dim2.

(** Convert a Unit to a NUnit *)
Definition u2n (u : Unit) : NUnit :=
  let coef := Ugetcoef u in
  let ds := Ugetdim u BUTime in
  let dm := Ugetdim u BULength in
  let dkg := Ugetdim u BUMass in
  let dA := Ugetdim u BUElectricCurrent in
  let dK := Ugetdim u BUThermodynamicTemperature in
  let dmol := Ugetdim u BUAmountOfSubstance in
  let dcd := Ugetdim u BULuminousIntensity in
    (coef, (ds,dm,dkg,dA,dK,dmol,dcd)).

(** Convert a NUnit to a Unit *)
Definition n2u (nu : NUnit) : Unit :=
  let '(coef, (ds,dm,dkg,dA,dK,dmol,dcd)) := nu in
  let u1 := $coef in
  let u1 := Ucons u1 BUTime ds in
  let u1 := Ucons u1 BULength dm in
  let u1 := Ucons u1 BUMass dkg in
  let u1 := Ucons u1 BUElectricCurrent dA in
  let u1 := Ucons u1 BUThermodynamicTemperature dK in
  let u1 := Ucons u1 BUAmountOfSubstance dmol in
  let u1 := Ucons u1 BULuminousIntensity dcd in
    u1.

(* (** Test examples *)
Compute u2n (m * $1 * s * s).
Compute u2n N.
Compute u2n N'.

Compute NUeqb (u2n($1 * m * s)) (u2n (s * m * $1)). *)


(** ** Properties *)

(** NUnit boolean equality is commutative *)
Lemma NUeqb_comm : forall nu1 nu2, NUeqb nu1 nu2 = NUeqb nu2 nu1.
Proof.
  intros. destruct nu1,nu2. simpl.
  rewrite Reqb_comm. rewrite Dims_eqb_comm. auto.
Qed.

(** NUnit boolean equality is reflexive *)
Lemma NUeqb_refl : forall u, NUeqb u u = true.
Proof.
  destruct u. simpl. rewrite andb_true_intro; auto. split.
  - apply Reqb_refl.
  - apply Dims_eqb_refl.
Qed.

(** NUnit boolean equality is transitive *)
Lemma NUeqb_trans : forall u1 u2 u3, NUeqb u1 u2 = true ->
  NUeqb u2 u3 = true ->
  NUeqb u1 u3 = true.
Proof.
  intros. destruct u1,u2,u3. unfold NUeqb in *.
  apply andb_true_iff in H,H0. apply andb_true_iff. destruct H,H0. split.
  apply Reqb_trans with r0; auto.
  apply Dims_eqb_trans with d0; auto.
Qed.

(** n1 <> n2, iff at least one of the corresponding components is not equal *)
Lemma Neq_not_iff : forall (n1 n2 : NUnit),
  n1 <> n2 <->
  let '(coef1, d1) := n1 in
  let '(coef2, d2) := n2 in
    (coef1 <> coef2) \/ (d1 <> d2).
Proof.
  intros n1 n2.
  destruct n1 as [coef1 d1]. destruct n2 as [coef2 d2]. split; intros H.
  - assert (not (coef1 = coef2 /\ d1 = d2)); try tauto.
    intros H1. destruct H1; subst. destruct H; auto.
  - intros H1; inversion H1; clear H1; auto. subst.
    repeat destruct H; auto.
Qed.

(** NUeqb true, iff they are equal *)
Lemma NUeqb_true_iff : forall (n1 n2 : NUnit), NUeqb n1 n2 = true <-> n1 = n2.
Proof.
  destruct n1,n2. unfold NUeqb. split; intros H.
  - apply Bool.andb_true_iff in H. destruct H as [H1 H2].
    apply Reqb_true_iff in H1; subst. apply Dims_eqb_true_iff in H2; subst.
    auto.
  - inversion H. subst. rewrite andb_true_iff. split.
    apply Reqb_true_iff; auto. apply Dims_eqb_true_iff; auto.
Qed.

(** NUeqb false, iff they are not equal *)
Lemma NUeqb_false_iff : forall n1 n2, NUeqb n1 n2 = false <-> n1 <> n2.
Proof.
  intros n1 n2. split.
  - intros H H1. rewrite <- NUeqb_true_iff in H1. rewrite H in H1. lra.
  - destruct n1,n2. intros H. apply Neq_not_iff in H. unfold NUeqb.
    destruct H.
    + apply Reqb_false_iff in H. rewrite H. auto.
    + apply Dims_eqb_false_iff in H. rewrite H. lra.
Qed.

(** NUnit equality is decidable *)
Lemma NUnit_eq_dec (n1 n2 : NUnit) : {n1 = n2} + {n1 <> n2}.
Proof.
  destruct (NUeqb n1 n2) eqn : E1.
  - left. apply NUeqb_true_iff in E1. auto.
  - right. apply NUeqb_false_iff in E1. auto.
Qed.

(** Coefficient of [n2u n] is the coefficient of [n] *)
Lemma Ugetcoef_n2u : forall n coef dims,
  (coef, dims) = n -> Ugetcoef (n2u n) = coef.
Proof.
  intros. induction n as [coef1 dims1]. inversion H; subst.
  destruct dims1 as [[[[[[ds dm] dkg] dA] dK] dmol] dcd]. simpl.
  rewrite ?Ugetcoef_Ucons. auto.
Qed.

(** Dimension of [n2u n] is the dimension of n *)
Lemma Ugetdim_n2u : forall n coef ds dm dkg dA dK dmol dcd,
  (coef, (ds,dm,dkg,dA,dK,dmol,dcd)) = n ->
  Ugetdim (n2u n) BUTime = ds /\
  Ugetdim (n2u n) BULength = dm /\
  Ugetdim (n2u n) BUMass = dkg /\
  Ugetdim (n2u n) BUElectricCurrent = dA /\
  Ugetdim (n2u n) BUThermodynamicTemperature = dK /\
  Ugetdim (n2u n) BUAmountOfSubstance = dmol /\
  Ugetdim (n2u n) BULuminousIntensity = dcd.
Proof.
  intros.
  induction n as [coef1 dims1].
  destruct dims1 as [[[[[[ds1 dm1] dkg1] dA1] dK1] dmol1] dcd1].
  inversion H; subst. simpl.
  rewrite ?Ugetdim_Ucons. repeat split; 
  destruct BasicUnit_beq eqn: E1; simpl; try ring;
  try (rewrite BasicUnit_beq_neq in E1; destruct E1; auto);
  try (rewrite BasicUnit_beq_eq in E1; inversion E1; auto).
Qed.

(** Ugetcoef_n2u is injective *)
Lemma Ugetcoef_n2u_inj : forall coef1 coef2 d1 d2, 
  n2u (coef1, d1) = n2u (coef2, d2) -> coef1 = coef2.
Proof.
  intros.
  assert (forall u1 u2, u1 = u2 -> Ugetcoef u1 = Ugetcoef u2);
  intros; subst; auto.
  apply H0 in H. simpl in H.
  destruct d1 as [[[[[[ds1 dm1] dkg1] dA1] dK1] dmol1] dcd1].
  destruct d2 as [[[[[[ds2 dm2] dkg2] dA2] dK2] dmol2] dcd2].
  rewrite ?Ugetcoef_Ucons in H. simpl in H. auto.
Qed.

(** A tactic to handle "Ugetdim (n2u xx) = dyy" *)
Ltac dim_n2u_simp :=
  simpl; 
  repeat rewrite Ugetdim_Ucons; simpl; 
  auto with zarith.

(** Ugetdim_n2u is injective *)
Lemma Ugetdim_n2u_inj : forall coef1 coef2 d1 d2, 
  n2u (coef1, d1) = n2u (coef2, d2) -> d1 = d2.
Proof.
  intros.
  assert (forall u1 u2 k, u1 = u2 -> Ugetdim u1 k = Ugetdim u2 k);
  intros; subst; auto. simpl in H.
  destruct d1 as [[[[[[ds1 dm1] dkg1] dA1] dK1] dmol1] dcd1].
  destruct d2 as [[[[[[ds2 dm2] dkg2] dA2] dK2] dmol2] dcd2].
  (* BUTime *)
  remember H as H1 eqn : E1; clear E1;
  apply (H0 _ _ &T) in H1; rewrite ?Ugetdim_Ucons in H1; simpl in H1;
  rewrite ?Z.add_0_r,?Z.add_0_l in H1; subst.
  (* BULength *)
  remember H as H1 eqn : E1; clear E1;
  apply (H0 _ _ &L) in H1; rewrite ?Ugetdim_Ucons in H1; simpl in H1;
  rewrite ?Z.add_0_r,?Z.add_0_l in H1; subst.
  (* BUMass *)
  remember H as H1 eqn : E1; clear E1;
  apply (H0 _ _ &M) in H1; rewrite ?Ugetdim_Ucons in H1; simpl in H1;
  rewrite ?Z.add_0_r,?Z.add_0_l in H1; subst.
  (* BUElectricCurrent *)
  remember H as H1 eqn : E1; clear E1;
  apply (H0 _ _ &I) in H1; rewrite ?Ugetdim_Ucons in H1; simpl in H1;
  rewrite ?Z.add_0_r,?Z.add_0_l in H1; subst.
  (* BUThermodynamicTemperature *)
  remember H as H1 eqn : E1; clear E1;
  apply (H0 _ _ &O) in H1; rewrite ?Ugetdim_Ucons in H1; simpl in H1;
  rewrite ?Z.add_0_r,?Z.add_0_l in H1; subst.
  (* BUAmountOfSubstance *)
  remember H as H1 eqn : E1; clear E1;
  apply (H0 _ _ &N) in H1; rewrite ?Ugetdim_Ucons in H1; simpl in H1;
  rewrite ?Z.add_0_r,?Z.add_0_l in H1; subst.
  (* BULuminousIntensity *)
  remember H as H1 eqn : E1; clear E1;
  apply (H0 _ _ &J) in H1; rewrite ?Ugetdim_Ucons in H1; simpl in H1;
  rewrite ?Z.add_0_r,?Z.add_0_l in H1; subst.
  auto.
Qed.

(** n2u is injective *)
Lemma n2u_inj : forall n1 n2, n2u n1 = n2u n2 -> n1 = n2.
Proof.
  intros n1 n2 H. remember H as H1 eqn: E1; clear E1.
  destruct n1 as (coef1, d1). destruct n2 as (coef2, d2).
  apply Ugetcoef_n2u_inj in H.
  apply Ugetdim_n2u_inj in H1. subst. auto.
Qed.

(** n2u then u2n, return back *)
Lemma u2n_n2u : forall (n : NUnit), u2n (n2u n) = n.
Proof.
  intros n. unfold u2n. induction n as [coef dims].
  destruct dims as [[[[[[ds dm] dkg] dA] dK] dmol] dcd]. simpl.
  rewrite ?Ugetcoef_Ucons,?Ugetdim_Ucons; simpl. repeat f_equal; ring.
Qed.



(** * Equality of two Units *)

(** ** Definitions *)

(** Proposional Euqality of two Units *)
Definition Ueq (u1 u2 : Unit) : Prop := u2n u1 = u2n u2.

Notation "u1 == u2" := (Ueq u1 u2) (at level 70) : Unit_scope.

(** Boolean Equality of two Units *)
Definition Ueqb (u1 u2 : Unit) : bool := NUeqb (u2n u1) (u2n u2).

Notation "u1 =? u2" := (Ueqb u1 u2) (at level 70) : Unit_scope.


(** ** Properties *)

(** from two equal base Unit, use same construction got two equal units *)
Lemma Ueq_imply_Ueq_of_Ucons : forall u1 u2 b dim,
  Ueq u1 u2 -> Ueq (Ucons u1 b dim) (Ucons u2 b dim).
Proof.
  intros. unfold Ueq in *. unfold u2n in *.
  inversion H.
  rewrite ?Ugetcoef_Ucons,?Ugetdim_Ucons.
  rewrite H1,H2,H3,H4,H5,H6,H7,H8. auto.
Qed.

(** Ueq is equivalence relation *)

Lemma Ueq_refl : forall (u : Unit), u == u.
Proof.
  intros. unfold Ueq. auto.
Qed.

Lemma Ueq_sym : forall (u1 u2 : Unit), u1 == u2 -> u2 == u1.
Proof.
  intros. unfold Ueq, u2n in *. inversion H. auto.
Qed.

Lemma Ueq_trans : forall (u1 u2 u3 : Unit), 
  u1 == u2 -> u2 == u3 -> u1 == u3.
Proof.
  intros. unfold Ueq, u2n in *. inversion H. inversion H0.
  repeat (f_equal; auto).
Qed.

(** Unit boolean equality is reflexive *)
Lemma Ueqb_refl : forall u, u =? u = true.
Proof. intros. unfold Ueqb. apply NUeqb_refl. Qed.

(** Unit boolean equality is commutative *)
Lemma Ueqb_comm : forall (u1 u2 : Unit), (u1 =? u2) = (u2 =? u1).
Proof.
  intros. unfold Ueqb in *. apply NUeqb_comm.
Qed.

(** Unit boolean equality is transtive *)
Lemma Ueqb_trans : forall (u1 u2 u3 : Unit), 
  u1 =? u2 = true -> u2 =? u3 = true -> u1 =? u3 = true.
Proof.
  intros. unfold Ueqb in *. apply NUeqb_trans with (u2n u2); auto.
Qed.

(** from two base Unit, use same construction rule got units will be equal or
  not depends on equality of the two base units. *)
Lemma Ueqb_imply_Ueqb_of_Ucons : forall u1 u2 k dim,
  Ueqb (Ucons u1 k dim) (Ucons u2 k dim) = Ueqb u1 u2.
Proof.
  intros. unfold Ueqb in *. unfold u2n in *.
  rewrite ?Ugetcoef_Ucons, ?Ugetdim_Ucons.
  unfold NUeqb.
  repeat apply andb_eq_inv; auto;
  rewrite Zadd_eqb_cancel_r; auto.
Qed.



(** * Normalization of a Unit *)


(** ** Definitions *)

Definition unorm (u : Unit) : Unit := n2u (u2n u).

(** Examples *)
(* Compute unorm (kg * m * s). *)
(* Compute unorm (kg * s * m). *)
(* Compute unorm (s * m * kg * $3 ). *)
(* Compute unorm (unorm (s * m * kg * $3 )). *)


(** ** Properties *)

(* 再次思考：如何表达 soundness 和 completeness？ *)

(** Completeness of unorm operation *)
Lemma unorm_complete : forall (u : Unit), unorm u = unorm (unorm u).
Proof.
  intros u. unfold unorm. rewrite u2n_n2u. auto.
Qed.



(** * Approximate relation of two Units *)

(** ** Definitions *)

(** Check if two Unit is approximate, propositional version *)
Definition Unit_approx (u1 u2 : Unit) (diff : R) : Prop :=
  let (c1, nd1) := u2n u1 in
  let (c2, nd2) := u2n u2 in
    (nd1 = nd2) /\ (Rapprox c1 c2 diff).

(** Check if two Unit is approximate, boolean version *)
Definition Unit_approxb (u1 u2 : Unit) (diff : R) : bool :=
  let (c1, nd1) := u2n u1 in
  let (c2, nd2) := u2n u2 in
    (Dims_eqb nd1 nd2) && (Rapproxb c1 c2 diff).


(** Syntaxs and semantics of operations are equal *)
(* Lemma Umul_iff_Nmul :  *)
