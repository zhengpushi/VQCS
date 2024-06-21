(*
  Copyright 2024 ZhengPu Shi
  This file is part of VQCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Normalized Unit, semantics of unit.
  author    : ZhengPu Shi
  date      : 2021.05
  
  reference :
  1. https://en.wikipedia.org/wiki/Dimensional_analysis
  
  remark    :
  1. Dimension & dimension exponent.
    every Unit could be represented with 7 dimension exponent,
    for example, A = L^a * M^b * T^c ...
    these units are called coherent units. But there are some units are not 
    coherent, like minute, it need a coefficient, i.e., 1min = 60s.
  2. How to unify these two different types of units?
    we use a coefficient and dimensions (7 corresponding dimension) of a Unit 
    to be considered as the semantics of the unit.
  3. What are dimensions used for?
    (a). an intermediary when converting two different units
    (b). to verify an equation by checking left and right has same dimensions.
         Two quantities could be compare or plus or subtract only when they have 
         same dimensions.
    (c). to find relation between physical quantities.
      for example, if we know a quantity X is related to Length and Time, but 
      we don't know how, then an assumption equation X = L^a * T^b could be 
      used to find the real relation after lots of experiments and guessed the 
      suitable dimension exponent a and b.
    (d). use PI theorem to find/verify relations between physical quantities.
 *)

Require Export Unit. 


(* ######################################################################### *)
(** * Dimensions of Unit *)

(* ======================================================================= *)
(** ** Difinition of dimensions *)

(** A tuple of 7 integers which each one means the dimension of a [BasicUnit]. *)
Definition Dims := (Z * Z * Z * Z * Z * Z * Z)%type.

(** Zero dimensions, means a pure number value. *)
Definition dzero : Dims := (0,0,0,0,0,0,0)%Z.


(* ======================================================================= *)
(** ** Equality Decidable of [Dims] *)

(* Destruct one [Dims] to its components with same name *)
Ltac des_dims1 d1 :=
  destruct d1 as [[[[[[?a ?a] ?a] ?a] ?a] ?a] ?a].

(* Destruct two [Dims] to its components with same name *)
Ltac des_dims2 d1 d2 :=
  destruct d1 as [[[[[[?a ?a] ?a] ?a] ?a] ?a] ?a];
  destruct d2 as [[[[[[?b ?b] ?b] ?b] ?b] ?b] ?b].

(* Destruct three [Dims] to its components with same name *)
Ltac des_dims3 d1 d2 d3 :=
  destruct d1 as [[[[[[?a ?a] ?a] ?a] ?a] ?a] ?a];
  destruct d2 as [[[[[[?b ?b] ?b] ?b] ?b] ?b] ?b];
  destruct d3 as [[[[[[?c ?c] ?c] ?c] ?c] ?c] ?c].

(** Equality of Dims is decidable.  *)
Lemma deq_dec : forall (d1 d2 : Dims), {d1 = d2} + {d1 <> d2}.
Proof.
  intros. des_dims2 d1 d2. eapply pair_dec7.
  Unshelve. all: apply Z.eq_dec.
Defined.

(** Equality of Dims, iff all components are equal. *)
Lemma deq_iff : forall (d1 d2 : Dims),
    let '(a,a0,a1,a2,a3,a4,a5) := d1 in
    let '(b,b0,b1,b2,b3,b4,b5) := d2 in
    d1 = d2 <-> a = b /\ a0 = b0 /\ a1 = b1 /\ a2 = b2 /\ a3 = b3 /\ a4 = b4 /\ a5 = b5.
Proof. intros. des_dims2 d1 d2. apply pair_eq7. Qed.

(** Inequality of Dims, iff at least one of the dimension is not equal. *)
Lemma dneq_iff : forall (d1 d2 : Dims),
    let '(a,a0,a1,a2,a3,a4,a5) := d1 in
    let '(b,b0,b1,b2,b3,b4,b5) := d2 in
    d1 <> d2 <-> a <> b \/ a0 <> b0 \/ a1 <> b1 \/ a2 <> b2 \/ a3 <> b3 \/ a4 <> b4 \/ a5 <> b5.
Proof. intros. des_dims2 d1 d2. apply pair_neq7. Qed.

(* ======================================================================= *)
(** ** Boolean equality of [Dims] *)

(** Boolean equality of [Dims] is defined as the equality of each component. *)
Definition deqb (d1 d2 : Dims) : bool.
  des_dims2 d1 d2.
  exact (
      Z.eqb a b &&
        Z.eqb a0 b0 &&
        Z.eqb a1 b1 &&
        Z.eqb a2 b2 &&
        Z.eqb a3 b3 &&
        Z.eqb a4 b4 &&
        Z.eqb a5 b5).
Defined.

(** [deqb] is true, iff propositonal equal. *)
Lemma deqb_true_iff (d1 d2 : Dims) : deqb d1 d2 = true <-> d1 = d2.
Proof.
  pose proof (deq_iff d1 d2). des_dims2 d1 d2. rewrite H. simpl.
  rewrite <- !Z.eqb_eq. rewrite !andb_true_iff. tauto.
Qed.

(** [deqb] is false, iff propositonal not equal. *)
Lemma deqb_false_iff (d1 d2 : Dims) : 
  deqb d1 d2 = false <-> d1 <> d2.
Proof. intros. rewrite <- deqb_true_iff. autoBool. Qed.

Lemma deqb_reflect : forall d1 d2 : Dims, reflect (d1 = d2) (deqb d1 d2).
Proof.
  intros. destruct (deqb d1 d2) eqn:E1; constructor.
  apply deqb_true_iff; auto. apply deqb_false_iff; auto.
Qed.

Hint Resolve deqb_reflect : bdestruct.


(** [deqb] is reflexive. *)
Lemma deqb_refl (d : Dims) : deqb d d = true.
Proof. apply deqb_true_iff. auto. Qed.

(** [deqb] is commutative. *)
Lemma deqb_comm d1 d2 : deqb d1 d2 = deqb d2 d1.
Proof. bdestruct (deqb d1 d2); bdestruct (deqb d2 d1); auto. congruence. Qed.

(* ======================================================================= *)
(** ** Make [Dims] with [BaseUnit] *)
Definition dmakeByBU (b : BaseUnit) (z : Z) : Dims :=
  match b with
  | &T => (z,0,0,0,0,0,0)%Z
  | &L => (0,z,0,0,0,0,0)%Z
  | &M => (0,0,z,0,0,0,0)%Z
  | &I => (0,0,0,z,0,0,0)%Z
  | &Q => (0,0,0,0,z,0,0)%Z
  | &N => (0,0,0,0,0,z,0)%Z
  | &J => (0,0,0,0,0,0,z)%Z
  end.

(* ======================================================================= *)
(** ** All components of [Dims] holds *)

(** All components of [Dims] is hold for (P : Z -> Prop) *)
Definition dAll (d : Dims) (P : Z -> Prop) : Prop.
  des_dims1 d.
  exact (P a /\ P a0 /\ P a1 /\ P a2 /\ P a3 /\ P a4 /\ P a5).
Defined.

(** All components of [Dims] is true for (P : Z -> bool) *)
Definition dAllb (d : Dims) (P : Z -> bool) : bool.
  des_dims1 d.
  exact (P a && P a0 && P a1 && P a2 && P a3 && P a4 && P a5).
Defined.


(* ======================================================================= *)
(** ** Get dim of a [BaseUnit] from [Dims] *)
Definition dimFromDims (d : Dims) (b : BaseUnit) : Z.
  des_dims1 d.
  exact (match b with
         | &T => a | &L => a0 | &M => a1 | &I => a2
         | &Q => a3 | &N => a4 | &J => a5
         end).
Defined.

(* ======================================================================= *)
(** ** Map of [Dims] *)

(** Mapping unary function `f` to [Dims] `d` *)
Definition dmap (d : Dims) (f : Z -> Z) : Dims.
  des_dims1 d.
  exact (f a, f a0, f a1, f a2, f a3, f a4, f a5).
Defined.

(** Mapping binary function `f` to [Dims] `d1` and `d2` *)
Definition dmap2 (d1 d2 : Dims) (f : Z -> Z -> Z) : Dims.
  des_dims2 d1 d2.
  exact (f a b, f a0 b0, f a1 b1, f a2 b2, f a3 b3, f a4 b4, f a5 b5).
Defined.

(** [dmap2] is commutative, if the operation is. *)
Lemma dmap2_comm : forall d1 d2 f,
    (forall a b, f a b = f b a) ->
    dmap2 d1 d2 f = dmap2 d2 d1 f.
Proof.
  intros. unfold dmap2. des_dims2 d1 d2; simpl. repeat (f_equal; auto).
Qed.

(** [dmap2] is associative, if the operation is. *)
Lemma dmap2_assoc : forall d1 d2 d3 f,
    (forall a b c, f (f a b) c = f a (f b c)) ->
    dmap2 (dmap2 d1 d2 f) d3 f = dmap2 d1 (dmap2 d2 d3 f) f.
Proof.
  intros. unfold dmap2. des_dims3 d1 d2 d3. repeat (f_equal; auto).
Qed.

(** [dmap2] has left identity, if the operation does. *)
Lemma dmap2_0_l : forall d f, (forall a, f 0 a = a)%Z -> dmap2 dzero d f = d.
Proof. intros. des_dims1 d; simpl. repeat (f_equal; auto). Qed.

(** [dmap2] has right identity, if the operation does. *)
Lemma dmap2_0_r : forall d f, (forall a, f a 0 = a)%Z -> dmap2 d dzero f = d.
Proof. intros. des_dims1 d; simpl. repeat (f_equal; auto). Qed.

(** [dmap2] has left inverse, if the operation does. *)
Lemma dmap2_inv_l : forall d f g, (forall a, f (g a) a = 0)%Z -> dmap2 (dmap d g) d f = dzero.
Proof. intros. des_dims1 d; simpl. unfold dzero. repeat (f_equal; auto). Qed.

(** [dmap2] has right inverse, if the operation does. *)
Lemma dmap2_inv_r : forall d f g, (forall a, f a (g a) = 0)%Z -> dmap2 d (dmap d g) f = dzero.
Proof. intros. des_dims1 d; simpl. unfold dzero. repeat (f_equal; auto). Qed.

(** [dmap2] cancel law on left *)
Lemma dmap2_cancel_l : forall d d1 d2 f,
    (forall a b c : Z, (f a b = f a c)%Z -> b = c) ->
    dmap2 d d1 f = dmap2 d d2 f <-> d1 = d2.
Proof.
  intros. split; intros; [| subst; auto].
  des_dims3 d d1 d2. simpl in H0. inversion H0.
  apply H in H2,H3,H4,H5,H6,H7,H8. repeat f_equal; auto.
Qed.

(** [dmap2] cancel law on right *)
Lemma dmap2_cancel_r : forall d d1 d2 f,
    (forall a b c : Z, (f a c = f b c)%Z -> a = b) ->
    dmap2 d1 d f = dmap2 d2 d f <-> d1 = d2.
Proof.
  intros. split; intros; [| subst; auto].
  des_dims3 d d1 d2. simpl in H0. inversion H0.
  apply H in H2,H3,H4,H5,H6,H7,H8. repeat f_equal; auto.
Qed.

(* ======================================================================= *)
(** ** Addition of [Dims] *)

(** Addition of [Dims] is defined as the addition of each component. *)
Definition dplus (d1 d2 : Dims) : Dims := dmap2 d1 d2 Z.add.

(** [dplus] is commutative. *)
Lemma dplus_comm : forall (d1 d2 : Dims), dplus d1 d2 = dplus d2 d1.
Proof. intros. apply dmap2_comm. auto with zarith. Qed.

(** [dplus] is associative. *)
Lemma dplus_assoc : forall (d1 d2 d3 : Dims),
    dplus (dplus d1 d2) d3 = dplus d1 (dplus d2 d3).
Proof. intros. apply dmap2_assoc. auto with zarith. Qed.

(** 0 + d = d *)
Lemma dplus_0_l : forall d, dplus dzero d = d.
Proof. intros. apply dmap2_0_l. auto with zarith. Qed.

(** d + 0 = d *)
Lemma dplus_0_r : forall d, dplus d dzero = d.
Proof. intros. apply dmap2_0_r. auto with zarith. Qed.

(** d + d1 = d + d2 -> d1 = d2 *)
Lemma dplus_cancel_l : forall d d1 d2, dplus d d1 = dplus d d2 <-> d1 = d2.
Proof.
  intros. split; intros; [| subst; auto].
  apply dmap2_cancel_l in H; auto. intros. lia.
Qed.

(** d1 + d = d2 + d -> d1 = d2 *)
Lemma dplus_cancel_r : forall d d1 d2, dplus d1 d = dplus d2 d <-> d1 = d2.
Proof.
  intros. split; intros; [| subst; auto].
  apply dmap2_cancel_r in H; auto. intros. lia.
Qed.

(** ((d + d1) =? (d + d2)) = (d1 =? d2) *)
Lemma deqb_dplus_cancel_l : forall d1 d2 d,
    deqb (dplus d d1) (dplus d d2) = deqb d1 d2.
Proof.
  intros. bdestruct (deqb d1 d2).
  - subst. apply deqb_refl.
  - apply deqb_false_iff. intro. apply dplus_cancel_l in H0. easy.
Qed.

(** ((d1 + d) =? (d2 + d)) = (d1 =? d2) *)
Lemma deqb_dplus_cancel_r : forall d1 d2 d,
    deqb (dplus d1 d) (dplus d2 d) = deqb d1 d2.
Proof.
  intros. bdestruct (deqb d1 d2).
  - subst. apply deqb_refl.
  - apply deqb_false_iff. intro. apply dplus_cancel_r in H0. easy.
Qed.

(* ======================================================================= *)
(** ** Negation of a [Dims] *)

(** Negation of a [Dims] is defined as the negation of each component. *)
Definition dopp (d : Dims) := dmap d Z.opp.

(** (-d) + d = 0 *)
Lemma dplus_dopp_l (d : Dims) : dplus (dopp d) d = dzero.
Proof. intros. apply dmap2_inv_l. auto with zarith. Qed.

(** d + (-d) = 0 *)
Lemma dplus_dopp_r (d1 : Dims) : dplus d1 (dopp d1) = dzero.
Proof. intros. apply dmap2_inv_r. auto with zarith. Qed.

(* ======================================================================= *)
(** ** Subtraction of [Dims] *)

(** A - B is defined as the A + (-B) *)
Definition dsub (d1 d2 : Dims) : Dims := dplus d1 (dopp d2).

(* ======================================================================= *)
(** ** Scale multiplication of [Dims] *)
Definition dscal (z : Z) (d : Dims) := dmap d (fun x => z * x)%Z.

(** 0 * d = 0 *)
Lemma dscal_0_l (d : Dims) : dscal 0 d = dzero.
Proof. des_dims1 d. simpl. unfold dzero. auto. Qed.

(* ======================================================================= *)
(** ** scale division of a [Dims] *)

(** Divide a [Dims] `d` to `z` pieces, not that `z` must be positive  *)
Definition ddiv (z : Z) (d : Dims) := dmap d (fun x => x / z)%Z.

(** The valid condition for [ddiv] is every dimension is divisible by `z` (bool) *)
Definition ddivCondb (z : Z) (d : Dims) : bool :=
  dAllb d (fun x => Z.eqb (Z.modulo x z) 0).

(** The valid condition for [ddiv] is every dimension is divisible by `z` (Prop) *)
Definition ddivCond (z : Z) (d : Dims) : Prop :=
  dAll d (fun x => Z.modulo x z = 0)%Z.

(** z <> 0 -> (n * d) / n = d *)
Lemma ddiv_dscal z d : (z <> 0)%Z -> ddiv z (dscal z d) = d.
Proof.
  intros. des_dims1 d. lazy [ddiv dscal dmap]. repeat f_equal; auto with Z.
Qed.

(** ddivCond z d -> dscal z (ddiv z d) = d *)
Lemma dscal_ddiv z d : ddivCond z d -> dscal z (ddiv z d) = d.
Proof.
  intros. des_dims1 d. lazy [ddiv dscal dmap]. hnf in H. logic.
  repeat f_equal; auto with Z.
Qed.


(* ======================================================================= *)
(** ** Dimensions of a Unit *)
Definition udims (u : Unit) : Dims :=
  (udim u &T, udim u &L, udim u &M, udim u &I, udim u &Q, udim u &N, udim u &J).

Section udims_spec.
  Infix "+" := dplus.
  
  (** Verify the consistent with [dmakeByBU] *)
  Lemma udims_spec : forall u,
      let dimByBU b : Dims := dmakeByBU b (udim u b) in
      (* Note, the sequence is not important *)
      udims u =
        (dimByBU &T) + (dimByBU &L) + (dimByBU &M) + (dimByBU &N) +
          (dimByBU &J) + (dimByBU &Q) + (dimByBU &I).
  Proof.
    intros. unfold udims, dimByBU. simpl.
    repeat f_equal; auto with zarith.
  Qed.
End udims_spec.


(** Two [udims] equal, iff its components equal (Prop version) *)
Lemma udims_eq_iffP : forall u1 u2,
    udims u1 = udims u2 <->
      udim u1 &T = udim u2 &T /\
        udim u1 &L = udim u2 &L /\
        udim u1 &M = udim u2 &M /\
        udim u1 &I = udim u2 &I /\
        udim u1 &Q = udim u2 &Q /\
        udim u1 &N = udim u2 &N /\
        udim u1 &J = udim u2 &J.
Proof.
  intros. unfold udims. split; intros.
  - inversion H. repeat split; auto.
  - do 6 destruct H as [? H]. repeat (f_equal; auto).
Qed.

(** Two [udims] equal, iff its components equal (bool version) *)
Lemma udims_eq_iffb : forall u1 u2,
    udims u1 = udims u2 <->
      (udim u1 &T =? udim u2 &T)%Z &&
        (udim u1 &L =? udim u2 &L)%Z &&
        (udim u1 &M =? udim u2 &M)%Z &&
        (udim u1 &I =? udim u2 &I)%Z &&
        (udim u1 &Q =? udim u2 &Q)%Z &&
        (udim u1 &N =? udim u2 &N)%Z &&
        (udim u1 &J =? udim u2 &J)%Z = true.
Proof.
  intros. rewrite udims_eq_iffP.
  rewrite !andb_true_iff. rewrite !Z.eqb_eq. tauto.
Qed.

(** [udims] of [Unone] is zero *)
Lemma udims_Unone : forall r : R, udims (Unone r) = dzero.
Proof. intros. unfold udims. simpl. auto. Qed.

(** [udims] of [Ubu b] is [dmakeByBU b 1] *)
Lemma udims_Ubu : forall b, udims (Ubu b) = dmakeByBU b 1.
Proof. unfold udims. destruct b; simpl; auto. Qed.

(** [udims] of [Umul] is addition *)
Lemma udims_Umul : forall u1 u2, udims (u1 * u2) = dplus (udims u1) (udims u2).
Proof. intros. unfold udims. simpl. auto. Qed.

(** [udims] of [Upow u z] equal to multiply of z and [udims u] *)
Lemma udims_upow : forall u z, udims (u ^ z) = dscal z (udims u).
Proof.
  intros. simpl. unfold udims.
  repeat f_equal; rewrite udim_upow; auto with zarith.
Qed.

(** [udims] of [Ucons u b z] equal to addition of [udims u] and [dmakeByBU b z] *)
Lemma udims_ucons : forall u b z, udims (ucons u b z) = dplus (udims u) (dmakeByBU b z).
Proof.
  intros. simpl. unfold udims.
  destruct b; simpl; simp_udim; repeat f_equal; auto with zarith.
Qed.


(* ######################################################################### *)
(** * Normalized unit: the semantics of a Unit *)

(* Declare Scope NU_scope.
Delimit Scope NU_scope with NU.
Open Scope NU_scope.
 *)

(* ======================================================================= *)
(** ** Definitions of normalized unit *)

(** A normalized unit is a pair of a coefficient and a dimensions. *) 
Definition Nunit := (R * Dims)%type.
Definition ncoef (n : Nunit) : R := fst n.
Definition ndims (n : Nunit) : Dims := snd n.

(* Bind Scope NU_scope with Nunit. *)

(** [Nunit] of no-dimensional *)
Definition nunitOne : Nunit := (1, dzero).

(* ======================================================================= *)
(** ** Equality of Nunit *)

(** [Nunit] equal, iff, all components equal. *)
Lemma neq_iff : forall n1 n2 : Nunit,
    n1 = n2 <-> ncoef n1 = ncoef n2 /\ ndims n1 = ndims n2.
Proof. intros. destruct n1, n2. simpl in *. apply pair_eq2. Qed.

(** [Nunit] not equal, iff coefficient or dimensions not equal. *)
Lemma nneq_iff : forall n1 n2 : Nunit,
    n1 <> n2 <-> (ncoef n1 <> ncoef n2) \/ (ndims n1 <> ndims n2).
Proof. intros. rewrite neq_iff. tauto. Qed.

(** Boolean equality of [Nunit] *)
Definition neqb (n1 n2 : Nunit) : bool :=
  (ncoef n1 =? ncoef n2) && deqb (ndims n1) (ndims n2).

(** [neqb] = true is reflexive *)
Lemma neqb_refl n1 : neqb n1 n1 = true.
Proof. unfold neqb. rewrite andb_true_iff, Reqb_true, deqb_true_iff; auto. Qed.

(** [neqb] is true, iff [eq]. *)
Lemma neqb_true_iff n1 n2 : (neqb n1 n2 = true) <-> n1 = n2.
Proof.
  unfold neqb. rewrite !andb_true_iff.
  rewrite Reqb_true, deqb_true_iff. rewrite neq_iff. easy.
Qed.

(** [neqb] is false, iff not [eq] *)
Lemma neqb_false_iff n1 n2 : (neqb n1 n2 = false) <-> (n1 <> n2).
Proof. intros. rewrite <- neqb_true_iff. split; solve_bool. Qed.

Lemma neqb_reflect : forall n1 n2, reflect (n1 = n2) (neqb n1 n2).
Proof.
  intros. destruct (neqb n1 n2) eqn:E1; constructor.
  apply neqb_true_iff; auto. apply neqb_false_iff; auto.
Qed.

Hint Resolve neqb_reflect : bdestruct.

(** [Nunit eq] is decidable *)
Lemma neq_dec (n1 n2 : Nunit) : {n1 = n2} + {n1 <> n2}.
Proof. bdestruct (neqb n1 n2); auto. Qed.

(** [neqb] is commutative. *)
Lemma neqb_comm n1 n2 : neqb n1 n2 = neqb n2 n1.
Proof. bdestruct (neqb n1 n2); bdestruct (neqb n2 n1); auto; congruence. Qed.

(* ======================================================================= *)
(** ** Multiplication of [Nunit] *)

Definition nmul (n1 n2 : Nunit) : Nunit :=
  ((ncoef n1 * ncoef n2)%R, dplus (ndims n1) (ndims n2)).

Lemma nmul_comm (n1 n2 : Nunit) : nmul n1 n2 = nmul n2 n1.
Proof.
  destruct n1,n2. unfold nmul; simpl.
  rewrite Rmult_comm, dplus_comm; auto.
Qed.

Lemma nmul_assoc (n1 n2 n3 : Nunit) : nmul (nmul n1 n2) n3 = nmul n1 (nmul n2 n3).
Proof.
  destruct n1,n2,n3. unfold nmul; simpl.
  rewrite Rmult_assoc, dplus_assoc; auto.
Qed.

Lemma nmul_1_l (n : Nunit) : nmul nunitOne n = n.
Proof. cbv. destruct n. des_dims1 d. f_equal. lra. Qed.

Lemma nmul_1_r (n : Nunit) : nmul n nunitOne = n.
Proof. intros. rewrite nmul_comm. apply nmul_1_l. Qed.

(* ======================================================================= *)
(** ** Inverse of [Nunit] *)
Definition ninv (n1 : Nunit) : Nunit := (Rinv (ncoef n1), dopp (ndims n1)).

(* ======================================================================= *)
(** ** Division of [Nunit] *)
Definition ndiv (n1 n2 : Nunit) : Nunit := nmul n1 (ninv n2).

(* ======================================================================= *)
(** ** Integer power of a [Nunit] *)
Definition npow (n : Nunit) (z : Z) :=
  (powerRZ (ncoef n) z, dscal z (ndims n)).

(** npow n 2 = nmul n n *)
Lemma npow2_eq_nmul : forall (n : Nunit), npow n 2 = nmul n n.
Proof.
  intros. unfold npow, nmul. f_equal.
  - cbv. ra.
  - destruct n. des_dims1 d.
    lazy [dscal dmap ndims snd dplus dmap2]. repeat (f_equal; try lia).
Qed.


(* ======================================================================= *)
(** ** nth root of a [Nunit] *)

(** z-th root of a [Nunit] `n`. Note that z should be positive *)
Definition nroot (n : Nunit) (z : Z) : Nunit :=
  (Rpower (ncoef n) (/ Z2R z), ddiv z (ndims n)).

(** Condition of [nroot] is that: z is positive && d is divisible by n (Proposition) *)
Definition nrootCond (n : Nunit) (z : Z) : Prop :=
  (0 < z)%Z /\ ddivCond z (ndims n).

(** Condition of [nroot] is that: z is positive && d is divisible by n (boolean) *)
Definition nrootCondb (n : Nunit) (z : Z) : bool :=
  (Z.gtb z 0) && ddivCondb z (ndims n).

(** nroot (npow n z) z = n *)
Lemma nroot_npow : forall n z, (0 < z)%Z -> 0 < ncoef n -> nroot (npow n z) z = n.
Proof.
  intros. destruct n. des_dims1 d. unfold nroot. f_equal.
  - simpl. unfold Z2R. apply Rpower_powerRZ_inv; auto. lia.
  - simpl. assert (z <> 0)%Z by lia. repeat f_equal; auto with Z.
Qed.

(** npow (nroot n z) z = n *)
Lemma npow_nroot : forall n z,
    (0 < z)%Z -> 0 < ncoef n -> nrootCond n z -> npow (nroot n z) z = n.
Proof.
  intros. destruct n. des_dims1 d. unfold npow, nroot in *. simpl in *. f_equal.
  - unfold Z2R. apply powerRZ_Rpower_inv; auto. lia.
  - unfold nrootCond in H1. simpl in H1. logic. repeat f_equal; auto with Z.
Qed.

(** nroot 2 (nmul n n) = n *)
Lemma nroot2_nmul : forall n, 0 < ncoef n -> nroot (nmul n n) 2 = n.
Proof.
  intros. replace (nmul n n) with (npow n 2). apply nroot_npow; auto. lia.
  rewrite npow2_eq_nmul. auto.
Qed.

(** npow (nroot 2 n) 2 = n *)
Lemma npow_nroot2 : forall n, 0 < ncoef n -> nrootCond n 2 -> npow (nroot n 2) 2 = n.
Proof. intros. apply npow_nroot; auto; try lia. Qed.


(* ======================================================================= *)
(** ** Conversion between [Unit] and [Nunit]. *)

(** Conversion from [Unit] to [Nunit]. *)
Definition u2n (u : Unit) : Nunit := (ucoef u, udims u).

Section test.
  Let m : Unit := &L.
  Let s : Unit := &T.
  Let u1 : Unit := 1 * m * s.
  Let u2 : Unit := s * 1 * m.
  (* Compute u2n u1. *)
  (* Compute u2n u2. *)
  (* Compute neqb (u2n u1) (u2n u2). *)

  (* (10m)^3 = 1000 m^3 *)
  Goal npow (u2n (10 * m)) 3 = u2n (1000 * m * m * m).
  Proof. cbv. f_equal. lra. Qed.

  
  (* 3\sqrt(1000 m^3) = 10 m *)
  Goal npow (u2n (10 * m)) 3 = u2n (1000 * m * m * m).
  Proof. cbv. f_equal. lra. Qed.

  
End test.

(** [ncoef] of [u2n u] is the coefficient of the `u` *)
Lemma ncoef_u2n : forall u, ncoef (u2n u) = ucoef u.
Proof. intros. reflexivity. Qed.

(** Dimension of [u2n u] has known form *)
Lemma udim_u2n : forall u,
    let '(coef, (ds, dm, dkg, dA, dK, dmol, dcd)) := u2n u in
    udim u BUTime = ds /\
      udim u BULength = dm /\
      udim u BUMass = dkg /\
      udim u BUElectricCurrent = dA /\
      udim u BUThermodynamicTemperature = dK /\
      udim u BUAmountOfSubstance = dmol /\
      udim u BULuminousIntensity = dcd.
Proof. intros. simpl. repeat split; auto. Qed.

(** [ndims] of [u2n u] is [udims u] *)
Lemma ndims_u2n u : ndims (u2n u) = udims u.
Proof.
  destruct (u2n u) as [c d] eqn:H. des_dims1 d. unfold ndims, udims.
  pose proof (udim_u2n u). rewrite H in H0. logic. simpl. subst. auto.
Qed.

(** [u2n] of [Unone]. *)
Lemma u2n_Unone : forall r, u2n (Unone r) = (r, dzero).
Proof. auto. Qed.

(** u2n of [b]. *)
Lemma u2n_Ubu : forall b, u2n (Ubu b) = (1, dmakeByBU b 1).
Proof. intros. unfold u2n. f_equal. simpl. rewrite udims_Ubu. auto. Qed.

(** A rewriting of [u2n] [Umul]. *)
Lemma u2n_Umult : forall (u1 u2 : Unit),
  u2n (u1 * u2) =
    ((ncoef (u2n u1) * ncoef (u2n u2))%R,
      dplus (ndims (u2n u1)) (ndims (u2n u2))).
Proof. intros. simpl. reflexivity. Qed.

Lemma u2n_Umult_cancel_l : forall u1 u2 u,
  u2n u1 = u2n u2 -> u2n (u * u1) = u2n (u * u2).
Proof.
  intros. rewrite !u2n_Umult. destruct (u2n u1),(u2n u2),(u2n u).
  rewrite neq_iff in *; simpl in *. destruct H; subst. auto.
Qed.

Lemma u2n_Umult_cancel_r : forall u1 u2 u,
  u2n u1 = u2n u2 -> u2n (u1 * u) = u2n (u2 * u).
Proof.
  intros. rewrite !u2n_Umult. destruct (u2n u1),(u2n u2),(u2n u).
  rewrite neq_iff in *; simpl in *. destruct H; subst. auto.
Qed.

(** [u2n] is compatible for [Umul]. *)
Lemma u2n_Umult_wd u1 u2 u3 u4 :
  u2n u1 = u2n u2 -> u2n u3 = u2n u4 ->
  u2n (u1 * u3) = u2n (u2 * u4).
Proof.
  intros. rewrite !u2n_Umult.
  destruct (u2n u1), (u2n u2), (u2n u3), (u2n u4).
  inversion H. inversion H0. auto.
Qed.

(** A rewriting of [u2n] [Uinv]. *)
Lemma u2n_Uinv : forall u,
  u2n (/u) = ((/(ncoef (u2n u)))%R, dopp (ndims (u2n u))).
Proof. easy. Qed.

(** [u2n] is compatible for [Uinv]. *)
Lemma u2n_Uinv_wd u1 u2 : u2n u1 = u2n u2 -> u2n (/u1) = u2n (/u2).
Proof.
  intros. rewrite !u2n_Uinv. destruct (u2n u1), (u2n u2). 
  inversion H. simpl in *. auto.
Qed.

(** [u2n] is compatible for [upowNat]. *)
Lemma u2n_upowNat_wd u1 u2 n :
  u2n u1 = u2n u2 -> u2n (upowNat u1 n) = u2n (upowNat u2 n).
Proof.
  intros. induction n; simpl; auto. destruct n; auto.
  apply u2n_Umult_wd; auto.
Qed.

(** [ucoef] of [upowNat]. *)
Lemma ucoef_upowNat u n : ucoef (upowNat u n) = pow (ncoef (u2n u)) n.
Proof.
  intros. induction n; simpl; auto. destruct n.
  - simpl. rewrite <- ncoef_u2n. simpl. ring.
  - rewrite ucoef_Umul. rewrite IHn. rewrite <- ncoef_u2n; simpl. auto.
Qed.

(** [u2n] is compatible for [Upow]. *)
Lemma u2n_Upow_wd u1 u2 z : u2n u1 = u2n u2 -> u2n (u1 ^ z) = u2n (u2 ^ z).
Proof.
  intros. unfold upow. destruct z; auto.
  - apply u2n_upowNat_wd. auto.
  - apply u2n_Uinv_wd. apply u2n_upowNat_wd. auto.
Qed.

(** [ucoef] of [upow]. *)
Lemma ucoef_upow u z : ucoef (upow u z) = powerRZ (ncoef (u2n u)) z.
Proof.
  intros. unfold upow. destruct z; auto.
  - apply ucoef_upowNat.
  - simpl. f_equal. apply ucoef_upowNat.
Qed.

(** A rewriting of [u2n] [upow]. *)
Lemma u2n_upow_rw u z :
  u2n (u ^ z) = (powerRZ (ncoef (u2n u)) z, dscal z (ndims (u2n u))).
Proof.
  intros. apply neq_iff; simpl. split.
  apply ucoef_upow. apply udims_upow.
Qed.

(** Conversion from [Nunit] to [Unit]. *)
Definition n2u (n : Nunit) : Unit :=
  let '(coef, (ds, dm, dkg, dA, dK, dmol, dcd)) := n in
  let u := Unone coef in
  let u := ucons u &T ds in
  let u := ucons u &L dm in
  let u := ucons u &M dkg in
  let u := ucons u &I dA in
  let u := ucons u &Q dK in
  let u := ucons u &N dmol in
  let u := ucons u &J dcd in
  u.

(** [ucoef] of [n2u n] equal to [ncoef n] *)
Lemma ucoef_n2u : forall n, ucoef (n2u n) = ncoef n.
Proof.
  intros. destruct n as [c d]. des_dims1 d; simpl. simp_ucoef. auto.
Qed.

(** Dimension of [n2u n] is the dimension of the n. *)
Lemma udim_n2u n b : udim (n2u n) b = dimFromDims (ndims n) b.
Proof.
  destruct n as [c d]. des_dims1 d. simpl.
  destruct b; simp_udim; repeat split; lia.
Qed.

(** Dimension of [n2u n] is the dimension of the n (extended version). *)
Lemma udim_n2u_ext n :
  let '(_, (ds, dm, dkg, dA, dK, dmol, dcd)) := n in
  udim (n2u n) BUTime = ds /\
    udim (n2u n) BULength = dm /\
    udim (n2u n) BUMass = dkg /\
    udim (n2u n) BUElectricCurrent = dA /\
    udim (n2u n) BUThermodynamicTemperature = dK /\
    udim (n2u n) BUAmountOfSubstance = dmol /\
    udim (n2u n) BULuminousIntensity = dcd.
Proof.
  destruct n as [? d]. des_dims1 d. simpl. simp_udim. simpl. tauto.
Qed.

(** [udims] of [n2u (c,d)] equal to `d` *)
Lemma udims_n2u : forall c d, udims (n2u (c, d)) = d.
Proof. intros. unfold udims. des_dims1 d. rewrite !udim_n2u. simpl. auto. Qed.

(** [n2u] is injective about coefficient. *)
Lemma n2u_eq_imply_coef_eq : forall n1 n2,
    n2u n1 = n2u n2 -> ncoef n1 = ncoef n2.
Proof. intros. rewrite <- !ucoef_n2u. rewrite H. auto. Qed.


(** [n2u] is injective about dimensions. *)
Lemma n2u_eq_imply_dims_eq : forall n1 n2,
    n2u n1 = n2u n2 -> ndims n1 = ndims n2.
Proof.
  logic. pose proof (udim_n2u_ext n1). rewrite H in H0.
  destruct n1 as [c1 d1], n2 as [c2 d2]. des_dims2 d1 d2.
  logic. rewrite udim_n2u in *. simpl in *. subst. auto.
Qed.

(** [n2u] equal, iff [Nunit] equal. *)
Lemma n2u_eq_iff : forall n1 n2, n2u n1 = n2u n2 <-> n1 = n2.
Proof.
  intros n1 n2. split; intros H; subst; auto.
  apply neq_iff. split.
  apply n2u_eq_imply_coef_eq; auto. apply n2u_eq_imply_dims_eq; auto.
Qed.

(** [n2u] not equal, iff [Nunit] not equal. *)
Lemma n2u_neq_iff : forall n1 n2, n2u n1 <> n2u n2 <-> n1 <> n2.
Proof. intros. rewrite <- n2u_eq_iff. easy. Qed.

(** [u2n] o [n2u] is identity *)
Lemma u2n_n2u : forall (n : Nunit), u2n (n2u n) = n.
Proof.
  intros n. unfold u2n, udims.
  induction n as [c d]. des_dims1 d.
  rewrite ucoef_n2u, !udim_n2u. simpl. auto.
Qed.

(* ======================================================================= *)
(** ** Dimensionless unit *)

(** Is a [Nunit] `n` is dimensionless? *)
Definition ndim1b (n : Nunit) : bool := neqb n nunitOne.

(** [ndim1b] of `n` return true, iff `n` is [nunitOne] *)
Lemma ndimb1b_true_iff : forall n, ndim1b n = true <-> n = nunitOne.
Proof. intros. unfold ndim1b. rewrite neqb_true_iff. tauto. Qed.

(** Is a [Unit] `u` is dimensionless? *)
Definition udim1b (u : Unit) : bool := neqb (u2n u) nunitOne.

(** [udim1b] of `u` return true, iff [u2n] of `u` is [nunitOne] *)
Lemma udimb1b_true_iff : forall u, udim1b u = true <-> u2n u = nunitOne.
Proof. intros. unfold udim1b. rewrite neqb_true_iff. tauto. Qed.


(* ######################################################################### *)
(** * Comparison of [Unit]: with [Nunit] comparison. *)

Open Scope Unit_scope.

(* ======================================================================= *)
(** ** Boolean Equality of [Unit] *)
Definition ueqb (u1 u2 : Unit) : bool := neqb (u2n u1) (u2n u2).

Notation "u1 =? u2" := (ueqb u1 u2) : Unit_scope.

(** [ueqb] of [ucons u1] and [ucons u2], equal to [ueqb u1 u2]. *)
Lemma ueqb_ucons : forall u1 u2 b dim,
    ueqb (ucons u1 b dim) (ucons u2 b dim) = ueqb u1 u2.
Proof.
  intros. unfold ueqb, neqb. apply andb_eq_inv; auto.
  - simpl. simp_ucoef. auto.
  - rewrite !ndims_u2n. rewrite !udims_ucons. rewrite deqb_dplus_cancel_r. auto.
Qed.

(** [ueqb] is true, it is reflexive *)
Lemma ueqb_true_refl (u : Unit) : u =? u = true.
Proof. unfold ueqb. apply neqb_refl. Qed.

(** [ueqb] is commutative. *)
Lemma ueqb_comm (u1 u2 : Unit) : (u1 =? u2)%U = (u2 =? u1)%U.
Proof.
  unfold ueqb in *. apply neqb_comm.
Qed.

(** [ueqb] is true, iff, equality of [u2n] *)
Lemma ueqb_true_iff : forall (u1 u2 : Unit), u1 =? u2 = true <-> u2n u1 = u2n u2.
Proof. intros. unfold ueqb. apply neqb_true_iff. Qed.

(** [ueqb] is false, iff, inequality of [u2n] *)
Lemma ueqb_false_iff : forall (u1 u2 : Unit), u1 =? u2 = false <-> u2n u1 <> u2n u2.
Proof. intros. rewrite <- ueqb_true_iff. split; solve_bool. Qed.

(** [ueqb] reflects the equality of [u2n] *)
Lemma ueqb_reflect : forall u1 u2, reflect (u2n u1 = u2n u2) (u1 =? u2).
Proof.
  intros. destruct (u1 =? u2) eqn:Eu; constructor.
  apply ueqb_true_iff; auto. apply ueqb_false_iff; auto.
Qed.

(* ======================================================================= *)
(** ** Proposional euqality of [Unit] *)

(** Two [Unit] is semantical equal *)
Definition ueq (u1 u2 : Unit) : Prop := u2n u1 = u2n u2.

Infix "==" := (ueq) (at level 70) : Unit_scope.

(** [ueq] iff [ueqb]. *)
Lemma ueq_iff_ueqb u1 u2 : (u1 == u2) <-> (u1 =? u2 = true).
Proof.
  unfold ueq, ueqb.
  rewrite neqb_true_iff. reflexivity.
Qed.

(** [ueq] of [ucons]. *)
Lemma ueq_ucons : forall u1 u2 b dim,
    u1 == u2 -> ucons u1 b dim == ucons u2 b dim.
Proof.
  intros. rewrite !ueq_iff_ueqb in *.
  rewrite ueqb_ucons. auto.
Qed.

(** Equality of two units, iff their coefficients and dimensions all equal. *)
Lemma ueq_iff_coef_dims : forall (u1 u2 : Unit),
    let (c1,d1) := u2n u1 in
    let (c2,d2) := u2n u2 in
    u1 == u2 <-> c1 = c2 /\ d1 = d2.
Proof. intros. simpl. unfold ueq. rewrite neq_iff. simpl. easy. Qed.

(** [ueq] is an equivalence relation. *)
Lemma ueq_refl : forall (u : Unit), u == u.
Proof. intros. unfold ueq. reflexivity. Qed.

Lemma ueq_sym : forall (u1 u2 : Unit), u1 == u2 -> u2 == u1.
Proof.
  intros u1 u2. rewrite !ueq_iff_ueqb. rewrite ueqb_comm. auto.
Qed.

Lemma ueq_trans : forall (u1 u2 u3 : Unit), u1 == u2 -> u2 == u3 -> u1 == u3.
Proof.
  intros until u3. rewrite !ueq_iff_ueqb, !ueqb_true_iff.
  intros. rewrite H; auto.
Qed.

#[export] Instance ueq_equiv : Equivalence ueq.
Proof.
  constructor; hnf; intros; auto.
  apply ueq_refl. apply ueq_sym; auto. apply ueq_trans with y; auto.
Qed.

(* ======================================================================= *)
(** ** Approximate relation of [Unit] *)

(** Check if two units is approximate, propositional version. *)
Definition unit_approx (u1 u2 : Unit) (diff : R) : Prop :=
  let (c1, d1) := u2n u1 in
  let (c2, d2) := u2n u2 in
  (d1 = d2) /\ (Rapprox c1 c2 diff).

(** Check if two units is approximate, boolean version. *)
Definition unit_approxb (u1 u2 : Unit) (diff : R) : bool :=
  let (c1, d1) := u2n u1 in
  let (c2, d2) := u2n u2 in
  (deqb d1 d2) && (Rapproxb c1 c2 diff).

Example unit1 : Unit := (1.5e-100 * &L).
Example unit2 : Unit := (1.6e-100 * &L).
Example diff : R := 0.1e-100.
Goal unit_approxb unit1 unit2 diff = true.
  (*   compute. (* expanded too much *) *)
  lazy [unit_approxb]. simpl.
  unfold Rapproxb, diff. rewrite Rabs_left; ra. autoRbool; ra.
Qed.


(* ######################################################################### *)
(** * Normalization of [Unit] *)

(* The idea is inspired by [Qred] in [Qcanon] *)

(* ======================================================================= *)
(** ** Normaliztion of a [Unit] *)

(** Normalize a [Unit] `u` *)
Definition unorm (u : Unit) : Unit := n2u (u2n u).

Section test.
  Let m := &L.
  Let kg := &M.
  Let s := &T.
  (* Compute unorm (kg * m * s * 2). *)
  (* Compute unorm (2 * kg * s * m). *)
  (* Compute unorm (unorm (2 * kg * s * m)). *)
End test.

(** Every two [Unit] with same semantics, [unorm] generate same form. *)
Lemma unorm_complete : forall (u1 u2 : Unit),
    (u1 =? u2 = true) -> unorm u1 = unorm u2.
Proof. intros. unfold unorm. apply ueqb_true_iff in H. rewrite H. auto. Qed.

(** Every two [Unit] with same form, have same semantics *)
Lemma unorm_sound : forall (u1 u2 : Unit),
    unorm u1 = unorm u2 -> (u1 =? u2 = true).
Proof.
  intros. unfold unorm in *. apply n2u_eq_iff in H.
  apply ueqb_true_iff. auto.
Qed.

(** [unorm] involution law *)
Lemma unorm_involutive : forall u : Unit, unorm (unorm u) = unorm u.
Proof. intros. unfold unorm. rewrite u2n_n2u. auto. Qed.


(* ======================================================================= *)
(** ** Normalized [Unit] *)

(** A unit is normalized *)
Definition unormed (u : Unit) : Prop := unorm u = u.

(** [unorm] generate a normalized result *)
Lemma unorm_unormed : forall u, unormed (unorm u).
Proof. intros. unfold unormed. rewrite unorm_involutive. auto. Qed.

(** [n2u (1,d)] is normalized *)
Lemma n2u_coef1_unormed : forall d, unormed (n2u (1, d)).
Proof.
  intros. des_dims1 d. hnf. unfold unorm. rewrite u2n_n2u. auto.
Qed.

