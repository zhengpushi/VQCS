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

Require Import BasicExt.
Require Export Unit. 

(* 分解 {a=b} + {a<>b} 并消除 a<>b *)
Ltac des_zdec_neq a b :=
  destruct (Z.eq_dec a b); [
      subst |
      let H := fresh "H" in
      right; intros H; inversion H; auto
    ].


(** * Dimensions of Unit *)

(** ** Difinition of dimensions *)

(** A tuple of 7 integers which each one means the dimension of a [BasicUnit]. *)
Definition Dims := (Z * Z * Z * Z * Z * Z * Z)%type.

(** Zero dimensions, means a pure number value. *)
Definition Dzero : Dims := (0,0,0,0,0,0,0)%Z.


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
Lemma Deq_dec : forall (d1 d2 : Dims), {d1 = d2} + {d1 <> d2}.
Proof.
  intros.
  des_dims2 d1 d2.
  des_zdec_neq a b.
  des_zdec_neq a0 b0.
  des_zdec_neq a1 b1.
  des_zdec_neq a2 b2.
  des_zdec_neq a3 b3.
  des_zdec_neq a4 b4.
  des_zdec_neq a5 b5. auto.
Qed.

(** Equality of Dims, iff all components are equal. *)
Lemma Deq_eq_iff : forall (d1 d2 : Dims),
    let '(a,a0,a1,a2,a3,a4,a5) := d1 in
    let '(b,b0,b1,b2,b3,b4,b5) := d2 in
    d1 = d2 <-> a = b /\ a0 = b0 /\ a1 = b1 /\ a2 = b2 /\ a3 = b3 /\ a4 = b4 /\ a5 = b5.
Proof. intros. des_dims2 d1 d2. apply pair_eq_iff_7. Qed.

(** Inequality of Dims, iff at least one of the dimension is not equal. *)
Lemma Deq_neq_iff : forall (d1 d2 : Dims),
    let '(a,a0,a1,a2,a3,a4,a5) := d1 in
    let '(b,b0,b1,b2,b3,b4,b5) := d2 in
    d1 <> d2 <-> a <> b \/ a0 <> b0 \/ a1 <> b1 \/ a2 <> b2 \/ a3 <> b3 \/ a4 <> b4 \/ a5 <> b5.
Proof. intros. des_dims2 d1 d2. apply pair_neq_iff_7. Qed.


(** ** Boolean equality of [Dims] *)

(** Boolean equality of [Dims] is defined as the equality of each component. *)
Definition Deqb (d1 d2 : Dims) : bool.
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

(** [Deqb] is true, iff propositonal equal. *)
Lemma Deqb_true_iff (d1 d2 : Dims) : Deqb d1 d2 = true <-> d1 = d2.
Proof.
  pose proof (Deq_eq_iff d1 d2). des_dims2 d1 d2. rewrite H. simpl.
  rewrite <- !Z.eqb_eq. rewrite !andb_true_iff. tauto.
Qed.

(** [Deqb] is false, iff propositonal not equal. *)
Lemma Deqb_false_iff (d1 d2 : Dims) : 
  Deqb d1 d2 = false <-> d1 <> d2.
Proof. intros. rewrite <- Deqb_true_iff. split; solve_bool. Qed.

Lemma Deqb_reflect : forall d1 d2 : Dims, reflect (d1 = d2) (Deqb d1 d2).
Proof.
  intros. destruct (Deqb d1 d2) eqn:E1; constructor.
  apply Deqb_true_iff; auto. apply Deqb_false_iff; auto.
Qed.

Global Hint Resolve Deqb_reflect : bdestruct.

(** [Deqb] is reflexive. *)
Lemma Deqb_refl (d : Dims) : Deqb d d = true.
Proof. apply Deqb_true_iff. auto. Qed.

(** [Deqb] is commutative. *)
Lemma Deqb_comm d1 d2 : Deqb d1 d2 = Deqb d2 d1.
Proof. bdestruct (Deqb d1 d2); bdestruct (Deqb d2 d1); auto; congruence. Qed.


(** ** Make [Dims] with [BaseUnit] *)
Definition DmakeByBU (b : BaseUnit) (z : Z) : Dims :=
  match b with
  | &T => (z,0,0,0,0,0,0)%Z
  | &L => (0,z,0,0,0,0,0)%Z
  | &M => (0,0,z,0,0,0,0)%Z
  | &I => (0,0,0,z,0,0,0)%Z
  | &Q => (0,0,0,0,z,0,0)%Z
  | &N => (0,0,0,0,0,z,0)%Z
  | &J => (0,0,0,0,0,0,z)%Z
  end.


(** ** All of [Dims] *)

(** All of [Dims] satisfy P, means all components satisfy P. *)
Definition DAll (d : Dims) (P : Z -> Prop) : Prop.
  des_dims1 d.
  exact (P a /\ P a0 /\ P a1 /\ P a2 /\ P a3 /\ P a4 /\ P a5).
Defined.


(** ** Get dim of a [BaseUnit] from [Dims] *)
Definition DimFromDims (d : Dims) (b : BaseUnit) : Z.
  des_dims1 d.
  exact (match b with
         | &T => a
         | &L => a0
         | &M => a1
         | &I => a2
         | &Q => a3
         | &N => a4
         | &J => a5
         end).
Defined.
  

(** ** Map of [Dims] *)

(** Mapping unary function `f` to [Dims] `d` *)
Definition Dmap (d : Dims) (f : Z -> Z) : Dims.
  des_dims1 d.
  exact (f a, f a0, f a1, f a2, f a3, f a4, f a5).
Defined.

(** Mapping binary function `f` to [Dims] `d1` and `d2` *)
Definition Dmap2 (d1 d2 : Dims) (f : Z -> Z -> Z) : Dims.
  des_dims2 d1 d2.
  exact (f a b, f a0 b0, f a1 b1, f a2 b2, f a3 b3, f a4 b4, f a5 b5).
Defined.

(** [Dmap2] is commutative, if the operation is. *)
Lemma Dmap2_comm : forall d1 d2 f,
    (forall a b, f a b = f b a) ->
    Dmap2 d1 d2 f = Dmap2 d2 d1 f.
Proof.
  intros. unfold Dmap2. des_dims2 d1 d2; simpl. repeat (f_equal; auto).
Qed.

(** [Dmap2] is associative, if the operation is. *)
Lemma Dmap2_assoc : forall d1 d2 d3 f,
    (forall a b c, f (f a b) c = f a (f b c)) ->
    Dmap2 (Dmap2 d1 d2 f) d3 f = Dmap2 d1 (Dmap2 d2 d3 f) f.
Proof.
  intros. unfold Dmap2. des_dims3 d1 d2 d3. repeat (f_equal; auto).
Qed.

(** [Dmap2] has left identity, if the operation has. *)
Lemma Dmap2_0_l : forall d f, (forall a, f 0 a = a)%Z -> Dmap2 Dzero d f = d.
Proof. intros. des_dims1 d; simpl. repeat (f_equal; auto). Qed.

(** [Dmap2] has right identity, if the operation has. *)
Lemma Dmap2_0_r : forall d f, (forall a, f a 0 = a)%Z -> Dmap2 d Dzero f = d.
Proof. intros. des_dims1 d; simpl. repeat (f_equal; auto). Qed.

(** [Dmap2] has left inverse, if the operation has. *)
Lemma Dmap2_inv_l : forall d f g, (forall a, f (g a) a = 0)%Z -> Dmap2 (Dmap d g) d f = Dzero.
Proof. intros. des_dims1 d; simpl. unfold Dzero. repeat (f_equal; auto). Qed.

(** [Dmap2] has right inverse, if the operation has. *)
Lemma Dmap2_inv_r : forall d f g, (forall a, f a (g a) = 0)%Z -> Dmap2 d (Dmap d g) f = Dzero.
Proof. intros. des_dims1 d; simpl. unfold Dzero. repeat (f_equal; auto). Qed.

(** [Dmap2] cancel law on left *)
Lemma Dmap2_cancel_l : forall d d1 d2 f,
    (forall a b c : Z, (f a b = f a c)%Z -> b = c) ->
    Dmap2 d d1 f = Dmap2 d d2 f <-> d1 = d2.
Proof.
  intros. split; intros; [| subst; auto].
  des_dims3 d d1 d2. simpl in H0. inversion H0.
  apply H in H2,H3,H4,H5,H6,H7,H8. repeat f_equal; auto.
Qed.

(** [Dmap2] cancel law on right *)
Lemma Dmap2_cancel_r : forall d d1 d2 f,
    (forall a b c : Z, (f a c = f b c)%Z -> a = b) ->
    Dmap2 d1 d f = Dmap2 d2 d f <-> d1 = d2.
Proof.
  intros. split; intros; [| subst; auto].
  des_dims3 d d1 d2. simpl in H0. inversion H0.
  apply H in H2,H3,H4,H5,H6,H7,H8. repeat f_equal; auto.
Qed.


(** ** Addition of [Dims] *)

(** Addition of [Dims] is defined as the addition of each component. *)
Definition Dplus (d1 d2 : Dims) : Dims := Dmap2 d1 d2 Z.add.

(** [Dplus] is commutative. *)
Lemma Dplus_comm : forall (d1 d2 : Dims), Dplus d1 d2 = Dplus d2 d1.
Proof. intros. apply Dmap2_comm. auto with zarith. Qed.

(** [Dplus] is associative. *)
Lemma Dplus_assoc : forall (d1 d2 d3 : Dims),
    Dplus (Dplus d1 d2) d3 = Dplus d1 (Dplus d2 d3).
Proof. intros. apply Dmap2_assoc. auto with zarith. Qed.

(** 0 + d = d *)
Lemma Dplus_0_l : forall d, Dplus Dzero d = d.
Proof. intros. apply Dmap2_0_l. auto with zarith. Qed.

(** d + 0 = d *)
Lemma Dplus_0_r : forall d, Dplus d Dzero = d.
Proof. intros. apply Dmap2_0_r. auto with zarith. Qed.

(** d + d1 = d + d2 -> d1 = d2 *)
Lemma Dplus_cancel_l : forall d d1 d2, Dplus d d1 = Dplus d d2 <-> d1 = d2.
Proof.
  intros. split; intros; [| subst; auto].
  apply Dmap2_cancel_l in H; auto. intros. lia.
Qed.

(** d1 + d = d2 + d -> d1 = d2 *)
Lemma Dplus_cancel_r : forall d d1 d2, Dplus d1 d = Dplus d2 d <-> d1 = d2.
Proof.
  intros. split; intros; [| subst; auto].
  apply Dmap2_cancel_r in H; auto. intros. lia.
Qed.

(** ((d + d1) =? (d + d2)) = (d1 =? d2) *)
Lemma Deqb_Dplus_cancel_l : forall d1 d2 d,
    Deqb (Dplus d d1) (Dplus d d2) = Deqb d1 d2.
Proof.
  intros. bdestruct (Deqb d1 d2).
  - subst. apply Deqb_refl.
  - apply Deqb_false_iff. intro. apply Dplus_cancel_l in H0. easy.
Qed.

(** ((d1 + d) =? (d2 + d)) = (d1 =? d2) *)
Lemma Deqb_Dplus_cancel_r : forall d1 d2 d,
    Deqb (Dplus d1 d) (Dplus d2 d) = Deqb d1 d2.
Proof.
  intros. bdestruct (Deqb d1 d2).
  - subst. apply Deqb_refl.
  - apply Deqb_false_iff. intro. apply Dplus_cancel_r in H0. easy.
Qed.


(** ** Negation of a [Dims] *)

(** Negation of a [Dims] is defined as the negation of each component. *)
Definition Dopp (d : Dims) := Dmap d Z.opp.

(** (-d) + d = 0 *)
Lemma Dplus_Dopp_l (d : Dims) : Dplus (Dopp d) d = Dzero.
Proof. intros. apply Dmap2_inv_l. auto with zarith. Qed.

(** d + (-d) = 0 *)
Lemma Dplus_Dopp_r (d1 : Dims) : Dplus d1 (Dopp d1) = Dzero.
Proof. intros. apply Dmap2_inv_r. auto with zarith. Qed.


(** ** Subtraction of [Dims] *)

(** A - B is defined as the A + (-B) *)
Definition Dsub (d1 d2 : Dims) : Dims := Dplus d1 (Dopp d2).


(** ** Scale multiplication of [Dims] *)
Definition Dcmul (z : Z) (d : Dims) := Dmap d (fun x => z * x)%Z.

(** 0 * d = 0 *)
Lemma Dcmul_0_l (d : Dims) : Dcmul 0 d = Dzero.
Proof. des_dims1 d. simpl. unfold Dzero. auto. Qed.


(** ** Square root of a [Dims] *)

(** Square root of a [Dims] *)
Definition Dsqrt (d : Dims) : Dims := Dmap d (fun x => x / 2)%Z.

(** The valid condition for [Dsqrt]: every dimension is even *)
Definition Dsqrt_cond (d : Dims) : Prop := DAll d (Z.Even).

(** √(2 * d) = d *)
Lemma Dsqrt_Dcmul2 d : Dsqrt (Dcmul 2 d) = d.
Proof.
  des_dims1 d. Opaque Z.mul. simpl. repeat f_equal; apply zdiv2_mul2_eq.
Qed.

(** 2 * √d = d *)
Lemma Dcmul2_Dsqrt d : Dsqrt_cond d -> Dcmul 2 (Dsqrt d) = d.
Proof.
  intros. des_dims1 d. simpl. do 6 destruct H as [? H].
  repeat f_equal; apply zmul2_div2_eq; auto.
Qed.

(** ** Dimensions of a Unit *)
Definition Udims (u : Unit) : Dims :=
  (Udim u &T, Udim u &L, Udim u &M, Udim u &I, Udim u &Q, Udim u &N, Udim u &J).

Section Udims_spec.
  Infix "+" := Dplus.
  
  (** Verify the consistent with [DmakeByBU] *)
  Lemma Udims_spec2 : forall u,
      let dimByBU b : Dims := DmakeByBU b (Udim u b) in
      (* Note, the sequence is not important *)
      Udims u =
        (dimByBU &T) + (dimByBU &L) + (dimByBU &M) + (dimByBU &N) +
          (dimByBU &J) + (dimByBU &Q) + (dimByBU &I).
  Proof.
    intros. unfold Udims, dimByBU. simpl.
    repeat f_equal; auto with zarith.
  Qed.
End Udims_spec.


(** Two [Udims] equal, iff its components equal (Prop version) *)
Lemma Udims_eq_iffP : forall u1 u2,
    Udims u1 = Udims u2 <->
      Udim u1 &T = Udim u2 &T /\
        Udim u1 &L = Udim u2 &L /\
        Udim u1 &M = Udim u2 &M /\
        Udim u1 &I = Udim u2 &I /\
        Udim u1 &Q = Udim u2 &Q /\
        Udim u1 &N = Udim u2 &N /\
        Udim u1 &J = Udim u2 &J.
Proof.
  intros. unfold Udims. split; intros.
  - inversion H. repeat split; auto.
  - simp_logic. repeat (f_equal; auto).
Qed.

(** Two [Udims] equal, iff its components equal (bool version) *)
Lemma Udims_eq_iffb : forall u1 u2,
    Udims u1 = Udims u2 <->
      (Udim u1 &T =? Udim u2 &T)%Z &&
        (Udim u1 &L =? Udim u2 &L)%Z &&
        (Udim u1 &M =? Udim u2 &M)%Z &&
        (Udim u1 &I =? Udim u2 &I)%Z &&
        (Udim u1 &Q =? Udim u2 &Q)%Z &&
        (Udim u1 &N =? Udim u2 &N)%Z &&
        (Udim u1 &J =? Udim u2 &J)%Z = true.
Proof.
  intros. rewrite Udims_eq_iffP.
  rewrite !andb_true_iff. rewrite !Z.eqb_eq. tauto.
Qed.

(** [Udims] of [Unone] is zero *)
Lemma Udims_Unone : forall r : R, Udims (Unone r) = Dzero.
Proof. intros. unfold Udims. simpl. auto. Qed.

(** [Udims] of [Ubu b] is [DmakeByBU b 1] *)
Lemma Udims_Ubu : forall b, Udims (Ubu b) = DmakeByBU b 1.
Proof. unfold Udims. destruct b; simpl; auto. Qed.

(** [Udims] of [Umul] is addition *)
Lemma Udims_Umul : forall u1 u2, Udims (u1 * u2) = Dplus (Udims u1) (Udims u2).
Proof. intros. unfold Udims. simpl. auto. Qed.

(** [Udims] of [Upow u z] equal to multiply of z and [Udims u] *)
Lemma Udims_Upow : forall u z, Udims (u ^ z) = Dcmul z (Udims u).
Proof.
  intros. simpl. unfold Udims.
  repeat f_equal; rewrite Udim_Upow; auto with zarith.
Qed.

(** [Udims] of [Ucons u b z] equal to addition of [Udims u] and [DmakeByBU b z] *)
Lemma Udims_Ucons : forall u b z, Udims (Ucons u b z) = Dplus (Udims u) (DmakeByBU b z).
Proof.
  intros. simpl. unfold Udims.
  destruct b; simpl; simp_Udim; repeat f_equal; auto with zarith.
Qed.


(** * Normalized unit: the semantics of a Unit *)

(* Declare Scope NU_scope.
Delimit Scope NU_scope with NU.
Open Scope NU_scope.
 *)

(** ** Definitions of normalized unit *)

(** A normalized unit is a pair of a coefficient and a dimensions. *) 
Definition Nunit := (R * Dims)%type.
Definition Ncoef (n : Nunit) : R := fst n.
Definition Ndims (n : Nunit) : Dims := snd n.

(* Bind Scope NU_scope with Nunit. *)

(** [Nunit] of no-dimensional *)
Definition Nunitone : Nunit := (1, Dzero).



(** ** Equality of Nunit *)

(** [Nunit] equal, iff, all components equal. *)
Lemma Neq_iff : forall n1 n2 : Nunit,
    (Ncoef n1 = Ncoef n2 /\ Ndims n1 = Ndims n2) <-> n1 = n2.
Proof.
  intros. destruct n1, n2. simpl in *. split; intros.
  - destruct H. subst; auto.
  - inversion H. subst; auto.
Qed.

(** [Nunit] not equal, iff coefficient or dimensions not equal. *)
Lemma Nneq_iff_not : forall n1 n2 : Nunit,
    (Ncoef n1 <> Ncoef n2) \/ (Ndims n1 <> Ndims n2) <-> n1 <> n2.
Proof. intros. rewrite <- Neq_iff. split; tauto. Qed.

(** Boolean equality of [Nunit] *)
Definition Neqb (n1 n2 : Nunit) : bool :=
  (Reqb (Ncoef n1) (Ncoef n2)) && Deqb (Ndims n1) (Ndims n2).

(** [Neqb] = true is reflexive *)
Lemma Neqb_refl n1 : Neqb n1 n1 = true.
Proof. unfold Neqb. rewrite andb_true_iff, Reqb_true_iff, Deqb_true_iff; auto. Qed.

(** [Neqb] is true, iff [eq]. *)
Lemma Neqb_true_iff n1 n2 : (Neqb n1 n2 = true) <-> n1 = n2.
Proof.
  unfold Neqb. rewrite !andb_true_iff.
  rewrite Reqb_true_iff, Deqb_true_iff. rewrite Neq_iff. easy.
Qed.

(** [Neqb] is false, iff not [eq] *)
Lemma Neqb_false_iff n1 n2 : (Neqb n1 n2 = false) <-> (n1 <> n2).
Proof. intros. rewrite <- Neqb_true_iff. split; solve_bool. Qed.

Lemma Neqb_reflect : forall n1 n2, reflect (n1 = n2) (Neqb n1 n2).
Proof.
  intros. destruct (Neqb n1 n2) eqn:E1; constructor.
  apply Neqb_true_iff; auto. apply Neqb_false_iff; auto.
Qed.

Global Hint Resolve Neqb_reflect : bdestruct.

(** [Neqb] is commutative. *)
Lemma Neqb_comm n1 n2 : Neqb n1 n2 = Neqb n2 n1.
Proof. bdestruct (Neqb n1 n2); bdestruct (Neqb n2 n1); auto; congruence. Qed.

(** [Neq] is decidable *)
Lemma Neq_dec (n1 n2 : Nunit) : {n1 = n2} + {n1 <> n2}.
Proof. bdestruct (Neqb n1 n2); auto. Qed.



(** ** Multiplication of [Nunit] *)

Definition Nmult (n1 n2 : Nunit) : Nunit :=
  ((Ncoef n1 * Ncoef n2)%R, Dplus (Ndims n1) (Ndims n2)).

Lemma Nmult_comm (n1 n2 : Nunit) : Nmult n1 n2 = Nmult n2 n1.
Proof.
  destruct n1,n2. unfold Nmult; simpl.
  rewrite Rmult_comm, Dplus_comm; auto.
Qed.

Lemma Nmult_assoc (n1 n2 n3 : Nunit) : 
  Nmult (Nmult n1 n2) n3 = Nmult n1 (Nmult n2 n3).
Proof.
  destruct n1,n2,n3. unfold Nmult; simpl.
  rewrite Rmult_assoc, Dplus_assoc; auto.
Qed.



(** ** Inversion of [Nunit] *)
Definition Ninv (n1 : Nunit) : Nunit := (Rinv (Ncoef n1), Dopp (Ndims n1)).


(** ** Division of [Nunit] *)
Definition Ndiv (n1 n2 : Nunit) : Nunit := Nmult n1 (Ninv n2).


(** ** Integer power of a [Nunit] *)
Definition Npow (n : Nunit) (z : Z) :=
  (powerRZ (Ncoef n) z, Dcmul z (Ndims n)).


(** ** Square root of a [Nunit] *)

(** Square root of a [Nunit] *)
Definition Nsqrt (n1 : Nunit) : Nunit :=
  (sqrt (Ncoef n1), Dsqrt (Ndims n1)).

(** Condition of [Nsqrt]: coef must positive, dim must be even *)
Definition Nsqrt_cond (n1 : Nunit) : Prop := (0 < Ncoef n1) /\ Dsqrt_cond (Ndims n1).


(** ** Conversion between [Unit] and [Nunit]. *)

(** Conversion from [Unit] to [Nunit]. *)
Definition u2n (u : Unit) : Nunit := (Ucoef u, Udims u).

Section test.
  Let m : Unit := &L.
  Let s : Unit := &T.
  Let u1 : Unit := 1 * m * s.
  Let u2 : Unit := s * 1 * m.
  (* Compute u2n u1. *)
  (* Compute u2n u2. *)
  (* Compute Neqb (u2n u1) (u2n u2). *)
End test.

(** [Ncoef] of [u2n u] is the coefficient of the `u` *)
Lemma Ncoef_u2n u : Ncoef (u2n u) = Ucoef u.
Proof. intros. reflexivity. Qed.

(** Dimension of [u2n u] has known form *)
Lemma Udim_u2n : forall u,
    let '(coef, (ds, dm, dkg, dA, dK, dmol, dcd)) := u2n u in
    Udim u BUTime = ds /\
      Udim u BULength = dm /\
      Udim u BUMass = dkg /\
      Udim u BUElectricCurrent = dA /\
      Udim u BUThermodynamicTemperature = dK /\
      Udim u BUAmountOfSubstance = dmol /\
      Udim u BULuminousIntensity = dcd.
Proof. intros. simpl. repeat split; auto. Qed.

(** [u2n] of [Unone]. *)
Lemma u2n_Unone r : u2n (Unone r) = (r, Dzero).
Proof. auto. Qed.

(** u2n of [b]. *)
Lemma u2n_Ubu b : u2n (Ubu b) = (1, DmakeByBU b 1).
Proof. unfold u2n. f_equal. simpl. rewrite Udims_Ubu. auto. Qed.

(** A rewriting of [u2n] [Umul]. *)
Lemma u2n_Umult (u1 u2 : Unit) :
  u2n (u1 * u2) =
    ((Ncoef (u2n u1) * Ncoef (u2n u2))%R,
      Dplus (Ndims (u2n u1)) (Ndims (u2n u2))).
Proof. simpl. reflexivity. Qed.

Lemma u2n_Umult_cancel_l u1 u2 u :
  u2n u1 = u2n u2 -> u2n (u * u1) = u2n (u * u2).
Proof.
  intros. rewrite !u2n_Umult. destruct (u2n u1),(u2n u2),(u2n u).
  rewrite <- Neq_iff in *; simpl in *. destruct H; subst. auto.
Qed.

Lemma u2n_Umult_cancel_r u1 u2 u :
  u2n u1 = u2n u2 -> u2n (u1 * u) = u2n (u2 * u).
Proof.
  intros. rewrite !u2n_Umult. destruct (u2n u1),(u2n u2),(u2n u).
  rewrite <- Neq_iff in *; simpl in *. destruct H; subst. auto.
Qed.

(** [u2n] is compatible for [Umul]. *)
Lemma u2n_Umult_Umult u1 u2 u3 u4 :
  u2n u1 = u2n u2 -> u2n u3 = u2n u4 ->
  u2n (u1 * u3) = u2n (u2 * u4).
Proof.
  intros. rewrite !u2n_Umult.
  destruct (u2n u1), (u2n u2), (u2n u3), (u2n u4).
  inversion H. inversion H0. auto.
Qed.

(** A rewriting of [u2n] [Uinv]. *)
Lemma u2n_Uinv_rw u :
  u2n (/u) = ((/(Ncoef (u2n u)))%R, Dopp (Ndims (u2n u))).
Proof. easy. Qed.

(** [u2n] is compatible for [Uinv]. *)
Lemma u2n_Uinv u1 u2 : u2n u1 = u2n u2 -> u2n (/u1) = u2n (/u2).
Proof.
  intros. rewrite !u2n_Uinv_rw. destruct (u2n u1), (u2n u2). 
  inversion H. simpl in *. auto.
Qed.

(** [u2n] is compatible for [UpowNat]. *)
Lemma u2n_UpowNat u1 u2 n :
  u2n u1 = u2n u2 -> u2n (UpowNat u1 n) = u2n (UpowNat u2 n).
Proof.
  intros. induction n; simpl; auto. destruct n; auto.
  apply u2n_Umult_Umult; auto.
Qed.

(** [Ucoef] of [UpowNat]. *)
Lemma Ucoef_UpowNat u n : Ucoef (UpowNat u n) = pow (Ncoef (u2n u)) n.
Proof.
  intros. induction n; simpl; auto. destruct n.
  - simpl. rewrite <- Ncoef_u2n. simpl. ring.
  - rewrite Ucoef_Umul. rewrite IHn. rewrite <- Ncoef_u2n; simpl. auto.
Qed.

(** [u2n] is compatible for [Upow]. *)
Lemma u2n_Upow u1 u2 z : u2n u1 = u2n u2 -> u2n (u1 ^ z) = u2n (u2 ^ z).
Proof.
  intros. unfold Upow. destruct z; auto.
  - apply u2n_UpowNat. auto.
  - apply u2n_Uinv. apply u2n_UpowNat. auto.
Qed.

(** [Ucoef] of [Upow]. *)
Lemma Ucoef_Upow u z : Ucoef (Upow u z) = powerRZ (Ncoef (u2n u)) z.
Proof.
  intros. unfold Upow. destruct z; auto.
  - apply Ucoef_UpowNat.
  - simpl. f_equal. apply Ucoef_UpowNat.
Qed.

(** A rewriting of [u2n] [Upow]. *)
Lemma u2n_Upow_rw u z :
  u2n (u ^ z) = (powerRZ (Ncoef (u2n u)) z, Dcmul z (Ndims (u2n u))).
Proof.
  intros. apply Neq_iff; simpl. split.
  apply Ucoef_Upow. apply Udims_Upow.
Qed.

(** Conversion from [Nunit] to [Unit]. *)
Definition n2u (n : Nunit) : Unit :=
  let '(coef, (ds, dm, dkg, dA, dK, dmol, dcd)) := n in
  let u := Unone coef in
  let u := Ucons u &T ds in
  let u := Ucons u &L dm in
  let u := Ucons u &M dkg in
  let u := Ucons u &I dA in
  let u := Ucons u &Q dK in
  let u := Ucons u &N dmol in
  let u := Ucons u &J dcd in
  u.

(** [Ucoef] of [n2u n] equal to [Ncoef n] *)
Lemma Ucoef_n2u : forall n, Ucoef (n2u n) = Ncoef n.
Proof.
  intros. destruct n as [c d]. des_dims1 d; simpl. simp_Ucoef. auto.
Qed.

(** Dimension of [n2u n] is the dimension of the n. *)
Lemma Udim_n2u n b : Udim (n2u n) b = DimFromDims (Ndims n) b.
Proof.
  destruct n as [c d]. des_dims1 d. simpl.
  destruct b; simp_Udim; repeat split; lia.
Qed.

(** Dimension of [n2u n] is the dimension of the n (extended version). *)
Lemma Udim_n2u_ext n :
  let '(_, (ds, dm, dkg, dA, dK, dmol, dcd)) := n in
  Udim (n2u n) BUTime = ds /\
    Udim (n2u n) BULength = dm /\
    Udim (n2u n) BUMass = dkg /\
    Udim (n2u n) BUElectricCurrent = dA /\
    Udim (n2u n) BUThermodynamicTemperature = dK /\
    Udim (n2u n) BUAmountOfSubstance = dmol /\
    Udim (n2u n) BULuminousIntensity = dcd.
Proof.
  destruct n as [? d]. des_dims1 d. simpl.
  rewrite ?Udim_Ucons; simpl. repeat split; lia.
Qed.

(** [Udims] of [n2u (c,d)] equal to `d` *)
Lemma Udims_n2u : forall c d, Udims (n2u (c, d)) = d.
Proof. intros. unfold Udims. des_dims1 d. rewrite !Udim_n2u. simpl. auto. Qed.

(** [n2u] is injective about coefficient. *)
Lemma n2u_eq_imply_coef_eq : forall n1 n2,
    n2u n1 = n2u n2 -> Ncoef n1 = Ncoef n2.
Proof. intros. rewrite <- !Ucoef_n2u. rewrite H. auto. Qed.

(** [n2u] is injective about dimensions. *)
Lemma n2u_eq_imply_dims_eq : forall n1 n2,
    n2u n1 = n2u n2 -> Ndims n1 = Ndims n2.
Proof.
  intros. pose proof (Udim_n2u_ext n1). rewrite H in H0.
  destruct n1 as [c1 d1], n2 as [c2 d2]. des_dims2 d1 d2. simpl in *.
  simp_logic. subst. clear. simp_Udim. f_equal.
Qed.

(** [n2u] equal, iff [Nunit] equal. *)
Lemma n2u_eq_iff : forall n1 n2, n2u n1 = n2u n2 <-> n1 = n2.
Proof.
  intros n1 n2. split; intros H.
  - apply Neq_iff. split.
    apply n2u_eq_imply_coef_eq; auto. apply n2u_eq_imply_dims_eq; auto.
  - subst. auto.
Qed.

(** [n2u] not equal, iff [Nunit] not equal. *)
Lemma n2u_neq_iff : forall n1 n2, n2u n1 <> n2u n2 <-> n1 <> n2.
Proof. intros. rewrite <- n2u_eq_iff. easy. Qed.

(** [u2n] o [n2u] is identity *)
Lemma u2n_n2u : forall (n : Nunit), u2n (n2u n) = n.
Proof.
  intros n. unfold u2n, Udims.
  induction n as [c d]. des_dims1 d. simpl.
  simp_Ucoef. simp_Udim. f_equal.
Qed.



(** * Comparison of [Unit]: use corresponding [Nunit] comparison. *)

Open Scope Unit_scope.

(** ** Boolean Equality of [Unit] *)
Definition Ueqb (u1 u2 : Unit) : bool := Neqb (u2n u1) (u2n u2).

Notation "u1 =? u2" := (Ueqb u1 u2) (at level 70) : Unit_scope.

(** [Ndims] of [u2n u] is [Udims u] *)
Lemma Ndims_u2n u : Ndims (u2n u) = Udims u.
Proof.
  destruct (u2n u) as [c d] eqn:H. des_dims1 d. unfold Ndims, Udims.
  pose proof (Udim_u2n u). rewrite H in H0. simp_logic. subst. auto.
Qed.

(** [Ueqb] of [Ucons u1] and [Ucons u2], equal to [Ueqb u1 u2]. *)
Lemma Ueqb_Ucons : forall u1 u2 b dim,
    Ueqb (Ucons u1 b dim) (Ucons u2 b dim) = Ueqb u1 u2.
Proof.
  intros. unfold Ueqb, Neqb. apply andb_eq_inv; auto.
  - simpl. simp_Ucoef. auto.
  - rewrite !Ndims_u2n. rewrite !Udims_Ucons. rewrite Deqb_Dplus_cancel_r. auto.
Qed.

(** [Ueqb] is true, it is reflexive *)
Lemma Ueqb_true_refl (u : Unit) : u =? u = true.
Proof. unfold Ueqb. apply Neqb_refl. Qed.

(** [Ueqb] is commutative. *)
Lemma Ueqb_comm (u1 u2 : Unit) : (u1 =? u2)%U = (u2 =? u1)%U.
Proof.
  unfold Ueqb in *. apply Neqb_comm.
Qed.

(** [Ueqb] is true, iff, equality of [u2n] *)
Lemma Ueqb_true_iff : forall (u1 u2 : Unit), u1 =? u2 = true <-> u2n u1 = u2n u2.
Proof. intros. unfold Ueqb. apply Neqb_true_iff. Qed.

(** [Ueqb] is false, iff, inequality of [u2n] *)
Lemma Ueqb_false_iff : forall (u1 u2 : Unit), u1 =? u2 = false <-> u2n u1 <> u2n u2.
Proof. intros. rewrite <- Ueqb_true_iff. split; solve_bool. Qed.

(* [Ueqb] reflects the equality of [u2n] *)
Lemma Ueqb_reflect : forall u1 u2, reflect (u2n u1 = u2n u2) (u1 =? u2).
Proof.
  intros. destruct (u1 =? u2) eqn:Eu; constructor.
  apply Ueqb_true_iff; auto. apply Ueqb_false_iff; auto.
Qed.


(** ** Proposional euqality of [Unit] *)

(** Two [Unit] is semantical equal *)
Definition Ueq (u1 u2 : Unit) : Prop := u2n u1 = u2n u2.

Infix "==" := (Ueq) (at level 70) : Unit_scope.

(** [Ueq] iff [Ueqb]. *)
Lemma Ueq_iff_Ueqb u1 u2 : (u1 == u2) <-> (u1 =? u2 = true).
Proof.
  unfold Ueq, Ueqb.
  rewrite Neqb_true_iff. reflexivity.
Qed.

(** [Ueq] of [Ucons]. *)
Lemma Ueq_Ucons : forall u1 u2 b dim,
    u1 == u2 -> Ucons u1 b dim == Ucons u2 b dim.
Proof.
  intros. rewrite !Ueq_iff_Ueqb in *.
  rewrite Ueqb_Ucons. auto.
Qed.

(** Equality of two units, iff their coefficients and dimensions all equal. *)
Lemma Ueq_iff_coef_dims_old : forall (u1 u2 : Unit),
    u1 == u2 <-> 
      let (c1,d1) := u2n u1 in
      let (c2,d2) := u2n u2 in
      c1 = c2 /\ d1 = d2.
Proof.
  intros. rewrite Ueq_iff_Ueqb. rewrite Ueqb_true_iff.
  destruct (u2n u1), (u2n u2). split; intros H; inversion H; subst; auto.
Qed.

Lemma Ueq_iff_coef_dims : forall (u1 u2 : Unit),
    let (c1,d1) := (Ncoef (u2n u1), Ndims (u2n u1)) in
    let (c2,d2) := (Ncoef (u2n u2), Ndims (u2n u2)) in
    u1 == u2 <-> c1 = c2 /\ d1 = d2.
Proof. intros. simpl. unfold Ueq. rewrite <- Neq_iff. simpl. easy. Qed.

(** [Ueq] is an equivalence relation. *)
Lemma Ueq_refl : forall (u : Unit), u == u.
Proof. intros. unfold Ueq. reflexivity. Qed.

Lemma Ueq_sym : forall (u1 u2 : Unit), u1 == u2 -> u2 == u1.
Proof.
  intros u1 u2. rewrite !Ueq_iff_Ueqb. rewrite Ueqb_comm. auto.
Qed.

Lemma Ueq_trans : forall (u1 u2 u3 : Unit), u1 == u2 -> u2 == u3 -> u1 == u3.
Proof.
  intros until u3. rewrite !Ueq_iff_Ueqb, !Ueqb_true_iff.
  intros. rewrite H; auto.
Qed.

#[export] Instance Ueq_equiv : Equivalence Ueq.
Proof.
  constructor; hnf; intros; auto.
  apply Ueq_refl. apply Ueq_sym; auto. apply Ueq_trans with y; auto.
Qed.


(** ** Approximate relation of [Unit] *)

(** Check if two units is approximate, propositional version. *)
Definition Unit_approx_old (u1 u2 : Unit) (diff : R) : Prop :=
  let (c1, d1) := u2n u1 in
  let (c2, d2) := u2n u2 in
  (d1 = d2) /\ (Rapprox c1 c2 diff).

Definition Unit_approx (u1 u2 : Unit) (diff : R) : Prop :=
  let (c1,d1) := (Ncoef (u2n u1), Ndims (u2n u1)) in
  let (c2,d2) := (Ncoef (u2n u2), Ndims (u2n u2)) in
  (d1 = d2) /\ (Rapprox c1 c2 diff).

(** Check if two units is approximate, boolean version. *)
Definition Unit_approxb_old (u1 u2 : Unit) (diff : R) : bool :=
  let (c1, d1) := u2n u1 in
  let (c2, d2) := u2n u2 in
  (Deqb d1 d2) && (Rapproxb c1 c2 diff).

Definition Unit_approxb (u1 u2 : Unit) (diff : R) : bool :=
  let (c1,d1) := (Ncoef (u2n u1), Ndims (u2n u1)) in
  let (c2,d2) := (Ncoef (u2n u2), Ndims (u2n u2)) in
  (Deqb d1 d2) && (Rapproxb c1 c2 diff).

Example unit1 : Unit := (1.5e-100 * &L).
Example unit2 : Unit := (1.6e-100 * &L).
Example diff : R := 0.1e-100.
Goal Unit_approxb unit1 unit2 diff = true.
  (*   compute. (* expanded too much *) *)
  lazy [unit1 unit2 diff Unit_approxb].
  lazy [u2n Ucoef Rapproxb Rabs]; simpl.
  lazy [Rleb].
  destruct (Rcase_abs); try lra.
  destruct (Rle_lt_dec); try lra.
Qed.


(** * Normalization of [Unit] *)

(* The idea is inspired by [Qred] in [Qcanon] *)

(** ** Normaliztion of a [Unit] *)

(** Normalize a [Unit] `u` *)
Definition Unorm (u : Unit) : Unit := n2u (u2n u).

Section test.
  Let m := &L.
  Let kg := &M.
  Let s := &T.
  (* Compute Unorm (kg * m * s * 2). *)
  (* Compute Unorm (2 * kg * s * m). *)
  (* Compute Unorm (Unorm (2 * kg * s * m)). *)
End test.

(** Every two [Unit] with same semantics, [Unorm] generate same form. *)
Lemma Unorm_complete : forall (u1 u2 : Unit),
    (u1 =? u2 = true) -> Unorm u1 = Unorm u2.
Proof. intros. unfold Unorm. apply Ueqb_true_iff in H. rewrite H. auto. Qed.

(** Every two [Unit] with same form, have same semantics *)
Lemma Unorm_sound : forall (u1 u2 : Unit),
    Unorm u1 = Unorm u2 -> (u1 =? u2 = true).
Proof.
  intros. unfold Unorm in *. apply n2u_eq_iff in H.
  apply Ueqb_true_iff. auto.
Qed.

(** [Unorm] involution law *)
Lemma Unorm_involutive : forall u : Unit, Unorm (Unorm u) = Unorm u.
Proof. intros. unfold Unorm. rewrite u2n_n2u. auto. Qed.


(** ** Normalized [Unit] *)

(** A unit is normalized *)
Definition Unormalized (u : Unit) : Prop := Unorm u = u.

(** [Unorm] generate a normalized result *)
Lemma Unorm_Unormalized : forall u, Unormalized (Unorm u).
Proof. intros. unfold Unormalized. rewrite Unorm_involutive. auto. Qed.

(** [n2u (1,d)] is normalized *)
Lemma n2u_coef1_Unormalized : forall d, Unormalized (n2u (1, d)).
Proof.
  intros. des_dims1 d. hnf. cbn. simp_Ucoef. simp_Udim. repeat f_equal.
Qed.

