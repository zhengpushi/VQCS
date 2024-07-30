(*
  Copyright 2024 Zhengpu Shi
  This file is part of VQCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Unit, syntax of unit.
  author    : Zhengpu Shi
  date      : 2021.05

  reference : 
  1. SI-Brochure-9-EN.pdf 国际单位制
  2. https://zhuanlan.zhihu.com/p/365196503 量纲分析基本概念 
  
  remark    :
  1. Basic Unit and derived Unit
    There are 7 basic unit. eg., Time, Length, Mass, etc.
    basic unit can be composed to construct derived unit, and the coefficient 
    could be added. eg., 1min=60's, 1N=1kg*m/s².
  2. Comparing Q and R: Which is suitable for data type of Unit coefficient?
    * Q is constructed while R is axiomized, making Q more user-friendly than R.
    * Both Q and R differ from float and double types.
    * Both Q and R can be eliminated using the 'field' tactic.
    * Q requires the use of Qeq instead of eq; R requires the use of R_EM_T.
    * Q cannot represent π (an irrational number).
*)

Require Export Utils.

Open Scope R_scope.

Declare Scope Unit_scope.
Delimit Scope Unit_scope with U.
Open Scope Unit_scope.


(* ######################################################################### *)
(** * BaseUnit, which come from SI *)

(* ======================================================================= *)
(** ** Definition of BaseUnit *)
Inductive BaseUnit : Set :=
| BUTime
| BULength
| BUMass
| BUElectricCurrent
| BUThermodynamicTemperature
| BUAmountOfSubstance
| BULuminousIntensity
(* | BURadian *)
.

Notation "&T" := (BUTime) (at level 0) : Unit_scope.
Notation "&L" := (BULength) (at level 0) : Unit_scope.
Notation "&M" := (BUMass) (at level 0) : Unit_scope.
Notation "&I" := (BUElectricCurrent) (at level 0) : Unit_scope.
Notation "&Q" := (BUThermodynamicTemperature) (at level 0) : Unit_scope.
Notation "&N" := (BUAmountOfSubstance) (at level 0) : Unit_scope.
Notation "&J" := (BULuminousIntensity) (at level 0) : Unit_scope.
(* Notation "&R" := (BURadian) (at level 0). *)


(* ======================================================================= *)
(** ** Conversion between [BaseUnit] and [nat] *)

(** Conversion from [BaseUnit] to [Nat] *)
Definition bu2nat (b : BaseUnit) : nat :=
  match b with
  | &T => 0 | &L => 1 | &M => 2 | &I => 3 | &Q => 4 | &N => 5 | &J => 6
  end.

(** Conversion from [nat] to [BaseUnit] *)
Definition nat2bu (n : nat) : option BaseUnit :=
  (match n with
  | 0 => Some &T | 1 => Some &L | 2 => Some &M | 3 => Some &I | 4 => Some &Q
  | 5 => Some &N | 6 => Some &J | _ => None
  end)%nat.

(** The valid condition of [nat2bu] *)
Definition nat2bu_validCond (n : nat) : Prop := (n < 7)%nat.

(** if the given [n] is valid, then nat2bu have valid value  *)
Lemma nat2bu_Some : forall n : nat,
    nat2bu_validCond n -> exists b : BaseUnit, nat2bu n = Some b.
Proof.
  intros. unfold nat2bu_validCond in H.
  do 7 (destruct n; [eexists; reflexivity|]). lia.
Qed.

(** if the given [n] is invalid, then nat2bu have invalid value  *)
Lemma nat2bu_None : forall n : nat,
    ~(nat2bu_validCond n) -> nat2bu n = None.
Proof.
  intros. unfold nat2bu_validCond in H.
  do 7 (destruct n; [lia|]). auto.
Qed.

(** Inversion of [nat2bu] *)
Lemma nat2bu_inv : forall n b, nat2bu n = Some b -> n = bu2nat b.
Proof.
  intros.
  do 7 (destruct n; [simpl in H; inversion H; subst; simpl; auto|]).
  simpl in H. easy.
Qed.

(** [bu2nat] o [nat2bu] is identity *)
Lemma bu2nat_nat2bu_id : forall n : nat,
    nat2bu_validCond n -> exists b : BaseUnit, nat2bu n = Some b /\ bu2nat b = n.
Proof.
  intros. pose proof (nat2bu_Some n H).
  destruct H0. exists x. split; auto.
  apply nat2bu_inv in H0. auto.
Qed.

(** [nat2bu] o [bu2nat] is identity *)
Lemma nat2bu_bu2nat_id : forall b : BaseUnit, nat2bu (bu2nat b) = Some b.
Proof. intros. destruct b; simpl; auto. Qed.


(* ======================================================================= *)
(** ** Equality of BaseUnit *)

(** Generate some simple functions and propertie:
<<
    BaseUnit_beq : BaseUnit -> BaseUnit -> bool
    BaseUnit_eq_dec : forall x y : BaseUnit, {x = y} + {x <> y}
>>
 *)
Scheme Equality for BaseUnit.

(** A short name for boolean equality of [BasicUnit] *)
Definition bueqb := BaseUnit_beq.

(** bueqb is true，iff b1 = b2. *)
Lemma bueqb_true_iff : forall b1 b2, bueqb b1 b2 = true <-> b1 = b2.
Proof.
  intros. split; intros.
  - destruct b1,b2; simpl in *; easy.
  - destruct b1,b2; simpl in *; easy.
Qed.

(** bueqb is false, iff b1 <> b2. *)
Lemma bueqb_false_iff : forall b1 b2, bueqb b1 b2 = false <-> b1 <> b2.
Proof.
  intros. rewrite <- bueqb_true_iff.
  destruct (bueqb b1 b2); split; intros; easy.
Qed.

(** [bueqb] reflect equality of BaseUnit *)
Lemma bueqb_reflect : forall b1 b2 : BaseUnit, reflect (b1 = b2) (bueqb b1 b2).
Proof.
  intros. destruct (bueqb b1 b2) eqn:E1; constructor.
  apply bueqb_true_iff; auto. apply bueqb_false_iff; auto.
Qed.
  
#[export] Hint Resolve bueqb_reflect : bdestruct.

(** [bueqb] = true is reflexive. *)
Lemma bueqb_refl b : bueqb b b = true.
Proof. apply bueqb_true_iff. auto. Qed.


(* ######################################################################### *)
(** * Unit: syntax representation of a unit *)

(* ======================================================================= *)
(** ** Definition of Unit *)

(** Unit is an AST that can represent any unit. *)
Inductive Unit : Set :=
| Unone (coef : R) :> Unit        (* a unit with no dimension. eg: a number *)
| Ubu (bu : BaseUnit) :> Unit     (* a unit with single dimension. eg: m *)
| Uinv (u : Unit)         (* inversion of a unit. eg: Hz = /s *)
| Umul (u1 u2 : Unit).    (* multiplication of two units. eg: m*s *)

(** Notation for constructor of unit *)
Notation "u1 * u2" := (Umul u1 u2) : Unit_scope.
Notation " / u" := (Uinv u) : Unit_scope.
Notation "u1 / u2" := (u1 * (/ u2)) : Unit_scope.


(* ======================================================================= *)
(** ** Properties for [Unit] *)

(** [Umul] is injective *)
Lemma umul_inj : forall u1 u2 u3 u4, u1 * u2 = u3 * u4 -> u1 = u3 /\ u2 = u4.
Proof. intros. inversion H; auto. Qed.

(** u * u1 = u * u2 -> u1 = u2 *)
Lemma umul_cancel_l : forall u1 u2 u, u * u1 = u * u2 -> u1 = u2.
Proof. intros. inversion H; auto. Qed.

(** u1 * u = u2 * u -> u1 = u2 *)
Lemma umul_cancel_r : forall u1 u2 u, u1 * u = u2 * u -> u1 = u2.
Proof. intros. inversion H; auto. Qed.

(** u1 <> u1 * u2 *)
Lemma umul_eq_contro_l : forall u1 u2, u1 <> u1 * u2.
Proof. induction u1; intros; intro H; inv H. apply IHu1_1 in H1. auto. Qed.

(** u1 <> u2 * u1 *)
Lemma umul_eq_contro_r : forall u1 u2, u1 <> u2 * u1.
Proof. induction u1; intros; intro H; inv H. apply IHu1_2 in H2. auto. Qed.


(* ======================================================================= *)
(** Power of a unit *)

(** Natual number power of a unit *)
Fixpoint upowNat (u : Unit) (n : nat) : Unit :=
  match n with
  | O => Unone 1
  | S 0 => u
  | S n' => Umul u (upowNat u n')
  end.

(** Integer number power of a unit  *)
Definition upow (u : Unit) (z : Z) : Unit :=
  match z with
  | Z0 => Unone 1
  | Zpos p => upowNat u (Pos.to_nat p)
  | Zneg p => Uinv (upowNat u (Pos.to_nat p))
  end.

Notation "a ^ z" := (upow a z) : Unit_scope.
Notation "a ²" := (a ^ 2) : Unit_scope.
Notation "a ³" := (a ^ 3) : Unit_scope.
Notation "a ⁴" := (a ^ 4) : Unit_scope.
Notation "a ⁵" := (a ^ 5) : Unit_scope.
Notation "a ⁶" := (a ^ 6) : Unit_scope.

Section test.
  Let m := &L.
  Let m3 := m ^ 3.
  Let kg := &M.
  Let s := &T.
  Let hour := 3600 * s.
  Let km := 1000 * m.
  Let N := 2 * (kg * m) / (s * s).
  Let N' := (2 * kg / s) * (m / s).

  (* Compute m3. *)
  (* Compute N. *)

  (** Considering that how to make sure N == N'? *)
  Goal N = N'.
  Proof.
    cbv.
    (* we need semantics equal, not syntax equal *)
  Abort.
End test.


(* ======================================================================= *)
(** ** Coefficient of a Unit *)

(** Get coefficient of a Unit *)
Fixpoint ucoef (u : Unit) : R :=
  match u with
  | Unone c => c
  | Ubu bu => 1
  | Uinv u1 => Rinv (ucoef u1)
  | Umul u1 u2 => Rmult (ucoef u1) (ucoef u2)
  end.

Section test.
  Let rpm := 2 * PI / (60 * &T).
  
  Goal ucoef rpm = (PI/30)%R.
  Proof. cbv. field. Qed.
End test.

(** [ucoef] of [Unone] equal to its value *)
Lemma ucoef_Unone : forall r, ucoef (Unone r) = r.
Proof. intros. simpl. reflexivity. Qed.

(** [ucoef] of [Ubu] equal to 1 *)
Lemma ucoef_Ubu : forall b, ucoef (Ubu b) = 1.
Proof. intros. simpl. reflexivity. Qed.

(** [ucoef] of [Uinv] equal to [Rinv] *)
Lemma ucoef_Uinv : forall u, ucoef (/ u) = (/ ucoef u)%R.
Proof. intros. simpl. reflexivity. Qed.

(** [ucoef] of [Umul] equal to [Rmult] *)
Lemma ucoef_Umul : forall u1 u2, ucoef (u1 * u2) = (ucoef u1 * ucoef u2)%R.
Proof. intros. simpl. reflexivity. Qed.


(* ======================================================================= *)
(** ** Dimension of a unit *)

(** Get dimension of a unit with given base unit *)
Fixpoint udim (u : Unit) (b : BaseUnit) : Z :=
  match u with
  | Unone c => 0
  | Ubu bu => if bueqb bu b then 1 else 0
  | Uinv u1 => Z.opp (udim u1 b)
  | Umul u1 u2 => Z.add (udim u1 b) (udim u2 b)
  end.

Section test.
  Let m := &L.
  Let kg := &M.
  Let s := &T.
  Let ex1 : Unit := 100 * kg * m / (s * s).
  
  Goal udim ex1 &T = (-2)%Z.
  Proof. reflexivity. Qed.
End test.

(** [udim] of [Unone] equal 0. *)
Lemma udim_Unone : forall r b, udim (Unone r) b = 0%Z.
Proof. intros; simpl; auto. Qed.

(** [udim] of [Ubu] with same key equal 1. *)
Lemma udim_Ubu_same : forall b : BaseUnit, udim b b = Z.of_nat 1.
Proof. intros; simpl. rewrite bueqb_refl; auto. Qed.

(** [udim] of [Ubu] with different key equal 0. *)
Lemma udim_Ubu_diff : forall b b' : BaseUnit, b <> b' -> udim b b' = 0%Z.
Proof. intros; simpl. apply bueqb_false_iff in H. rewrite H; auto. Qed.

(** [udim] of [Uinv] equal to [Z.opp]. *)
Lemma udim_Uinv : forall u b, udim (/u) b = Z.opp (udim u b).
Proof. intros; simpl. auto. Qed.

(** [udim] of [Umul] equal to [Z.plus]. *)
Lemma udim_Umul : forall u1 u2 b, udim (u1 * u2) b = Z.add (udim u1 b) (udim u2 b).
Proof. intros; simpl. auto. Qed.

(** [udim] of [upowNat] equal to [nat.mult]. *)
Lemma udim_upowNat : forall u bu n,
    udim (upowNat u n) bu = (Z.of_nat n * (udim u bu))%Z.
Proof.
  intros. induction n; simpl; auto. destruct n; simpl in *.
  - destruct (udim u bu); auto.
  - rewrite IHn. destruct (udim u bu); auto; lia.
Qed.

(** [udim] of [upow] equal to Z.mult. *)
Lemma udim_upow : forall u bu z,  udim (u ^ z) bu = ((udim u bu) * z)%Z.
Proof.
  intros. unfold upow. destruct z; simpl; try rewrite udim_upowNat; lia.
Qed.


(* ======================================================================= *)
(** ** Generate a unit by power of a base unit *)

(** Generate a unit by natural number power of a base unit *)
Fixpoint ugenByBUNat (b : BaseUnit) (n : nat) : Unit :=
  match n with
  | O => 1
  | S O => b
  | S n' => (ugenByBUNat b n') * b
  end.

Section test.
  (* Compute ugenByBUNat &T 0. *)
  (* Compute ugenByBUNat &T 1. *)
  (* Compute ugenByBUNat &T 3. *)
End test.

(** [ugenByBUNat] is injective for exponent *)
Lemma ugenByBUNat_inj_exp : forall n1 n2 b,
    ugenByBUNat b n1 = ugenByBUNat b n2 -> n1 = n2.
Proof.
  induction n1, n2; intros; simpl in *; auto.
  destruct n2; easy. destruct n1; easy.
  destruct n1, n2; auto. easy. easy.
  apply umul_cancel_r in H. apply IHn1 in H. lia.
Qed.

(** [ugenByBUNat] is injective for [BaseUnit] *)
Lemma ugenByBUNat_inj_BU : forall n b1 b2,
    (n > 0)%nat -> ugenByBUNat b1 n = ugenByBUNat b2 n -> b1 = b2.
Proof.
  destruct n; intros; simpl in *. lia. destruct n.
  - inversion H0. auto.
  - apply umul_inj in H0. destruct H0. inversion H1; auto.
Qed.

(** [ugenByBUNat b (Pos.to_nat p)] cannot be Uone *)
Lemma ugenByBUNat_PosToNat_eq_Unone_contro : forall b p n,
    ugenByBUNat b (Pos.to_nat p) <> Unone n.
Proof.
  intros. destruct (Pos.to_nat p) eqn:Ep; auto; auto with zarith.
  intro. simpl in H. destruct n0; easy.
Qed.

(** [ugenByBUNat b (Pos.to_nat p)] cannot be Uinv *)
Lemma ugenByBUNat_PosToNat_eq_Uinv_contro : forall b p u,
    ugenByBUNat b (Pos.to_nat p) <> / u.
Proof.
  intros. destruct (Pos.to_nat p) eqn:Ep; auto; auto with zarith.
  intro. simpl in H. destruct n; easy.
Qed.

(** [ucoef] of [ugenByBUNat] equal to 1. *)
Lemma ucoef_ugenByBUNat : forall (b : BaseUnit) (n : nat),
    ucoef (ugenByBUNat b n) = 1.
Proof.
  intros. induction n; simpl; auto. destruct n; auto.
  rewrite ucoef_Umul. rewrite IHn. rewrite ucoef_Ubu. ring.
Qed.

(** [udim b] of [ugenByBUNat b n] equal to n *) 
Lemma udim_ugenByBUNat_same : forall (b : BaseUnit) (n : nat),
    udim (ugenByBUNat b n) b = Z.of_nat n.
Proof.
  intros. induction n; simpl; auto. destruct n.
  - rewrite udim_Ubu_same. lia.
  - rewrite udim_Umul. rewrite IHn. rewrite udim_Ubu_same. lia.
Qed.

(** [udim b'] of [ugenByBUNat b n] equal to 0 *) 
Lemma udim_ugenByBUNat_diff : forall (b1 b2 : BaseUnit) (n : nat),
    b1 <> b2 -> udim (ugenByBUNat b1 n) b2 = 0%Z.
Proof.
  intros. induction n; simpl; auto. destruct n.
  - apply udim_Ubu_diff; auto.
  - rewrite udim_Umul. rewrite IHn. rewrite udim_Ubu_diff; auto.
Qed.

(** Generate a unit by integer number power of a base unit *)
Definition ugenByBU (b : BaseUnit) (z : Z) : Unit :=
  match z with
  | Z0 => 1
  | Zpos p => ugenByBUNat b (Pos.to_nat p)
  | Zneg p => / (ugenByBUNat b (Pos.to_nat p))
  end.

Section test.
  (* Compute ugenByBU &T 2. *)
  (* Compute ugenByBU &T 1. *)
  (* Compute ugenByBU &T 0. *)
  (* Compute ugenByBU &T (-1). *)
  (* Compute ugenByBU &T (-2). *)
End test.

(** [ugenByBU] is injective for exponent *)
Lemma ugenByBU_inj_exp : forall b z1 z2,
    ugenByBU b z1 = ugenByBU b z2 -> z1 = z2.
Proof.
  intros. unfold ugenByBU in H. destruct z1,z2; try easy.
  - symmetry in H. apply ugenByBUNat_PosToNat_eq_Unone_contro in H; easy.
  - apply ugenByBUNat_PosToNat_eq_Unone_contro in H; easy.
  - apply ugenByBUNat_inj_exp in H. lia.
  - apply ugenByBUNat_PosToNat_eq_Uinv_contro in H; easy.
  - symmetry in H. apply ugenByBUNat_PosToNat_eq_Uinv_contro in H; easy.
  - inversion H. apply ugenByBUNat_inj_exp in H1. lia.
Qed.

(** [ugenByBU] is injective for [BaseUnit] *)
Lemma ugenByBU_inj_BU : forall b1 b2 z,
    (z <> 0)%Z -> ugenByBU b1 z = ugenByBU b2 z -> b1 = b2.
Proof.
  intros. unfold ugenByBU in H0. destruct z; try easy.
  - apply ugenByBUNat_inj_BU in H0; auto. lia.
  - inversion H0. apply ugenByBUNat_inj_BU in H2; auto. lia.
Qed.


(** [ucoef] of [ugenByBU b z] equal to `1`. *)
Lemma ucoef_ugenByBU : forall b z, ucoef (ugenByBU b z) = 1.
Proof.
  intros. destruct z; simpl; auto.
  - rewrite ucoef_ugenByBUNat. auto.
  - rewrite ucoef_ugenByBUNat. field.
Qed.

(** [udim b] of [ugenByBU b z] equal to `z`. *)
Lemma udim_ugenByBU_same : forall b z, udim (ugenByBU b z) b = z.
Proof.
  intros. destruct z; simpl; auto.
  - rewrite udim_ugenByBUNat_same. lia.
  - rewrite udim_ugenByBUNat_same. lia.
Qed.

(** [udim b'] of [ugenByBU b z] equal to `0`. *)
Lemma udim_ugenByBU_diff : forall b b' z, b <> b' -> udim (ugenByBU b z) b' = 0%Z.
Proof.
  intros. destruct z; simpl; auto.
  - rewrite udim_ugenByBUNat_diff; auto.
  - rewrite udim_ugenByBUNat_diff; auto.
Qed.


(* ======================================================================= *)
(** ** Generate a unit with a given unit and [ugenByBU] *)

(** Generate a unit by multiply [ugenByBU b z] and a given unit `u` *)
Definition ucons (u : Unit) (b : BaseUnit) (z : Z) : Unit :=
  if (z =? 0)%Z 
  then u
  else (ugenByBU b z) * u.

(** [ucons] is injective for exponent *)
Lemma ucons_inj_exp : forall u b z1 z2, ucons u b z1 = ucons u b z2 -> z1 = z2.
Proof.
  intros. unfold ucons in H.
  bdestruct (z1 =? 0)%Z; bdestruct (z2 =? 0)%Z; subst; auto.
  - apply umul_eq_contro_r in H; easy.
  - symmetry in H. apply umul_eq_contro_r in H; easy.
  - apply umul_cancel_r in H. apply ugenByBU_inj_exp in H; auto.
Qed.

(** [ucons] is injective for exponent (extend version) *)
Lemma ucons_inj_exp_ext : forall u1 u2 b z1 z2,
    u1 = u2 -> ucons u1 b z1 = ucons u2 b z2 -> z1 = z2.
Proof. intros. subst. apply ucons_inj_exp in H0; auto. Qed.

(** [ucons] is injective for [BaseUnit] *)
Lemma ucons_inj_BU : forall u b1 b2 z,
    (z <> 0)%Z -> ucons u b1 z = ucons u b2 z -> b1 = b2.
Proof.
  intros. unfold ucons in H0.
  bdestruct (z =? 0)%Z; subst; auto. lia.
  apply umul_cancel_r in H0. apply ugenByBU_inj_BU in H0; auto.
Qed.

(** [ucons] is injective for initial [Unit] *)
Lemma ucons_inj_Unit : forall u1 u2 b z,
    ucons u1 b z = ucons u2 b z -> u1 = u2.
Proof.
  intros. unfold ucons in H.
  bdestruct (z =? 0)%Z; subst; auto.
  apply umul_cancel_l in H. auto.
Qed.

(* (** [ucons] is injective for both initial [Unit] and exponent *) *)
(* Lemma ucons_inj_Unit_exp : forall u1 u2 b z1 z2, *)
(*     ucons u1 b z1 = ucons u2 b z2 -> u1 = u2 /\ z1 = z2. *)
(* Proof. *)
(*   intros. unfold ucons in H. *)
(*   bdestruct (z1 =? 0)%Z; bdestruct (z2 =? 0)%Z; auto. *)
(*   - subst. auto. *)
(*   - apply umul_eq_contro_r in H; easy. *)
(*   - symmetry in H. apply umul_eq_contro_r in H; easy. *)
(*   - apply umul_cancel_r in H. apply ugenByBU_inj_exp in H; auto. *)
(* Qed. *)

  
(** [ucoef] of [ucons u b z] equal to [ucoef u] *)
Lemma ucoef_ucons : forall u b z, ucoef (ucons u b z) = ucoef u.
Proof.
  intros. unfold ucons. destruct (z =? 0)%Z; simpl; auto.
  rewrite ucoef_ugenByBU. ring.
Qed.

(** [udim b] of [ucons u b z] equal to [udim u b] + z *)
Lemma udim_ucons_same : forall u b z, udim (ucons u b z) b = ((udim u b) + z)%Z.
Proof.
  intros. unfold ucons. destruct (z =? 0)%Z eqn:En.
  - apply Z.eqb_eq in En. lia.
  - rewrite udim_Umul. rewrite udim_ugenByBU_same. lia.
Qed.
  
(** [udim b'] of [ucons u b z] equal to [udim u b'] *)
Lemma udim_ucons_diff : forall u b b' z, b <> b' -> udim (ucons u b z) b' = (udim u b').
Proof.
  intros. unfold ucons. destruct (z =? 0)%Z eqn:En; auto.
  rewrite udim_Umul. rewrite udim_ugenByBU_diff; auto.
Qed.

(** A rewriting for [udim] of [ucons]. *)
Lemma udim_ucons : forall (u : Unit) (b1 b2 : BaseUnit) (z : Z),
  udim (ucons u b1 z) b2 = ((udim u b2) + (if (bueqb b1 b2) then z else 0))%Z.
Proof.
  intros. bdestruct (bueqb b1 b2).
  - subst. apply udim_ucons_same.
  - rewrite udim_ucons_diff; auto. ring.
Qed.


(** simplify the [ucoef] expression *)
Ltac simp_ucoef :=
  repeat
      match goal with
      (* ucoef (ucons u b z) = ucoef u *)
      | |- context [ucoef (ucons ?u ?b ?z)] => rewrite ucoef_ucons
      (* ucoef (Unone r) = r *)
      | |- context [ucoef (Unone ?r)] => rewrite ucoef_Unone
      end.

(** simplify the [udim] expression *)
Ltac simp_udim :=
  repeat
    match goal with
    (* udim (ucons u b z) b = udim u b + z *)
    | |- context [udim (ucons ?u ?b ?z) ?b] => rewrite udim_ucons_same
    (* udim (ucons u b z) b' = udim u b' *)
    | |- context [udim (ucons ?u ?b ?z) ?b'] => try rewrite udim_ucons_diff;[|easy]
    (* udim (Uone r) b = 0 *)
    | |- context [udim (Unone _) ?b] => rewrite udim_Unone
    (* udim (Ubu b) b = 1 *)
    | |- context [udim (Ubu ?b) ?b] => rewrite udim_Ubu_same
    (* udim (Ubu b) b' = 0 *)
    | |- context [udim (Ubu ?b) ?b'] => try rewrite udim_Ubu_diff;[|easy]
    end.
