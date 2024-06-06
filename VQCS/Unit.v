(*
  Copyright 2024 ZhengPu Shi
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

From FinMatrix Require Export BoolExt ZExt RExt.

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
| BURadian.

Notation "&T" := (BUTime) (at level 0).
Notation "&L" := (BULength) (at level 0).
Notation "&M" := (BUMass) (at level 0).
Notation "&I" := (BUElectricCurrent) (at level 0).
Notation "&Q" := (BUThermodynamicTemperature) (at level 0).
Notation "&N" := (BUAmountOfSubstance) (at level 0).
Notation "&J" := (BULuminousIntensity) (at level 0).  
Notation "&R" := (BURadian) (at level 0).


(* ======================================================================= *)
(** ** Conversion between [BaseUnit] and [nat] *)
(*
(** Conversion from [BaseUnit] to [Nat] *)
Definition BU2nat (b : BaseUnit) : nat :=
  match b with
  | &T => 0
  | &L => 1
  | &M => 2
  | &I => 3
  | &Q => 4
  | &N => 5
  | &J => 6
  end.

(** Conversion from [nat] to [BaseUnit] *)
Definition nat2BU (n : nat) : option BaseUnit :=
  (match n with
   | 0 => Some &T
   | 1 => Some &L
   | 2 => Some &M
   | 3 => Some &I
   | 4 => Some &Q
   | 5 => Some &N
   | 6 => Some &J
   | _ => None
   end)%nat.

(** The valid condition of [nat2BU] *)
Definition nat2BU_validCond (n : nat) : Prop := (n < 7)%nat.

(** if the given [n] is valid, then nat2BU have valid value  *)
Lemma nat2BU_Some : forall n : nat,
    nat2BU_validCond n -> exists b : BaseUnit, nat2BU n = Some b.
Proof.
  intros. unfold nat2BU_validCond in H.
  do 7 (destruct n; [eexists; reflexivity|]). lia.
Qed.

(** if the given [n] is invalid, then nat2BU have invalid value  *)
Lemma nat2BU_None : forall n : nat,
    ~(nat2BU_validCond n) -> nat2BU n = None.
Proof.
  intros. unfold nat2BU_validCond in H.
  do 7 (destruct n; [lia|]). auto.
Qed.

(** Inversion of [nat2BU] *)
Lemma nat2BU_inv : forall n b, nat2BU n = Some b -> n = BU2nat b.
Proof.
  intros.
  do 7 (destruct n; [simpl in H; inversion H; subst; simpl; auto|]).
  simpl in H. easy.
Qed.

(** [BU2nat] o [nat2BU] is identity *)
Lemma BU2nat_nat2BU_id : forall n : nat,
    nat2BU_validCond n -> exists b : BaseUnit, nat2BU n = Some b /\ BU2nat b = n.
Proof.
  intros. pose proof (nat2BU_Some n H).
  destruct H0. exists x. split; auto.
  apply nat2BU_inv in H0. auto.
Qed.

(** [nat2BU] o [BU2nat] is identity *)
Lemma nat2BU_BU2nat_id : forall b : BaseUnit, nat2BU (BU2nat b) = Some b.
Proof. intros. destruct b; simpl; auto. Qed.
 *)


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
Definition BUeqb := BaseUnit_beq.

(** BUeqb is true，iff b1 = b2. *)
Lemma BUeqb_true_iff : forall b1 b2, BUeqb b1 b2 = true <-> b1 = b2.
Proof.
  intros. split; intros.
  - destruct b1,b2; simpl in *; easy.
  - destruct b1,b2; simpl in *; easy.
Qed.

(** BUeqb is false, iff b1 <> b2. *)
Lemma BUeqb_false_iff : forall b1 b2, BUeqb b1 b2 = false <-> b1 <> b2.
Proof.
  intros. rewrite <- BUeqb_true_iff.
  destruct (BUeqb b1 b2); split; intros; easy.
Qed.

(** [BUeqb] reflect equality of BaseUnit *)
Lemma BUeqb_reflect : forall b1 b2 : BaseUnit, reflect (b1 = b2) (BUeqb b1 b2).
Proof.
  intros. destruct (BUeqb b1 b2) eqn:E1; constructor.
  apply BUeqb_true_iff; auto. apply BUeqb_false_iff; auto.
Qed.
  
#[export] Hint Resolve BUeqb_reflect : bdestruct.

(** [BUeqb] = true is reflexive. *)
Lemma BUeqb_refl b : BUeqb b b = true.
Proof. apply BUeqb_true_iff. auto. Qed.


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
Lemma Umul_inj : forall u1 u2 u3 u4, u1 * u2 = u3 * u4 -> u1 = u3 /\ u2 = u4.
Proof. intros. inversion H; auto. Qed.

(** u * u1 = u * u2 -> u1 = u2 *)
Lemma Umul_cancel_l : forall u1 u2 u, u * u1 = u * u2 -> u1 = u2.
Proof. intros. inversion H; auto. Qed.

(** u1 * u = u2 * u -> u1 = u2 *)
Lemma Umul_cancel_r : forall u1 u2 u, u1 * u = u2 * u -> u1 = u2.
Proof. intros. inversion H; auto. Qed.

(** u1 <> u1 * u2 *)
Lemma Umul_eq_contro_l : forall u1 u2, u1 <> u1 * u2.
Proof.
  induction u1; intros; intro H; inversion H. apply IHu1_1 in H1. auto.
Qed.

(** u1 <> u2 * u1 *)
Lemma Umul_eq_contro_r : forall u1 u2, u1 <> u2 * u1.
Proof.
  induction u1; intros; intro H; inversion H. apply IHu1_2 in H2. auto.
Qed.


(* ======================================================================= *)
(** Power of a unit *)

(** Natual number power of a unit *)
Fixpoint UpowNat (u : Unit) (n : nat) : Unit :=
  match n with
  | O => Unone 1
  | S 0 => u
  | S n' => Umul u (UpowNat u n')
  end.

(** Integer number power of a unit  *)
Definition Upow (u : Unit) (z : Z) : Unit :=
  match z with
  | Z0 => Unone 1
  | Zpos p => UpowNat u (Pos.to_nat p)
  | Zneg p => Uinv (UpowNat u (Pos.to_nat p))
  end.

Notation "a ^ z" := (Upow a z) (at level 30, right associativity) :Unit_scope.
Notation "a ²" := (a ^ 2) (at level 1, format "a ²") : Unit_scope.
Notation "a ³" := (a ^ 3) (at level 1, format "a ³") : Unit_scope.
Notation "a ⁴" := (a ^ 4) (at level 1, format "a ⁴") : Unit_scope.
Notation "a ⁵" := (a ^ 5) (at level 1, format "a ⁵") : Unit_scope.

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
Fixpoint Ucoef (u : Unit) : R :=
  match u with
  | Unone c => c
  | Ubu bu => 1
  | Uinv u1 => Rinv (Ucoef u1)
  | Umul u1 u2 => Rmult (Ucoef u1) (Ucoef u2)
  end.

Section test.
  Let rpm := 2 * PI / (60 * &T).
  
  Goal Ucoef rpm = (PI/30)%R.
  Proof. cbv. field. Qed.
End test.

(** [Ucoef] of [Unone] equal to its value *)
Lemma Ucoef_Unone : forall r, Ucoef (Unone r) = r.
Proof. intros. simpl. reflexivity. Qed.

(** [Ucoef] of [Ubu] equal to 1 *)
Lemma Ucoef_Ubu : forall b, Ucoef (Ubu b) = 1.
Proof. intros. simpl. reflexivity. Qed.

(** [Ucoef] of [Uinv] equal to [Rinv] *)
Lemma Ucoef_Uinv : forall u, Ucoef (/ u) = Rinv (Ucoef u).
Proof. intros. simpl. reflexivity. Qed.

(** [Ucoef] of [Umul] equal to [Rmult] *)
Lemma Ucoef_Umul : forall u1 u2, Ucoef (u1 * u2) = Rmult (Ucoef u1) (Ucoef u2).
Proof. intros. simpl. reflexivity. Qed.


(* ======================================================================= *)
(** ** Dimension of a unit *)

(** Get dimension of a unit with given base unit *)
Fixpoint Udim (u : Unit) (b : BaseUnit) : Z :=
  match u with
  | Unone c => 0
  | Ubu bu => if BUeqb bu b then 1 else 0
  | Uinv u1 => Z.opp (Udim u1 b)
  | Umul u1 u2 => Z.add (Udim u1 b) (Udim u2 b)
  end.

Section test.
  Let m := &L.
  Let kg := &M.
  Let s := &T.
  Let ex1 : Unit := 100 * kg * m / (s*s).
  
  Goal Udim ex1 &T = (-2)%Z. Proof. reflexivity. Qed.
End test.

(** [Udim] of [Unone] equal 0. *)
Lemma Udim_Unone : forall r b, Udim (Unone r) b = 0%Z.
Proof. intros; simpl; auto. Qed.

(** [Udim] of [Ubu] with same key equal 1. *)
Lemma Udim_Ubu_same : forall b : BaseUnit, Udim b b = Z.of_nat 1.
Proof. intros; simpl. rewrite BUeqb_refl; auto. Qed.

(** [Udim] of [Ubu] with different key equal 0. *)
Lemma Udim_Ubu_diff : forall b b' : BaseUnit, b <> b' -> Udim b b' = 0%Z.
Proof. intros; simpl. apply BUeqb_false_iff in H. rewrite H; auto. Qed.

(** [Udim] of [Uinv] equal to [Z.opp]. *)
Lemma Udim_Uinv : forall u b, Udim (/u) b = Z.opp (Udim u b).
Proof. intros; simpl. auto. Qed.

(** [Udim] of [Umul] equal to [Z.plus]. *)
Lemma Udim_Umul : forall u1 u2 b, Udim (u1 * u2) b = Z.add (Udim u1 b) (Udim u2 b).
Proof. intros; simpl. auto. Qed.

(** [Udim] of [UpowNat] equal to [nat.mult]. *)
Lemma Udim_UpowNat : forall u bu n,
    Udim (UpowNat u n) bu = (Z.of_nat n * (Udim u bu))%Z.
Proof.
  intros. induction n; simpl; auto. destruct n; simpl in *.
  - destruct (Udim u bu); auto.
  - rewrite IHn. destruct (Udim u bu); auto; lia.
Qed.

(** [Udim] of [Upow] equal to Z.mult. *)
Lemma Udim_Upow : forall u bu z,  Udim (u ^ z) bu = ((Udim u bu) * z)%Z.
Proof.
  intros. unfold Upow. destruct z; simpl; try rewrite Udim_UpowNat; lia.
Qed.


(* ======================================================================= *)
(** ** Generate a unit by power of a base unit *)

(** Generate a unit by natural number power of a base unit *)
Fixpoint UgenByBUNat (b : BaseUnit) (n : nat) : Unit :=
  match n with
  | O => 1
  | S O => b
  | S n' => (UgenByBUNat b n') * b
  end.

Section test.
  (* Compute UgenByBUNat &T 0. *)
  (* Compute UgenByBUNat &T 1. *)
  (* Compute UgenByBUNat &T 3. *)
End test.

(** [UgenByBUNat] is injective for exponent *)
Lemma UgenByBUNat_inj_exp : forall n1 n2 b,
    UgenByBUNat b n1 = UgenByBUNat b n2 -> n1 = n2.
Proof.
  induction n1, n2; intros; simpl in *; auto.
  destruct n2; easy. destruct n1; easy.
  destruct n1, n2; auto. easy. easy.
  apply Umul_cancel_r in H. apply IHn1 in H. lia.
Qed.

(** [UgenByBUNat] is injective for [BaseUnit] *)
Lemma UgenByBUNat_inj_BU : forall n b1 b2,
    (n > 0)%nat -> UgenByBUNat b1 n = UgenByBUNat b2 n -> b1 = b2.
Proof.
  destruct n; intros; simpl in *. lia. destruct n.
  - inversion H0. auto.
  - apply Umul_inj in H0. destruct H0. inversion H1; auto.
Qed.

(** [UgenByBUNat b (Pos.to_nat p)] cannot be Uone *)
Lemma UgenByBUNat_PosToNat_eq_Unone_contro : forall b p n,
    UgenByBUNat b (Pos.to_nat p) <> Unone n.
Proof.
  intros. destruct (Pos.to_nat p) eqn:Ep; auto; auto with zarith.
  intro. simpl in H. destruct n0; easy.
Qed.

(** [UgenByBUNat b (Pos.to_nat p)] cannot be Uinv *)
Lemma UgenByBUNat_PosToNat_eq_Uinv_contro : forall b p u,
    UgenByBUNat b (Pos.to_nat p) <> / u.
Proof.
  intros. destruct (Pos.to_nat p) eqn:Ep; auto; auto with zarith.
  intro. simpl in H. destruct n; easy.
Qed.

(** [Ucoef] of [UgenByBUNat] equal to 1. *)
Lemma Ucoef_UgenByBUNat : forall (b : BaseUnit) (n : nat),
    Ucoef (UgenByBUNat b n) = 1.
Proof.
  intros. induction n; simpl; auto. destruct n; auto.
  rewrite Ucoef_Umul. rewrite IHn. rewrite Ucoef_Ubu. ring.
Qed.

(** [Udim b] of [UgenByBUNat b n] equal to n *) 
Lemma Udim_UgenByBUNat_same : forall (b : BaseUnit) (n : nat),
    Udim (UgenByBUNat b n) b = Z.of_nat n.
Proof.
  intros. induction n; simpl; auto. destruct n.
  - rewrite Udim_Ubu_same. lia.
  - rewrite Udim_Umul. rewrite IHn. rewrite Udim_Ubu_same. lia.
Qed.

(** [Udim b'] of [UgenByBUNat b n] equal to 0 *) 
Lemma Udim_UgenByBUNat_diff : forall (b1 b2 : BaseUnit) (n : nat),
    b1 <> b2 -> Udim (UgenByBUNat b1 n) b2 = 0%Z.
Proof.
  intros. induction n; simpl; auto. destruct n.
  - apply Udim_Ubu_diff; auto.
  - rewrite Udim_Umul. rewrite IHn. rewrite Udim_Ubu_diff; auto.
Qed.

(** Generate a unit by integer number power of a base unit *)
Definition UgenByBU (b : BaseUnit) (z : Z) : Unit :=
  match z with
  | Z0 => 1
  | Zpos p => UgenByBUNat b (Pos.to_nat p)
  | Zneg p => / (UgenByBUNat b (Pos.to_nat p))
  end.

Section test.
  (* Compute UgenByBU &T 2. *)
  (* Compute UgenByBU &T 1. *)
  (* Compute UgenByBU &T 0. *)
  (* Compute UgenByBU &T (-1). *)
  (* Compute UgenByBU &T (-2). *)
End test.

(** [UgenByBU] is injective for exponent *)
Lemma UgenByBU_inj_exp : forall b z1 z2,
    UgenByBU b z1 = UgenByBU b z2 -> z1 = z2.
Proof.
  intros. unfold UgenByBU in H. destruct z1,z2; try easy.
  - symmetry in H. apply UgenByBUNat_PosToNat_eq_Unone_contro in H; easy.
  - apply UgenByBUNat_PosToNat_eq_Unone_contro in H; easy.
  - apply UgenByBUNat_inj_exp in H. lia.
  - apply UgenByBUNat_PosToNat_eq_Uinv_contro in H; easy.
  - symmetry in H. apply UgenByBUNat_PosToNat_eq_Uinv_contro in H; easy.
  - inversion H. apply UgenByBUNat_inj_exp in H1. lia.
Qed.

(** [UgenByBU] is injective for [BaseUnit] *)
Lemma UgenByBU_inj_BU : forall b1 b2 z,
    (z <> 0)%Z -> UgenByBU b1 z = UgenByBU b2 z -> b1 = b2.
Proof.
  intros. unfold UgenByBU in H0. destruct z; try easy.
  - apply UgenByBUNat_inj_BU in H0; auto. lia.
  - inversion H0. apply UgenByBUNat_inj_BU in H2; auto. lia.
Qed.


(** [Ucoef] of [UgenByBU b z] equal to `1`. *)
Lemma Ucoef_UgenByBU : forall b z, Ucoef (UgenByBU b z) = 1.
Proof.
  intros. destruct z; simpl; auto.
  - rewrite Ucoef_UgenByBUNat. auto.
  - rewrite Ucoef_UgenByBUNat. field.
Qed.

(** [Udim b] of [UgenByBU b z] equal to `z`. *)
Lemma Udim_UgenByBU_same : forall b z, Udim (UgenByBU b z) b = z.
Proof.
  intros. destruct z; simpl; auto.
  - rewrite Udim_UgenByBUNat_same. lia.
  - rewrite Udim_UgenByBUNat_same. lia.
Qed.

(** [Udim b'] of [UgenByBU b z] equal to `0`. *)
Lemma Udim_UgenByBU_diff : forall b b' z, b <> b' -> Udim (UgenByBU b z) b' = 0%Z.
Proof.
  intros. destruct z; simpl; auto.
  - rewrite Udim_UgenByBUNat_diff; auto.
  - rewrite Udim_UgenByBUNat_diff; auto.
Qed.


(* ======================================================================= *)
(** ** Generate a unit with a given unit and [UgenByBU] *)

(** Generate a unit by multiply [UgenByBU b z] and a given unit `u` *)
Definition Ucons (u : Unit) (b : BaseUnit) (z : Z) : Unit :=
  if (z =? 0)%Z 
  then u
  else (UgenByBU b z) * u.

(** [Ucons] is injective for exponent *)
Lemma Ucons_inj_exp : forall u b z1 z2, Ucons u b z1 = Ucons u b z2 -> z1 = z2.
Proof.
  intros. unfold Ucons in H.
  bdestruct (z1 =? 0)%Z; bdestruct (z2 =? 0)%Z; subst; auto.
  - apply Umul_eq_contro_r in H; easy.
  - symmetry in H. apply Umul_eq_contro_r in H; easy.
  - apply Umul_cancel_r in H. apply UgenByBU_inj_exp in H; auto.
Qed.

(** [Ucons] is injective for exponent (extend version) *)
Lemma Ucons_inj_exp_ext : forall u1 u2 b z1 z2,
    u1 = u2 -> Ucons u1 b z1 = Ucons u2 b z2 -> z1 = z2.
Proof.
  intros. subst. apply Ucons_inj_exp in H0; auto.
Qed.

(** [Ucons] is injective for [BaseUnit] *)
Lemma Ucons_inj_BU : forall u b1 b2 z,
    (z <> 0)%Z -> Ucons u b1 z = Ucons u b2 z -> b1 = b2.
Proof.
  intros. unfold Ucons in H0.
  bdestruct (z =? 0)%Z; subst; auto. lia.
  apply Umul_cancel_r in H0. apply UgenByBU_inj_BU in H0; auto.
Qed.

(** [Ucons] is injective for initial [Unit] *)
Lemma Ucons_inj_Unit : forall u1 u2 b z,
    Ucons u1 b z = Ucons u2 b z -> u1 = u2.
Proof.
  intros. unfold Ucons in H.
  bdestruct (z =? 0)%Z; subst; auto.
  apply Umul_cancel_l in H. auto.
Qed.

(* (** [Ucons] is injective for initial [Unit] and exponent meanwhile *) *)
(* Lemma Ucons_inj_Unit_exp : forall u1 u2 b z1 z2, *)
(*     Ucons u1 b z1 = Ucons u2 b z2 -> u1 = u2 /\ z1 = z2. *)
(* Proof. *)
(*   intros. unfold Ucons in H. *)
(*   bdestruct (z1 =? 0)%Z; bdestruct (z2 =? 0)%Z; auto. *)
(*   - subst. auto. *)
(*   - apply Umul_eq_contro_r in H; easy. *)
(*   - symmetry in H. apply Umul_eq_contro_r in H; easy. *)
(*   - apply Umul_cancel_r in H. apply UgenByBU_inj_exp in H; auto. *)
(* Qed. *)

  
(** [Ucoef] of [Ucons u b z] equal to [Ucoef u] *)
Lemma Ucoef_Ucons : forall u b z, Ucoef (Ucons u b z) = Ucoef u.
Proof.
  intros. unfold Ucons. destruct (z =? 0)%Z; simpl; auto.
  rewrite Ucoef_UgenByBU. ring.
Qed.

(** [Udim b] of [Ucons u b z] equal to [Udim u b] + z *)
Lemma Udim_Ucons_same : forall u b z, Udim (Ucons u b z) b = ((Udim u b) + z)%Z.
Proof.
  intros. unfold Ucons. destruct (z =? 0)%Z eqn:En.
  - apply Z.eqb_eq in En. lia.
  - rewrite Udim_Umul. rewrite Udim_UgenByBU_same. lia.
Qed.
  
(** [Udim b'] of [Ucons u b z] equal to [Udim u b'] *)
Lemma Udim_Ucons_diff : forall u b b' z, b <> b' -> Udim (Ucons u b z) b' = (Udim u b').
Proof.
  intros. unfold Ucons. destruct (z =? 0)%Z eqn:En; auto.
  rewrite Udim_Umul. rewrite Udim_UgenByBU_diff; auto.
Qed.

(** A rewriting for [Udim] of [Ucons]. *)
Lemma Udim_Ucons : forall (u : Unit) (b1 b2 : BaseUnit) (z : Z),
  Udim (Ucons u b1 z) b2 = ((Udim u b2) + (if (BUeqb b1 b2) then z else 0))%Z.
Proof.
  intros. bdestruct (BUeqb b1 b2).
  - subst. apply Udim_Ucons_same.
  - rewrite Udim_Ucons_diff; auto. ring.
Qed.


(* 化简 Ucoef 表达式 *)
Ltac simp_Ucoef :=
  repeat
      match goal with
      (* Ucoef (Ucons u b z) = Ucoef u *)
      | |- context [Ucoef (Ucons ?u ?b ?z)] => rewrite Ucoef_Ucons
      (* Ucoef (Unone r) = r *)
      | |- context [Ucoef (Unone ?r)] => rewrite Ucoef_Unone
      end.

(* 化简 Udim 表达式 *)
Ltac simp_Udim :=
  repeat
    match goal with
    (* Udim (Ucons u b z) b = Udim u b + z *)
    | |- context [Udim (Ucons ?u ?b ?z) ?b] => rewrite Udim_Ucons_same
    (* Udim (Ucons u b z) b' = Udim u b' *)
    | |- context [Udim (Ucons ?u ?b ?z) ?b'] => try rewrite Udim_Ucons_diff;[|easy]
    (* Udim (Uone r) b = 0 *)
    | |- context [Udim (Unone _) ?b] => rewrite Udim_Unone
    (* Udim (Ubu b) b = 1 *)
    | |- context [Udim (Ubu ?b) ?b] => rewrite Udim_Ubu_same
    (* Udim (Ubu b) b' = 0 *)
    | |- context [Udim (Ubu ?b) ?b'] => try rewrite Udim_Ubu_diff;[|easy]
    end.
