(*
  purpose   : Unit, syntax of unit.
  author    : Zhengpu Shi
  date      : 2021.05
  reference : 
  1. 力学，郑永年，2.2 单位制与量纲
  2. SI-Brochure-9-EN.pdf
  
  remark    :
  1. 基本量与导出量
  基本量。例如 长度、质量、时间、发光强度、热力学温度、物质的量
  基本单位。
  导出量。例如 速度、加速度、力
  导出单位。
  2. 量纲
  任何物理量与基本量之间都存在一定的关系，它必定是基本量的一定幂次的组合。
  在SI中，力学只需要三个基本量，长度、质量、时间，分别用L、M、T表示，
  则任意力学量 A（就起单位度量来讲）总可以表示为 A = L^a * M^b * T^c
  而各项的L、M、T的指数 a b c 则相同。

  为表示导出量与基本量在单位度量上的关系，引入量纲的概念。
  dim A = L^p * M^q * T^r
  上式右边称为力学量A的量纲。此处，
    dim A 表示 A 的量纲。
    L、M、T分别称为 L、M、T的量纲。
    p,q,r称为量纲指数。
  例如，dim V = L T^(-1), dim F = L M T^(-2)
  
  量纲法则：只有量纲相同的物理量才能相加、相减和相等。
  量纲法则是量纲分析的基础。
  量纲分析是一种有用的方法，它的主要用处：
  (1). 在基本量相同的单位制之间进行单位换算。
   例如，牛顿与达因的换算关系。
    dim F = L M T^(-2), 1 m = 100 cm, 1 kg = 1000 g
    所以，1 N = 100 * 1000 dyn = 10^5 dyn
  (2). 验证公式。从量纲的角度验证。
    例如，v^2 = 2*a*x，两边的量纲都是 L^2 * T^(-2)，故此公式可能是正确的。
    若有人给出 v^2 = 2*a*x^2，则此公式必定是错误的。
  (3). 为推导某些复杂公式提供线索。
  另外，量纲分析在空气动力学和流体力学中有重要应用。
  
*)
Require Import List.
Import ListNotations.

Require Import Bool.
Require Import ZArith.
Require Export TacticExt BoolExt RExt. 


Open Scope R_scope.

(** * Basic Unit *)


(** ** New scope for Unit *)

Declare Scope Unit_scope.
Delimit Scope Unit_scope with U.
Open Scope Unit_scope.


(** ** Definition of Basic Unit *)

(** seven basic unit kind *)
Inductive BasicUnit : Set :=
  | BUTime
  | BULength
  | BUMass
  | BUElectricCurrent
  | BUThermodynamicTemperature
  | BUAmountOfSubstance
  | BULuminousIntensity.

(** symbol of dimensions *)
Notation "&T" := (BUTime) (at level 0).
Notation "&L" := (BULength) (at level 0).
Notation "&M" := (BUMass) (at level 0).
Notation "&I" := (BUElectricCurrent) (at level 0).
Notation "&O" := (BUThermodynamicTemperature) (at level 0).
Notation "&N" := (BUAmountOfSubstance) (at level 0).
Notation "&J" := (BULuminousIntensity) (at level 0).  


(** ** Equality of BasicUnit *)

(** auto generate BasicUnit_beq and BasicUnit_eq_dec *)
Scheme Equality for BasicUnit.


(** ** Properties of BasicUnit *)

(** BasicUnit_beq is reflexive *)
Lemma BasicUnit_beq_refl b : BasicUnit_beq b b = true.
Proof.
  destruct b; auto.
Qed. 

(** BasicUnit_beq is true，iff b1 = b2 *)
Lemma BasicUnit_beq_eq : forall b1 b2, 
  BasicUnit_beq b1 b2 = true <-> b1 = b2.
Proof.
  intros. split; intros.
  - destruct b1,b2; simpl; simpl; easy.
  - subst. apply BasicUnit_beq_refl.
Qed.

(** BasicUnit_beq is false, iff b1 <> b2 *)
Lemma BasicUnit_beq_neq : forall b1 b2, 
  BasicUnit_beq b1 b2 = false <-> b1 <> b2.
Proof.
  intros. split; intros.
  - destruct (BasicUnit_beq b1 b2) eqn : E1. easy.
    intro H1. apply BasicUnit_beq_eq in H1. rewrite E1 in H1. easy.
  - destruct b1,b2; simpl; auto; destruct H; auto.
Qed.



(** * Unit, which is a syntax representation of any unit *)


(** ** Definition of Unit *)

(** Unit is an expression that could represent any quantity with unit *)
Inductive Unit : Set :=
  | Unone (coef : R)        (* a unit with no dimension. eg: a number *)
  | Ubu (bu : BasicUnit)    (* a unit with single dimension. eg: m *)
  | Uinv (u : Unit)         (* inversion of a unit. eg: Hz = /s *)
  | Umul (u1 u2 : Unit).    (* multiplication of two units. eg: m*s *)


(** Power of unit with a natural number *)
Fixpoint Upow (u : Unit) (n : nat) : Unit :=
  match n with
  | O => Unone 1
  | 1 => u
  | S n' => Umul u (Upow u n')
  end. 

(** Symbols used to construct an unit expression *)

Notation "$ coef" := (Unone coef) (at level 0) : Unit_scope. 
Notation "[ kind ]" := (Ubu kind) (at level 0) : Unit_scope.
Notation " / u" := (Uinv u) : Unit_scope.
Notation "u1 / u2" := (Umul u1 (Uinv u2)) : Unit_scope.
Notation "u1 * u2" := (Umul u1 u2) : Unit_scope.
Notation " a ^ n " := (Upow a n) (at level 30, right associativity) :Unit_scope.
Notation " a ² " := (a ^ 2) (at level 1) : Unit_scope.
Notation " a ³ " := (a ^ 3) (at level 1) : Unit_scope.
Notation " a ⁴ " := (a ^ 4) (at level 1) : Unit_scope.
Notation " a ⁵ " := (a ^ 5) (at level 1) : Unit_scope.
Notation " a ⁶ " := (a ^ 6) (at level 1) : Unit_scope.
Notation " a ⁷ " := (a ^ 7) (at level 1) : Unit_scope.

(** Examples *)
Example m := [BULength].
Example kg :=  [BUMass].
Example s := [BUTime].
Example hour := $3600 * [BUTime].
Example km := $1000 * m.

(** Question: How to make sure N == N' *)
Example N := $2 * (kg * m) / (s * s).
Example N' := ($2 * kg / s) * (m / s).


(** ** Properties of Unit *)

(** Upower n equality *)

Lemma Upow_eq_0 u : Upow u 0 = $1.
Proof. auto. Qed.

Lemma Upow_eq_1 u : Upow u 1 = u.
Proof. auto. Qed.

Lemma Upow_eq_2 u : Upow u 2 = u².
Proof. auto. Qed.

Lemma Upow_plus u n1 n2 : (Upow u n1) * (Upow u n2) = Upow u (n1 + n2).
Abort.  (* need semantics equal, not syntax equal *)

