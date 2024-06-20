(*
  filename:     Unit.v
  author:       Zhengpu Shi
  date:         2021.05.08
  purpose:      A coq formalization of SI (International System of Units)
  reference:    https://en.wikipedia.org/wiki/International_System_of_Units

*)

(** Import necessary libraries *)

Require Import Extraction.
(* Require Import extraction.ExtrOcamlBasic.
Require Import extraction.ExtrOcamlNatInt. *)

(* Require Import List.
Import ListNotations. *)

Require Import QArith.
Require Import Reals.
Require Import Lra.


(** We are going to use real numbers *)
Open Scope R_scope.


(** * Definition and operations of Unit *)

(** Declare a scope for Unit *)
Declare Scope Unit_scope.
Delimit Scope Unit_scope with unit.
Open Scope Unit_scope.

(** ** Quantity Prefix, 
 some common symbols that can represent quantitative prefixes *)

(** Definition of Quantity Prefix *)
Inductive QuantityPrefix : Set :=
  (* multiples *)
  | Deca | Hecto | Kilo | Mega | Giga | Tera | Peta | Exa | Zetta | Yotta 
  (* submultiples *)
  | Deci | Centi | Milli | Micro | Nano | Pico | Femto | Atto | Zepto | Yocto
  .

(** Convert a Quantity Prefix to a number *)
Definition QuantityPrefix2Number : QuantityPrefix -> R :=
  fun p => match p with
  | Deca => 1e1     | Hecto => 1e2    | Kilo => 1e3    | Mega => 1e6   
  | Giga => 1e9     | Tera => 1e12    | Peta => 1e15   | Exa => 1e18     
  | Zetta => 1e21   | Yotta => 1e24
  | Deci => 1e-1    | Centi => 1e-2   | Milli => 1e-3  | Micro => 1e-6
  | Nano => 1e-9    | Pico => 1e-12   | Femto => 1e-15 | Atto => 1e-18
  | Zepto => 1e-21  | Yocto => 1e-24
  end.

(** Convert QuantityPrefix to R if necessary. *)
Coercion QuantityPrefix2Number : QuantityPrefix >-> R.

(** Example *)
Definition QuantityPrefix_ex := Eval compute in Mega + Milli.
(* Print QuantityPrefix_ex. *)


(** ** Unit Kind,
 there are seven basic unit kind in SI. *)

(** Definition of Unit Kind *)
Inductive UnitKind : Set :=
  | Time                  (* second, s *)
  | Length                (* metre, m *)
  | Mass                  (* kilogram, kg *)
  | ElectricCurrent       (* ampere, A *)
  | Temperature           (* kelvin, K *)
  | AmountOfSubstance     (* mole, mol *)
  | LuminousIntensity.    (* candela, cd *)


(** ** Unit,
 it could be used to represent any expression with Unit *)

(** Definition of Unit *)
Inductive Unit : Set :=
  | Unone (n : R)           (* a number *)
  | Ubase (k : UnitKind)    (* a basic unit *)
  | Uadd (u1 u2 : Unit)     (* u1 + u2 *)
  | Uopp (u : Unit)         (* - u *)
  | Umul (u1 u2 : Unit)     (* u1 * u2 *)
  | Uinv (u : Unit)         (* / u *)
  | Upow (u1 u2 : Unit)     (* u1 ^ u2 *)
  .

(** Convert R to Unit if necessary *)
Coercion Unone : R >-> Unit.

(** Two additional operations: subtraction and division *)
Definition Usub (u1 u2 : Unit) : Unit := Uadd u1 (Uopp u2).
Definition Udiv (u1 u2 : Unit) : Unit := Umul u1 (Uinv u2).

(** Notations *)
Notation "# n" := (Unone n) (at level 1) : Unit_scope.
Notation "$ k" := (Ubase k) (at level 1) : Unit_scope.

Infix "+" := Uadd : Unit_scope.
Notation " - a" := (Uopp a) : Unit_scope.
Infix "-" := Usub : Unit_scope.

Infix "*" := Umul : Unit_scope.
Notation " a ² " := (a * a) : Unit_scope.
Notation " a ³ " := ((a²) * a) (at level 1) : Unit_scope.
Notation " a ⁴ " := ((a³) * a) (at level 1) : Unit_scope.
Notation " / a" := (Uinv a) : Unit_scope.
Infix "/" := Udiv : Unit_scope.


(** ** Unit is a Ring and Field structure *)

(** Axioms for Ring structure of Unit *)
Axiom uadd_comm : forall u1 u2, u1 + u2 = u2 + u1.
Axiom uadd_assoc : forall u1 u2 u3, u1 + (u2 + u3) = (u1 + u2) + u3.
Axiom uadd_opp_l : forall u, - u + u = #0.
Axiom uadd_0_l : forall u, #0 + u = u.

Axiom umul_comm : forall u1 u2, u1 * u2 = u2 * u1.
Axiom umul_assoc : forall u1 u2 u3, u1 * (u2 * u3) = (u1 * u2) * u3.
Axiom umul_inv_l : forall u, / u * u = #1.
Axiom umul_1_l : forall u, #1 * u = u.

Axiom udistr_l : forall a b c, (a + b) * c = a * c + b * c.
Axiom usub_def : forall u1 u2, u1 - u2 = u1 + (-u2).
Axiom uopp_def : forall u, u + (-u) = #0.

(** Construct a ring theory *)
Lemma unit_ring_theory : ring_theory #0 #1 Uadd Umul Usub Uopp eq.
Proof.
  split. 
  apply uadd_0_l. apply uadd_comm. apply uadd_assoc. 
  apply umul_1_l. apply umul_comm. apply umul_assoc. apply udistr_l.
  apply usub_def. apply uopp_def.
Qed.

(** Add ring theory to system *)
Add Ring unit_ring : unit_ring_theory.

(** Some easy lemmas *)
Lemma udistr_r : forall a b c, a * (b + c) = a * b + a * c.
Proof. intros. ring. Qed.

(** Extra axioms for Field structure of Unit *)
Axiom u_1_neq_0 : #1 <> #0.
Axiom udiv_def : forall u1 u2, u1 / u2 = u1 * / u2.
Axiom uinv_def : forall u, u <> #0 -> / u * u = #1.

(** Construct a field theory *)
Lemma unit_field_theory : field_theory #0 #1 Uadd Umul Usub Uopp Udiv Uinv eq.
Proof.
  split.
  apply unit_ring_theory. apply u_1_neq_0. apply udiv_def. apply uinv_def.
Qed.

(** Add field theory to system *)
Add Field unit_field : unit_field_theory.


(** ** Extra axioms for operations meaning *)

Axiom uadd_none_none : forall r1 r2, 
  #r1 + #r2 = #(r1 + r2).

Axiom umul_none_none : forall r1 r2, 
  #r1 * #r2 = #(r1 * r2).

Axiom umul_none_umul_l : forall r1 r2 u,
  #r1 * (#r2 * u) = #(r1*r2) * u.

Axiom uadd_ax_ay : forall r1 r2 u,
  (#r1 * u) + (#r2 * u) = #(r1 + r2) * u.
Axiom usub_ax_ay : forall r1 r2 u,
  (#r1 * u) - (#r2 * u) = #(r1 - r2) * u.
Axiom umul_ax_ay : forall r1 r2 u1 u2,
  (#r1 * u1) * (#r2 * u2) = #(r1 * r2) * (u1 * u2).

Axiom upow_num_num : forall r1 r2,
  Upow #r1 #r2 = #(Rpower r1 r2).

Axiom udiv_ax_bx : forall a b x,
  (#b * x <> #0) ->
  (#a * x) / (#b * x) = #(a/b).


(* Ltac umul_none_none_simp :=
  rewrite umul_none_none; f_equal; ring. *)

(** Expand internal Hint database of Resolve *)
Global Hint Resolve
  uadd_none_none uadd_ax_ay usub_ax_ay
  umul_none_none umul_none_umul_l
  umul_ax_ay upow_num_num
  : unit.

(** Expand internal Hint database of Rewrite *)
Hint Rewrite
  uadd_none_none uadd_ax_ay usub_ax_ay
  umul_none_none umul_none_umul_l
  umul_ax_ay upow_num_num
  : unit.

(** ** Concrete Unit *)

(** *** Time *)

Definition second x := x * $ Time.
Notation "'s" := (second 1) (at level 0).

Definition millisecond x := x * 0.001 * 's.
Notation "'ms" := (millisecond 1) (at level 0).

Definition minute x := x * 60 * 's.
Notation "'min" := (minute 1) (at level 0).

Definition hour x := x * 60 * 'min.
Notation "'h" := (hour 1) (at level 0).

Definition day x := x * 24 * 'h.
Notation "'d" := (day 1) (at level 0).

Global Hint Unfold millisecond minute hour day : unit.

(** Prove that 1s = 1000ms *)
Lemma second_millisecond : 's = 1000 * 'ms.
Proof. compute. autorewrite with unit. f_equal. f_equal. field. Qed.

(** Prove that 1.5s = 1500ms *)
Example timeunit_ex1 : 1.5 * 's = 1500 * 'ms.
Proof. compute. autorewrite with unit. f_equal. f_equal. field. Qed.

(** *** Length *)

Definition metre x := x * $Length.
Notation "'m" := (metre 1) (at level 0).

Definition killometre x := x * 1000 * 'm.
Notation "'km" := (killometre 1) (at level 0).

Definition millimetre x := x * 0.001 * 'm.
Notation "'mm" := (millimetre 1) (at level 0).

Global Hint Unfold killometre millimetre : unit.

(** *** Mass *)

Definition killogram x := x * $Mass.
Notation "'kg" := (killogram 1) (at level 0).

Definition gram x := x * 0.001 * 'kg.
Notation "'g" := (gram 1) (at level 0).

(** *** Electric current *)

Definition ampere x := x * $ElectricCurrent.
Notation "'A" := (ampere 1) (at level 0).

Definition milliampere x := x * 0.001 * 'A.
Notation "'mA" := (milliampere 1) (at level 0).

(** *** Temperature *)

Definition kelvin x := x * $Temperature.
Notation "'K" := (kelvin 1) (at level 0).

(* Notice, Celisus is very different, need an offset. *)
Definition celsius x := x * $Temperature.
Notation "'℃" := (celsius 1) (at level 0).

(* Example tempunit_ex1 : 2 '℃ = 275.15 'K.
Proof. compute. autorewrite with unit. f_equal. f_equal. field. Qed.

Example tempunit_ex2 : 2 * 3 'K = 6 'K.
Proof. compute. autorewrite with unit. f_equal. Qed. *)

(** *** Amount of substance *)

Definition mole x := x * $ AmountOfSubstance.
Notation "'mol" := (mole 1) (at level 0).

(** *** Luminous intensity *)

Definition candela x := x * $ AmountOfSubstance.
Notation "'cd" := (candela 1) (at level 0).


(** ** Exercises *)

(* 1 m + 2 m = 3 m *)
Example ex1 : 'm + (2 * 'm) = 3 * 'm.
Proof. compute. autorewrite with unit. f_equal. f_equal. field. Qed.

(* 2 m * 3 m = 6 m^2 *)
Example ex2 : (2 * 'm) * (3 * 'm) = 6 * ('m²).
Proof. compute. autorewrite with unit. f_equal. Qed.

(** A bit hard situation, it shows that the automatic ability is weak *)
(* 2 m * 3 = 6 * m *)
Example ex3 : 2 * 'm * 3 = 6 * 'm.
Proof. compute. autorewrite with unit.
  rewrite umul_comm. rewrite umul_assoc. 
  f_equal. autorewrite with unit. f_equal. ring.
Qed.

(** Add more automatic ability, prove again *)

Axiom umul_none_umul_r : forall r1 r2 u,
  (#r1 * u) * #r2 = #(r1*r2) * u.

Hint Rewrite umul_none_umul_r : unit.

Example ex3' : 2 * 'm * 3 = 6 * 'm.
Proof. compute. autorewrite with unit. f_equal. Qed.


(** * Derived units with special names in the SI *)
Module DerivedUnits.
  
  (* plane angle, 平面角（弧度）, 1 rad = m / m = 1 *)
  Definition radian (x : R) := x * 'm / 'm.
  Notation "'rad" := (radian 1) (at level 0).
  Global Hint Unfold radian : unit.
  
  Lemma radian_rule : 'rad = 1.
  Proof. 
    (* compute. autorewrite with unit. field.  *)
    unfold radian. field. discriminate. Qed.
  
  (* solid angle, 立体角（球面度），1 sr = 1 m^2/m^2 = 1 *)
  Definition steradian (x : R) := x * 'm² / 'm².
  Notation "'sr" := (steradian 1) (at level 0).
  
  Lemma steradian_rule : 'sr = 1.
  Proof. unfold steradian. field. discriminate. Qed.
  
  (* frequency, 频率（赫兹），1 Hz = 1/s *)
  Definition herz (x : R) := x / 's.
  Notation "'Hz" := (herz 1) (at level 0).
  
  (* force, 力（牛顿）, 1 N = 1 kg*m/s^2 *)
  Definition newton (x : R) := x * 'kg * 'm / 's².
  Notation "'N" := (newton 1) (at level 0).
  
  (* pressure,stress, 压力/压强/应力(帕斯卡), 1 Pa = 1N/m^2 = 1 kg/m/s^2 *)
  Definition pascal (x : R) := x * 'N / 'm².
  Notation "'Pa" := (pascal 1) (at level 0).
  
  Lemma pascal_rule : 'Pa = 'kg / 'm / 's².
  Proof.
    unfold pascal. unfold newton. field. split; discriminate.
  Qed.
  
  (* energy,work,amout of heart,能[量]/功/热量(焦耳), 1J=1N*m = 1kg*m^2/s^2 *)
  Definition joule (x : R) := x * 'N * 'm.
  Notation "'J" := (joule 1) (at level 0).
  
  Lemma joule_rule : 'J = 'kg * 'm² / 's².
  Proof.
    unfold joule. unfold newton. field. discriminate.
  Qed.
  
  (* power,radiant flux, 功率,辐射[能]通量(瓦特), 1W=1J/s=1kg*m^2/s^3 *)
  Definition power (x : R) := x * 'J / 's.
  Notation "'W" := (power 1) (at level 0).
  
  Lemma power_rule : 'W = 'kg * 'm² / 's³.
  Proof.
    unfold power. rewrite joule_rule. field. discriminate.
  Qed.
  
  (* electric charge,电荷[量](库仑), 1C=1A*s *)
  Definition coulomb (x : R) := x * 'A * 's.
  Notation "'C" := (coulomb 1) (at level 0).
  
  (* electric potential difference,电势差/电压(伏特), 1V=1W/A=1kg*m^2/s^3/A *)
  Definition volt (x : R) := x * 'W / 'A.
  Notation "'V" := (volt 1) (at level 0).
  
  Lemma volt_rule : 'V = 'kg * 'm² / 's³ / 'A.
  Proof.
    unfold volt. rewrite power_rule. field. split; discriminate.
  Qed.
  
  (* capacitance,电容(法拉), 1F=1C/V=1/kg/m^2 *s^4*A^2 *)
  Definition farad (x : R) := x * 'C / 'V.
  Notation "'F" := (farad 1) (at level 0).
  
  Lemma farad_rule : 'F = / 'kg / 'm² * 's⁴ * 'A².
  Proof.
    unfold farad. unfold coulomb. rewrite volt_rule. field. 
    repeat split; try discriminate.
  Qed.
  
  (* electric resistance,电阻(欧姆), 1Ω=1V/A=1kg*m^2/s^3/A^2 *)
  Definition ohm (x : R) := x * 'V / 'A.
  Notation "'Ω" := (ohm 1) (at level 0).
  
  Lemma ohm_rule : 'Ω = 'kg * 'm² / 's³ / 'A².
  Proof.
    unfold ohm. rewrite volt_rule. field. split; discriminate.
  Qed.
  
  (* electric conductance,电导(西门子),1S=1A/V=1/kg*m^2*s^3*A^2 *)
  Definition siemens (x : R) := x * 'A / 'V.
  Notation "'S" := (siemens 1) (at level 0).
  
  Lemma siemens_rule : 'S = /'kg / 'm² * 's³ * 'A².
  Proof.
    unfold siemens. rewrite volt_rule. field. repeat split; discriminate.
  Qed.
  
  (* magnetic flux,磁通[量](韦伯),1Wb=1V*s=1kg*m^2/s^2/A *)
  Definition weber (x : R) := x * 'V * 's.
  Notation "'Wb" := (weber 1) (at level 0).
  
  Lemma weber_rule : 'Wb = 'kg * 'm² / 's² / 'A.
  Proof.
    unfold weber. rewrite volt_rule. field. repeat split; discriminate.
  Qed.
  
  (* magnetic flux density,磁通密度/磁感应强度(特斯拉),1T=1Wb/m^2=1kg/s^2/A *)
  Definition tesla (x : R) := x * 'Wb / 'm².
  Notation "'T" := (tesla 1) (at level 0).
  
  Lemma tesla_rule : 'T = 'kg / 's² / 'A.
  Proof.
    unfold tesla. rewrite weber_rule. field. repeat split; discriminate.
  Qed.
  
  (* inductance,电感(亨利), 1H=1Wb/A=1kg*m^2/s^2/A^2 *)
  Definition henry (x : R) := x * 'Wb / 'A.
  Notation "'H" := (henry 1) (at level 0).
  
  Lemma henry_rule : 'H = 'kg * 'm² / 's² / 'A².
  Proof.
    unfold henry. rewrite weber_rule. field. repeat split; discriminate.
  Qed.

End DerivedUnits.
