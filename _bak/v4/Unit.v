(*
  category:     Utilities
  filename:     Unit.v
  author:       Zhengpu Shi
  date:         2021.05.08
  purpose:      International System of Units (SI).
  
  modify:
  1. 为解决绝对尺度与相对尺度的问题，引入 K'表示相对尺度单位，它含有一个默认参考点，
     或称基准值，需要通过该基准值进行单位之间的换算。另外，这里的运算也有限制。
  2. 为了区分数值和单位，将unit改造成 quantity[magnitude,unit]，数量和单位区分开。

  copyright:    Formalized Engineering Mathematics team of NUAA.
  website:      http://fem-nuaa.cn/FML4FCS
*)

Require Import List.
Import ListNotations.

Require Export Reals.
Open Scope R_scope.

Require Export QArith.
Open Scope Q.

(** * Scope for Unit *)


(** * Unit Kind *)

(** seven basic physical quantity by SI *)
Inductive UnitKind : Set :=
  | UKs     (* Time, second, s *)
  | UKm     (* Length, metre, m *)
  | UKkg    (* Mass, kilogram, kg *)
  | UKA     (* Electric current, ampere, A *)
  | UKK     (* Temperature, kelvin, K *)
  | UKmol   (* Amount of substance, mole, mol *)
  | UKcd.   (* Luminous intensity, candela, cd *)

Scheme Equality for UnitKind. 

(** order of UnitKind *)
Definition UnitKind_ord (u : UnitKind) : nat :=
  match u with
  | UKs => 1 | UKm => 2 | UKkg => 3 | UKA => 4
  | UKK => 5 | UKmol => 6 | UKcd => 7
  end.

Coercion UnitKind_ord : UnitKind >-> nat.


(** * Element Unit. Then we could represent: m, mm, km etc. *)

Declare Scope ElementUnit_scope.
Delimit Scope ElementUnit_scope with elementUnit.
Open Scope ElementUnit_scope.

(* 1s:(UKs,1),  1min:(UKs,60) *)
Record ElementUnit : Set := mkElementUnit {
  EUkind : UnitKind;
  EUcoef : Q
}.

(* we won't use it, because automatic generated Q_beq is different with 
  Qeq_bool. *)
(* Scheme Equality for ElementUnit. *)

Definition ElementUnit_beq (u1 u2 : ElementUnit) : bool :=
  let (k1,c1) := u1 in 
  let (k2,c2) := u2 in
    andb (UnitKind_beq k1 k2) (Qeq_bool c1 c2).

Notation "coef & kind" := (mkElementUnit kind coef) (at level 0).

Definition ElementUnit_eq (u1 u2 : ElementUnit) : Prop :=
  ElementUnit_beq u1 u2 = true.

Notation "u1 == u2" := (ElementUnit_eq u1 u2) : ElementUnit_scope.


(** order of ElementUnit *)
Definition ElementUnit_ord (eu : ElementUnit) : nat := EUkind eu.

Coercion ElementUnit_ord : ElementUnit >-> nat.


(** * Basic Unit *)

Declare Scope BasicUnit_scope.
Delimit Scope BasicUnit_scope with basicUnit.
Open Scope BasicUnit_scope.

(* 1 * 1 * m * s = m * s *)
(* 1 / 1 * 1 / 1 / 1  = 1 *)
Inductive BasicUnit : Set :=
  | buone               (* 1 *)
  | bueu  (eu : ElementUnit)      (* normal. eg, s *)
  | bueui (eu : ElementUnit)      (* inverse. eg, Hz = /s. *)
  .

(*
  beueui UKs  :  Hz
  beueu  UKs  :  s
  
*)

Notation "1" := (buone) : BasicUnit_scope.
Notation "$ eu" := (bueu eu) (at level 0) : BasicUnit_scope.
Notation "$' eu" := (bueui eu) (at level 0) : BasicUnit_scope.

(* Scheme Equality for BasicUnit. *)

Definition BasicUnit_beq (u1 u2 : BasicUnit) : bool :=
  match u1 with
  | 1 => match u2 with
    | 1 => true
    | _ => false
    end
  | $ eu1 => match u2 with
    | $ eu2 => ElementUnit_beq eu1 eu2
    | _ => false
    end
  | $' eu1 => match u2 with
    | $' eu2 => ElementUnit_beq eu1 eu2
    | _ => false
    end
  end.

Check 1 + 2.
Compute BasicUnit_beq 1 $(60&UKs).

Definition BasicUnit_eq (u1 u2 : BasicUnit) :=
  BasicUnit_beq u1 u2 = true.

Notation "u1 == u2" := (BasicUnit_eq u1 u2) : BasicUnit_scope.

(** order of BasicUnit *)
Definition BasicUnit_ord (u : BasicUnit) : Z :=
  match u with
  | 1 => 0
  | $ eu => Z.of_nat eu
  | $' eu => Z.opp (Z.of_nat eu)
  end.

Coercion BasicUnit_ord : BasicUnit >-> Z.

(** * Unit *)

Declare Scope Unit_scope.
Delimit Scope Unit_scope with unit.
Open Scope Unit_scope.

Inductive Unit : Set :=
  | ub (u : BasicUnit)
  | uinv (u : Unit)
  | umul (u1 u2 : Unit).

(** Bind Scope to these structures *)
Bind Scope Unit_scope with UnitKind ElementUnit BasicUnit Unit.

Coercion ub : BasicUnit >-> Unit.

(** notations *)
Notation " / u" := (uinv u) : Unit_scope.
Notation "u1 * u2" := (umul u1 u2) : Unit_scope.
Notation " a ² " := (a * a) (at level 1) : Unit_scope.
Notation " a ³ " := ((a²) * a) (at level 1) : Unit_scope.
Notation " a ⁴ " := ((a³) * a) (at level 1) : Unit_scope.
Notation "u1 / u2" := (umul u1 (uinv u2)) : Unit_scope.


(** * Normalization of a unit *)

(** Calculate the unit recursion level *)
Fixpoint ulevel (u : Unit) : nat :=
  match u with
  | ub _ => 0
  | / u => (ulevel u) + 1
  | u1 * u2 => (ulevel u1) + (ulevel u2) + 1
  end.


(** translate all [uinv] operation, it looks like to flatten a unit with 
  multiplication of BasicUnit *)

Fixpoint uflat_aux (n : nat) (u : Unit) : Unit :=
  match n, u with
  | 0%nat, _ => u
  | S n, / (ub b) => match b with
    | 1 => 1
    | $ k => ub ($' k)
    | $' k => ub ($ k)
    end
  | S n, / / u => uflat_aux n u
  | S n, / (u1 * u2) => uflat_aux n
    ((uflat_aux n (/(uflat_aux n u1))) *
    (uflat_aux n (/(uflat_aux n u2))))
  | S n, u1 * u2 => match u1, u2 with
    | /_, _ => uflat_aux n ((uflat_aux n u1) * u2)
    | _, /_ => uflat_aux n (u1 * (uflat_aux n u2))
    | 1, 1 => 1
    | 1, _ => uflat_aux n u2
    | _, 1 => uflat_aux n u1
    | _, _ => (* uflat_inv_aux n  *)
      (uflat_aux n u1) * (uflat_aux n u2)
    end
  | S n, _ => u
  end.

(* uflat的作用：
1. 去掉所有的 uinv. 
  /($a) => $'a
  /($a*$b) => $'a * $'b
  /(/$a) => $a
2. 化简掉多余的1，比如 1 * a => a, a * 1 => a
*)

(* 需要补充证明，其规范：验证norm form是否已经不能再化简，
1. 先列出所有的化简规则
2. 证明这些规则（对于输出结果）已经无法再产生效果。
*)
Definition uflat (u : Unit) : Unit := uflat_aux (ulevel u) u.


Eval compute in uflat (1*1*1*1).
Eval compute in uflat (/(1*1)).
Eval compute in uflat (/($(1&UKm))).
(* Eval compute in uflat (/('s * 'm)).
Eval compute in uflat (/(1 * 's / ('s * 'm))).    (* 1/s * s * m *)
Eval compute in uflat (/('s * 'm) / ('m * 's)).
Eval compute in uflat (/('s * 'm) / ('m * 's) * 'm * 's). *)

(** Convert [a Unit without (uinv)] to [list BasicUnit] *)
Fixpoint u2list (u : Unit) : list BasicUnit :=
  match u with
  | ub b => [b]
  | / u0 => []
  | u1 * u2 => match u1, u2 with
    | _, _ => (u2list u1) ++ (u2list u2)
    end
  end.

(*
作用：
1. 调整顺序为标准排序
  a. 标准排序。 m * A * s => s * A * m
  b. 相同单位集中在一起。 m * s * m => m * m * s => 用户看到的效果 m² * s
2. 合并对偶单位。 m * /m => 1
3. 消除单位元 1 (无量纲)
*)
(** Insert an element to [list BasicUnit] meanwhile with automatic unify *)
Fixpoint ulinsert (ls : list BasicUnit) (u2 : BasicUnit) 
  : list BasicUnit :=
  match ls with
  | [] => [u2]
  | u1 :: tl => match u1, u2 with
    | 1, 1 => ls
    | 1, _ => u1 :: (ulinsert tl u2)
    | _, 1 => ls
    | $eu1, $eu2 => if (Nat.leb eu1 eu2)
      then u1 :: (ulinsert tl u2)
      else u2 :: (ulinsert tl u1)
    | $eu1, $'eu2 => if (Nat.eqb eu1 eu2)
      then tl
      else if (Nat.leb eu1 eu2)
        then u1 :: (ulinsert tl u2)
        else u2 :: (ulinsert tl u1)
    | $'eu1, $eu2 => if (Nat.eqb eu1 eu2)
      then tl
      else if (Nat.leb eu1 eu2)
        then u1 :: (ulinsert tl u2)
        else u2 :: (ulinsert tl u1)
    | $'eu1, $'eu2 => if (Nat.leb eu1 eu2)
      then u1 :: (ulinsert tl u2)
      else u2 :: (ulinsert tl u1)
    end
  end.

(** Automatic clean a [list BasicUnit] *)
Fixpoint ulclean (ls : list BasicUnit) : list BasicUnit :=
  match ls with
  | [] => []
  | hd :: tl => ulinsert (ulclean tl) hd
  end.

(** Convert a [list BasicUnit] to a [Unit] *)
Fixpoint list2u (ls : list BasicUnit) : Unit :=
  match ls with
  | [] => 1
  | [hd] => hd
  | hd :: tl => (list2u tl) * hd
  end.

(** Normalize a Unit *)
Definition unorm (u : Unit) : Unit :=
(*   Eval compute in list2u (ulclean (u2list (uflat u))). *)
  list2u (ulclean (u2list (uflat u))).

(** * Equivalence Relation for ueq *)
Definition ueq (u1 u2 : Unit) : Prop := unorm u1 = unorm u2.

Notation "u1 == u2" := (unorm u1 = unorm u2) : Unit_scope.


(** Equality of two unit *)
(* Scheme Equality for Unit. *)
(* 
  let u1 := unorm X in
  let u2 := unorm Y in *)
Fixpoint Unit_beq_aux (u1 u2 : Unit) : bool :=
    match u1 with
    | ub u10 => match u2 with
      | ub u20 => BasicUnit_beq u10 u20
      | _ => false
      end
    | / u10 => match u2 with
      | / u20 => Unit_beq_aux u10 u20
      | _ => false
      end
    | u11 * u12 => match u2 with
      | u21 * u22 => (Unit_beq_aux u11 u21) && (Unit_beq_aux u12 u22)
      | _ => false
      end
    end.

Definition Unit_beq (u1 u2 : Unit) : bool := 
  Unit_beq_aux (unorm u1) (unorm u2).

Compute Unit_beq_aux (1*1) 1.
Compute Unit_beq (1*1) 1.


(** * Units for SI *)
Module SI.

  (** * BASIC SEVEN TYPES *)
  
  (** Time *)
  
  Definition second := ub (bueu (1 & UKs)).
  Notation "'s" := (second) (at level 0).

  Definition millisecond := ub (bueu (0.001 & UKs)).
  Notation "'ms" := (millisecond) (at level 0).
  
  Definition minute := ub (bueu (60 & UKs)).
  Notation "'min" := (minute) (at level 0).
  
  Definition hour := ub (bueu (3600 & UKs)).
  Notation "'h" := (hour) (at level 0).
  
  Definition day := ub (bueu (86400 & UKs)).
  Notation "'d" := (day) (at level 0).
  
  (** Length *)
  
  Definition metre := ub (bueu (1 & UKm)).
  Notation "'m" := (metre) (at level 0).
  
  Definition killometre := ub (bueu (1000 & UKm)).
  Notation "'km" := (killometre) (at level 0).
  
  Definition millimetre := ub (bueu (0.001 & UKm)).
  Notation "'mm" := (millimetre) (at level 0).
  
  (** Mass *)
  
  Definition killogram := ub (bueu (1 & UKkg)).
  Notation "'kg" := (killogram) (at level 0).
  
  Definition gram := ub (bueu (0.001 & UKkg)).
  Notation "'g" := (gram) (at level 0).
  
  (** Electric current *)
  
  Definition ampere := ub (bueu (1 & UKA)).
  Notation "'A" := (ampere) (at level 0).
  
  Definition milliampere := ub (bueu (0.001 & UKA)).
  Notation "'mA" := (milliampere) (at level 0).
  
  (** Temperature *)
  
  (* Notice, temperature unit has two type:
    first, a quantity of heat.
      a. Kelvin = (1 & UKK)
      b. Celsius = (1 & UKK)
      c. Fahrenheit = (5/9 & UKK)
    second, a state of temperature at a certain measurement scale.
      a. Kelvin,
      b. Celsius,
      c. Fahrenheit
    we mainly talk about first type, the second type means a state, cannot 
    be used directly, and the operation of them is limited too.
  *)
  Definition kelvin := ub (bueu (1 & UKK)).
  Notation "'K" := (kelvin) (at level 0).
  
  Definition celsius := ub (bueu (1 & UKK)).
  Notation "'℃" := (celsius) (at level 0).
  
  Definition fahrenheit := ub (bueu ((5/9) & UKK)).
  Notation "'℉" := (celsius) (at level 0).
  
(*   (** * A measurement *)
  Record Measurement : Set := mkMeasurement {
    meas_origin : Q;      (* original point with default unit *)
    meas_unit : Unit;     (* unit of every piece of energy *)
    meas_offset : Q       (* offset of energy *)
  }. *)
  
  (** Amount of substance *)
  
  Definition mole := ub (bueu (1 & UKmol)).
  Notation "'mol" := (mole) (at level 0).
  
  (** Luminous intensity *)
  
  Definition candela := ub (bueu (1 & UKcd)).
  Notation "'cd" := (candela) (at level 0).
  
  (** * DERIVED UNITS from 7 basic units *)
  
  (* plane angle, 平面角（弧度）, 1 rad = m / m = 1 *)
  Definition radian := 'm * / 'm.
  Notation "'rad" := (radian) (at level 0).

  Ltac pfueq :=
    compute;    (* u -> quant *)
    f_equal;    (* quant -> R*)
    try field.      (* solve R equation *)
    
  Lemma radian_rule : 'rad == 1.
  Proof. (* unfold radian. unfold unorm. simpl. *)  compute. auto. Qed.
  
  (* solid angle, 立体角（球面度），1 sr = 1 m^2/m^2 = 1 *)
  Definition steradian := 'm² / 'm².
  Notation "'sr" := (steradian) (at level 0).

  Lemma steradian_rule : 'sr == 1.
  Proof. compute. auto. Qed.
  
  (* frequency, 频率（赫兹），1 Hz = 1/s *)
  Definition herz := / 's.
  Notation "'Hz" := (herz) (at level 0).
  
  (* force, 力（牛顿）, 1 N = 1 kg*m/s^2 *)
  Definition newton := 'kg * 'm / 's².
  Notation "'N" := (newton) (at level 0).
  
  (* pressure,stress, 压力/压强/应力(帕斯卡), 1 Pa = 1N/m^2 = 1 kg/m/s^2 *)
  Definition pascal := 'N / 'm².
  Notation "'Pa" := (pascal) (at level 0).
  
  Lemma pascal_rule : 'Pa == 'kg / 'm / 's².
  Proof. compute. auto. Qed.
  
  (* energy,work,amout of heart,能[量]/功/热量(焦耳), 1J=1N*m = 1kg*m^2/s^2 *)
  Definition joule := 'N * 'm.
  Notation "'J" := (joule) (at level 0).
  
  Lemma joule_rule : 'J == 'kg * 'm² / 's².
  Proof. compute. auto. Qed.
  
  (* power,radiant flux, 功率,辐射[能]通量(瓦特), 1W=1J/s=1kg*m^2/s^3 *)
  Definition power := 'J / 's.
  Notation "'W" := (power) (at level 0).
  
  Lemma power_rule : 'W == 'kg * 'm² / 's³.
  Proof. compute. auto. Qed.
  
  (* electric charge,电荷[量](库仑), 1C=1A*s *)
  Definition coulomb := 'A * 's.
  Notation "'C" := (coulomb) (at level 0).
  
  (* electric potential difference,电势差/电压(伏特), 1V=1W/A=1kg*m^2/s^3/A *)
  Definition volt := 'W / 'A.
  Notation "'V" := (volt) (at level 0).
  
  Lemma volt_rule : 'V == 'kg * 'm² / 's³ / 'A.
  Proof. compute. auto. Qed.
  
  (* capacitance,电容(法拉), 1F=1C/V=1/kg/m^2 *s^4*A^2 *)
  Definition farad := 'C / 'V.
  Notation "'F" := (farad) (at level 0).
  
  Lemma farad_rule : 'F == / 'kg / 'm² * 's⁴ * 'A².
  Proof. compute. auto. Qed.
  
  (* electric resistance,电阻(欧姆), 1Ω=1V/A=1kg*m^2/s^3/A^2 *)
  Definition ohm := 'V / 'A.
  Notation "'Ω" := (ohm) (at level 0).
  
  Lemma ohm_rule : 'Ω == 'kg * 'm² / 's³ / 'A².
  Proof. compute. auto. Qed.
  
  (* electric conductance,电导(西门子),1S=1A/V=1/kg*m^2*s^3*A^2 *)
  Definition siemens := 'A / 'V.
  Notation "'S" := (siemens) (at level 0).
  
  Lemma siemens_rule : 'S == /'kg / 'm² * 's³ * 'A².
  Proof. compute. auto. Qed.
  
  (* magnetic flux,磁通[量](韦伯),1Wb=1V*s=1kg*m^2/s^2/A *)
  Definition weber := 'V * 's.
  Notation "'Wb" := (weber) (at level 0).
  
  Lemma weber_rule : 'Wb == 'kg * 'm² / 's² / 'A.
  Proof. compute. auto. Qed.
  
  (* magnetic flux density,磁通密度/磁感应强度(特斯拉),1T=1Wb/m^2=1kg/s^2/A *)
  Definition tesla := 'Wb / 'm².
  Notation "'T" := (tesla) (at level 0).
  
  Lemma tesla_rule : 'T == 'kg / 's² / 'A.
  Proof. compute. auto. Qed.
  
  (* inductance,电感(亨利), 1H=1Wb/A=1kg*m^2/s^2/A^2 *)
  Definition henry := 'Wb / 'A.
  Notation "'H" := (henry) (at level 0).
  
  Lemma henry_rule : 'H == 'kg * 'm² / 's² / 'A².
  Proof. compute. auto. Qed.

End SI.

Export SI.

(** 练习 *)

(* 规范化一个单位 *)
(* Compute unorm ('s * 'm * /('m *'s)). *)

(* 气体状态方程 P = ρRT 中 R 有两个单位，验证它们相同 *)
Example ex_rho_R_T : 'N * 'm / ('kg * 'K) == 'm² / ('s² * 'K).
Proof. pfueq. Qed.
 

(** 一些零散的测试 *)
Example ex1 : Unit := 1 * 1.
Example ex2 : Unit := 's * 'm * 1.
Example ex3 : Unit := 1 * 's * 'ms.
Example ex4 : Unit := 1 * 's * 'Hz.

Eval compute in uflat (1*1*1*1).
Eval compute in uflat (/(1*1)).
Eval compute in uflat (/(1 * 's)).
Eval compute in uflat (/('s * 'm)).
Eval compute in uflat (/(1 * 's / ('s * 'm))).    (* 1/s * s * m *)
Eval compute in uflat (/('s * 'm) / ('m * 's)).
Eval compute in uflat (/('s * 'm) / ('m * 's) * 'm * 's).

Eval compute in uflat (/(1 * 's / ('s * 'm))).  
Eval compute in u2list (uflat (/(1 * 's / ('s * 'm)))).    (* 1/s * s * m *)

Eval compute in ulclean [$(1&UKs);$'(1&UKm);$(1&UKm);$'(1&UKs)].


Eval compute in list2u (ulclean (u2list (uflat (/(1 * 's / ('s * 'm)))))).

Example ul1 : list BasicUnit := [].
Example ul2 := Eval compute in ulinsert ul1 $(2&UKs). Print ul2.
Example ul3 := Eval compute in ulinsert ul2 $'(3&UKm). Print ul3.
Example ul4 := Eval compute in ulinsert ul3 $(4&UKm). Print ul4.  (* 应该有误 *)
Example ul5 := Eval compute in ulinsert ul4 $(1&UKs). Print ul5.

