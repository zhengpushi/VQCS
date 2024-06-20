(*
  filename:     Unit.v
  author:       Zhengpu Shi
  date:         2021.05.08
  purpose:      A coq formalization of SI (International System of Units)
  reference:    https://en.wikipedia.org/wiki/International_System_of_Units
  
  modify:
  1. 为解决绝对尺度与相对尺度的问题，引入 K'表示相对尺度单位，它含有一个默认参考点，
     或称基准值，需要通过该基准值进行单位之间的换算。另外，这里的运算也有限制。
  2. 为了区分数值和单位，将unit改造成 quantity[magnitude,unit]，数量和单位区分开。

*)

Require Export Reals.
Open Scope R_scope.

(** Import necessary libraries *)

Declare Scope Unit_scope.
Delimit Scope Unit_scope with unit.
Open Scope Unit_scope.


(** * Unit Kind *)

(* seven basic SI physical quantity *)
Inductive UnitKind : Set :=
  | UKs     (* Time, second, s *)
  | UKm     (* Length, metre, m *)
  | UKkg    (* Mass, kilogram, kg *)
  | UKA     (* Electric current, ampere, A *)
  | UKK     (* Temperature, kelvin, K *)
  | UKmol   (* Amount of substance, mole, mol *)
  | UKcd.   (* Luminous intensity, candela, cd *)

(* we need UnitKind_beq : u -> u -> bool *)
Scheme Equality for UnitKind. 

(* calculate an order of an UnitKind *)
Definition UnitKind_ord (u : UnitKind) : nat :=
  match u with
  | UKs => 0 | UKm => 1 | UKkg => 2 | UKA => 3
  | UKK => 4 | UKmol => 5 | UKcd => 6
  end.

Coercion UnitKind_ord : UnitKind >-> nat.
  
(** * Unit *)

(* A unit expression *)
Inductive Unit : Set :=
  | Ucoef (n : R)           (* a number, non-dimensional *)
  | Ukind (k : UnitKind)    (* a basic unit *)
  | Upow (base exponent : Unit) (* base ^ exponent *)
  | Uopp (u : Unit)         (* - u *)
  | Uadd (u1 u2 : Unit)     (* u1 + u2 *)
  | Umul (u1 u2 : Unit)     (* u1 * u2 *)
  | Uinv (u : Unit)         (* / u *)
  .

Coercion Ucoef : R >-> Unit.
Coercion Ukind : UnitKind >-> Unit.

(* substract and division operation, only a syntatic sugar *)
Definition Usub (u1 u2 : Unit) : Unit := Uadd u1 (Uopp u2).
Definition Udiv (u1 u2 : Unit) : Unit := Umul u1 (Uinv u2).

(** Notations *)

Infix "+" := Uadd : Unit_scope.
Notation " - a" := (Uopp a) : Unit_scope.
Infix "-" := Usub : Unit_scope.

Infix "*" := Umul : Unit_scope.
Notation " a ² " := (a * a) : Unit_scope.
Notation " a ³ " := ((a²) * a) (at level 1) : Unit_scope.
Notation " a ⁴ " := ((a³) * a) (at level 1) : Unit_scope.
Notation " / a" := (Uinv a) : Unit_scope.
Infix "/" := Udiv : Unit_scope.

(** More notations, final usage is convenient, but this files needn't *)
Notation "# n" := (Ucoef n) (at level 1) : Unit_scope.
Notation "$ k" := (Ukind k) (at level 1) : Unit_scope.


(** Evaluation *)

(* 问题：如何比较两个Unit *)

(* 方法一：手写一个转换函数，将Unit的复杂语法转换成唯一的格式。暂未完成 *)

Fixpoint ulevel (u : Unit) : nat :=
  match u with
  | Ucoef n => 0
  | Ukind k => 0
  | Upow base exp => (ulevel base) + (ulevel exp) + 1
  | - u => (ulevel u) + 1
  | u1 + u2 => (ulevel u1) + (ulevel u2) + 1
  | / u => (ulevel u) + 1
  | u1 * u2 => (ulevel u1) + (ulevel u2) + 1
  end.

Fixpoint uevalx (level : nat) (u : Unit) : Unit :=
  match level, u with
  | O, _ => u
  | S c', Ucoef n => u
  | S c', Ukind k => u
  | S c', Upow base exp => u
  | S c', - u' => (uevalx c' (uevalx c' ((-1) * u')))
  | S c', / u' => (uevalx c' (uevalx c' u'))
  | S c', u1 * u2 => match u1,u2 with
    | Ucoef n1, Ucoef n2 => Ucoef ((n1*n2))
    | Ucoef n1, Ukind k2 => u
    | Ucoef n1, / (Ucoef n2) => Ucoef ((n1/n2))
    | Ucoef n1, / (Ukind k2) => u
    | Ucoef n1, (Ucoef n2 * u20) => uevalx c' (Ucoef (n1*n2) * (uevalx c' u20))
    | Ucoef _, _ => uevalx c' (u1 * (uevalx c' u2))
    | Ukind k1, Ucoef n2 => uevalx c' (u2 * u1)
    | Ukind k1, Ukind k2 => if Nat.leb k1 k2 then u else u2 * u1
    | Ukind k1, / (Ucoef n2) => Ucoef (1/n2) * u1
    | Ukind k1, / (Ukind k2) => if UnitKind_beq k1 k2 then 1 
      else if Nat.leb k1 k2 then u else u2 * u1
    | Ukind k1, Ucoef n1 * u20 => uevalx c' (Ucoef n1 * (Ukind k1 * u20))
    | Ukind k1, (Ukind k2 * u20) => if UnitKind_beq k1 k2 
      then uevalx c' ((Ukind k1 * Ukind k2) * u20) else u
    | Ukind _, _ => uevalx c' (u1 * (uevalx c' u2))
    | (Ucoef n1 * u1'), Ucoef n2 => uevalx c' (Ucoef (n1*n2) * u1')
    | _, Ucoef _ => uevalx c' (u2 * u1)
    | _, Ukind _ => uevalx c' (u2 * u1)
    | _, _ => uevalx c' (uevalx c' u1) * (uevalx c' u2)
    end
  | S c', u1 + u2 => u
  end.

Definition ueval (u : Unit) : Unit := uevalx (ulevel u) u.

Definition unit_eq (u1 u2 : Unit) := ueval u1 = ueval u2.
(*   Infix "==" := unit_eq (at level 180, left associativity) : Unit_scope. *)

(* 这些例子用来测试 ueval 的功能 *)

Check (2/2).
Compute ueval (2/2).
Compute ueval (1 * 2 * 3 * 4 * 5).
Compute ueval (UKs * 1).
Compute ueval (UKs * 1 * 2 * 3 * 4).
Compute ueval (UKs * UKs * 1).
Compute ueval (1 * 1 * UKs * UKs).
Compute ueval (1 * UKs * UKs * 1).
Compute ueval (60 * (60 * (1 * UKs))).
Compute ueval (UKs / UKs).
Compute ueval (1 * UKs * UKs * 2).
Compute ueval (1 * UKs * 2 * UKs * 3).
Compute ueval (1 * UKs * 1 * UKs * 1).

Compute ueval (UKs * (UKs * UKs)).
Compute ueval (UKs * UKs * UKs).

Compute ueval (UKs * (UKs * UKm)).
Compute ueval (UKs * (1 * UKs)).
Compute ueval (UKs * 2 * UKm * 1 * UKs).


(** 方法二：统计每个分量，然后重建一个 *)

(** calculate the componens of a unit *)
(* eg. 2 * m^2 * /s ==> none=2,m=2,s=-1 *)

(** calculate coefficient *)
Fixpoint unit_calc_coef (u : Unit) : R :=
  match u with
  | Ucoef n => n
  | Ukind k => 1
  | Upow base exp =>
    let rbase := unit_calc_coef base in
    let rexp := unit_calc_coef exp in
      Rpower rbase rexp
  | - u => (-1) * (unit_calc_coef u)
  | u1 + u2 => (unit_calc_coef u1) + (unit_calc_coef u2)
  | / u => (1 / (unit_calc_coef u))
  | u1 * u2 => (unit_calc_coef u1) * (unit_calc_coef u2)
  end.

(** forbid unfold *)
Global Opaque Rpower.

Compute unit_calc_coef (1 * 2 * UKs * 4).
Compute unit_calc_coef (1 * 2 * UKs * 4 / 1).


(** count the occurance of unit_kind, maybe Zero, Positive or Negative *)
Fixpoint unit_count_kind (u : Unit) (k : UnitKind) : Z :=
  match u with
  | Ucoef n => 0
  | Ukind k1 => if UnitKind_beq k k1 then 1 else 0
  | Upow base exp => 0
  | - u => unit_count_kind u k
  | u1 + u2 => 
    (* two side should be equal *)
    let z1 := unit_count_kind u1 k in
    let z2 := unit_count_kind u2 k in
      if (z1 =? z2)%Z then z1 else 999
  | / u => Z.opp (unit_count_kind u k)
  | u1 * u2 => unit_count_kind u1 k + unit_count_kind u2 k
  end.

Compute unit_count_kind (1 * UKs / UKs * UKm) UKm.



(** construct a complex unit of $k with a natural number *)
(* for example, pow m 3 = m^3 *)
Fixpoint unit_gen_pow (k : UnitKind) (n : nat) : Unit :=
  match n with
  | O => 1
  | S O => k
  | S n => (unit_gen_pow k n) * k
  end.
Compute unit_gen_pow UKs 3.
Compute unit_gen_pow UKs 2.
Compute unit_gen_pow UKs 1.
Compute unit_gen_pow UKs 0.

(** generate a complex basic unit of $k using given number *)
Definition unit_gen_base_byN (k : UnitKind) (cnt : Z) : Unit :=
  match Z_dec 0 cnt with  (* 0<c + 0>c + 0=c *)
  | inleft dec2 => match dec2 with
    | left _ => unit_gen_pow k (Z.to_nat cnt)
    | right _ => / (unit_gen_pow k (Z.to_nat (Z.opp cnt)))
    end
  | inright _ => 1
  end.

Compute unit_gen_base_byN UKs 2.
Compute unit_gen_base_byN UKs 1.
Compute unit_gen_base_byN UKs 0.
Compute unit_gen_base_byN UKs (-1).
Compute unit_gen_base_byN UKs (-2).


(** 这个函数从原始的raw单位，逐步构建一个新的单位，
  每次从 raw 中取出一个分量，然后再来构造。
  相当于，把 取出分量、使用分量来构造 这两件事一起做了 *)

(** construct the unit with READY unit from RAW unit *)
Definition unit_cons_base (raw : Unit) (ready : Unit) (k : UnitKind) : Unit :=
  let n := unit_count_kind raw k in
    if (n =? 0)%Z then ready
    else ready * (unit_gen_base_byN k n).


(** * Quantity, high level operations *)

Definition Quantity := (R * Unit)%type.

(** 规范化一个单位 *)
Definition unit_unify (u : Unit) : Quantity :=
  let n_coef := unit_calc_coef u in
  let u_time := unit_cons_base u 1 UKs in
  let u_length := unit_cons_base u u_time UKm in
  let u_mass := unit_cons_base u u_length UKkg in
  let u_amount := unit_cons_base u u_mass UKmol in
  let u_current := unit_cons_base u u_amount UKA in
  let u_temp := unit_cons_base u u_current UKK in
  let u_light := unit_cons_base u u_temp UKcd in
    (n_coef, u_light).

Notation "u1 == u2" := (unit_unify u1 = unit_unify u2) 
  (at level 180, left associativity) : Unit_scope.
  
Compute unit_unify (1 * 2 * 3 * UKs * 4 * UKm).

Definition quantity_make (r:R) (u:Unit) : Quantity := (r,u).


(* Examples *)
Compute unit_unify (UKs * UKm + 2 * UKm * UKs).
Compute unit_unify (UKs * UKm + 2 * UKm * UKs / UKs).

Compute unit_unify (UKs * (UKs * UKs)).
Compute unit_unify (UKs * UKs * UKs).

Compute unit_unify (UKs * (UKs * UKm)).
Compute unit_unify (UKs * (1 * UKs)).
Compute unit_unify (UKs * 2 * UKm * 1 * UKs).

Compute unit_unify (1 * UKs * UKs * 2).
Compute unit_unify (1 * UKs * 2 * UKs * 3).
Compute unit_unify (1 * UKs * 1 * UKs * 1).
Compute unit_unify (UKs / UKs).
Compute unit_unify (1 * (2 * (3 * UKs))).
Compute unit_unify (1 * UKs * UKs * 1).
Compute unit_unify (1 * 1 * UKs * UKs).
Compute unit_unify (UKs * UKs * 1).
Compute unit_unify (UKs * 1 * 2 * 3 * 4).
Compute unit_unify (UKs * 1).
Compute unit_unify (1 * 2 * 3 * 4 * 5).

Compute unit_unify (1 * UKs + 1 * UKm). (* 1s + 1m 是错误的，这里展开形式复杂 *)

(* 看看到底有多复杂，compute太直接了，用交互式模式调试 *)
Lemma ex1 : 1 * UKs + 1 * UKm == 2 *UKs.
Proof.
  unfold unit_unify. simpl.
  remember (unit_cons_base (# 1 * $ UKs + # 1 * $ UKm) # 1 UKs).
  Abort.  (* 太复杂，减小规模 *)

(* 小规模的问题 *)
Compute (unit_cons_base (# 1 * $ UKs + # 1 * $ UKm) # 1 UKs).

(* 还是复杂，继续交互式调试 *)
Lemma ex1 : unit_cons_base (# 1 * $ UKs + # 1 * $ UKm) # 1 UKs = 1.
Proof.
  unfold unit_cons_base.
  Compute ((unit_count_kind (# 1 * $ UKs + # 1 * $ UKm)%unit UKs)).
  (* 原来问题出在这里，返回了 999，所以会有很多层循环，看不到了。
    这种默认值的处理，没有 option 优雅，但是简洁一些。
    那么，如果恰好有个 999 的量纲，也许就错误了！！ *)
  Abort.


(** A convenient tactic for solve unit equivalence judgement *)
Ltac solve_ueq :=
  compute;    (* u -> quant *)
  f_equal;    (* quant -> R*)
  try field.      (* solve R equation *)

(** * Concrete units *)

Open Scope Unit_scope.

(** Time *)
Definition second := $ UKs.
Notation "'s" := (second) (at level 0).

Definition millisecond x := x * 0.001 * 's.
Notation "'ms" := (millisecond 1) (at level 0).

Definition minute x := x * 60 * 's.
Notation "'min" := (minute 1) (at level 0).

Definition hour x := x * 60 * 'min.
Notation "'h" := (hour 1) (at level 0).

Definition day x := x * 24 * 'h.
Notation "'d" := (day 1) (at level 0).

Global Hint Unfold millisecond minute hour day : unit.

Compute unit_unify (1000 * 500 * 's * 'h).

Compute (60 * (1 * UKs)).
Compute (1 * UKs).

Lemma second_millisecond : 'h == 3600 * 's.
Proof. solve_ueq. Qed.

Example timeunit_ex1 : 1.5 * 's == 1500 * 'ms.
Proof. solve_ueq. Qed.

(** Length *)

Definition metre := $ UKm.
Notation "'m" := (metre) (at level 0).

Definition killometre x := x * 1000 * 'm.
Notation "'km" := (killometre 1) (at level 0).

Definition millimetre x := x * 0.001 * 'm.
Notation "'mm" := (millimetre 1) (at level 0).

Global Hint Unfold killometre millimetre : unit.

(** Mass *)

Definition killogram := $ UKkg.
Notation "'kg" := (killogram) (at level 0).

Definition gram x := x * 0.001 * 'kg.
Notation "'g" := (gram 1) (at level 0).

(** Electric current *)

Definition ampere := $ UKA.
Notation "'A" := (ampere) (at level 0).

Definition milliampere x := x * 0.001 * 'A.
Notation "'mA" := (milliampere 1) (at level 0).

(** Temperature *)

(* Notice, temperature unit is different with other units *)
Definition kelvin := $ UKK.
Notation "'K" := (kelvin) (at level 0).

(*   (* Notice, Celisus is very different, need an offset. *)
Definition celsius x := (x + 273.15) * $Temperature.
Notation "x '℃" := (celsius x) (at level 0).

Example tempunit_ex1 : 2 '℃ = 275.15 'K.
Proof.
  unfold celsius,kelvin. autorewrite with unit.
  repeat f_equal. compute;field. 
Qed. *)

(** Amount of substance *)

Definition mole := $ UKmol.
Notation "'mol" := (mole) (at level 0).

(** Luminous intensity *)

Definition candela :=  UKcd.
Notation "'cd" := (candela) (at level 0).


(** * Exercises *)

(* 4 m^2 = 2m * 2m *)
Example ex_area_4m2_eq : 4 * 'm² == (2 * 'm) * (2 * 'm).
Proof. solve_ueq. Qed.

(* 1 m + 1 m = 2 m *)
Example ex2 : 'm + 'm == 2 * 'm.
Proof. solve_ueq. Qed.

(* 2 m * 3 m = 6 m^2 *)
Example ex3 : (2 * 'm) * (3 * 'm) == 6 * ('m²).
Proof. solve_ueq. Qed.


(* Derived units with special ames in the SI *)
Module DerivedUnits.
  
  (* plane angle, 平面角（弧度）, 1 rad = m / m = 1 *)
  Definition radian (x : R) := x * 'm / 'm.
  Notation "'rad" := (radian 1) (at level 0).
  Global Hint Unfold radian : unit.
  
  Lemma radian_rule : 'rad == 1.
  Proof. solve_ueq. Qed.
  
  (* solid angle, 立体角（球面度），1 sr = 1 m^2/m^2 = 1 *)
  Definition steradian (x : R) := x * 'm² / 'm².
  Notation "'sr" := (steradian 1) (at level 0).
  
  Lemma steradian_rule : 'sr == 1.
  Proof. solve_ueq. Qed.
  
  (* frequency, 频率（赫兹），1 Hz = 1/s *)
  Definition herz (x : R) := x / 's.
  Notation "'Hz" := (herz 1) (at level 0).
  
  (* force, 力（牛顿）, 1 N = 1 kg*m/s^2 *)
  Definition newton (x : R) := x * 'kg * 'm / 's².
  Notation "'N" := (newton 1) (at level 0).
  
  (* pressure,stress, 压力/压强/应力(帕斯卡), 1 Pa = 1N/m^2 = 1 kg/m/s^2 *)
  Definition pascal (x : R) := x * 'N / 'm².
  Notation "'Pa" := (pascal 1) (at level 0).
  
  Lemma pascal_rule : 'Pa == 'kg / 'm / 's².
  Proof. solve_ueq. Qed.
  
  (* energy,work,amout of heart,能[量]/功/热量(焦耳), 1J=1N*m = 1kg*m^2/s^2 *)
  Definition joule (x : R) := x * 'N * 'm.
  Notation "'J" := (joule 1) (at level 0).
  
  Lemma joule_rule : 'J == 'kg * 'm² / 's².
  Proof. solve_ueq. Qed.
  
  (* power,radiant flux, 功率,辐射[能]通量(瓦特), 1W=1J/s=1kg*m^2/s^3 *)
  Definition power (x : R) := x * 'J / 's.
  Notation "'W" := (power 1) (at level 0).
  
  Lemma power_rule : 'W == 'kg * 'm² / 's³.
  Proof. solve_ueq. Qed.
  
  (* electric charge,电荷[量](库仑), 1C=1A*s *)
  Definition coulomb (x : R) := x * 'A * 's.
  Notation "'C" := (coulomb 1) (at level 0).
  
  (* electric potential difference,电势差/电压(伏特), 1V=1W/A=1kg*m^2/s^3/A *)
  Definition volt (x : R) := x * 'W / 'A.
  Notation "'V" := (volt 1) (at level 0).
  
  Lemma volt_rule : 'V == 'kg * 'm² / 's³ / 'A.
  Proof. solve_ueq. Qed.
  
  (* capacitance,电容(法拉), 1F=1C/V=1/kg/m^2 *s^4*A^2 *)
  Definition farad (x : R) := x * 'C / 'V.
  Notation "'F" := (farad 1) (at level 0).
  
  Lemma farad_rule : 'F == / 'kg / 'm² * 's⁴ * 'A².
  Proof. solve_ueq. Qed.
  
  (* electric resistance,电阻(欧姆), 1Ω=1V/A=1kg*m^2/s^3/A^2 *)
  Definition ohm (x : R) := x * 'V / 'A.
  Notation "'Ω" := (ohm 1) (at level 0).
  
  Lemma ohm_rule : 'Ω == 'kg * 'm² / 's³ / 'A².
  Proof. solve_ueq. Qed.
  
  (* electric conductance,电导(西门子),1S=1A/V=1/kg*m^2*s^3*A^2 *)
  Definition siemens (x : R) := x * 'A / 'V.
  Notation "'S" := (siemens 1) (at level 0).
  
  Lemma siemens_rule : 'S == /'kg / 'm² * 's³ * 'A².
  Proof. solve_ueq. Qed.
  
  (* magnetic flux,磁通[量](韦伯),1Wb=1V*s=1kg*m^2/s^2/A *)
  Definition weber (x : R) := x * 'V * 's.
  Notation "'Wb" := (weber 1) (at level 0).
  
  Lemma weber_rule : 'Wb == 'kg * 'm² / 's² / 'A.
  Proof. solve_ueq. Qed.
  
  (* magnetic flux density,磁通密度/磁感应强度(特斯拉),1T=1Wb/m^2=1kg/s^2/A *)
  Definition tesla (x : R) := x * 'Wb / 'm².
  Notation "'T" := (tesla 1) (at level 0).
  
  Lemma tesla_rule : 'T == 'kg / 's² / 'A.
  Proof. solve_ueq. Qed.
  
  (* inductance,电感(亨利), 1H=1Wb/A=1kg*m^2/s^2/A^2 *)
  Definition henry (x : R) := x * 'Wb / 'A.
  Notation "'H" := (henry 1) (at level 0).
  
  Lemma henry_rule : 'H == 'kg * 'm² / 's² / 'A².
  Proof. solve_ueq. Qed.

End DerivedUnits.





