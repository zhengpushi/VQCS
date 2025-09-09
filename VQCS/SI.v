(*
  Copyright 2024 ***
  This file is part of VQCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : International System of Unit (SI).
  author    : ***
  date      : 2021.05

  remark    :
  1. About power of `R` type:
     * Power of `R` has three functions:
       pow: R -> nat -> R           `lra` is ok (need `simpl` first)
       powerRZ: R -> Z -> R         `lra` is ok (need `simpl` first)
       Rpower: R -> R -> R          `lra` dont' support
     * `x ^ n` is the notation of `pow:R->nat->R`, and is also the notation of
       `Upow:Unit->Z->Unit`
     * About "10^3" and "1e3", or "/(10^3)" and "1e-3"
       * When talking about Q and R type,
         10^-3 = Q2R 0.001, 0.001 = Q2R 0.001, 1e-3 = Rdiv 1 1000, they are equal.
         But, Q2R is not supported by "ring/field", although "lra" is working.
         Contrast to `1e-3`, it is both supported by "ring/field/lra"
       * When talking about Unit type, "/(10^3)" is "Uinv (Upow (Unone 10) 3)",
         "1e-3" is "Unone (1e-3)". So "1e-3" is simpler.
       * So, "1e3" is better than "10^3", and "1e-3" is better than "/(10^3)"
         and "0.001". Thus, we use scientific notations whenever possible, e
         specially if values contain decimals.
.
  2. Coding style for `R` type:
     `6.626_070_15e-34` is a better style, because:
     * There are `dash` seperate 626, 070 and 15 every three digits
     * It has the same notation as scientific notation
*)

Require Export Nunit.

(** Create a new scope, to manage the valid domain of symbols. *)
Declare Scope SI_scope.
Delimit Scope SI_scope with SI.
Open Scope SI.

(* ======================================================================= *)
(** ** Decimal multiples and sub-multiples of SI *)
Module SI_Prefix.

  Definition deca (u : Unit) : Unit := 1e1 * u.
  Definition hecto (u : Unit) : Unit := 1e2 * u.
  Definition kilo (u : Unit) : Unit := 1e3 * u.
  Definition mega (u : Unit) : Unit := 1e6 * u.
  Definition giga (u : Unit) : Unit := 1e9 * u.
  Definition tera (u : Unit) : Unit := 1e12 * u.
  Definition peta (u : Unit) : Unit := 1e15 * u.
  Definition exa (u : Unit) : Unit := 1e18 * u.
  Definition zetta (u : Unit) : Unit := 1e21 * u.
  Definition yotta (u : Unit) : Unit := 1e24 * u.
  Notation "'_da' x" :=
    (deca x) (at level 5, right associativity, format "'_da' x") : SI_scope.
  Notation "'_h' x" :=
    (hecto x) (at level 5, right associativity, format "'_h' x") : SI_scope.
  Notation "'_k' x" :=
    (kilo x)  (at level 5, right associativity, format "'_k' x") : SI_scope.
  Notation "'_M' x" :=
    (mega x)  (at level 5, right associativity, format "'_M' x") : SI_scope.
  Notation "'_G' x" :=
    (giga x)  (at level 5, right associativity, format "'_G' x") : SI_scope.
  Notation "'_T' x" :=
    (tera x)  (at level 5, right associativity, format "'_T' x") : SI_scope.
  Notation "'_P' x" :=
    (peta x)  (at level 5, right associativity, format "'_P' x") : SI_scope.
  Notation "'_E' x" :=
    (exa x)   (at level 5, right associativity, format "'_E' x") : SI_scope.
  Notation "'_Z' x" :=
    (zetta x) (at level 5, right associativity, format "'_Z' x") : SI_scope.
  Notation "'_Y' x" :=
    (yotta x) (at level 5, right associativity, format "'_Y' x") : SI_scope.
  
  Definition deci (u : Unit) : Unit := 1e-1 * u.
  Definition centi (u : Unit) : Unit := 1e-2 * u.
  Definition milli (u : Unit) : Unit := 1e-3 * u.
  Definition micro (u : Unit) : Unit := 1e-6 * u.
  Definition nano (u : Unit) : Unit := 1e-9 * u.
  Definition pico (u : Unit) : Unit := 1e-12 * u.
  Definition femto (u : Unit) : Unit := 1e-15 * u.
  Definition atto (u : Unit) : Unit := 1e-18 * u.
  Definition zepto (u : Unit) : Unit := 1e-21 * u.
  Definition yocto (u : Unit) : Unit := 1e-24 * u.
  Notation "'_d' x" :=
    (deci x)  (at level 5, right associativity, format "'_d' x") : SI_scope.
  Notation "'_c' x" :=
    (centi x) (at level 5, right associativity, format "'_c' x") : SI_scope.
  Notation "'_m' x" :=
    (milli x) (at level 5, right associativity, format "'_m' x") : SI_scope.
  Notation "'_μ' x" :=
    (micro x) (at level 5, right associativity, format "'_μ' x") : SI_scope.
  Notation "'_n' x" :=
    (nano x)  (at level 5, right associativity, format "'_n' x") : SI_scope.
  Notation "'_p' x" :=
    (pico x)  (at level 5, right associativity, format "'_p' x") : SI_scope.
  Notation "'_f' x" :=
    (femto x) (at level 5, right associativity, format "'_f' x") : SI_scope.
  Notation "'_a' x" :=
    (atto x)  (at level 5, right associativity, format "'_a' x") : SI_scope.
  Notation "'_z' x" :=
    (zepto x) (at level 5, right associativity, format "'_z' x") : SI_scope.
  Notation "'_y' x" :=
    (yocto x) (at level 5, right associativity, format "'_y' x") : SI_scope.

End SI_Prefix.


(** ** 7 basic unit of SI. *)
Module SI_Basic.

  (** Time *)
  Definition second := BUTime.
  Notation "'s" := (second) (at level 5) : SI_scope.

  (** Length *)
  Definition metre := BULength.
  Notation "'m" := (metre) (at level 5) : SI_scope.

  (** Mass *)
  Definition killogram := BUMass.
  Notation "'kg" := (killogram) (at level 5) : SI_scope.
  
  (** Electric current *)
  Definition ampere := BUElectricCurrent.
  Notation "'A" := (ampere) (at level 5) : SI_scope.
  
  (** Temperature *)
  Definition kelvin := BUThermodynamicTemperature.
  Notation "'K" := (kelvin) (at level 5) : SI_scope.
  
  (** Amount of substance *)
  Definition mole := BUAmountOfSubstance.
  Notation "'mol" := (mole) (at level 5) : SI_scope.
  
  (** Luminous intensity *)
  Definition candela := BULuminousIntensity.
  Notation "'cd" := (candela) (at level 5) : SI_scope.

End SI_Basic.


(** ** 22 derived units of SI *)
Module SI_Derived.
  Export SI_Basic.

  (* plane angle, 平面角（弧度）, 1 rad = m / m = 1 *)
  Definition radian := 'm / 'm.
  Notation "'rad" := (radian) (at level 5) : SI_scope.
    
  Lemma radian_spec : 'rad == 1.
  Proof. ueq. Qed.
  
  (* solid angle, 立体角（球面度），1 sr = 1 m^2/m^2 = 1 *)
  Definition steradian := 'm² / 'm².
  Notation "'sr" := (steradian) (at level 5) : SI_scope.

  Lemma steradian_spec : 'sr == 1.
  Proof. ueq. Qed.
  
  (* frequency, 频率（赫兹），1 Hz = 1/s *)
  Definition herz := / 's.
  Notation "'Hz" := (herz) (at level 5) : SI_scope.
  
  (* Hza is a unit of frequency Hertz defined in terms of angular velocity. *)
  (* This idea is come from `PTC Mathcad unit` *)
  Definition herza := (2 * PI)%R / 's.
  Notation "'Hza" := (herza) (at level 5) : SI_scope.
  
  (* force, 力（牛顿）, 1 N = 1 kg*m/s^2 *)
  Definition newton := 'kg * 'm * (/'s²).
  Notation "'N" := (newton) (at level 5) : SI_scope.
  
  (* pressure,stress, 压力/压强/应力(帕斯卡), 1 Pa = 1N/m^2 = 1 kg/m/s^2 *)
  Definition pascal := 'kg * (/'m) * (/'s²).
  Notation "'Pa" := (pascal) (at level 5) : SI_scope.
  
  Lemma pascal_spec : 'Pa == 'N / 'm².
  Proof. ueq. Qed.
  
  (* energy,work,amout of heart,能[量]/功/热量(焦耳), 1J=1N*m = 1kg*m^2/s^2 *)
  Definition joule := 'kg * 'm² * (/'s²).
  Notation "'J" := (joule) (at level 5) : SI_scope.
  
  Lemma joule_spec : 'J == 'N * 'm.
  Proof. ueq. Qed.
  
  Lemma pascal_spec2 : 'Pa == 'J / 'm³.
  Proof. ueq. Qed.
  
  (* power,radiant flux, 功率,辐射[能]通量(瓦特), 1W=1J/s=1kg*m^2/s^3 *)
  Definition watt := 'kg * 'm² * (/'s³).
  Notation "'W" := (watt) (at level 5) : SI_scope.
  
  Lemma power_spec : 'W == 'J * (/'s).
  Proof. ueq. Qed.
  
  (* electric charge,电荷[量](库仑), 1C=1A*s *)
  Definition coulomb := 'A * 's.
  Notation "'C" := (coulomb) (at level 5) : SI_scope.
  
  (* electric potential difference,电势差/电压(伏特), 1V=1W/A=1kg*m^2/s^3/A *)
  Definition volt := 'kg * 'm² * (/'s³) * (/'A).
  Notation "'V" := (volt) (at level 5) : SI_scope.
  
  Lemma volt_spec : 'V == 'W / 'A.
  Proof. ueq. Qed.

  (* (N.m)/A = V.s *)
  Example N_m_A_V_s : ('N * 'm) / 'A == 'V * 's.
  Proof. ueq. Qed.
  
  (* capacitance,电容(法拉), 1F=1C/V=1/kg/m^2 *s^4*A^2 *)
  Definition farad := (/'kg) * (/'m²) * 's⁴ * 'A².
  Notation "'F" := (farad) (at level 5) : SI_scope.
  
  Lemma farad_spec : 'F == 'C / 'V.
  Proof. ueq. Qed.
  
  (* electric resistance,电阻(欧姆), 1Ω=1V/A=1kg*m^2/s^3/A^2 *)
  Definition ohm := 'kg * 'm² * (/'s³) * (/'A²).
  Notation "'Ω" := (ohm) (at level 5) : SI_scope.
  
  Lemma ohm_spec : 'Ω == 'V / 'A.
  Proof. ueq. Qed.
  
  (* electric conductance,电导(西门子),1S=1A/V=1/kg*m^2*s^3*A^2 *)
  Definition siemens := (/'kg) * (/'m²) * 's³ * 'A².
  Notation "'S" := (siemens) (at level 5) : SI_scope.
  
  Lemma siemens_spec : 'S == 'A / 'V.
  Proof. ueq. Qed.
  
  (* magnetic flux,磁通[量](韦伯),1Wb=1V*s=1kg*m^2/s^2/A *)
  Definition weber := 'kg * 'm² * (/'s²) * (/'A).
  Notation "'Wb" := (weber) (at level 5) : SI_scope.
  
  Lemma weber_spec : 'Wb == 'V * 's.
  Proof. ueq. Qed.
  
  (* magnetic flux density,磁通密度/磁感应强度(特斯拉),1T=1Wb/m^2=1kg/s^2/A *)
  Definition tesla := 'kg * (/'s²) * (/'A).
  Notation "'T" := (tesla) (at level 5) : SI_scope.
  
  Lemma tesla_spec : 'T == 'Wb / 'm².
  Proof. ueq. Qed.
  
  (* inductance,电感(亨利), 1H=1Wb/A=1kg*m^2/s^2/A^2 *)
  Definition henry := 'kg * 'm² * (/'s²) * (/'A²).
  Notation "'H" := (henry) (at level 5) : SI_scope.
  
  Lemma henry_spec : 'H == 'Wb / 'A.
  Proof. ueq. Qed.
  
  (* Celsius temperature, 摄氏温度(摄氏度),1℃=1K *)
  (* This is a special case, which described in another module below. *)
  
  (* luminous flux,光通量（流明），lm=cd sr *)
  Definition lumen := 'cd * 'sr.
  Notation "'lm" := (lumen) (at level 5) : SI_scope.
  
  (* illuminance，照度（勒克斯），1lx=1cd*sr/m^2=1lm/m^2 *)
  Definition lux := 'cd * 'sr * (/'m²).
  Notation "'lx" := (lux) (at level 5) : SI_scope.
  
  Lemma lux_spec : 'lx == 'lm / 'm².
  Proof. ueq. Qed.
  
  (* activity referred to a radionuclide，放射性活度（贝克勒尔），1Bq=/s *)
  Definition becquerel := /'s.
  Notation "'Bq" := (becquerel) (at level 5) : SI_scope.
  
  (* absorbed dose, kerma，电离辐射能量吸收剂量（格瑞），Gy=m^2/s^2=J/kg *)
  Definition gray := 'm² / 's².
  Notation "'Gy" := (gray) (at level 5) : SI_scope.
  
  Lemma gray_spec : 'Gy == 'J / 'kg.
  Proof. ueq. Qed.
  
  (* dose equivalent，受辐射等效生物当量（西弗），Sv=m^2/s^2=J/kg *)
  Definition sievert := 'm² / 's².
  Notation "'Sv" := (sievert) (at level 5) : SI_scope.
  
  Lemma sievert_spec : 'Sv == 'J / 'kg.
  Proof. ueq. Qed.
  
  (* catalytic activity, 催化活性(开特），kat=mol/s *)
  Definition katal := 'mol / 's.
  Notation "'kat" := (katal) (at level 5) : SI_scope.

End SI_Derived.

(* Export SI_Derived. *)

(** ** Temperature and Temperature Difference *)
(**
<<
   Note that there are two types of temperature units:
   1. (Absolute) Temperature. The reference point is 0K (Absolute Zero).
      a. Kelvin, 1 K = 1 [K]
      b. Celsius, x ℃ = (273.15 + x) [K]
      c. Fahrenheit, x ℉ = ((x - 32) / 1.8 + 273.15) [K]
   2. Temperature Difference.
      a. Delta Kelvin, x DeltaK = x [K]
      b. Delta Celsius, x DeltaC = x [K]
      c. Delta Fahrenheit, x DeltaF = (x/1.8) [K]
   3. Conversion
	  kel2cel x := x - 273.15
	  cel2kel x := x + 273.15
      cel2fah x := x * 1.8 + 32
	  fah2cel x := (x - 32) / 1.8
	  fah2kel x := (x - 32) / 1.8 + 273.15
	  kel2fah x := (x - 273.15) * 1.8 + 32
>>
*)
Module Temperature_TemperatureDifference.
  Export SI_Basic.

  (** *** Conversion between temperature unit on `R` type *)

  Definition cel2kelR (x : R) : R := x + 273.15.
  Definition kel2celR (x : R) : R := x - 273.15.
  
  Definition cel2fahR (x : R) : R := x * 1.8 + 32.
  Definition fah2celR (x : R) : R := (x - 32) / 1.8.
  
  Definition kel2fahR (x : R) : R := (x - 273.15) * 1.8 + 32.
  Definition fah2kelR (x : R) : R := (x - 32) / 1.8 + 273.15.

  (* Solve equation of `temperature unit` *)
  Local Ltac solve_tempUnit := intros; autounfold with unit; field; lra.

  (* [kel2celR] o [cel2kelR] = id *)
  Lemma kel2celR_cel2kelR_id : forall x, kel2celR (cel2kelR x) = x.
  Proof. intros; cbv; lra. Qed.
  (* [cel2kelR] o [kel2celR] = id *)
  Lemma cel2kelR_kel2celR_id : forall x, cel2kelR (kel2celR x) = x.
  Proof. intros; cbv; lra. Qed.
  
  Lemma fah2celR_cel2fahR_id : forall x, fah2celR (cel2fahR x) = x.
  Proof. intros; cbv; lra. Qed.
  Lemma cel2fahR_fah2celR_id : forall x, cel2fahR (fah2celR x) = x.
  Proof. intros; cbv; lra. Qed.
  
  Lemma fah2kelR_kel2fahR_id : forall x, fah2kelR (kel2fahR x) = x.
  Proof. intros; cbv; lra. Qed.
  Lemma kel2fahR_fah2kelR_id : forall x, kel2fahR (fah2kelR x) = x.
  Proof. intros; cbv; lra. Qed.

  (* [kel2fahR] is consistent with [kel2celR] and [cel2fahR] *)
  Lemma kel2fahR_spec : forall x, kel2fahR x = cel2fahR (kel2celR x).
  Proof. intros; cbv; lra. Qed.
  (* [fah2kelR] is consistent with [fah2celR] and [cel2kelR] *)
  Lemma fah2kelR_spec : forall x, fah2kelR x = cel2kelR (fah2celR x).
  Proof. intros; cbv; lra. Qed.

  
  (** *** Definition of temperature difference unit on `R` type *)
  Definition deltaKel (x : R) : R := x.
  Definition deltaCel (x : R) : R := x.
  Definition deltaFah (x : R) : R := (x / 1.8).

  (* [deltaKel] is consistent with [K] *)
  Lemma deltaKel_spec : forall x y, x + (deltaKel y) = x + y.
  Proof. intros; cbv; lra. Qed.
  (* [deltaCel] is consistent with [cel2kelR] *)
  Lemma deltaCel_spec : forall x y, cel2kelR x + (deltaCel y) = cel2kelR (x + y).
  Proof. intros; cbv; lra. Qed.
  (* [deltaFah] is consistent with [fah2kelR] *)
  Lemma deltaFah_spec : forall x y, fah2kelR x + (deltaFah y) = fah2kelR (x + y).
  Proof. intros; cbv; lra. Qed.

  
  (** *** Definition of temperature unit on `Unit` type *)

  (* Absolute temperature (Celsius) *)
  Definition temperatureCel (x : R) : Unit := (cel2kelR x) * 'K.
  Notation "x '℃" := (temperatureCel x) (at level 5) : SI_scope.
  
  (* [temperatureCel] is consistent with [cel2kelR] *)
  Lemma temperatureCel_spec : forall x, ucoef (temperatureCel x) = cel2kelR x.
  Proof. intros; cbv; lra. Qed.

  (* Absolute temperature (Fahrenheit) *)
  Definition temperatureFah (x : R) : Unit := (fah2kelR x) * 'K.
  Notation "'℉" := (temperatureFah) (at level 5) : SI_scope.
  
  (* [temperatureFah] is consistent with [fah2kelR] *)
  Lemma temperatureFah_spec : forall x, ucoef (temperatureFah x) = fah2kelR x.
  Proof. intros; cbv; lra. Qed.

  (* Temperature difference (Kelvin) *)
  Definition temperatureDiffKel (x : R) : Unit := (deltaKel x) * 'K.
  Notation "x 'ΔK" := (temperatureDiffKel x) (at level 5) : SI_scope.
  
  (* [temperatureDiffKel] is consistent with [deltaKel] *)
  Lemma temperatureDiffKel_spec : forall x, ucoef (temperatureDiffKel x) = deltaKel x.
  Proof. intros; cbv; lra. Qed.

  (* Temperature difference (Celsius) *)
  Definition temperatureDiffCel (x : R) : Unit := (deltaCel x) * 'K.
  Notation "x 'Δ℃" := (temperatureDiffCel x) (at level 5) : SI_scope.
  
  (* [temperatureDiffCel] is consistent with [deltaCel] *)
  Lemma temperatureDiffCel_spec : forall x, ucoef (temperatureDiffCel x) = deltaCel x.
  Proof. intros; cbv; lra. Qed.
  
  (* Temperature difference (Fahrenheit) *)
  Definition temperatureDiffFah (x : R) : Unit := (deltaFah x) * 'K.
  Notation "x 'Δ℉" := (temperatureDiffFah x) (at level 5) : SI_scope.
  
  (* [temperatureDiffFah] is consistent with [deltaFah] *)
  Lemma temperatureDiffFah_spec : forall x, ucoef (temperatureDiffFah x) = deltaFah x.
  Proof. intros; cbv; lra. Qed.

  Section test.
    Local Lemma ex1 : 30 '℃ == 303.15 * 'K.
    Proof. ueq. Qed.

    (* 20 ℃ + 5 Δ℃ = 25 ℃ *)
    (* Let ex2 : 20 '℃ + 5 'Δ℃ == 25 '℃. *)
    (* Note that, `Addition` is defined on `Quantity`, not `Unit` *)
  End test.
End Temperature_TemperatureDifference.


(** ** Non-SI units that are accepted for use with the SI *)
Module SI_Accepted.
  Export SI_Derived.

  Definition millisecond := 1e-3 * 's.
  Notation "'ms" := (millisecond) (at level 5) : SI_scope.
  
  Lemma second_millisecond : 's == 1e3 * 'ms.
  Proof. ueq. Qed.

  Definition killometre := 1e3 * 'm.
  Notation "'km" := (killometre) (at level 5) : SI_scope.
  
  Definition centmetre := 1e-2 * 'm.
  Notation "'cm" := (centmetre) (at level 5) : SI_scope.
  
  Definition millimetre := 1e-3 * 'm.
  Notation "'mm" := (millimetre) (at level 5) : SI_scope.
  
  Definition gram := 1e-3 * 'kg.
  Notation "'g" := (gram) (at level 5) : SI_scope.
  
  Definition milliampere := 1e-3 * 'A.
  Notation "'mA" := (milliampere) (at level 5) : SI_scope.
  
  Definition minute := 60 * 's.
  Notation "'min" := (minute) (at level 5) : SI_scope.

  Definition hour := 60 * 'min.
  Notation "'hrs" := (hour) (at level 5) : SI_scope.

  Lemma hour2second : 'hrs == 3600 * 's.
  Proof. ueq. Qed.
  
  Definition day := 24 * 'hrs.
  Notation "'d" := (day) (at level 5) : SI_scope.
  
  Lemma day2second : 'd == 86400 * 's.
  Proof. ueq. Qed.
  
  Lemma day2minute : 'd == 1440 * 'min.
  Proof. ueq. Qed.
  
  (** astronomical Unit, 天文单位 *)
  Definition astronomicalUnit := 149_597_870_700 * 'm.
  Notation "'au" := (astronomicalUnit) (at level 5) : SI_scope.
  
  (** plane and phase angle, 平面角、相位角 *)
  Definition degree_angle := PI/180 * 'rad.
  Notation "'ᵒ" := (degree_angle) (at level 5) : SI_scope.
  
  (** area(hectare), 面积（公顷），=100m*100m *)
  Definition hectare := 1e4 * 'm².
  Notation "'ha" := (hectare) (at level 5) : SI_scope.
  
  (** volume(litre), 体积（升），= 1dm^3 = 10^3 cm^3 = 10^{-3} m^3 *)
  Definition litre := 1e-3 * 'm³.
  Notation "'L" := (litre) (at level 5) : SI_scope.

  (** mass(tonne), 质量（吨） *)
  Definition tonne := 1e3 * 'kg.
  Notation "'t" := (tonne) (at level 5) : SI_scope.

  (** mass(dalton), 质量（道尔顿） *)
  Definition dalton := (1.660_539_066_60*(/10^27)) * 'kg.
  Notation "'Da" := (dalton) (at level 5) : SI_scope.

  (** energy(electronical voltage), 能量（电子伏） *)
  Definition electronvolt := (1.602_176_634*(/10^27)) * 'J.
  Notation "'eV" := (electronvolt) (at level 5) : SI_scope.
  
  (** round speed, round per minute *)
  Definition round_per_minute := (2 * PI)%R /'min.
  Notation "'rpm" := (round_per_minute) (at level 5) : SI_scope.

  (* (N.m)/A = 60(V/rpm) *)
  Example N_m_A_V_rpm : ('N * 'm) / 'A == ((2*PI) / 60) * ('V / 'rpm).
  Proof. ueq. ra. Qed.
  
  (** battery capacity *)
  Definition milli_amper_hour := 'mA * 'hrs.
  Notation "'mAh" := (milli_amper_hour) (at level 5) : SI_scope.
  
End SI_Accepted.


(** ** The 7 defining constants of SI *)
Module SI_Constants.
  Export SI_Derived.
  
  (** hyperfine transition frequency of Cs，铯原子能级跃迁辐射频率 *)
  Definition hyper_trans_freq_of_Cs := 9_192_631_770 * 'Hz.
  Notation "'ΔV" := (hyper_trans_freq_of_Cs) (at level 5) : SI_scope.
  
  (** speed of light in vaccum，真空中光速 *)
  Definition speed_of_light_in_vaccum := 299_792_458 * ('m/'s).
  Notation "'c" := (speed_of_light_in_vaccum) (at level 5) : SI_scope.
  
  (** Planck constant，普朗克常量 *)
  Definition planck_constant := 6.626_070_15e-34 * ('J*'s).
  Notation "'h" := (planck_constant) (at level 5) : SI_scope.
  
  (** elementary charge，元电荷 *)
  Definition elementary_charge := 1.602_176_634e-19 * 'C.
  Notation "'e" := (elementary_charge) (at level 5) : SI_scope.
  
  (** Boltzmann constant，玻尔兹曼常数 *)
  Definition boltzmann_constant := 1.380_649e-23 * ('J/'K).
  Notation "'k" := (boltzmann_constant) (at level 5) : SI_scope.
  
  (** Avogadro constant，阿伏伽德罗常数 *)
  Definition avogadro_constant  := 6.022_140_76e23 * (/'mol).
  Notation "'NA" := (avogadro_constant) (at level 5) : SI_scope.
  
  (** luminous efficacy，最大发光效能 *)
  Definition luminous_efficacy := 683 * 'lm * (/'W).
  Notation "'Kcd" := (luminous_efficacy) (at level 5) : SI_scope.
  
End SI_Constants.


(** ** Verify consistency between defining constants and basic unit *)
Module SI_Constants_spec.
  Export SI_Constants.

  (** Tactic for proof unit approximate reletion. *)
  Ltac uapprox :=
    unfold unit_approx; simpl; split; auto;
    (* solve Rapprox with constant value *)
    unfold Rapprox;
    match goal with
    | |- (Rabs ?r1 <= ?r2)%R => unfold Rabs; destruct Rcase_abs; lra
    end.
  
  (** Properties about second *)
  Lemma Hz_def : 1 * 'Hz == 'ΔV / 9_192_631_770.
  Proof. ueq. Qed.
  
  Lemma s_def : 1 * 's == 9_192_631_770 / 'ΔV.
  Proof. ueq. Qed.
  
  (** Properties about metre *)
  Lemma m_def1 : 1 * 'm == ('c / 299_792_458) * 's.
  Proof. ueq. Qed.

  Lemma m_def2 : 1 * 'm == (9_192_631_770 / 299_792_458) * ('c / 'ΔV).
  Proof. ueq. Qed.
  
  Lemma m_def3 : unit_approx (1 * 'm) (30.663319 * ('c/'ΔV)) 1e-9.
  Proof. uapprox. Qed.
  
  (** Properties about kilogram *)
  Lemma kg_def1 : 1 * 'kg == 
    ('h / (6.62607015e-34)) * ((/'m²)*'s).
  Proof. ueq. Qed.
  
  Lemma kg_def2 : 1 * 'kg == 
    ((299792458)² / (6.62607015e-34 * 9192631770)) *
    (('h * 'ΔV) / ('c²)).
  Proof. ueq. Qed.
  
  Lemma kg_def3 : unit_approx (1 * 'kg)
    ((1.4755214e40) * (('h * 'ΔV) / ('c²))) 1e-9.
  Proof. uapprox. Qed.
  
  (** Properties about ampere *)
  Lemma A_def1 : 1 * 'A == ('e / 1.602176634e-19) * (/'s).
  Proof. ueq. Qed.
  
  Lemma A_def2 : 1 * 'A == (/(9192631770 * 1.602176634e-19)) * ('ΔV * 'e).
  Proof. ueq. Qed.
  
  Lemma A_def3 : unit_approx (1 * 'A) (6.7896868e8 * ('ΔV * 'e)) 1e-8.
  Proof. uapprox. Qed.
  
  (** Properties about kelvin *)
  Lemma kelvin_def1 : 1 * 'K == (1.380649e-23 /'k) * ('kg * 'm² * (/'s²)).
  Proof. ueq. Qed.
  
  Lemma kelvin_def2 : 1 * 'K == (1.380649e-23 / (6.62607015e-34 * 9192631770))
                                * ('ΔV * 'h * (/'k)).
  Proof. ueq. Qed.
  
  Lemma kelvin_def3 : unit_approx (1*'K) (2.2666653 * ('ΔV * 'h * (/'k))) 1e-7.
  Proof. uapprox. Qed.
  
  (** Properties about mole *)
  Lemma mol_def : 1 * 'mol == 6.02214076e23 / 'NA.
  Proof. ueq. Qed.
  
  (** Properties about candela *)
  Lemma cd_def1 : 1 * 'cd == ('Kcd/683) * ('kg * 'm² * (/'s³) * (/'sr)).
  Proof. ueq. Qed.
  
  Lemma cd_def2 : 1 * 'cd == 
    (/(6.62607015e-34 * 9192631770² * 683)) * ('ΔV² * 'h * 'Kcd).
  Proof. ueq. Qed.
  
  Lemma cd_def3 : unit_approx (1 * 'cd) (2.6148305e10 * ('ΔV² * 'h * 'Kcd)) 1e-8.
  Proof. uapprox. Qed.

End SI_Constants_spec.


Section test.

  Import SI_Derived.
  Import SI_Accepted.
  Import SI_Prefix.
  Import SI_Constants.

  Section ex1.
    (* https://en.wikipedia.org/wiki/Gas_constant
     在热力学公式 pV = nRT 中，R称为理想气体常数，它有多种单位。见下表
     SI units
   ✓8.31446261815324       J ⋅ K−1 ⋅ mol−1
   ✓8.31446261815324 	    m3 ⋅ Pa ⋅ K−1 ⋅ mol−1
   ✓8.31446261815324 	    kg ⋅ m2 ⋅ s−2 ⋅ K−1 ⋅ mol−1
     Other common units
   ✓8314.46261815324       L ⋅ Pa ⋅ K−1 ⋅ mol−1
   ✓8.31446261815324 	    L ⋅ kPa ⋅ K−1 ⋅ mol−1
   ✓0.0831446261815324 	L ⋅ bar ⋅ K−1 ⋅ mol−1
     8.31446261815324×107 	erg ⋅ K−1 ⋅ mol−1
     1.985875279009 	    BTU ⋅ lbmol−1 ⋅ °R−1
     0.082057366080960 	    L ⋅ atm ⋅ K−1 ⋅ mol−1
     62.363598221529 	    L ⋅ Torr ⋅ K−1 ⋅ mol−1
     1.98720425864083... 	cal ⋅ K−1 ⋅ mol−1
     8.20573660809596...×10−5 	m3 ⋅ atm ⋅ K−1 ⋅ mol−1
     
     其中，
     J      焦耳           能量       已定义
     K      开尔文         温度       已定义
     mol    摩尔           物质地量   已定义
     m      米             长度       已定义
     s      秒             时间       已定义
     L      升             体积       已定义
     Pa     帕斯卡         压强       已定义
     kPa    千帕斯卡       压强       现在定义 = 1000 Pa = 'k 'Pa
     bar    巴             压强       现在定义 = 1e-5 Pa
     mbar   毫巴           压强       现在定义 = 100 kPa = 'h 'kPa
     erh    --             能量       现在定义 = 1e-7 J = 1e-7 * 'J
     atm    一个标准大气压  压强
     *)

    Let killoPa := _k 'Pa.
    Let bar := (1e5) * 'Pa.
    Notation "'bar" := (bar) (at level 5) : SI_scope.
    Let Ru1 : Unit := 'J / 'K / 'mol.
    Let Ru2 : Unit := 'm³ * 'Pa / 'K / 'mol.
    Let Ru3 : Unit := 'kg * 'm² / 's² / 'K / 'mol.
    Let Ru4 : Unit := 1000 * 'L * 'Pa / 'K / 'mol. (* added 1000 *)
    Let Ru5 : Unit := 'L * _k 'Pa / 'K / 'mol.
    Let Ru6 : Unit := 0.01 * 'L * 'bar / 'K / 'mol.

    Goal Ru1 == Ru2. ueq. Qed.
    Goal Ru1 == Ru3. ueq. Qed.
    Goal Ru1 == Ru4. ueq. Qed.
    Goal Ru1 == Ru5. ueq. Qed.
    Goal Ru1 == Ru6. ueq. Qed.
  End ex1.

  Section ex2.
    (** Test the ability that if Coq can handle large numbers.
    In astronomy, where there are some very large numbers involved,
    and Coq can check the equation or inequalities of these numbers *)
    Local Lemma large_number_ex1 : (1.234567e200 * 2.345678e100 = 2.895896651426e300)%R.
    Proof. lra. Qed.

    (* a bigger example *)
    (* Let large_number_ex2 : (1.234567e400 * 2.345678e600 = 2.895896651426e1000)%R. *)
    (* Proof. Time lra. (* 2.417secs *) Qed. *)
    
    (** 天文学中的一个关系式：3.26 light-year <= parsec <= 3.27 light-year *)
    
    (* 儒略年，是一种时间测量单位，定义为 365.25 天 *)
    Let julian_year := 365.25 * day. (* = 3.15576×10⁷ s *)

    (* 光年(符号 ly)，是长度单位，定义为是光在真空中传播一儒略年的距离。*)
    Let light_year := 'c * julian_year. (* = 9.460730473×10¹⁵ *)
    
    (* 天文单位(符号au、AU)，是长度单位，大致等于从地球到太阳的距离。
     最初被认为是地球远日点和近日点的平均值；自 2012 年起，它被准确定义。*)
    Let astronomical_unit := 149597870700 * 'm.
    Notation "'au" := astronomical_unit.
    
    (* 秒差，是一种长度单位，用以测量太阳系以外天体的长度单位。
     秒差的原理使用了三角学，定义为1天文单位的对角为1角秒时的距离。*)
    Let parsec := (648000/PI) * 'au.
    
    (* we need to define <= relation first, use Quantity, not Unit *) 
    (* Let parsec_le_lightyear : parsec <= 3.27 * light_year. *)
    (* Let parsec_ge_lightyear : parsec >= 3.26 * light_year. *)
  End ex2.
  
End test.
