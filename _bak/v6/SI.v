(*
  purpose   : International System of Unit (SI).
  author    : Zhengpu Shi
  date      : 2021.05
*)

Require Export NUnit. 


(** Create a new scope, to manage the valid domain of symbols. *)
Declare Scope SI_scope.
Delimit Scope SI_scope with SI.
Open Scope SI.


(** ** Tactics *)

(** proof unit equality *)
Ltac pfueq :=
  compute;
  f_equal;
  try field.


(** ** Decimal multiples and sub-multiples of SI *)
Module SI_multiples.

  Definition deca : R := 10^1.
  Definition hecto : R := 10^2.
  Definition kilo : R := 10^3.
  Definition mega : R := 10^6.
  Definition giga : R := 10^9.
  Definition tera : R := 10^12.
  Definition peta : R := 10^15.
  Definition exa : R := 10^18.
  Definition zetta : R := 10^21.
  Definition yotta : R := 10^24.
  Notation "'da" := (deca) (at level 5) : SI_scope.
  Notation "'h" := (hecto) (at level 5) : SI_scope.
  Notation "'k" := (kilo) (at level 5) : SI_scope.
  Notation "'M" := (mega) (at level 5) : SI_scope.
  Notation "'G" := (giga) (at level 5) : SI_scope.
  Notation "'T" := (tera) (at level 5) : SI_scope.
  Notation "'P" := (peta) (at level 5) : SI_scope.
  Notation "'E" := (exa) (at level 5) : SI_scope.
  Notation "'Z" := (zetta) (at level 5) : SI_scope.
  Notation "'Y" := (yotta) (at level 5) : SI_scope.
  
  Definition deci : R := /10^1.
  Definition centi : R := /10^2.
  Definition milli : R := /10^3.
  Definition micro : R := /10^6.
  Definition nano : R := /10^9.
  Definition pico : R := /10^12.
  Definition femto : R := /10^15.
  Definition atto : R := /10^18.
  Definition zepto : R := /10^21.
  Definition yocto : R := /10^24.
  Notation "'d" := (deci) (at level 5) : SI_scope.
  Notation "'c" := (centi) (at level 5) : SI_scope.
  Notation "'m" := (milli) (at level 5) : SI_scope.
  Notation "'μ" := (micro) (at level 5) : SI_scope.
  Notation "'n" := (nano) (at level 5) : SI_scope.
  Notation "'p" := (pico) (at level 5) : SI_scope.
  Notation "'f" := (femto) (at level 5) : SI_scope.
  Notation "'a" := (atto) (at level 5) : SI_scope.
  Notation "'z" := (zepto) (at level 5) : SI_scope.
  Notation "'y" := (yocto) (at level 5) : SI_scope.
  
End SI_multiples.

(* Export SI_multiples. *)



(** ** 7 basic unit of SI. *)
Module SI_Basic.

  (** Time *)
  Definition second := [BUTime].
  Notation "'s" := (second) (at level 0) : SI_scope.
  
  (** Length *)
  Definition metre := [BULength].
  Notation "'m" := (metre) (at level 0) : SI_scope.
  
  (** Mass *)
  Definition killogram := [BUMass].
  Notation "'kg" := (killogram) (at level 0) : SI_scope.
  
  (** Electric current *)
  Definition ampere := [BUElectricCurrent].
  Notation "'A" := (ampere) (at level 0) : SI_scope.
  
  (** Temperature *)
  Definition kelvin := [BUThermodynamicTemperature].
  Notation "'K" := (kelvin) (at level 0) : SI_scope.
  
  (** Amount of substance *)
  Definition mole := [BUAmountOfSubstance].
  Notation "'mol" := (mole) (at level 0) : SI_scope.
  
  (** Luminous intensity *)
  Definition candela := [BULuminousIntensity].
  Notation "'cd" := (candela) (at level 0) : SI_scope.

End SI_Basic.

Export SI_Basic.



(** ** 22 derived units of SI *)
Module SI_Derived.

  (* plane angle, 平面角（弧度）, 1 rad = m / m = 1 *)
  Definition radian := 'm / 'm.
  Notation "'rad" := (radian) (at level 0) : SI_scope.
    
  Lemma radian_rule : 'rad == 1.
  Proof. pfueq. Qed.
  
  (* solid angle, 立体角（球面度），1 sr = 1 m^2/m^2 = 1 *)
  Definition steradian := 'm² / 'm².
  Notation "'sr" := (steradian) (at level 0) : SI_scope.

  Lemma steradian_rule : 'sr == 1.
  Proof. pfueq. Qed.
  
  (* frequency, 频率（赫兹），1 Hz = 1/s *)
  Definition herz := / 's.
  Notation "'Hz" := (herz) (at level 0) : SI_scope.
  
  (* force, 力（牛顿）, 1 N = 1 kg*m/s^2 *)
  Definition newton := 'kg * 'm * (/'s²).
  Notation "'N" := (newton) (at level 0) : SI_scope.
  
  (* pressure,stress, 压力/压强/应力(帕斯卡), 1 Pa = 1N/m^2 = 1 kg/m/s^2 *)
  Definition pascal := 'kg * (/'m) * (/'s²).
  Notation "'Pa" := (pascal) (at level 0) : SI_scope.
  
  Lemma pascal_rule : 'Pa == 'N / 'm².
  Proof. pfueq. Qed.
  
  (* energy,work,amout of heart,能[量]/功/热量(焦耳), 1J=1N*m = 1kg*m^2/s^2 *)
  Definition joule := 'kg * 'm² * (/'s²).
  Notation "'J" := (joule) (at level 0) : SI_scope.
  
  Lemma joule_rule : 'J == 'N * 'm.
  Proof. pfueq. Qed.
  
  (* power,radiant flux, 功率,辐射[能]通量(瓦特), 1W=1J/s=1kg*m^2/s^3 *)
  Definition watt := 'kg * 'm² * (/'s³).
  Notation "'W" := (watt) (at level 0) : SI_scope.
  
  Lemma power_rule : 'W == 'J * (/'s).
  Proof. pfueq. Qed.
  
  (* electric charge,电荷[量](库仑), 1C=1A*s *)
  Definition coulomb := 'A * 's.
  Notation "'C" := (coulomb) (at level 0) : SI_scope.
  
  (* electric potential difference,电势差/电压(伏特), 1V=1W/A=1kg*m^2/s^3/A *)
  Definition volt := 'kg * 'm² * (/'s³) * (/'A).
  Notation "'V" := (volt) (at level 0) : SI_scope.
  
  Lemma volt_rule : 'V == 'W / 'A.
  Proof. pfueq. Qed.
  
  (* capacitance,电容(法拉), 1F=1C/V=1/kg/m^2 *s^4*A^2 *)
  Definition farad := (/'kg) * (/'m²) * 's⁴ * 'A².
  Notation "'F" := (farad) (at level 0) : SI_scope.
  
  Lemma farad_rule : 'F == 'C / 'V.
  Proof. pfueq. Qed.
  
  (* electric resistance,电阻(欧姆), 1Ω=1V/A=1kg*m^2/s^3/A^2 *)
  Definition ohm := 'kg * 'm² * (/'s³) * (/'A²).
  Notation "'Ω" := (ohm) (at level 0) : SI_scope.
  
  Lemma ohm_rule : 'Ω == 'V / 'A.
  Proof. pfueq. Qed.
  
  (* electric conductance,电导(西门子),1S=1A/V=1/kg*m^2*s^3*A^2 *)
  Definition siemens := (/'kg) * (/'m²) * 's³ * 'A².
  Notation "'S" := (siemens) (at level 0) : SI_scope.
  
  Lemma siemens_rule : 'S == 'A / 'V.
  Proof. pfueq. Qed.
  
  (* magnetic flux,磁通[量](韦伯),1Wb=1V*s=1kg*m^2/s^2/A *)
  Definition weber := 'kg * 'm² * (/'s²) * (/'A).
  Notation "'Wb" := (weber) (at level 0) : SI_scope.
  
  Lemma weber_rule : 'Wb == 'V * 's.
  Proof. pfueq. Qed.
  
  (* magnetic flux density,磁通密度/磁感应强度(特斯拉),1T=1Wb/m^2=1kg/s^2/A *)
  Definition tesla := 'kg * (/'s²) * (/'A).
  Notation "'T" := (tesla) (at level 0) : SI_scope.
  
  Lemma tesla_rule : 'T == 'Wb / 'm².
  Proof. pfueq. Qed.
  
  (* inductance,电感(亨利), 1H=1Wb/A=1kg*m^2/s^2/A^2 *)
  Definition henry := 'kg * 'm² * (/'s²) * (/'A²).
  Notation "'H" := (henry) (at level 0) : SI_scope.
  
  Lemma henry_rule : 'H == 'Wb / 'A.
  Proof. pfueq. Qed.
  
  (* Celsius temperature,摄氏温度(摄氏度),1℃=1K *)
  Definition degreeCelsius := 'K.
  Notation "'℃" := (degreeCelsius) (at level 0) : SI_scope.
  
  (* luminous flux,光通量（流明），lm=cd sr *)
  Definition lumen := 'cd * 'sr.
  Notation "'lm" := (lumen) (at level 0) : SI_scope.
  
  (* illuminance，照度（勒克斯），1lx=1cd*sr/m^2=1lm/m^2 *)
  Definition lux := 'cd * 'sr * (/'m²).
  Notation "'lx" := (lux) (at level 0) : SI_scope.
  
  Lemma lux_rule : 'lx == 'lm / 'm².
  Proof. pfueq. Qed.
  
  (* activity referred to a radionuclide，放射性活度（贝克勒尔），1Bq=/s *)
  Definition becquerel := /'s.
  Notation "'Bq" := (becquerel) (at level 0) : SI_scope.
  
  (* absorbed dose, kerma，电离辐射能量吸收剂量（格瑞），Gy=m^2/s^2=J/kg *)
  Definition gray := 'm² / 's².
  Notation "'Gy" := (gray) (at level 0) : SI_scope.
  
  Lemma gray_rule : 'Gy == 'J / 'kg.
  Proof. pfueq. Qed.
  
  (* dose equivalent，受辐射等效生物当量（西弗），Sv=m^2/s^2=J/kg *)
  Definition sievert := 'm² / 's².
  Notation "'Sv" := (sievert) (at level 0) : SI_scope.
  
  Lemma sievert_rule : 'Sv == 'J / 'kg.
  Proof. pfueq. Qed.
  
  (* catalytic activity, 催化活性(开特），kat=mol/s *)
  Definition katal := 'mol / 's.
  Notation "'kat" := (katal) (at level 0) : SI_scope.

End SI_Derived.

Export SI_Derived.


(** ** Non-SI units that are accepted for use with the SI *)
Module SI_Accepted.

  Definition millisecond := 0.001 * 's.
  Notation "'ms" := (millisecond) (at level 0) : SI_scope.
  
  Lemma second_millisecond : 's == 1000 * 'ms.
  Proof. pfueq. Qed.
  
  Definition killometre := 1000 * 'm.
  Notation "'km" := (killometre) (at level 0) : SI_scope.
  
  Definition millimetre := 0.001 * 'm.
  Notation "'mm" := (millimetre) (at level 0) : SI_scope.
  
  Definition gram := 0.001 * 'kg.
  Notation "'g" := (gram) (at level 0) : SI_scope.
  
  Definition milliampere := 0.001 * 'A.
  Notation "'mA" := (milliampere) (at level 0) : SI_scope.
  
  Definition minute := 60 * 's.
  Notation "'min" := (minute) (at level 0) : SI_scope.
  
  Definition hour := 60 * 'min.
  Notation "'hrs" := (hour) (at level 0) : SI_scope.
  
  Lemma hour2second : 'hrs == 3600 * 's.
  Proof. pfueq. Qed. 
  
  Definition day := 24 * 'hrs.
  Notation "'d" := (day) (at level 0) : SI_scope.
  
  Lemma day2second : 'd == 86400 * 's.
  Proof. pfueq. Qed.
  
  Lemma day2minute : 'd == 1440 * 'min.
  Proof. pfueq. Qed.
  
  (** astronomical Unit, 天文单位 *)
  Definition astronomicalUnit := 149_597_870_700 * 'm.
  Notation "'au" := (astronomicalUnit) (at level 0) : SI_scope.
  
  (** plane and phase angle, 平面角、相位角 *)
  Definition degree_angle := (PI/180) * 'rad.
  Notation "'ᵒ" := (degree_angle) (at level 0) : SI_scope.
  
  (** area(hectare), 面积（公顷），=100m*100m *)
  Definition hectare := 10000 * 'm².
  Notation "'ha" := (hectare) (at level 0) : SI_scope.
  
  (** volume(litre), 体积（升），= 1dm^3 = 10^3 cm^3 = 10^{-3} m^3 *)
  Definition litre := (/10^3) * 'm³.
  Notation "'L" := (litre) (at level 0) : SI_scope.

  (** mass(tonne), 质量（顿） *)
  Definition tonne := 1000 * 'kg.
  Notation "'t" := (tonne) (at level 0) : SI_scope.
  
  (** mass(dalton), 质量（道尔顿） *)
  Definition dalton := (1.660_539_066_60*(/10^27)) * 'kg.
  Notation "'Da" := (dalton) (at level 0) : SI_scope.

  (** energy(electronical voltage), 能量（电子伏） *)
  Definition electronvolt := (1.602_176_634*(/10^27)) * 'J.
  Notation "'eV" := (electronvolt) (at level 0) : SI_scope.
  
  (** round speed, round per minute *)
  Definition round_per_minute := /'min.
  Notation "'rpm" := (round_per_minute) (at level 0) : SI_scope.
  
  (** battery capacity *)
  Definition milli_amper_hour := 'mA * 'hrs.
  Notation "'mAh" := (milli_amper_hour) (at level 0) : SI_scope.
  
End SI_Accepted.

Export SI_Accepted.



(** ** Table 6, Examples of Coherent derived units *)

(** ** Special care of Relative Temperature and Temperature Difference *)
(**
<<
   Notice, temperature unit has two type:
    1. relative temperature, you have to give a reference point.
      a. Kelvin, reference point is 0K
      b. Celsius, reference point is 273.15K
    2. temperature difference, it is also considered as a piece of heat.
      a. Kelvin, 1'K = 1 &K
      b. Celsius, 1'℃ = 1 &K.
  This module is mainly talk about relative temperature.
>>
*)
Module Temperature_Relative_Difference.

  (** A special tactic to prove unit equality of Celsius *)
  Ltac pfueq_celsius :=
    compute; f_equal; f_equal; field.
  
  (** It's better to use a symbol, Coq is not good at direct arithmetic *)
  Parameter AbsoluteZeroTemp : R.
(*   Definition AbsoluteZeroTemp : R := -273.15. *)
    
  (** Absolute Celsius Temperature *)
  Inductive CelsiusRelativeType : Set := CelsiusRelative (r : R).
  
  (** Kelvin to CelsiusRelativeType. *)
  Definition k2celsiusRel_opt : Unit -> option CelsiusRelativeType :=
    fun u =>
      match (u2n u) with
      | (coef, dims) => match dims with
        | ((((((0,0),0),0),1),0),0)%Z => 
          Some (CelsiusRelative (coef + AbsoluteZeroTemp))
        | _ => None
        end
      end.
  
  (** CelsiusRelativeType to Kelvin. *)
  Definition celsiusRel2k : CelsiusRelativeType -> Unit :=
    fun c => let '(CelsiusRelative r) := c in
      (r - AbsoluteZeroTemp) * 'K.
  
  (** Convert relative celsius to kelvin, then convert back, keep same.*)
  Lemma celsiusRel2k_k2celsiusRel : forall (c : CelsiusRelativeType),
    k2celsiusRel_opt (celsiusRel2k c) = Some c.
  Proof.
    intros. destruct c. pfueq_celsius.
  Qed.
  
  (** Convert kelvin to relative celsius, then convert back, keep same. *)
  Lemma k2celsiusRel_celsiusRel2k : forall (r : R),
    let k := r * 'K in
      match (k2celsiusRel_opt k) with
      | Some c =>
        celsiusRel2k c = k
      | None => False
      end.
  Proof.
    intros. compute. f_equal. f_equal. field.
  Qed.
  
  (** Example1 : 30 ℃ equal to 303.15 K *)
  Fact temperature_example1 :(AbsoluteZeroTemp = -273.15) ->
    celsiusRel2k (CelsiusRelative 30) = 303.15 * 'K.
  Proof. intros. pfueq. rewrite H. f_equal. compute. field. Qed.
  
  (** Example1 : 293.15 K equal to 20 ℃ *)
  Fact temperature_example2 : (AbsoluteZeroTemp = -273.15) -> 
    k2celsiusRel_opt (293.15 * 'K) = Some (CelsiusRelative 20).
  Proof. intros. pfueq. rewrite H. f_equal. compute. field. Qed.
  
(*     Definition degreeCelsiusAbsolute := [UKK].
  Notation "'℃" := (celsius) (at level 0).
  
  Definition fahrenheit := (9/5) * [UKK].
  Notation "'℉" := (celsius) (at level 0). *)

End Temperature_Relative_Difference.

Export Temperature_Relative_Difference.



(** ** The 7 defining constants of SI *)
Module SI_defining_constants.
  
  (** hyperfine transition frequency of Cs，铯原子能级跃迁辐射频率 *)
  Definition hyper_trans_freq_of_Cs := 9_192_631_770 * 'Hz.
  Notation "'ΔV" := (hyper_trans_freq_of_Cs) (at level 0) : SI_scope.
  
  (** speed of light in vaccum，真空中光速 *)
  Definition speed_of_light_in_vaccum := 299_792_458 * ('m/'s).
  Notation "'c" := (speed_of_light_in_vaccum) (at level 0) : SI_scope.
  
  (** Planck constant，普朗克常量 *)
  (* Notice that,
    1. don't use (IZR (10^(-34))), it is 0%Z
    2. don't use Rpower x y, it is complicated, can't use Lra
    3. /10^34 means (/10)^34, means 10e-34
  *)
  Definition planck_constant := (6.626_070_15 * (/10^34)) * ('J*'s).
  Notation "'h" := (planck_constant) (at level 0) : SI_scope.
  
  (** elementary charge，元电荷 *)
  Definition elementary_charge := (1.602_176_634 * (/10^19))  * 'C.
  Notation "'e" := (elementary_charge) (at level 0) : SI_scope.
  
  (** Boltzmann constant，玻尔兹曼常数 *)
  Definition boltzmann_constant := (1.380_649 * (/10^23)) * ('J/'K).
  Notation "'k" := (boltzmann_constant) (at level 0) : SI_scope.
  
  (** Avogadro constant，阿伏伽德罗常数 *)
  Definition avogadro_constant  := (6.022_140_76 * (10^23)) * (/'mol).
  Notation "'NA" := (avogadro_constant) (at level 0) : SI_scope.
  
  (** luminous efficacy，最大发光效能 *)
  Definition luminous_efficacy := 683 * 'lm * (/'W).
  Notation "'Kcd" := (luminous_efficacy) (at level 0) : SI_scope.
  
End SI_defining_constants.

Export SI_defining_constants.



(** ** Verify consistency between defining constants and basic unit *)
Module SI_defining_constants_compatible.
  
  (** Tactic for proof unit approximate reletion. *)
  Ltac pfuapprox :=
    unfold Unit_approx; simpl; split; auto; unfold Rapprox;
    match goal with | |- (Rabs ?r1 <= ?r2)%R => remember r1 as r end;
    unfold Rabs; destruct (Rcase_abs _); subst; lra.
  
  (** Properties about second *)
  Lemma Hz_def : 1 * 'Hz == 'ΔV / 9_192_631_770.
  Proof. pfueq. Qed.
  
  Lemma s_def : 1 * 's == 9_192_631_770 / 'ΔV.
  Proof. pfueq. Qed.
  
  (** Properties about metre *)
  Lemma m_def1 : 1 * 'm == ('c / 299_792_458) * 's.
  Proof. pfueq. Qed.

  Lemma m_def2 : 1 * 'm == (9_192_631_770 / 299_792_458) * ('c / 'ΔV).
  Proof. pfueq. Qed.
  
  (* let's change different value, we got 0.000_000_001 *)
  Lemma m_def3 : Unit_approx (1 * 'm) (30.663319 * ('c/'ΔV)) (0.000000001).
  Proof. pfuapprox. Qed.
  
  (** Properties about kilogram *)
  Lemma kg_def1 : 1 * 'kg == 
    ('h / (6.62607015 * (/10^34))) * ((/'m²)*'s).
  Proof. pfueq. Qed.
  
  Lemma kg_def2 : 1 * 'kg == 
    ((299792458)² / (6.62607015 * (/10^34) * (9192631770))) *
    (('h * 'ΔV) / ('c²)).
  Proof. pfueq. Qed.
  
  Lemma kg_def3 : Unit_approx (1 * 'kg)
    ((1.4755214*10^40) * (('h * 'ΔV) / ('c²))) 0.00000001. 
  Proof. pfuapprox. Qed.
  
  (** Properties about ampere *)
  Lemma A_def1 : 1 * 'A == ('e / (1.602176634 * (/10^19))) * (/'s).
  Proof. pfueq. Qed.
  
  Lemma A_def2 : 1 * 'A == (/(9192631770 * (1.602176634 * (/10^19))))
    * ('ΔV * 'e).
  Proof. pfueq. Qed.
  
  Lemma A_def3 : Unit_approx (1 * 'A) ((6.7896868*(10^8)) * ('ΔV * 'e))
    0.00000001.
  Proof. pfuapprox. Qed.
  
  (** Properties about kelvin *)
  Lemma kelvin_def1 : 1 * 'K == ((1.380649 * (/10^23)) /'k)
    * ('kg * 'm² * (/'s²)).
  Proof. pfueq. Qed.
  
  Lemma kelvin_def2 : 1 * 'K == ((1.380649 * (/10^23)) /
    ((6.62607015 * (/10^34)) * (9192631770)))
    * ('ΔV * 'h * (/'k)).
  Proof. pfueq. Qed.
  
  Lemma kelvin_def3 : Unit_approx (1 * 'K) 
    ((2.2666653) * ('ΔV * 'h * (/'k))) 0.0000001.
  Proof. pfuapprox. Qed.
  
  (** Properties about mole *)
  Lemma mol_def : 1 * 'mol == ((6.02214076*(10^23))) / 'NA.
  Proof. pfueq. Qed.
  
  (** Properties about candela *)
  Lemma cd_def1 : 1 * 'cd == ('Kcd/683) * ('kg * 'm² * (/'s³) * (/'sr)).
  Proof. pfueq. Qed.
  
  Lemma cd_def2 : 1 * 'cd == 
    (/((6.62607015 * (/10^34)) * 9192631770² * 683)) * ('ΔV² * 'h * 'Kcd).
  Proof. pfueq. Qed.
  
  Lemma cd_def3 : Unit_approx (1 * 'cd) 
    ((2.6148305 * (10^10)) * ('ΔV² * 'h * 'Kcd)) 0.00000001.
  Proof. pfuapprox. Qed.

End SI_defining_constants_compatible.



(** ** Examples *)

Module examples.
  
  (* 气体状态方程 P = ρRT 中 R 有两个单位，验证它们相同 *)
  Example ex_rho_R_T : 'N * 'm / ('kg * 'K) == 'm² / ('s² * 'K).
  Proof. pfueq. Qed.
  
  (** Show the ability that Coq could verify large number.
    In astronomy, where there are some very large numbers involved, Coq can 
    check the equation or inequalities of this data type. *)
(*   Fact large_number_ex1 : (1.234567*10^300) * (2.345678*10^200)
    == (2.895896651426 * 10^500).
  Proof.
    Time pfueq. (* 1.7s *)
  Qed. *)

  
  (** 3.26 light-year <= parsec <= 3.27 light-year *)
  Definition julian_year := 365.25 * day.
  Definition light_year := 'c * julian_year.
  Definition parsec := (648000/PI).
 
  (* we need to define <= relation first *) 
(*   Lemma parsec_le_lightyear : parsec <= 3.27 * light_year.
  Lemma parsec_ge_lightyear : parsec >= 3.26 * light_year.
 *)
End examples.
