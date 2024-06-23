(*
  Copyright 2024 Zhengpu Shi
  This file is part of VQCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose    : Basic module for propulsion system
  author:       Zhengpu Shi
  date:         2020.11.17

  copyright:    Formalized Engineering Mathematics team of NUAA.
  website:      http://fem-nuaa.cn
*)

Require Export SI QalgebraR.
Export SI_Accepted SI_Prefix.


(** ** Constants *)

(** *** GENERAL NUMBER *)

(** Defind as R type. *)
(** Because old version COQ doesn't support enter decimal. *)
Parameter
  val_0_0065
  val_5_2561
  val_0_8
  val_0_25
  val_9_55
  val_0_06
  : R.

(** Defined as [Q]. *)
Definition value_0_0065 := u2qR val_0_0065 ('K/'m)%U.


(** *** GLOBAL *)
Parameters
  val_T_0       (* ISA temperature, 288.15 K (15 ℃), use ℃ *) 
  val_h         (* height of a multicopeter, m *)
  val_p_0       (* standard air presure, 101325 Pa *)
  val_rho_0     (* standard air density, 1.293 kg/m^3 *)
  val_T_t       (* temperature of environment, ℃ *)
  val_G         (* total weight, g *)
  val_I_other   (* other current, 1 A *)
  (* Note that, it should be integer, but we just simplify the problem. *)
  val_n_r       (* numbr of propellers, None. *)
  : R.


(** Notice that, T_0, T_t, we use 'K instead ℃, it is correct in such case. *)
Definition T_0 : QuR := u2qR val_T_0 'K.
Definition h : QuR := u2qR val_h 'm.
Definition p_0 : QuR := u2qR val_p_0 'Pa.
Definition rho_0 : QuR := u2qR val_rho_0 ('kg / 'm³)%U.
Definition T_t : QuR := u2qR val_T_t 'K. (* 
  = celsiusRel2k (CelsiusRelative val_T_t). *)
Definition G : QuR := u2qR val_G 'N.  (* not 'kg or 'g *)
Definition I_other : QuR := u2qR val_I_other 'A.
Definition p : QuR := p_0 * (qpower (1 - value_0_0065 * (h / (T_0 + T_t))) val_5_2561).

(* a simpler value*)
(* Definition rho : QuR := (T_0 * p) / (p_0 * (T_0 + T_t)) * rho_0. *)
Parameter val_rho : R.
Definition rho : QuR := u2qR val_rho ('kg/('m³))%U.
             
Definition n_r : QuR := val_n_r.


(** *** PROPELLER *)
Parameters 
  val_D_p
  val_H_p
  val_B_p 
  val_G_p 
  val_PP_A 
  val_PP_epsilon 
  val_PP_lambda 
  val_PP_zeta 
  val_PP_e 
  val_PP_K0 
  val_PP_alpha0 
  val_C_fd 
  : R.

Definition val_PP_alpha_ab : R := 
  (val_PP_epsilon * (atan (val_H_p / (PI * val_D_p))) - val_PP_alpha0).

(* Definition val_C_T : R := *)
(*   (val_0_25 * PI ^ 3 * val_PP_lambda * (val_PP_zeta ^ 2) * val_B_p * val_PP_K0  *)
(*                    * val_PP_alpha_ab / (PI * val_PP_A + val_PP_K0))%R. *)

(* Definition val_C_d : R := *)
(*   (val_C_fd + (PI * val_PP_A * (val_PP_K0 ^ 2) / val_PP_e) *  *)
(*                 ((val_PP_alpha_ab / (PI * val_PP_A + val_PP_K0)) ^ 2 ))%R. *)

(* Definition val_C_M : R := *)
(*   ((8 * val_PP_A) * ((PI * val_PP_zeta * val_B_p) ^ 2)  *)
(*    * val_C_d * val_PP_lambda)%R. *)


(* this parameter shoud be pre-calculated *)
Parameter val_C_T : R.
Parameter val_C_d : R.
Parameter val_C_M : R.

Definition D_p : QuR := u2qR val_D_p 'm.
Definition H_p : QuR := u2qR val_H_p 'm.
Definition C_T : QuR := val_C_T.
Definition C_d : QuR := val_C_d.
Definition C_M : QuR := val_C_M.


(** *** MOTOR *)
Parameters 
  val_K_V0 
  val_I_mMax 
  val_U_m0 
  val_I_m0 
  val_R_m 
  val_G_m : R.

Definition I_mMax : QuR := u2qR val_I_mMax 'A.
Definition U_m0 : QuR := u2qR val_U_m0 'V.
Definition I_m0 : QuR := u2qR val_I_m0 'A.
Definition R_m : QuR := u2qR val_R_m 'Ω.
Definition G_m : QuR := u2qR val_G_m 'g.
Definition K_E : QuR := (U_m0 - I_m0 * R_m) / (val_K_V0 * U_m0).
Definition K_T : QuR := val_9_55 * K_E.

(** *** ESC *)
Parameters 
  val_I_eMax 
  val_R_e 
  val_G_e : R.

Definition I_eMax : QuR := u2qR val_I_eMax 'A.
Definition R_e : QuR := u2qR val_R_e 'Ω.
Definition G_e : QuR := u2qR val_G_e 'g.


(** *** BATTERY *)
Parameters 
  val_C_b 
  val_C_min 
  val_K_b 
  val_R_b 
  val_U_b : R.

Definition C_b : QuR := u2qR val_C_b ('mAh).
Definition C_min : QuR := u2qR val_C_min 'mAh.
Definition K_b : QuR := val_K_b.
Definition R_b : QuR := u2qR val_R_b 'Ω.
Definition U_b : QuR := u2qR val_U_b 'V.



(** ** Definitions of functions *)

(* example: check, conversion of the units of parameters or output.
   * Before added the output unit convertion, the output unit is determined by 
     the input, though they are the same in physics, but they are not same in 
     mathematics and computer. 
   * For example: if the function return 2 'min or 120 's, it will be a mistake after
     removed the unit symbols, and it is a very common operation. *)

(** Check the unit of the input Quantity q with reference Unit u, 
    if they are equal return q, otherwise return !! *)
Definition CHK_UNIT (q : QuR) (u : Unit) : QuR :=
  if qsameub q u then q else !!.
Hint Unfold CHK_UNIT : Q.

(** Convert the unit of the input Quantity q with reference Unit u, 
    if it is convertible then return a proper q', otherwise return !! *)
Definition CVT_UNIT (q : QuR) (u : Unit) : QuR := q2quR q u.
Hint Unfold CVT_UNIT : Q.

(* A demo example to showing the advantages of unit system *)
Module demo1.
  (** The input parameter `N` could be any unit, and the output could be any unit. *)
  Definition get_T_by_N_NOCHECK (N : QuR) : QuR := 
    rho * C_T * (D_p ^ 4) * ((N / 60) ^ 2).

  (* Eval cbv in get_T_by_N_NOCHECK (u2qR 1 'rpm). *)
  (* Eval cbv in get_T_by_N_NOCHECK (u2qR 60 'Hz). *)
  (* Eval cbv in get_T_by_N_NOCHECK (u2qR 1 'A). *)

  (** we can check the unit of the input parameter *)
  Definition get_T_by_N_CHECK_INPUT (N : QuR) : QuR :=
    let N := CHK_UNIT N 'rpm in
    rho * C_T * (D_p ^ 4) * ((N / 60) ^ 2).

  (* Eval cbv in get_T_by_N_CHECK_INPUT (u2qR 1 'rpm). *)
  (* Eval cbv in get_T_by_N_CHECK_INPUT (u2qR 60 'Hz). *)
  (* Eval cbv in get_T_by_N_CHECK_INPUT (u2qR 1 'A). *)

  (* now, only 'rpm is accepted *)
  Goal get_T_by_N_CHECK_INPUT (u2qR 1 'rpm) <> !!. qeqR. Qed.
  Goal get_T_by_N_CHECK_INPUT (u2qR 60 'Hz) = !!. qeqR. Qed.
  Goal get_T_by_N_CHECK_INPUT (u2qR 1 'A) = !!. qeqR. Qed.

  (** we can convert the unit of the input parameter *)
  Definition get_T_by_N_CONVERT_INPUT N := 
    let N := CVT_UNIT N 'rpm in
    rho * C_T * (D_p ^ 4) * ((N / 60) ^ 2).

  (* now, 'rpm and 'Hz are accepted *)
  Goal get_T_by_N_CONVERT_INPUT (u2qR 1 'rpm) <> !!. qeqR. Qed.
  Goal get_T_by_N_CONVERT_INPUT (u2qR 60 'Hz) <> !!. qeqR. Qed.
  Goal get_T_by_N_CONVERT_INPUT (u2qR 1 'A) = !!. qeqR. Qed.

  (** we can convert the unit of the output parameter
      1. the output has a fixed unit, which is beneficial for caller which need 
         exactly unit.
      2. the function itself also accept any convertible units
      3. any not convertible units will be rejected. *)
  Definition get_T_by_N_CONVERT_OUTPUT N := 
    CVT_UNIT (rho * C_T * (D_p ^ 4) * ((N / 60) ^ 2)) 'N.

  (* Compute qunit (get_T_by_N_CONVERT_OUTPUT (u2qR 1 'rpm)). *)
  (* Compute qunit (get_T_by_N_CONVERT_OUTPUT (u2qR 60 'Hz)). *)
  (* Compute qunit (get_T_by_N_CONVERT_OUTPUT (u2qR 1 'A)). *)

  (* 总结几种不同的做法：
     1. 检查输入，则要求输入具有指定的单位
     2. 检查输出，则验证函数的输出具有指定的单位
     3. 转换输入，则接收可转换的输入参数
     4. 转换输出，则将输出的单位统一为指定的单位
     另外，无论输入参数是什么，函数体的设计是假定输入参数为SI的一贯单位来考虑的（待补充）
     因此，有多种做法，这里推荐一种：检查输入，转换输出。优点是：确定性和适应性。*)
End demo1.


(** *** Basic functions *)

(** demo for won't force change the output unit, keep what it is *)
Definition get_T_by_N N := 
  let N := CHK_UNIT N 'rpm in
  let _ret := rho * C_T * (D_p ^ 4) * ((N / 60) ^ 2) in
  CVT_UNIT _ret 'N.
Hint Unfold get_T_by_N : Q.

(* 验证 get_T_by_N 函数确实能否返回期望的单位，排除函数内部的单位错误 *)
Lemma get_T_by_N_unit : forall N, qsameu N 'rpm -> qsameu (get_T_by_N N) 'N.
Proof.
  intros. autounfold with Q. lazy [qsameu q2quR q2qu q2qn] in *.
  destruct N; auto. rewrite H. simpl.
  rewrite neqb_refl. simpl. auto.
Qed.

Definition get_M_by_N N := 
  let N := CHK_UNIT N 'rpm in 
  CVT_UNIT (C_M * rho * ((N / 60) ^ 2) * (D_p ^ 5)) ('N*'m)%U.

Definition get_E_a_by_N N := 
  let N := CHK_UNIT N 'rpm in 
  CVT_UNIT (K_E * N) 'V.

Definition get_M_by_I_m I_m :=
  let I_m := CHK_UNIT I_m 'A in
  CVT_UNIT (K_T * (I_m - I_m0)) ('N*'m)%U.

Definition get_U_m_by_E_a_and_I_m E_a I_m :=
  let E_a := CHK_UNIT E_a 'V in
  let I_m := CHK_UNIT I_m 'A in
  CVT_UNIT (E_a + R_m * I_m) 'V.

Section test.
  Variable E_a I_m : R.

  Goal qsameub (get_U_m_by_E_a_and_I_m (u2qR E_a 'V) (u2qR I_m 'A)) 'V = true.
  Proof. qeqR. Qed.

  (* we wrongly use 'mA for I_m *)
  Goal qsameub (get_U_m_by_E_a_and_I_m (u2qR E_a 'V) (u2qR I_m 'mA)) 'V = false.
  Proof. qeqR. Qed.

  (* we wrongly wanted to get 'mV for output *)
  Goal qsameub (get_U_m_by_E_a_and_I_m (u2qR E_a 'V) (u2qR I_m 'A)) (_m 'V) = false.
  Proof. qeqR. Qed.
End test.

Definition get_U_eo_by_U_m_and_I_m U_m I_m :=
  let U_m := CHK_UNIT U_m 'V in
  let I_m := CHK_UNIT I_m 'A in
  CVT_UNIT (U_m + I_m * R_e) 'V.

Definition get_U_eo_by_sigma_e sigma_e :=
  let sigma_e := CHK_UNIT sigma_e 1 in
  CVT_UNIT (sigma_e * U_b) 'V.

Definition get_I_e_by_sigma_e_and_I_m sigma_e I_m :=
  let sigma_e := CHK_UNIT sigma_e 1 in
  let I_m := CHK_UNIT I_m 'A in
  CVT_UNIT (sigma_e * I_m) 'A.

Definition get_I_b_by_I_e I_e :=
  let I_e := CHK_UNIT I_e 'A in
  CVT_UNIT (n_r * I_e + I_other) 'A.

Definition get_U_e_by_I_b I_b :=
  let I_b := CHK_UNIT I_b 'A in
  CVT_UNIT (U_b - I_b * R_b) 'V.

(* Tips: 一个很好的案例来说明检查单位的好处。
   C_b, C_min : 电池容量(mAh)，电池最小剩余容量(mAh)
   I_b : 电池放电电流 ('A)
   T_b : 电池时间 (分钟)
   所以，此处预估了电池使用寿命 T_b = ((C_b - C_min) / I_b * (60/1000)，单位才是分钟，
   这就是 val_0_06 := 0.06 的来历。
   如果不知道时间单位是什么，这里的公式的正确性无从谈起。*)
Definition get_T_b_by_I_b I_b :=
  let I_b := CHK_UNIT I_b 'A in
  CVT_UNIT ((C_b - C_min) / I_b * val_0_06) 'min.

(* 在OCaml中，对电池时间的预估，数据来自全权老师的书 *)
Module T_b_ex.
  (* C_b = 4000mAh, 
     C_min = 20% * C_b = 800mAh,
     I_b = 15A
     T_b = (4000-800)/15*0.06 ≈ 12.8 min *)
  Extract Constant val_0_06 => "0.06".
  Extract Constant val_C_b => "4000.".
  Extract Constant val_C_min => "800.".
  (* 应当得到 12.8 的结果 *)
  Example val_T_b_1 := qval (get_T_b_by_I_b (u2qR 15 'A)).
  (* 错误的使用 mA，看能否被成功识别 *)
  Example val_T_b_2 := qval (get_T_b_by_I_b (u2qR 15 'mA)).

  Extraction "test_T_b.ml" val_T_b_1 val_T_b_2.
(* 
utop[1]> T_b_ex.val_T_b_1;;
- : float option = Some 0.768
utop[2]> T_b_ex.val_T_b_2;;
- : float option = None
 *)
End T_b_ex.

Definition get_G_maxload_by_T T :=
  let T := CHK_UNIT T 'N in
  CVT_UNIT (n_r * T - G) 'N.

Definition get_theta_max_by_T T :=
  let T := CHK_UNIT T 'N in
  CVT_UNIT ('acos (G / (n_r * T))) 1.

Definition get_eta_by_M_and_N_and_I_b M N I_b :=
  let M := CHK_UNIT M ('N*'m)%U in
  let N := CHK_UNIT N 'rpm in
  let I_b := CHK_UNIT I_b 'A in
  CVT_UNIT (((2 * PI) / 60) * n_r * M * N / (U_b * I_b)) 1.


(** *** Basic inverse functions *)

Definition get_N_by_T T :=
  let T := CHK_UNIT T 'N in 
  CVT_UNIT (60 * qsqrt (T /(rho * C_T * (D_p ^ 4)))) 'rpm.


Definition get_N_by_M M :=
  let M := CHK_UNIT M ('N*'m)%U in
  CVT_UNIT (60 * (qsqrt (M / (rho * (D_p ^ 5) * C_M)))) 'rpm.

(*
Definition get_N_by_E_a E_a :=
  if negb (QUsameunitb E_a (#'V)) then !! else
  E_a / K_E.

Definition get_I_m_by_M M :=
  if negb (QUsameunitb M ('N*'m)) then !! else
  M / K_T + I_m0.

Definition get_sigma_e_by_U_eo U_eo :=
  if negb (QUsameunitb U_eo 'V) then !! else
  U_eo / U_b.

Definition get_I_e_by_I_b I_b :=
  if negb (QUsameunitb I_b 'A) then !! else
  (I_b - I_other) / n_r.

Definition get_I_b_by_T_b T_b :=
  if negb (QUsameunitb T_b 's) then !! else
  (C_b - C_min) / T_b * val_0_06.

Definition get_I_b_by_U_e U_e :=
  if negb (QUsameunitb U_e 'V) then !! else
  (U_b - U_e) / R_b.

Definition get_T_by_G_maxload G_maxload :=
  if negb (QUsameunitb G_maxload 'N) then !! else
  (G_maxload + G) / n_r.

Definition get_T_by_theta_max theta_max :=
  if negb (QUsameunitb theta_max 'rad) then !! else
  G / (n_r * Qcos theta_max).


(** *** Extended functions (basic part) *)

Definition get_T_by_M M :=
  if negb (QUsameunitb M ('N*'m)) then !! else
  (C_T * M) / (D_p * C_M).

Definition get_T_by_E_a E_a := 
  if negb (QUsameunitb E_a ('V)) then !! else
  rho * C_T * (D_p ^ 4) * (E_a / (60 * K_E)) ^ 2.

Definition get_M_by_T T :=
  if negb (QUsameunitb T 'N) then !! else
  (C_M * D_p * T) / C_T.

Definition get_I_m_by_T T :=
  if negb (QUsameunitb T 'N) then !! else
  (C_M * D_p * T) / (K_T * C_T) + I_m0.

Definition get_E_a_by_T T :=
  if negb (QUsameunitb T 'N) then !! else
  60 * K_E * Qsqrt (T / (rho * C_T * (D_p ^ 4))).

Definition get_U_m_by_T T :=
  if negb (QUsameunitb T 'N) then !! else
  60 * K_E * Qsqrt (T / (rho * C_T * (D_p ^ 4)))
  + R_m * ((C_M * D_p * T) / (K_T * C_T) + I_m0).

Definition get_U_m_by_N_and_M N M :=
  if negb ((QUsameunitb N 'rpm) && (QUsameunitb M ('N*'m))) then !! else
  K_E * N + R_m * (M / K_T + I_m0).

Definition get_U_m_by_N N := 
  if negb (QUsameunitb N 'rpm) then !! else
  K_E * N + R_m 
  * ((C_M * rho * ((N / 60) ^ 2) * (D_p ^ 5)) 
  / K_T + I_m0).

Definition get_U_m_by_M M :=
  if negb (QUsameunitb M ('N*'m)) then !! else
  60 * K_E * (Qsqrt (M / (rho * (D_p ^ 5) * C_M))) 
  + R_m * (M / K_T + I_m0).

Definition get_U_eo_by_E_a_and_I_m E_a I_m :=
  if negb ((QUsameunitb E_a 'V) && (QUsameunitb I_m 'A)) then !! else
  E_a + (R_m + R_e) * I_m.

Definition get_U_eo_by_N N :=
  if negb (QUsameunitb N 'rpm) then !! else
  ((R_m + R_e) * C_M * rho * (D_p ^ 5))
  / (K_T * (60 ^ 2)) * (N ^ 2) + K_E * N + (R_m + R_e) * I_m0.

Definition get_sigma_e_by_E_a_and_I_m E_a I_m :=
  if negb ((QUsameunitb E_a 'V) && (QUsameunitb I_m 'A)) then !! else
  (E_a + (R_m + R_e) * I_m) / U_b.

Definition get_I_e_by_E_a_and_I_m E_a I_m :=
  if negb ((QUsameunitb E_a 'V) && (QUsameunitb I_m 'A)) then !! else
  ((E_a + (R_m + R_e) * I_m) * I_m) / U_b.

Definition get_I_e_by_T T :=
  if negb (QUsameunitb T 'N) then !! else
  (((60 * K_E * Qsqrt (T / (rho * C_T * (D_p ^ 4)))) 
  + (R_m + R_e) * ((C_M * D_p * T) / (K_T * C_T) + I_m0)) 
  * ((C_M * D_p * T) / (K_T * C_T) + I_m0)) / U_b.

Definition get_U_e_by_I_e I_e :=
  if negb (QUsameunitb I_e 'A) then !! else
  U_b - (n_r * I_e + I_other) * R_b.

Definition get_T_b_by_I_e I_e :=
  if negb (QUsameunitb I_e 'A) then !! else
  (C_b - C_min) / (n_r * I_e + I_other) 
  * val_0_06.


(** *** Extended functions (advanced part) *)

(** calculate "Motor speed N" by "Motor input voltage U_m".
   Notice that, Quadratic equations with one variable can have two solutions,
   here, I keep the big one. In fact, another small solution should be 
   discarded, I will give a strict proof later. *)
Definition get_N_by_U_m U_m :=
  if negb (QUsameunitb U_m 'V) then !! else
  (1800 * K_T) / (R_m * C_M * rho * (D_p ^ 5)) * (-K_E + Qsqrt((K_E ^ 2) 
  - (R_m * C_M * rho * (D_p ^ 5) * (R_m * I_m0 - U_m)) / (900 * K_T) )).

(** calculate "Motor speed N" by "ESC output voltage U_eo" *)
Definition get_N_by_U_eo U_eo :=
  if negb (QUsameunitb U_eo 'V) then !! else
  (1800 * K_T) / ((R_m + R_e) * C_M * rho * (D_p ^ 5)) 
  * (-K_E + Qsqrt((K_E ^ 2) 
  - ((R_m + R_e) * C_M * rho * (D_p ^ 5)) / (900 * K_T)
  * ((R_m + R_e) * I_m0 - U_eo))).
  *)


(** ** Reasonable axioms of the system *)

(** Constant numbers *)
Axiom const_val_0_0065 : val_0_0065 = 0.0065.
Axiom const_val_5_2561 : val_5_2561 = 5.2561.
Axiom const_val_0_8 : val_0_8 = 0.8.
Axiom const_val_0_25 : val_0_25 = 0.0065.
Axiom const_val_9_55 : val_9_55 = 9.55.
Axiom const_val_0_06 : val_0_06 = 0.0065.


(** These assumptions should be checked by expert carefully. *)

Axiom const_val_T_0 : val_T_0 = 273.15.
Axiom gt0_val_p_0 : (0 < val_p_0)%R.
Axiom gt0_val_rho_0 : (0 < val_rho_0)%R.
Axiom gt0_val_T_t : (0 < val_T_t)%R.
(* Axiom const_val_n_r : n_r ?. *)
Axiom gt0_val_n_r : (0 < val_n_r)%R.
Axiom gt0_val_G : (0 < val_G)%R.

(** Temperature and Height assumption
<<
1. max flight height is [0~9200] meter, that means [0~30000] ft.
2. environment temperature is [-60,60] ℃
>>
*)
Axiom condL_val_h : (0 < val_h)%R.
Axiom condH_val_h : (val_h < 9200)%R.
Axiom condL_val_T_t : (-60 < val_T_t)%R.
Axiom condH_val_T_t : (val_T_t < 60)%R.
Axiom gt0_val_D_p : (0 < val_D_p)%R.
Axiom gt0_val_B_p : (0 < val_B_p)%R.
Axiom gt0_val_PP_A : (0 < val_PP_A)%R.
Axiom gt0_val_PP_K0 : (0 < val_PP_K0)%R.
Axiom gt0_val_PP_epsilon : (0 < val_PP_epsilon)%R.
Axiom gt0_val_PP_lambda : (0 < val_PP_lambda)%R.
Axiom gt0_val_PP_zeta : (0 < val_PP_zeta)%R.
Axiom gt0_val_PP_e : (0 < val_PP_e)%R.
Axiom gt0_val_C_fd : (0 < val_C_fd)%R. 
Axiom gt0_val_C_T : (0 < val_C_T)%R.  (* Todo: check this *)
Axiom gt0_val_C_M : (0 < val_C_M)%R.  (* Todo: check this *)
Axiom gt0_val_R_b : (0 < val_R_b)%R.
Axiom gt0_val_R_m : (0 < val_R_m)%R.
Axiom gt0_val_R_e : (0 < val_R_e)%R.
Axiom gt0_val_PP_alpha_ab : (0 < val_PP_alpha_ab)%R.
(* Axiom gt0_val_K_E : (0 < val_K_E)%R. *)
(* Axiom gt0_val_K_T : (0 < val_K_T)%R. *)
Axiom gt0_val_U_b : (0 < val_U_b)%R.
Axiom gt0_val_C_b_minus_C_min : 0 < val_C_b - val_C_min.  (* safe battery voltage *)
Axiom gt0_val_U_m0 : (0 < val_U_m0)%R.  (* Todo: check this *)
Axiom gt0_val_K_V0 : (0 < val_K_V0)%R.  (* Todo: check this *)




(** ** Update Hint database *)

Global Hint Unfold 
  get_E_a_by_N
  (* get_E_a_by_T *)
  get_G_maxload_by_T
  (* get_I_m_by_M *)
  (* get_I_m_by_T *)
  get_I_b_by_I_e
  (* get_I_b_by_T_b *)
  (* get_I_b_by_U_e *)
  (* get_I_e_by_I_b *)
  (* get_I_e_by_E_a_and_I_m *)
  get_I_e_by_sigma_e_and_I_m
  (* get_I_e_by_T *)
  get_M_by_N
  (* get_M_by_T *)
  get_M_by_I_m
  get_N_by_M
  get_N_by_T
(*  get_N_by_E_a
  get_N_by_U_m
  get_N_by_U_eo
  get_sigma_e_by_U_eo
  get_sigma_e_by_E_a_and_I_m
  get_T_by_M
  get_T_by_E_a *)
  get_T_by_N
(*  get_T_b_by_I_b
  get_T_b_by_I_e
  get_T_by_G_maxload
  get_T_by_theta_max
  get_theta_max_by_T
  get_U_m_by_T
  get_U_e_by_I_b
  get_U_e_by_I_e
  get_U_eo_by_sigma_e
  get_U_eo_by_N
  get_U_m_by_E_a_and_I_m
  get_U_m_by_N_and_M
  get_U_m_by_N
  get_U_m_by_M
  get_U_m_by_T
  get_U_eo_by_E_a_and_I_m
  get_U_eo_by_U_m_and_I_m *)
  : Q.

Global Hint Resolve
  gt0_val_p_0
  gt0_val_rho_0
  gt0_val_T_t
  gt0_val_G
  gt0_val_n_r
  condL_val_h
  condH_val_h
  condL_val_T_t
  condH_val_T_t
  gt0_val_D_p
  gt0_val_B_p
  gt0_val_PP_A
  gt0_val_PP_K0
  gt0_val_PP_epsilon
  gt0_val_PP_lambda
  gt0_val_PP_zeta
  gt0_val_PP_e
  gt0_val_C_fd
  gt0_val_C_T
  gt0_val_C_M
  gt0_val_R_b
  gt0_val_R_m
  gt0_val_R_e
  gt0_val_PP_alpha_ab
(*   gt0_val_K_E *)
(*   gt0_val_K_T *)
  gt0_val_U_b
  gt0_val_C_b_minus_C_min
  gt0_val_U_m0
  gt0_val_K_V0
  : Q.

Hint Rewrite 
  const_val_0_0065
  const_val_5_2561
  const_val_0_8
  const_val_0_25
  const_val_9_55
  const_val_0_06
  const_val_T_0
  : Q.


(* lemmas and proof details, please see "Basic_proof.v" *)
