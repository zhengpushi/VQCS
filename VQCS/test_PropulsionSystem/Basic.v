(*
  category:     flight control system - propulsion subsystem
  filename:     ExtractionThis.v
  author:       Zhengpu Shi
  email:        zhengpushi@nuaa.edu.cn
  date:         2020.11.17
  purpose:      Basic module, also considered as a common module.
                These definitions and relations are stable almost at any case.

  copyright:    Formalized Engineering Mathematics team of NUAA.
  website:      http://fem-nuaa.cn
*)

(* Require Export QUalgebra. *)
Require Export QUantity.


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
Definition value_0_0065 : Q := genQ val_0_0065 ('K/'m)%U.


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
Definition T_0 : Q := genQ val_T_0 'K.
Definition h : Q := genQ val_h 'm.
Definition p_0 : Q := genQ val_p_0 'Pa.
Definition rho_0 : Q := genQ val_rho_0 ('kg / 'm³)%U.
Definition T_t : Q := genQ val_T_t 'K. (* 
  = celsiusRel2k (CelsiusRelative val_T_t). *)
Definition G : Q := genQ val_G 'N.  (* not 'kg or 'g *)
Definition I_other : Q := genQ val_I_other 'A.
Definition p : Q := 
  p_0 * (QRpower (1 - value_0_0065 * (h / (T_0 + T_t))) val_5_2561).
  
Definition rho : Q := (T_0 * p) / (p_0 * (T_0 + T_t)) * rho_0.
Definition n_r : Q := val_n_r.


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

Definition val_C_T : R := (
  val_0_25 * PI ^ 3 * val_PP_lambda * (val_PP_zeta ^ 2) * val_B_p * val_PP_K0 
  * val_PP_alpha_ab / (PI * val_PP_A + val_PP_K0)
  )%R.

Definition val_C_d : R := (
  val_C_fd + (PI * val_PP_A * (val_PP_K0 ^ 2) / val_PP_e) * 
    ((val_PP_alpha_ab / (PI * val_PP_A + val_PP_K0)) ^ 2 )
  )%R.

Definition val_C_M : R := (
  /(8 * val_PP_A) * ((PI * val_PP_zeta * val_B_p) ^ 2) 
  * val_C_d * val_PP_lambda
  )%R.

Definition D_p : Q := genQ val_D_p 'm.
Definition H_p : Q := genQ val_H_p 'm.
Definition C_T : Q := val_C_T.
Definition C_d : Q := val_C_d.
Definition C_M : Q := val_C_M.



(** *** MOTOR *)
Parameters 
  val_K_V0 
  val_I_mMax 
  val_U_m0 
  val_I_m0 
  val_R_m 
  val_G_m : R.

Definition I_mMax : Q := genQ val_I_mMax 'A.
Definition U_m0 : Q := genQ val_U_m0 'V.
Definition I_m0 : Q := genQ val_I_m0 'A.
Definition R_m : Q := genQ val_R_m 'Ω.
Definition G_m : Q := genQ val_G_m 'g.
Definition K_E : Q := (U_m0 - I_m0 * R_m) / (val_K_V0 * U_m0).
Definition K_T : Q := val_9_55 * K_E.

(** *** ESC *)
Parameters 
  val_I_eMax 
  val_R_e 
  val_G_e : R.

Definition I_eMax := genQ val_I_eMax 'A.
Definition R_e := genQ val_R_e 'Ω.
Definition G_e := genQ val_G_e 'g.


(** *** BATTERY *)
Parameters 
  val_C_b 
  val_C_min 
  val_K_b 
  val_R_b 
  val_U_b : R.

Definition C_b := genQ val_C_b ('mAh).
Definition C_min := genQ val_C_min 'mAh.
Definition K_b := val_K_b.
Definition R_b := genQ val_R_b 'Ω.
Definition U_b := genQ val_U_b 'V.



(** ** Definitions of functions *)

(** *** Some demos for advantages by Q with Unit *)

(** First case: CHECK THE INPUT UNIT *)

(** The mathematical formula will produce an output for any kind of input. *)
Definition get_T_by_N__DONNOT_CHECK_INPUT N := 
  rho * C_T * (D_p ^ 4) * ((N / 60) ^ 2).

Opaque PI Rpower atan.
Compute C_T.
Eval cbv in val_C_T.
Eval lazy in val_C_T.
Eval cbv in Qeval (get_T_by_N__DONNOT_CHECK_INPUT (genQ 1 'rpm)).
Eval cbv in Qeval (get_T_by_N__DONNOT_CHECK_INPUT (genQ 1 'Hz)).
Eval cbv in Qeval (get_T_by_N__DONNOT_CHECK_INPUT (genQ 1 'A)).

? HOW TO CHECK THE UNIT OF INPUT PARAMETER,
? and, IF NEED TO CHECK?
(** After added the input check, we must give an input with correct unit. *)
Definition get_T_by_N__CHECK_INPUT N := 
  if negb (QUsameunitb N (#'rpm)) then !! else
  rho * C_T * (D_p ^ 4) * ((N / 60) ^ 2).

(* Compute QUunit (get_T_by_N__CHECK_INPUT (genQ 1 'rpm)).
Compute QUunit (get_T_by_N__CHECK_INPUT (genQ 1 'Hz)).
Compute QUunit (get_T_by_N__CHECK_INPUT (genQ 1 'A)).
 *)


(** Second case: CHECK AND CONVERT THE OUTPUT UNIT *)

(** Before added the output unit convertion, the output unit is determined by 
the input, though they are the same in physics, but they are not same in 
mathematics and computer. 
For example: if the function return 2 'min or 120 's, it will be a mistake after
 removed the unit symbols, and it is a very common operation.
*)

(** Notice that, only input unit check can't promise the output unit is 
correct. *)
Definition get_T_by_N__DONNOT_CHK_CVT_OUTPUT_ex1 N := 
  if negb (QUsameunitb N (#'rpm)) then !! else  (* correct input check *)
  rho * C_T * (D_p ^ 4) * ((N / 60) ^ 2).

Definition get_T_by_N__DONNOT_CHK_CVT_OUTPUT_ex2 N := 
  if negb (QUsameunitb N (#'s)) then !! else  (* error input check *)
  rho * C_T * (D_p ^ 4) * ((N / 60) ^ 2).

(* Eval lazy in (get_T_by_N__DONNOT_CHK_CVT_OUTPUT_ex1 (genQ 1 'rpm)).
Compute QUunit (get_T_by_N__DONNOT_CHK_CVT_OUTPUT_ex1 (genQ 1 'rpm)).
Compute QUunit (get_T_by_N__DONNOT_CHK_CVT_OUTPUT_ex2 (genQ 1 's)). *)


(** After added the output check and convertion, even though you forget the 
input check, the output unit won't mistake. And another benefit is that the 
output unit will be converted from compatible unit to a fixed unit.
For example, output 2 'min will be converted to 120 's. *)
Definition get_T_by_N__CHK_CVT_OUTPUT N := 
  QUconv (rho * C_T * (D_p ^ 4) * ((N / 60) ^ 2)) 'N.

(* Compute QUunit (get_T_by_N__CHK_CVT_OUTPUT (genQ 1 'rpm)).
Compute QUunit (get_T_by_N__CHK_CVT_OUTPUT (genQ 60 'Hz)).
Compute QUunit (get_T_by_N__CHK_CVT_OUTPUT (genQ 60 'A)). *)

(* Eval lazy in (get_T_by_N__CHK_CVT_OUTPUT (genQ 60 'Hz)). *)


(** CHECK INPUT vs. CHECK OUTPUT vs. CONVERT OUTPUT ?
1. CHECK INPUT will check the input has completely matched unit
2. CHECK OUTPUT will check the output has completely matched unit
3. CONVERT OUTPUT will automaticaly convert the output unit to the expected 
unit if they are compatible.
4. suggest that these three operations always enabled.
5. In fact, QUconv finished the CHECK OUTPUT and CONVERT OUTPUT sametime.
*)

(** Definitions for check and convertion, to simplify the writing. *)

(** Check a Q with reference unit *)
Definition CHK_UNIT (q : Q) (refunit : Unit) : Q :=
  if (QUsameunitb q (#refunit)) then q else !!.



(** *** Basic functions *)

(** demo for won't force change the output unit, keep what it is *)
Definition get_T_by_N N := 
  let N := CHK_UNIT N 'rpm in 
  QUconv (rho * C_T * (D_p ^ 4) * ((N / 60) ^ 2)) 'N.

(* Compute QUunit (get_T_by_N (genQ 1 'rpm)). *)


Definition get_M_by_N N := 
  let N := CHK_UNIT N 'rpm in 
  QUconv (C_M * rho * ((N / 60) ^ 2) * (D_p ^ 5)) ('N*'m)%U.

Definition get_E_a_by_N N := 
  let N := CHK_UNIT N 'rpm in 
  QUconv (K_E * N) 'V.

(* Definition get_M_by_I_m I_m := 
  if negb (QUsameunitb I_m ('A)) then !! else
  K_T * (I_m - I_m0).

Definition get_U_m_by_E_a_and_I_m E_a I_m := 
  if negb ((QUsameunitb E_a 'V) && (QUsameunitb I_m 'A)) then !! else
  E_a + R_m * I_m.

Definition get_U_eo_by_U_m_and_I_m U_m I_m := 
  if negb ((QUsameunitb U_m 'V) && (QUsameunitb I_m 'A)) then !! else
  U_m + I_m * R_e.

Definition get_U_eo_by_sigma_e sigma_e := 
  if negb (QUsameunitb sigma_e 1) then !! else
  sigma_e * U_b.

Definition get_I_e_by_sigma_e_and_I_m sigma_e I_m := 
  if negb ((QUsameunitb sigma_e 1) && (QUsameunitb I_m 'A)) then !! else
  sigma_e * I_m.

Definition get_I_b_by_I_e I_e :=
  if negb (QUsameunitb I_e 'A) then !! else
  n_r * I_e + I_other.

Definition get_U_e_by_I_b I_b :=
  if negb (QUsameunitb I_b 'A) then !! else
  U_b - I_b * R_b.

Definition get_T_b_by_I_b I_b :=
  if negb (QUsameunitb I_b 'A) then !! else
  (C_b - C_min) / I_b * val_0_06.

Definition get_G_maxload_by_T T :=
  if negb (QUsameunitb T 'N) then !! else
  n_r * T - G.

Definition get_theta_max_by_T T :=
  if negb (QUsameunitb T 'N) then !! else
  Qacos (G / (n_r * T)).

Definition get_eta_by_M_and_N_and_I_b M N I_b :=
  if negb ((QUsameunitb M ('N*'m)) && (QUsameunitb N 'rpm) && (QUsameunitb I_b 'A)) 
  then !! else
  ((2 * PI) / 60) * n_r * M * N / (U_b * I_b).
*)

(** *** Basic inverse functions *)

Definition get_N_by_T T :=
  let T := CHK_UNIT T 'N in 
  QUconv (60 * QUsqrt (T /(rho * C_T * (D_p ^ 4)))) 'rpm.

(* Compute QUunit (get_N_by_T (genQ 1 'N)). *)

(*
Definition get_N_by_M M :=
  if negb (QUsameunitb M ('N*'m)) then !! else
  60 * (Qsqrt (M / (rho * (D_p ^ 5) * C_M))).
*)

Definition get_N_by_E_a E_a :=
  if negb (QUsameunitb E_a (#'V)) then !! else
  E_a / K_E.
(*
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


(** *** Simplest Form of Function (SFF) *)

Definition get_T_by_G_maxload_sff G_maxload :=
  if negb (QUsameunitb G_maxload 'N) then !! else
  let x := G_maxload in
  let a := / n_r in
  let b := G / n_r in
    a * x + b.

Definition get_G_maxload_by_T_sff T :=
  if negb (QUsameunitb T 'N) then !! else
  let x := T in
  let a := n_r in
  let b := -G in
    a * x + b.

Definition get_N_by_T_sff T :=
  if negb (QUsameunitb T 'N) then !! else
  let x := T in
  let a := 3600 / (rho * C_T * D_p ^ 4) in
    Qsqrt (a * x).

Definition get_T_by_N_sff N :=
  if negb (QUsameunitb N 'rpm) then !! else
  let x := N in
  let a := (rho * C_T * D_p ^ 4) / 3600 in
    a * x ^ 2.

Definition get_M_by_T_sff T :=
  if negb (QUsameunitb T 'N) then !! else
  let x := T in
  let a := C_M * D_p / C_T in
    a * x.

Definition get_T_by_M_sff M :=
  if negb (QUsameunitb M ('N*'m)) then !! else
  let x := M in
  let a := C_T / (C_M * D_p) in
    a * x.

Definition get_M_by_N_sff N :=
  if negb (QUsameunitb N 'rpm) then !! else
  let x := N in
  let a := (C_M * rho * D_p ^ 5) / 3600 in
    a * x ^ 2.

Definition get_N_by_M_sff M :=
  if negb (QUsameunitb M ('N*'m)) then !! else
  let x := M in
  let a := 3600 / (C_M * rho * D_p ^ 5) in
    Qsqrt (a * x).

Definition get_N_by_E_a_sff E_a :=
  if negb (QUsameunitb E_a 'A) then !! else (* todo, I left a bug designed. *)
  let x := E_a in
  let a := /K_E in
    a * x.

Definition get_E_a_by_N_sff N :=
  if negb (QUsameunitb N 'rpm) then !! else
  let x := N in
  let a := K_E in
    a * x.

Definition get_E_a_by_T_sff T := 
  if negb (QUsameunitb T 'N) then !! else
  let x := T in
  let a := 60 * K_E * Qsqrt (/(rho * C_T * D_p ^ 4)) in
    a * (Qsqrt x).

Definition get_T_by_E_a_sff E_a :=
  if negb (QUsameunitb E_a 'V) then !! else
  let x := E_a in
  let a := rho * C_T * D_p ^ 4 * (/(60 * K_E)) ^ 2 in
    a * x ^ 2.

Definition get_U_m_by_N_sff N := 
  if negb (QUsameunitb N 'rpm) then !! else
  let x := N in
  let a := R_m * C_M * rho * (D_p ^ 5) 
    / (3600 * K_T) in
  let b := K_E in
  let c := R_m * I_m0 in
    a * x ^ 2 + b * x + c. *)


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
(*   get_E_a_by_T
  get_G_maxload_by_T
  get_I_m_by_M
  get_I_m_by_T
  get_I_b_by_I_e
  get_I_b_by_T_b
  get_I_b_by_U_e
  get_I_e_by_I_b
  get_I_e_by_E_a_and_I_m
  get_I_e_by_sigma_e_and_I_m
  get_I_e_by_T
  get_M_by_N
  get_M_by_T
  get_M_by_I_m
  get_N_by_M *)
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
  get_U_eo_by_U_m_and_I_m
  get_T_by_G_maxload_sff
  get_G_maxload_by_T_sff
  get_N_by_T_sff
  get_T_by_N_sff
  get_M_by_T_sff
  get_T_by_M_sff
  get_M_by_N_sff
  get_N_by_M_sff
  get_N_by_E_a_sff
  get_E_a_by_N_sff
  get_E_a_by_T_sff
  get_T_by_E_a_sff
  get_U_m_by_N_sff  *)
  : fcs.
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
  : fcs.

Hint Rewrite 
  const_val_0_0065
  const_val_5_2561
  const_val_0_8
  const_val_0_25
  const_val_9_55
  const_val_0_06
  const_val_T_0
  : fcs.


(* lemmas and proof details, please see "Basic_proof.v" *)
