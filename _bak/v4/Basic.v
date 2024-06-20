(*
  category:     flight control system - propulsion subsystem
  filename:     Basic.v
  author:       Zhengpu Shi
  date:         2020.11.17
  purpose:      Basic module for Propulsion System.

  copyright:    Formalized Engineering Mathematics team of NUAA.
  website:      http://fem-nuaa.cn/FML4FCS
*)

Require Export Quantity.
Require Export Raux.

Require Import Extraction.
Require Import Lra.

Open Scope BasicUnit_scope.
Open Scope Unit_scope.
Open Scope Quantity_scope.

(* (** * Quantity, composed by a Real number, and a Unit *)
Definition Quantity : Set := (R * Unit)%type.
Definition mkQ r u : Quantity := (r, u).
Definition Qcoef (q : Quantity) : R := let (r,_) := q in r.
Definition Qunit (q : Quantity) : Unit := let (_,u) := q in u. *)

(** ** Some real number. *)
(* the reason for these variables:
  1. Coq old version (below 8.9) doesn't support enter real numbers
  2. though Coq new version support enter real number, but the representation
     are too urgly.
  3. maintain consistency, forbid enter error.
*)
  
(* --------------------------------------------------------- *)
Parameter val_273_15 : R.     (* 273.15 *)
Parameter val_0_0065 : R.   (* 0.0065 ℃/m *)
Parameter val_5_2561 : R.   (* 5.2561 *)
Parameter val_0_8 : R.      (* 0.8 *)
Parameter val_0_25 : R.     (* 1/4=0.25 *)
Parameter val_9_55 : R.     (* 9.55 *)
Parameter val_0_06 : R.     (* 60/1000 = 0.06 *)

Definition q_0_0065 := val_0_0065 & ('℃/'m).

(* These given real number should positive *)

Axiom gt0_val_0_0065 : 0 < val_0_0065.
Axiom gt0_val_5_2561 : 0 < val_5_2561.
Axiom gt0_val_0_8 : 0 < val_0_8.
Axiom gt0_val_0_25 : 0 < val_0_25.
Axiom gt0_val_9_55 : 0 < val_9_55.
Axiom gt0_val_0_06 : 0 < val_0_06.

Global Hint Resolve 
  gt0_val_0_0065
  gt0_val_5_2561
  gt0_val_0_8
  gt0_val_0_25
  gt0_val_9_55
  gt0_val_0_06
  : fcs.


(** ** Constant of a multicopter *)
(* --------------------------------------------------------- *)

(** Global *)
Parameters
  val_T_0       (* ISA temperature, 288.15 K (15 ℃), use ℃ *) 
  val_h         (* height of a multicopeter, m *)
  val_p_0       (* standard air presure, 101325 Pa *)
  val_rho_0     (* standard air density, 1.293 kg/m^3 *)
  val_T_t       (* temperature of environment, °C  *)
  n_r       (* numbr of propulsiors, None *)
  val_G         (* total weight, g *)
  val_I_other   (* other current, 1 A *)
  : R.

Definition T_0 := val_T_0 & '℃.
Definition h := val_h & 'm.
Definition p_0 := val_p_0 & 'Pa.
Definition rho_0 := val_rho_0 & ('kg / 'm³).
Definition T_t :=  val_T_t & 'K. (* (val_273_15 + val_T_t) 'K. *)
Definition G := val_G & 'g.
Definition I_other := val_I_other & 'A.

(** Propeller *)
Parameters 
  D_p 
  H_p 
  B_p 
  G_p 
  PP_A 
  PP_epsilon 
  PP_lambda 
  PP_zeta 
  PP_e 
  PP_K0 
  PP_alpha0 
  C_fd : R.

(** Motor *)
Parameters 
  K_V0 
  val_I_mMax 
  val_U_m0 
  val_I_m0 
  val_R_m 
  val_G_m : R.

Definition I_mMax := val_I_mMax & 'A.
Definition U_m0 := val_U_m0 & 'V.
Definition I_m0 := val_I_m0 & 'A.
Definition R_m := val_R_m & 'Ω.
Definition G_m := val_G_m & 'g.

(** ESC *)
Parameters 
  val_I_eMax 
  val_R_e 
  val_G_e : R.

Definition I_eMax := val_I_eMax & 'A.
Definition R_e := val_R_e & 'Ω.
Definition G_e := val_G_e & 'g.

(** Battery *)
Parameters 
  val_C_b 
  val_C_min 
  val_K_b 
  val_R_b 
  val_U_b : R.

Definition C_b := val_C_b & 'A.
Definition C_min := val_C_min & 'A.
Definition K_b := val_K_b & 1.
Definition R_b := val_R_b & 'Ω.
Definition U_b := val_U_b & 'V.

(** ** Definitions of some constant numbers *)
(* --------------------------------------------------------- *)

Definition T : Quantity := T_0 - q_0_0065 * h.
Definition val_T : R := val_T_0 - val_0_0065 * val_h.

Print T_0.
Print val_T_0.

Print T.
Print val_T.

Lemma T_ok : T == (val_T & 'K).
Proof. compute. pfqeq. Qed.

Definition p := p_0 * (Qpower (T / T_0) val_5_2561).
Definition val_p : R := val_p_0 * (Rpower (val_T / val_T_0) val_5_2561).
Lemma p_ok : p == (val_p & 'Pa).
Proof. pfqeq. Qed.

Definition rho := (T_0 * p) / (p_0 * (T_0 + T_t)) * rho_0.
Definition val_rho : R := (val_T_0 * val_p) 
  / (val_p_0 * (val_T_0 + val_T_t)) * val_rho_0.
Lemma rho_ok : rho == val_rho & ('kg / 'm³).
Proof. pfqeq. Qed.

Definition C_T := val_0_25 * PI ^ 3 * PP_lambda * (PP_zeta ^ 2)
  * B_p * PP_K0 
  * (PP_epsilon * (Qatan (H_p/(PI*D_p))) - PP_alpha0) 
    / (PI * PP_A + PP_K0).
Definition val_C_T : R := val_0_25 * PI ^ 3 * PP_lambda 
  * (PP_zeta ^ 2)
  * B_p * PP_K0 
  * (PP_epsilon * (atan (H_p / (PI * D_p))) - PP_alpha0) 
    / (PI * PP_A + PP_K0).
Lemma C_T_ok : C_T == val_C_T & 1.
Proof. pfqeq. lra. Qed.

Definition C_d := C_fd + (PI * PP_A * (PP_K0 ^ 2) / PP_e)
  * (
    ((PP_epsilon * (Qatan (H_p/(PI*D_p))) - PP_alpha0) 
    / (PI * PP_A + PP_K0)) ^ 2
    ).

Definition val_C_d : R := C_fd + (PI * PP_A * 
  (PP_K0 ^ 2) / PP_e)
  * (
    ((PP_epsilon * (atan (H_p/(PI*D_p))) 
    - PP_alpha0) 
    / (PI * PP_A + PP_K0)) ^ 2
    ).
Lemma C_d_ok : C_d == val_C_d & 1.
Proof. pfqeq. lra. Qed.

Definition C_M := /((8 & 1) * PP_A) * ((PI * PP_zeta * B_p) ^ 2) 
  * C_d * PP_lambda.
Definition val_C_M : R := /(8 * PP_A) 
  * ((PI * PP_zeta * B_p) ^ 2) 
  * val_C_d * PP_lambda.
Lemma C_M_ok : C_M == val_C_M & 1.
Proof. pfqeq. lra. Qed.

Definition K_E := (U_m0 - I_m0 * R_m) / (K_V0 * U_m0).
Definition val_K_E : R := (val_U_m0 - val_I_m0 * val_R_m) 
  / (K_V0 * val_U_m0).
Lemma K_E_ok : K_E == val_K_E & 1.
Proof. pfqeq. Qed.

Definition K_T := val_9_55 * K_E.
Definition val_K_T : R := val_9_55 * val_K_E.
Lemma K_T_ok : K_T == val_K_T & 1.
Proof. pfqeq. Qed.

(** ** Definitions of basic functions *)
(* --------------------------------------------------------- *)

Definition get_T_by_N N := rho * C_T * (D_p ^ 4) * ((N / 60) ^ 2).

Definition get_M_by_N N := C_M * rho * ((N / 60) ^ 2) * (D_p ^ 5).

Definition get_E_a_by_N N := K_E * N.

Definition get_M_by_I_m I_m := K_T * (I_m - I_m0).

Definition get_U_m_by_E_a_and_I_m E_a I_m := E_a + R_m * I_m.

Definition get_U_eo_by_U_m_and_I_m U_m I_m := U_m + I_m * R_e.

Definition get_U_eo_by_sigma_e sigma_e := sigma_e * U_b.

Definition get_I_e_by_sigma_e_and_I_m sigma_e I_m := sigma_e * I_m.

Definition get_I_b_by_I_e I_e := n_r * I_e + I_other.

Definition get_U_e_by_I_b I_b := U_b - I_b * R_b.

Definition get_T_b_by_I_b I_b := (C_b - C_min) / I_b * val_0_06.

Definition get_G_maxload_by_T T := n_r * T - G.

Definition get_theta_max_by_T T := Qacos (G / (n_r * T)).

Definition get_eta_by_M_and_N_and_I_b M N I_b :=
  ((2 * PI) / 60) * n_r * M * N / (U_b * I_b).


(** ** Definitions of basic inverse functions *)
(* --------------------------------------------------------- *)

Definition get_N_by_T T := 60 * Qsqrt (T /(rho * C_T * (D_p ^ 4))).

Definition get_N_by_M M := 60 * (Qsqrt (M / (rho * (D_p ^ 5) * C_M))).

Definition get_N_by_E_a E_a := E_a / K_E.

Definition get_I_m_by_M M := M / K_T + I_m0.

Definition get_sigma_e_by_U_eo U_eo := U_eo / U_b.

Definition get_I_e_by_I_b I_b := (I_b - I_other) / n_r.

Definition get_I_b_by_T_b T_b := (C_b - C_min) / T_b * val_0_06.

Definition get_I_b_by_U_e U_e := (U_b - U_e) / R_b.

Definition get_T_by_G_maxload G_maxload := (G_maxload + G) / n_r.

Definition get_T_by_theta_max theta_max := G / (n_r * cos theta_max).


(** ** Definitions of extended functions (basic part) *)
(* --------------------------------------------------------- *)

Definition get_T_by_M M := (C_T * M) / (D_p * C_M).

Definition get_M_by_T T := (C_M * D_p * T) / C_T.

Definition get_I_m_by_T T := (C_M * D_p * T) / (K_T * C_T) + I_m0.

Definition get_E_a_by_T T := 60 * K_E * Qsqrt (T / (rho * C_T * (D_p ^ 4))).

Definition get_U_m_by_T T := 
  60 * K_E * Qsqrt (T / (rho * C_T * (D_p ^ 4)))
  + R_m * ((C_M * D_p * T) / (K_T * C_T) + I_m0).

Definition get_U_m_by_N_and_M N M := K_E * N + R_m * (M / K_T + I_m0).

Definition get_U_m_by_N N := 
  K_E * N + R_m 
  * ((C_M * rho * ((N / 60) ^ 2) * (D_p ^ 5)) 
  / K_T + I_m0).

Definition get_U_m_by_M M := 60 * K_E * (Qsqrt (M / (rho * (D_p ^ 5) * C_M))) 
  + R_m * (M / K_T + I_m0).

Definition get_U_eo_by_E_a_and_I_m E_a I_m := E_a + (R_m + R_e) * I_m.

Definition get_U_eo_by_N N := ((R_m + R_e) * C_M * rho * (D_p ^ 5))
  / (K_T * (60 ^ 2)) * (N ^ 2) + K_E * N + (R_m + R_e) * I_m0.

Definition get_sigma_e_by_E_a_and_I_m E_a I_m := 
  (E_a + (R_m + R_e) * I_m) / U_b.

Definition get_I_e_by_E_a_and_I_m E_a I_m := 
  ((E_a + (R_m + R_e) * I_m) * I_m) / U_b.

Definition get_I_e_by_T T := (((60 * K_E * Qsqrt (T / (rho * C_T * (D_p ^ 4)))) 
  + (R_m + R_e) * ((C_M * D_p * T) / (K_T * C_T) + I_m0)) 
  * ((C_M * D_p * T) / (K_T * C_T) + I_m0)) / U_b.

Definition get_U_e_by_I_e I_e := U_b - (n_r * I_e + I_other) * R_b.

Definition get_T_b_by_I_e I_e := (C_b - C_min) / (n_r * I_e + I_other) 
  * val_0_06.


(** ** Definitions of extended functions (advanced part) *)
(* --------------------------------------------------------- *)

(* calculate "Motor speed N" by "Motor input voltage U_m".
   Notice that, Quadratic equations with one variable can have two solutions,
   here, I keep the big one. In fact, another small solution should be 
   discarded, I will give a strict proof later. *)
Definition get_N_by_U_m U_m :=
  (1800 * K_T) / (R_m * C_M * rho * (D_p ^ 5)) * (-K_E + Qsqrt((K_E ^ 2) 
  - (R_m * C_M * rho * (D_p ^ 5) * (R_m * I_m0 - U_m)) / (900 * K_T) )).

(* calculate "Motor speed N" by "ESC output voltage U_eo" *)
Definition get_N_by_U_eo U_eo :=
  (1800 * K_T) / ((R_m + R_e) * C_M * rho * (D_p ^ 5)) 
  * (-K_E + Qsqrt((K_E ^ 2) 
  - ((R_m + R_e) * C_M * rho * (D_p ^ 5)) / (900 * K_T)
  * ((R_m + R_e) * I_m0 - U_eo))).


(** ** Definitions of Simplest Form of Function (SFF) *)
(* --------------------------------------------------------- *)

Definition get_T_by_G_maxload_sff G_maxload :=
  let x := G_maxload in
  let a := /n_r in
  let b := G / n_r in
    a * x + b.

Definition get_G_maxload_by_T_sff T :=
  let x := T in
  let a := n_r in
  let b := -G in
    a * x + b.

Definition get_N_by_T_sff T :=
  let x := T in
  let a := 3600 / (rho * C_T * D_p ^ 4) in
    Qsqrt (a * x).

Definition get_T_by_N_sff N :=
  let x := N in
  let a := (rho * C_T * D_p ^ 4) / 3600 in
    a * x ^ 2.

Definition get_M_by_T_sff T :=
  let x := T in
  let a := C_M * D_p / C_T in
    a * x.

Definition get_T_by_M_sff M :=
  let x := M in
  let a := C_T / (C_M * D_p) in
    a * x.

Definition get_M_by_N_sff N :=
  let x := N in
  let a := (C_M * rho * D_p ^ 5) / 3600 in
    a * x ^ 2.

Definition get_N_by_M_sff M :=
  let x := M in
  let a := 3600 / (C_M * rho * D_p ^ 5) in
    Qsqrt (a * x).

Definition get_N_by_E_a_sff E_a :=
  let x := E_a in
  let a := /K_E in
    a * x.

Definition get_E_a_by_N_sff N :=
  let x := N in
  let a := K_E in
    a * x.

Definition get_E_a_by_T_sff T := 
  let x := T in
  let a := 60 * K_E * Qsqrt (/(rho * C_T * D_p ^ 4)) in
    a * (sqrt x).

Definition get_T_by_E_a_sff E_a :=
  let x := E_a in
  let a := rho * C_T * D_p ^ 4 * (/60 * K_E) ^ 2 in
    a * x ^ 2.

Definition get_U_m_by_N_sff N := 
  let x := N in
  let a := R_m * C_M * rho * (D_p ^ 5) 
    / (3600 * K_T) in
  let b := K_E in
  let c := R_m * I_m0 in
    a * x ^ 2 + b * x + c.

(** ** Update database of autounfold tactics *)
(* --------------------------------------------------------- *)

Global Hint Unfold 
  get_E_a_by_N
  get_E_a_by_T
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
  get_N_by_M
  get_N_by_T
  get_N_by_E_a
  get_N_by_U_m
  get_N_by_U_eo
  get_sigma_e_by_U_eo
  get_sigma_e_by_E_a_and_I_m
  get_T_by_M
  get_T_by_N
  get_T_b_by_I_b
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
  get_U_m_by_N_sff : fcs.


(** ** Some reasonal assumptions *)
(* --------------------------------------------------------- *)

(* Some constant should bigger than zero, other word, should positive *)
Opaque PI atan R.

Axiom gt0_G : 0 < G.       (* total weight*)
Axiom gt0_n_r : 0 < n_r.   (* number of propeller numbers *)
Axiom gt0_D_p : 0 < D_p.   (* propeller diameter *)
Print C_T.
Locate "<".

Check Quantity_cmpP (0) (G) Rlt.
Check 0 < G.

Check Quantity_cmpP (0) (C_T) Rlt.
Check 0 < C_T.

Definition gt0_C_T_1 := 0 < C_T.
(* why Coq crashed here? *)
Parameter pp1 : Quantity_cmpP 0 C_T Rlt.
Compute Quantity_cmpP 0 C_T Rlt.

(* Coq crashed here too. *)
Axiom gt0_C_T_2 : gt0_C_T_1. (* 0 < C_T. *)

Print Rlt.
Print Qlt.
Check 0.
(* Opaque Quantity. *)
Definition q0 : Quantity := Qbasic R0 1.
Print q0.
Check C_T.
Print C_T.
Axiom gt0_C_T : q0 < C_T.   (* thrust coefficient *)
Axiom gt0_C_M : 0 < C_M.   (* torque coefficient *)
Axiom gt0_rho : 0 < rho.   (* atomospheric pressure *)
Axiom gt0_R_b : 0 < R_b.   (* battery resistence *)
Axiom gt0_R_m : 0 < R_m.   (* motor resistence *)
Axiom gt0_R_e : 0 < R_e.   (* ESC resistence *)
Axiom gt0_K_E : 0 < K_E.   (* back-electromotive force constant *)
Axiom gt0_K_T : 0 < K_T.   (* motor torque constant  *)
Axiom gt0_U_b : 0 < U_b.   (* battery voltage *)
Axiom gt0_C_b_minus_C_min : 0 < C_b - C_min.  (* valid range of battery 
  voltage *)

Global Hint Resolve 
  gt0_G
  gt0_n_r
  gt0_D_p
(*   gt0_C_T *)
  gt0_C_M
  gt0_rho
  gt0_R_b
  gt0_R_m
  gt0_R_e
  gt0_K_E
  gt0_K_T
  gt0_U_b
  gt0_C_b_minus_C_min
  : fcs.


(* lemmas and proof details, please see "Basic_proof.v" *)
