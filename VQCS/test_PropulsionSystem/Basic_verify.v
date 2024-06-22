(*
  Copyright 2024 ZhengPu Shi
  This file is part of VQCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Formal verification of Basic module - propulsion subsystem
  author    : Zhengpu Shi
  date      : 2020.11
*)


Require Export Basic.

(** ** Verification for inverse functions *)


(** THIS IS A DEMO for manually proof. *)

(** 不指定单位的证明比较困难，因为不能一步展开，需要手动推导 *)
Lemma verify_trans_N_and_T' N :
  (* 0 <= N ->  *)
  qsameub N 'rpm = true ->
  get_N_by_T (get_T_by_N N) = N.
Proof.
  intros.
  (* compute. (* too slow *) *)
  autounfold with Q. rewrite H. unfold q2quR.
  assert (qsameub (q2qu Rmult (rho * C_T * D_p⁴ * (N / 60)²) 'N) 'N = true).
  { apply qsameub_q2qu. 2:{ cbv. lra. } admit. }
  rewrite H0.
  assert (exists (x : R), Qmake x (u2n 'rpm) = N). admit.
  destruct H1. rewrite <- H1 in *. simpl in *.
  assert (0 < x). admit.
  pose proof (PI_bound).
  f_equal. ra.
  unfold Z2R. lazy [Rpower].
  rewrite ln_1. ra. field_simplify; ra.
  remember (val_rho * val_C_T * (val_D_p * (val_D_p * val_D_p²)))%R as r.
  replace (2² * PI² / 60² * (r * (x² / 60²)) / r)%R with
    (2² * PI² * x² / (3600²))%R.
  2:{ field_simplify_eq. ra. split; ra. split; ra. admit. }
  replace (2² * PI² * x² / 3600²)%R with ((2 * PI * x / 3600)^2)%R by ra.
  rewrite ln_pow; ra.
  replace (/ 2 * (INR 2 * ln (2 * PI * x / 3600)))%R with (ln (2 * PI * x / 3600))%R.
  2:{ remember (ln (2 * PI * x / 3600)) as r1. cbv. field. }
  rewrite exp_ln. field_simplify; ra. ra.
Admitted.

?
(** 一个辅助引理，证明 Rpower 函数的底数为正 *)
Fact Pa_Rpower_cond1 : 
  (0 < 1 + - (0.0065 * (val_h * / (273.15 + val_T_t))))%R.
Proof.
  generalize condL_val_h,condH_val_h,condL_val_T_t,condH_val_T_t; intros.
  ?
  tac_le.
Qed.

(** Simplify QUsameunitb *)
Ltac tac_qsimb :=
  repeat (match goal with
  | |- ((if negb (QUsameunitb (if ?b then !! else _) _) then !! else _) == _) =>
    replace b with false; auto
  | |- ((if negb true then !! else _) == _) => 
    lazy beta iota zeta delta [negb]
  | |- ((if negb ?b then !! else _) == _) =>
    replace b with true; auto
  (* 如何使用 !: 或 numgoals 来判断只有一个目标，否则报错，因为检查不通过 *)
  | |- _ => idtac
  end).

Section test.

Lemma verify_trans_N_and_T' (val_N : R) :
  let N := val_N * (#'rpm) in
    (0 <= val_N)%R ->
    (R1 + - (val_0_0065 * (val_h * / (val_T_0 + val_T_t))))%R <> 0 ->
    get_N_by_T (get_T_by_N N) == N.
Proof.
  intros.
  unfold get_N_by_T,get_T_by_N.
  (* 手动消除 CHK_UNIT *)
  replace (CHK_UNIT N 'rpm) with N; [
    idtac |
    compute; destruct (Req_EM_T) as [E1|E1]; [
      progress easy | destruct E1; field]].
  (* 手动消除 QUconv *)
(*   !! simpl.
  
    destruct E1. field.
    
    { simpl. easy.
  
   unfold CHK_UNIT.
  destruct (CHK_UNIT).
  Eval lazy in *.
  lazy. *)
  Abort.

End test.

(** 指定单位后，可以一步展开 *)
Lemma verify_trans_N_and_T' (val_N : R) :
  let N := val_N * (#'rpm) in
    (0 <= val_N)%R ->
    (R1 + - (val_0_0065 * (val_h * / (val_T_0 + val_T_t))))%R <> 0 ->
    get_N_by_T (get_T_by_N N) == N.
Proof.
  intros N Ha Hb.
(*   pfqeq.  (* crash! *) *)

  (* ##. open definitions *)
  autounfold with Q.
  (* ##. clear CHK_UNIT *)
(*   simpl. *)
  lazy [CHK_UNIT].
  (* ##. clear QUsameunitb *)
  destruct (QUsameunitb N (# 'rpm)) eqn:E1.
  2:{ compute in E1. destruct (Req_EM_T) as [E2|E2]; try easy.
    destruct E2. field. }
  1:{ clear E1. 
    destruct (QUsameunitb (QUconv (rho * C_T * D_p ⁴ * (N / 60) ²) 'N) 
    (# 'N)) eqn:E1.
    2:{ apply QUsameunitb_QUconv_false in E1. simpl in E1. easy. }
    1:{ clear E1.
(*       rewrite QUmult_QUsqrt_l. *)
      eapply (QUconv_elim').
      destruct (u2n 'rpm).
(*       simpl. *)
(*       erewrite QUcomps_QUmult.
      destruct (QUcomps 60 _) as [(v1,c1) d1].
      erewrite QUcomps_QUsqrt.
      unfold QUdiv. erewrite QUcomps_QUmult.
      erewrite QUcomps_QUconv.
      erewrite QUcomps_QUmult.
      erewrite QUcomps_QUmult.
      erewrite QUcomps_QUmult.
      unfold rho.
      erewrite QUcomps_QUmult.
      unfold QUdiv. erewrite QUcomps_QUmult.
      erewrite QUcomps_QUmult.
      destruct (QUcomps T_0 _). *)
      Abort.


(* Section verify_trans_N_and_T.
  Variable val_N : R.
  Definition N := val_N * #'rpm.
  Hypothesis H1 : (0 <= val_N)%R.
  
  Axiom exp_p : p == QUmake (val_p_0 * (Rpower (1 - val_0_0065 * (val_h / 
    (val_T_0 + val_T_t))) val_5_2561))%R (u2n 'Pa).
  Fact exp_rho : rho == 
  Eval lazy in (get_T_by_N N).
  Fact exp_get_T_by_N : get_T_by_N N == 
Lemma exp_get_T_by_N (val_N *)


(* (** Simplify Qsqrt *)
Ltac tac_qsqrt :=
  match goal with
  | |- (?a * Qsqrt ?b = ?c) => assert (b = (c/a)²) as H1; 
    try rewrite H1, Qsqrt_Qsqr; pfqeq; autorewrite with Q R
  end.
  
(** 进一步精简证明 *)
Lemma verify_trans_N_and_T (val_N : R) :
  let N := val_N * 'rpm in
    (0 <= val_N)%R ->
    get_N_by_T (get_T_by_N N) = N.
Proof.
  intros; autounfold with Q.
  tac_qsimb. tac_qsqrt.
  - repeat (split; auto with R Q); try (autorewrite with Q; lra).
    + generalize condL_val_T_t, condH_val_T_t; intros; lra.
    + apply Rpower_neq0.
      generalize condL_val_h, condH_val_h;
      generalize condL_val_T_t, condH_val_T_t; intros.
      tac_neq_zero. tac_le.
   - match goal with 
    | |- (?a * (if Rcase_abs ?b then _ else _) = _)%R =>
      destruct (Rcase_abs b); try field; try lra
    end.
Qed.
 
Lemma verify_trans_N_and_M (val_N : R) :
  let N := val_N * 'rpm in
    (0 <= val_N)%R ->
    get_N_by_M (get_M_by_N N) = N.
Proof.
  intros; autounfold with Q.
  tac_qsimb. tac_qsqrt.
  - repeat (split; auto with R Q); try (autorewrite with Q; lra).
    + generalize condL_val_T_t, condH_val_T_t; intros; lra.
    + tac_neq_zero. tac_zero_lt.
    + apply Rpower_neq0.
      generalize condL_val_h, condH_val_h;
      generalize condL_val_T_t, condH_val_T_t; intros.
      tac_neq_zero. tac_le.
   - match goal with 
    | |- (?a * (if Rcase_abs ?b then _ else _) = _)%R =>
      destruct (Rcase_abs b); try field; try lra
    end.
Qed. *)


(** Simplify cos_acos *)

(** Simplify equation in Q. *)
Ltac simple_equation :=
  intros; autounfold with Q;
  tac_qsimb;  (* clear qsimb, this step may not exist. *)
  pfqeq;      (* clear qeq *)
  repeat (try split; auto with R Q);  (* clear and, 0~n steps. *) 
  repeat (autorewrite with R Q; try field; try lra); (* final, 0~n steps. *)
  repeat (try split; auto with R Q).  (* clear and, 0~n steps. *) 
  
(** Simplify equation in Q (only preprocess, do not compute). *)
Ltac simple_equation_prep :=
  intros; autounfold with Q;
  tac_qsimb.

Lemma verify_trans_N_and_E_a (val_N : R) :
  let N := val_N * (#'rpm) in
    (0 <= val_N)%R ->
    (val_U_m0 + - (val_I_m0 * val_R_m))%R <> 0 -> 
    get_N_by_E_a (get_E_a_by_N N) = N.
Proof.
  intros.
  unfold get_N_by_E_a, get_E_a_by_N,N.
  Eval compute in CHK_UNIT (val_N * # 'rpm) 'rpm.
  replace (CHK_UNIT (val_N * # 'rpm) 'rpm) with (val_N * # 'rpm).
  2:{ compute. destruct Req_EM_T; try easy; try lra. }
  match goal with
  | |- (if ?b1 then !! else ?q1) = ?q2 => replace b1 with false
  end.
  2:{
  Compute K_E.
  Compute (K_E * (val_N * # 'rpm)).

  Compute ((QUconv (K_E * (val_N * # 'rpm)) 'V)).
   compute.
  1:{ simpl in E1.
  2:{ compute.
  
  match goal with
  | |- ?q1 / ?q2 = ?q3 => idtac q2
  | |- ?q1 = ?q2 => idtac q1
  end.
  

  
  unfold K_E.
  
  lazy [CHK_UNIT QUsameunitb N K_E].
  Locate "-".
  lazy [QUdiv QUmult QUinv QUsub QUopp QUplus QUconv].
  lazy [U_m0 I_m0 R_m genQU real2QU].
  Search n2u.
  lazy [u2n Nmult n2u].
  lazy [Dplus Uconv].
  lazy [u2n].
  lazy [Deqb].
  lazy beta.
  lazy iota.
  lazy zeta. ??
  lazy delta.
  
  lazy [Nmult n
  
  lazy [QUconv]. lazy [QUmult]. lazy [real2QU].
  lazy [K_E].
  unfold CHK_UNIT. unfold QUsameunitb.
  lazy [QUmult].
   simpl.
  
   unfold QUmult.
  replace (CHK_UNIT (val_N * # 'rpm) 'rpm) with 
  
  destruct (CHK_UNIT).
  2:{
  Eval compute in 
   simpl.
   simpl.
  autounfold with Q.
  
 !!
  lazy.

? simple_equation. Qed.

Lemma verify_trans_I_m_and_M (val_I_m : R) :
  let I_m := val_I_m * ('A) in
    (val_U_m0 + - (val_I_m0 * val_R_m))%R <> 0 ->
    get_I_m_by_M (get_M_by_I_m I_m) = I_m.
Proof. simple_equation. Qed.

Lemma verify_trans_sigma_e_and_U_eo (val_sigma_e : R) :
  let sigma_e := val_sigma_e * 1 in
    val_U_b <> 0 ->
    get_sigma_e_by_U_eo (get_U_eo_by_sigma_e sigma_e) = sigma_e.
Proof. simple_equation. Qed.

Lemma verify_trans_I_e_and_I_b (val_I_e : R) :
  let I_e := val_I_e * ('A) in
    val_n_r <> 0 ->
    get_I_e_by_I_b (get_I_b_by_I_e I_e) = I_e.
Proof. simple_equation. Qed.

Lemma verify_trans_I_b_and_T_b (val_I_b : R) :
  let I_b := val_I_b * ('A) in
    I_b <> 0 ->
    val_I_b <> 0 ->
    (val_C_b * 3600 + - (val_C_min * 3600))%R <> 0 ->
    get_I_b_by_T_b (get_T_b_by_I_b I_b) = I_b.
Proof. simple_equation. Qed.

Lemma verify_trans_I_b_and_U_e (val_I_b : R) :
  let I_b := val_I_b * ('A) in
    val_R_b <> 0 ->
    get_I_b_by_U_e (get_U_e_by_I_b I_b) = I_b.
Proof. simple_equation. Qed.

Lemma verify_trans_T_and_G_maxload (val_T : R) :
  let T := val_T * ('N) in
    get_T_by_G_maxload (get_G_maxload_by_T T) = T.
Proof. simple_equation. Qed.

Lemma verify_trans_T_and_sigma_max (val_T : R) :
  let T := val_T * ('N) in
    val_T <> 0 ->
    (0 < val_G)%R ->
    (-1 <= val_G * / (val_n_r * val_T) <= 1)%R ->
    get_T_by_theta_max (get_theta_max_by_T T) = T.
Proof. simple_equation. Qed.


(** ** Verification for composition of two or more functions *)
(* --------------------------------------------------------- *)

Lemma verify_get_T_by_M (val_M : R) :
  let M := val_M * ('N * 'm) in
    0 <= M ->
    (0 < val_M * / (273.15 * (val_p_0 * Rpower (1 + - (0.0065 * (val_h * / (273.15 
    + val_T_t)))) 5.2561) * / (val_p_0 * (273.15 + val_T_t)) * val_rho_0 *
    (val_D_p * (val_D_p * (val_D_p * val_D_p²))) * (/ ((1 + 1) * (1 + 1)² * 
    val_PP_A) * (PI² * val_PP_zeta² * val_B_p²) * (val_C_fd + PI * val_PP_A * 
    val_PP_K0² * / val_PP_e * ((val_PP_epsilon * atan (val_H_p * / (PI * 
    val_D_p)) + - val_PP_alpha0)² * (/ (PI * val_PP_A + val_PP_K0))²)) * 
    val_PP_lambda)))%R ->
    get_T_by_N (get_N_by_M M) = get_T_by_M M.
Proof.
(*   simple_equation. *)
  simple_equation_prep.
  unfold Qdiv. rewrite Qmult_Qinv_simpl_mid.
  match goal with 
  | |- ?a * (Qsqrt ?c)² = ?e => 
  idtac c end.
  2:{ simpl. lra. }
  rewrite Qsqr_Qsqrt.
  2:{ lazy. autorewrite with R Q.
    destruct (Rle_lt_dec); auto. lra. }
  pfqeq. autorewrite with R Q.
  destruct (Rcase_abs); auto. lra.
  Abort. (* because expand too much, but Rpower will not be solved automaticly.
    So, we need more advanced technology. *)
  

Lemma verify_get_T_by_E_a (val_E_a : R) :
  let E_a := val_E_a * ('V) in
    (val_U_m0 + - (val_I_m0 * val_R_m))%R <> 0 ->
    (273.15 + val_T_t)%R <> 0 ->
    get_T_by_E_a E_a = get_T_by_N (get_N_by_E_a E_a).
Proof. simple_equation. Qed.

Lemma verify_get_M_by_T (val_M : R) :
  let M := val_M * ('N * 'm) in
    (val_C_fd * (val_PP_e * (PI * val_PP_A + val_PP_K0)²) + PI * val_PP_A * 
      val_PP_K0² * (val_PP_epsilon * atan (val_H_p * / (PI * val_D_p)) 
      + - val_PP_alpha0)²)%R <> 0 ->
    get_M_by_T (get_T_by_M M) = M.
Proof. simple_equation. Qed.

Lemma verify_get_I_m_by_T (val_T : R) :
  let T := val_T * ('N) in
    (val_U_m0 + - (val_I_m0 * val_R_m))%R <> 0 ->
    get_I_m_by_T T = get_I_m_by_M (get_M_by_T T).
Proof. simple_equation. Qed.

Lemma verify_get_E_a_by_T (val_T : R) :
  let T := val_T * ('N) in
    get_E_a_by_T T = get_E_a_by_N (get_N_by_T T).
Proof. simple_equation. Qed.

Lemma verify_get_U_m_by_T (val_T : R) :
  let T := val_T * ('N) in
  get_U_m_by_T T = get_U_m_by_E_a_and_I_m (get_E_a_by_T T) (get_I_m_by_T T).
Proof. simple_equation. Qed.

Lemma verify_get_U_m_by_N_and_M (val_N val_M : R) :
  let N := val_N * 'rpm in
  let M := val_M * ('N * 'm) in
    get_U_m_by_N_and_M N M =
	get_U_m_by_E_a_and_I_m (get_E_a_by_N N) (get_I_m_by_M M).
Proof. simple_equation. Qed.

Lemma verify_get_U_m_by_N (val_N : R) :
  let N := val_N * 'rpm in
    get_U_m_by_N N = get_U_m_by_N_and_M N (get_M_by_N N).
Proof. simple_equation. Qed.

Lemma verify_get_U_m_by_M (val_M : R) :
  let M := val_M * ('N * 'm) in
    (val_U_m0 + - (val_I_m0 * val_R_m))%R <> 0 ->
    get_U_m_by_M M =
	get_U_m_by_N_and_M (get_N_by_M M) M.
Proof. simple_equation. Qed.

Lemma verify_get_U_eo_by_E_a_and_I_m E_a I_m : 
  get_U_eo_by_E_a_and_I_m E_a I_m = 
  get_U_eo_by_U_m_and_I_m (get_U_m_by_E_a_and_I_m E_a I_m) I_m.
Proof. ? simple_equation. Qed.

Lemma verify_get_U_eo_by_N N : get_U_eo_by_N N =
  get_U_eo_by_E_a_and_I_m (get_E_a_by_N N) 
  (get_I_m_by_M (get_M_by_N N)).
Proof. simple_equation. Qed.

Lemma verify_get_sigma_e_by_E_a_and_I_m E_a I_m : 
	get_sigma_e_by_E_a_and_I_m E_a I_m = 
	get_sigma_e_by_U_eo (get_U_eo_by_E_a_and_I_m E_a I_m).
Proof. simple_equation. Qed.

Lemma verify_get_I_e_by_E_a_and_I_m E_a I_m : 
  get_I_e_by_E_a_and_I_m E_a I_m = 
  get_I_e_by_sigma_e_and_I_m (get_sigma_e_by_E_a_and_I_m E_a I_m) I_m.
Proof. simple_equation. Qed.

Lemma verify_get_I_e_by_T (val_T : R) :
  let T := val_T * ('N) in
    get_I_e_by_T T = get_I_e_by_E_a_and_I_m (get_E_a_by_T T) (get_I_m_by_T T).
Proof. simple_equation. Qed.

Lemma verify_get_U_e_by_I_e I_e : get_U_e_by_I_e I_e = 
    get_U_e_by_I_b (get_I_b_by_I_e I_e).
Proof. simple_equation. Qed.

Lemma verify_get_T_b_by_I_e I_e : 0 < I_e -> 
  get_T_b_by_I_e I_e = get_T_b_by_I_b (get_I_b_by_I_e I_e).
Proof. simple_equation. Qed.

(* This lemma is come from "Rsqr_sol_eq_0_1", but could handle Real type 
  directly, because original lemman give more complex datatypes I needn't *)
Lemma Rsqr_sol_eq_0_1' :
  forall (a:R) (b c x:R),
    a <> 0 ->
    0 <= b ^ 2 - 4 * a * c ->
    x = (- b + sqrt (b ^ 2 - 4 * a * c)) / (2 * a) \/ 
    x = (- b - sqrt (b ^ 2 - 4 * a * c)) / (2 * a) 
    -> a * x ^ 2 + b * x + c = 0.
Proof.
    intros.
    elim H1.
    - intro.
      rewrite H2. field_simplify.
      rewrite pow2_sqrt. field. apply H. apply H0. apply H.
    - intro.
      rewrite H2. field_simplify.
      rewrite pow2_sqrt. field. apply H. apply H0. apply H.
  Qed.

Lemma verify_get_N_by_U_m U_m : 
  0 <= K_E ^ 2 - 4 * (R_m * C_M * rho * D_p ^ 5 
    * (/60) ^ 2 * (/K_T)) 
  * (R_m * I_m0 - U_m) ->
  get_U_m_by_N (get_N_by_U_m U_m) = U_m.
Proof.
  intros H.
  (* TO GET THIS FORM: a * x^2 + b * x + c = 0 *)
  remember (get_N_by_U_m U_m) as x.
  unfold get_U_m_by_N.
  remember (K_E) as b.
  ring_simplify.
  rewrite (Rminus_diag_uniq _ U_m); trivial.
  remember (R_m * I_m0 - U_m) as c.
  remember (R_m * C_M * rho * D_p ^ 5 * (/60) ^ 2 * (/K_T)) as a.
  assert (H0: (b * x + R_m * (C_M * rho * (x / 60) ^ 2 
    * D_p ^ 5 / K_T) + R_m * I_m0 - U_m) 
    = (a * x ^ 2 + b * x + c)).
  { rewrite Heqa, Heqc. unfold Rdiv. ring. }
  rewrite H0.
  (* THE FORM IS READY. try to get solution *)
  rewrite Rsqr_sol_eq_0_1'; auto with flyctrl.
  - (* a <> 0 *)
    rewrite Heqa.
    repeat (apply Rmult_integral_contrapositive_currified; simple_equation).
  (* - *)(* 0 <= b ^ 2 - 4 * a * c *)
  - (* x = exp1 \/ x = exp2 *)
    left.
    rewrite Heqx, Heqa, Heqb, Heqc.
    autounfold with flyctrl.
    ring_simplify.
    (* MANUALLY, extract some common expressions, use my eyes. *)
    remember (R_m * C_M * rho * D_p ^ 5) as k1.
    remember (R_m * I_m0 - U_m) as k2.
    remember (sqrt (K_E ^ 2 - k1 * k2 / (900 * K_T))) as k3.
    remember (sqrt (K_E ^ 2 - 4 * (k1 * (/ 60) ^ 2 * / K_T) 
      * k2)) as k4.
    replace k4 with k3.
    + field. rewrite Heqk1. simple_equation. simple_equation. 
    + (* k3 = k4 *)
      rewrite Heqk3, Heqk4. 
      f_equal. simple_equation.
  Qed.

Lemma verify_get_N_by_U_eo U_eo : 
  0 <= K_E ^ 2 - 4 * ((R_m + R_e) * C_M * rho * D_p ^ 5 * (/60) ^ 2 * (/K_T)) 
  * ((R_m + R_e) * I_m0 - U_eo) ->
  get_U_eo_by_N (get_N_by_U_eo U_eo) = U_eo.
Proof.
  intros.
  (* TO GET THIS FORM: a * x^2 + b * x + c = 0 *)
  remember (get_N_by_U_eo U_eo) as x.
  unfold get_U_eo_by_N.
  remember (K_E) as b.
  rewrite (Rminus_diag_uniq _ U_eo); auto.
  remember ((R_m + R_e) * I_m0 - U_eo) as c.
  remember ((R_m + R_e) * C_M * rho * D_p^5 * (/60)^2 * (/K_T)) as a.
  assert (H0: ((R_m + R_e) * C_M * rho * D_p ^ 5 / (K_T * 60 ^ 2) * x ^ 2 
    + b * x + (R_m + R_e) * I_m0 - U_eo) = (a * x^2 + b *x + c)).
  { rewrite Heqa, Heqc. repeat unfold Rdiv. simple_equation. }
  rewrite H0.
  (* THE FORM IS READY. try to get solution *)
  rewrite Rsqr_sol_eq_0_1'; auto with flyctrl.
  - (* a <> 0 *)
    rewrite Heqa.
    repeat (apply Rmult_integral_contrapositive_currified; simple_equation).
    (* R_m + R_e <> 0 *)
    apply tech_Rplus; simple_equation.
  (* - *)(* 0 <= b ^ 2 - 4 * a * c *)
  - (* x = exp1 \/ x = exp2 *)
    left.
    rewrite Heqx, Heqa, Heqb, Heqc.
    autounfold with flyctrl.
    ring_simplify.
    (* MANUALLY, extract some common expressions, use my eyes. *)
    remember (R_m * C_M * rho * D_p ^ 5) as k1.
    remember ((R_m + R_e) * I_m0 - U_eo) as k2.
    remember (sqrt (K_E ^ 2 - (R_m + R_e) * C_M * rho * D_p ^ 5 / (900 * K_T) 
      * k2)) as k3.
    remember (sqrt (K_E ^ 2 - 4 * ((R_m + R_e) * C_M * rho * D_p ^ 5 
      * (/ 60) ^ 2 * / K_T) * k2)) as k4.
    replace k4 with k3.
    simple_equation.
    repeat (split; auto with flyctrl).
    (* R_m + R_e <> 0 *)
    apply tech_Rplus; simple_equation.
    (* k3 = k4 *)
    rewrite Heqk3, Heqk4. 
    f_equal. simple_equation.
Qed.

(** ** Verification for SFF *)
(* --------------------------------------------------------- *)

Lemma verify_get_T_by_G_maxload_sff G_maxload : 
  get_T_by_G_maxload G_maxload = get_T_by_G_maxload_sff G_maxload.
Proof. simple_equation. Qed.

Lemma verify_get_G_maxload_by_T_sff T :
  get_G_maxload_by_T_sff T = get_G_maxload_by_T T.
Proof. simple_equation. Qed.

Lemma verify_get_N_by_T_sff T :
  0 <= T -> get_N_by_T_sff T = get_N_by_T T.
Proof. simple_equation.
  remember (rho * C_T * D_p ^ 4).
  replace (60 * sqrt (T * / r)) with (sqrt (3600 * (T * / r))).
  f_equal. ring. rewrite sqrt_mult; simple_equation.
  - f_equal. replace (3600) with (60 * 60); try lra.
    rewrite sqrt_square; try lra.
  - rewrite Heqr. simple_equation.
  Qed.

Lemma verify_get_T_by_N_sff T :
  get_T_by_N_sff T = get_T_by_N T.
Proof. simple_equation. Qed.

Lemma verify_get_M_by_T_sff T :
  get_M_by_T_sff T = get_M_by_T T.
Proof. simple_equation. Qed.

Lemma verify_get_T_by_M_sff T :
  get_T_by_M_sff T = get_T_by_M T.
Proof. simple_equation. Qed.

Lemma verify_get_M_by_N_sff T :
  get_M_by_N_sff T = get_M_by_N T.
Proof. simple_equation. Qed.

Lemma verify_get_N_by_E_a_sff T :
  get_N_by_E_a_sff T = get_N_by_E_a T.
Proof. simple_equation. Qed.

Lemma verify_get_E_a_by_N_sff T :
  get_E_a_by_N_sff T = get_E_a_by_N T.
Proof. simple_equation. Qed.

Lemma verify_get_T_by_E_a_sff T :
  get_T_by_E_a_sff T = get_T_by_E_a T.
Proof. simple_equation. Qed.

Lemma verify_get_U_m_by_N_sff T :
  get_U_m_by_N_sff T = get_U_m_by_N T.
Proof. simple_equation. Qed.




