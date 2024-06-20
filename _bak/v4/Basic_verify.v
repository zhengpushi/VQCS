(*
  category:     flight control system - propulsion subsystem
  filename:     Basic_verify.v
  author:       Zhengpu Shi
  date:         2020.11.17
  purpose:      Verification of Basic module.

  copyright:    Formalized Engineering Mathematics team of NUAA.
  website:      http://fem-nuaa.cn/FML4FCS
*)

Require Import Basic.


(** ** Verification for inverse functions *)
(* --------------------------------------------------------- *)

(* THIS IS A DEMO for manually proof. *)
Lemma verify_trans_N_and_T' N : 0 <= N -> get_N_by_T (get_T_by_N N) = N.
Proof.
  intros H1.
  unfold get_N_by_T, get_T_by_N.
  assert (rho * C_T * D_p ^ 4 * (N / 60) ^ 2 /
    (rho * C_T * D_p ^ 4) = (N / 60) ^ 2).
  - compute. f_equal. field. repeat split; auto with fcs.
  - rewrite H. autorewrite with fcs. field. lra.
Qed.

(* THIS IS A DEMO for manually proof, more complex. *)
Lemma verify_trans_N_and_T'' N : 0 <= N -> get_N_by_T (get_T_by_N N) = N.
Proof.
  intros H1.
  unfold get_N_by_T, get_T_by_N.
  remember (rho * C_T * D_p ^ 4) as a.
  (* 60 * sqrt (a * (N/60)^2 / a ) = N *)
  unfold Rdiv.
  rewrite Rinv_r_simpl_m.
  - (* 60 * sqrt ((N / 60) ^ 2) = N *)
    rewrite sqrt_pow2.
    + (* 60 * (N * / 60) = N *)
      rewrite <- Rmult_assoc.
      (* 60 * N * /60 = N *)
      rewrite Rinv_r_simpl_m.
      * reflexivity.
      * lra.    (* 60 <> 0 *)
    + (* 0 <= N * /60 *)
      apply Rle_mult_inv_pos.
      trivial. lra.
  - (* a <> 0 *)
    rewrite Heqa.
    (* rho * C_T * D_p ^ 4 <> 0 *)
    apply Rmult_integral_contrapositive. split.
    + (* rho * C_T <> 0 *)
      apply Rmult_integral_contrapositive. split.
      * (* rho <> 0 *) apply Rgt_not_eq;apply Rlt_gt;apply gt0_rho.
      * (* C_T <> 0 *) apply Rgt_not_eq;apply Rlt_gt;apply gt0_C_T.
    + (* D_p ^ 4 <> 0 *) apply pow_nonzero.
      apply Rgt_not_eq;apply Rlt_gt;apply gt0_D_p.
Qed.

(* THIS IS A DEMO for manually proof, more complex, no comment. *)
Lemma verify_trans_N_and_T''' N : 
  0 <= N -> get_N_by_T (get_T_by_N N) = N.
Proof.
  intros H1. unfold get_N_by_T, get_T_by_N.
  remember (rho * C_T * D_p ^ 4) as a.
  unfold Rdiv. rewrite Rinv_r_simpl_m.
  - rewrite sqrt_pow2.
    + rewrite <- Rmult_assoc. 
      rewrite Rinv_r_simpl_m; trivial.
    + apply Rle_mult_inv_pos. trivial. lra.
  - rewrite Heqa.
    apply Rmult_integral_contrapositive. split.
    + apply Rmult_integral_contrapositive. split.
      * apply Rgt_not_eq. 
        apply Rlt_gt; apply gt0_rho.
      * apply Rgt_not_eq.
      apply Rlt_gt; apply gt0_C_T.
    + apply pow_nonzero; apply Rgt_not_eq;
      apply Rlt_gt;apply gt0_D_p.
Qed.


(* THIS IS A DEMO for automatic proof. *)
Lemma verify_trans_N_and_T N : 
  0 <= N -> get_N_by_T (get_T_by_N N) = N.
Proof. simple_equation. Qed.

Lemma verify_trans_N_and_M N : 0 <= N ->
  get_N_by_M (get_M_by_N N) = N.
Proof.
  simple_equation.
  assert (C_M * rho * (N * / 60) ^ 2 * D_p ^ 5 *
     / (rho * D_p ^ 5 * C_M) = (N /60) ^ 2) as H5.
  - simple_equation.
  - rewrite H5. simple_equation.
Qed.

Lemma verify_trans_N_and_E_a N : U_m0 - I_m0 * R_m <> 0 -> 
  get_N_by_E_a (get_E_a_by_N N) = N.
Proof. simple_equation. Qed.

Lemma verify_trans_I_m_and_M I_m : get_I_m_by_M (get_M_by_I_m I_m) = I_m.
Proof. simple_equation. Qed.

Lemma verify_trans_sigma_e_and_U_eo sigma_e: 
  get_sigma_e_by_U_eo (get_U_eo_by_sigma_e sigma_e) = sigma_e.
Proof. simple_equation. Qed.

Lemma verify_trans_I_e_and_I_b I_e : 
  get_I_e_by_I_b (get_I_b_by_I_e I_e) = I_e.
Proof. simple_equation. Qed.

Lemma verify_trans_I_b_and_T_b I_b : I_b <> 0 ->
  get_I_b_by_T_b (get_T_b_by_I_b I_b) = I_b.
Proof. simple_equation. Qed.

Lemma verify_trans_I_b_and_U_e I_b : 
  get_I_b_by_U_e (get_U_e_by_I_b I_b) = I_b.
Proof. simple_equation. Qed.

Lemma verify_trans_T_and_G_maxload T : 
  get_T_by_G_maxload (get_G_maxload_by_T T) = T.
Proof. simple_equation. Qed.

Lemma verify_trans_T_and_sigma_max T : 
  T <> 0 -> -1 <= G * / (n_r * T) <= 1 ->
  get_T_by_theta_max (get_theta_max_by_T T) = T.
Proof.
  simple_equation. rewrite cos_acos; auto.
  field. repeat split; auto with fcs.
Qed.


(** ** Verification for composition of two or more functions *)
(* --------------------------------------------------------- *)

Lemma verify_get_T_by_M M : 0 <= M ->
  get_T_by_M M = get_T_by_N (get_N_by_M M).
Proof. simple_equation. Qed.

Lemma verify_get_M_by_T M : get_M_by_T (get_T_by_M M) = M.
Proof. simple_equation. Qed.

Lemma verify_get_I_m_by_T T : get_I_m_by_T T = get_I_m_by_M (get_M_by_T T).
Proof. simple_equation. Qed.

Lemma verify_get_E_a_by_T T : get_E_a_by_T T = get_E_a_by_N (get_N_by_T T).
Proof. simple_equation. Qed.

Lemma verify_get_U_m_by_T T :  get_U_m_by_T T = 
  get_U_m_by_E_a_and_I_m 
  (get_E_a_by_T T) (get_I_m_by_T T).
Proof. simple_equation. Qed.

Lemma verify_get_U_m_by_N_and_M N M : get_U_m_by_N_and_M N M =
	get_U_m_by_E_a_and_I_m (get_E_a_by_N N) (get_I_m_by_M M).
Proof. simple_equation. Qed.

Lemma verify_get_U_m_by_N N : get_U_m_by_N N =
	get_U_m_by_N_and_M N (get_M_by_N N).
Proof. simple_equation. Qed.

Lemma verify_get_U_m_by_M M : get_U_m_by_M M =
	get_U_m_by_N_and_M (get_N_by_M M) M.
Proof. simple_equation. Qed.
	
Lemma verify_get_U_eo_by_E_a_and_I_m E_a I_m : 
  get_U_eo_by_E_a_and_I_m E_a I_m = 
  get_U_eo_by_U_m_and_I_m (get_U_m_by_E_a_and_I_m E_a I_m) I_m.
Proof. simple_equation. Qed.

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

Lemma verify_get_I_e_by_T T : 
  get_I_e_by_T T =
	get_I_e_by_E_a_and_I_m (get_E_a_by_T T) (get_I_m_by_T T).
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
  rewrite Rsqr_sol_eq_0_1'; auto with fcs.
  - (* a <> 0 *)
    rewrite Heqa.
    repeat (apply Rmult_integral_contrapositive_currified; simple_equation).
  (* - *)(* 0 <= b ^ 2 - 4 * a * c *)
  - (* x = exp1 \/ x = exp2 *)
    left.
    rewrite Heqx, Heqa, Heqb, Heqc.
    autounfold with fcs.
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
  rewrite Rsqr_sol_eq_0_1'; auto with fcs.
  - (* a <> 0 *)
    rewrite Heqa.
    repeat (apply Rmult_integral_contrapositive_currified; simple_equation).
    (* R_m + R_e <> 0 *)
    apply tech_Rplus; simple_equation.
  (* - *)(* 0 <= b ^ 2 - 4 * a * c *)
  - (* x = exp1 \/ x = exp2 *)
    left.
    rewrite Heqx, Heqa, Heqb, Heqc.
    autounfold with fcs.
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
    repeat (split; auto with fcs).
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

Lemma verify_get_N_by_T_sff T :
  get_N_by_T_sff T = get_N_by_T T.
Proof.
  simple_equation.
  rewrite <- (sqrt_square 60); try lra.
  rewrite <- sqrt_mult_alt; try lra.
  f_equal. field.
  repeat split; auto with fcs.
Qed.
