(*
  purpose:    Extension to equality and inequalities of Real number.
  author:     Zhengpu Shi
  date:       2020.11
*)

Require Export Reals.
Require Export Fourier.
Require Export DiscrR.
Require Export Lra.

Open Scope R.


(** Expand Database of automatic tactics and method *)

(* Some lemmas which about inequalities of real number from Standard Library *)
Global Hint Resolve 
  Rlt_0_1               (* 0 < 1 *)
  Rmult_le_pos          (* 0 <= r1 -> 0 <= r2 -> 0 <= r1 * r2 *)
  Rmult_lt_0_compat     (* 0 < r1 -> 0 < r2 -> 0 < r1 * r2 *)
  Rgt_not_eq            (* r1 > r2 -> r1 <> r2 *)
  Rgt_lt                (* r1 > r2 -> r2 < r1 *)
  Rlt_le                (* r1 < r2 -> r1 <= r2 *)
  Rlt_not_eq            (* r1 < r2 -> r1 <> r2 *)
  Rlt_gt                (* r1 < r2 -> r2 > r1 *)
  pow_lt                (* 0 < x -> 0 < x ^ n *)
  pow_nonzero           (* x <> 0 -> x ^ n <> 0 *)
  Rinv_neq_0_compat     (* r <> 0 -> / r <> 0 *)
  Rmult_integral_contrapositive (* r1 <> 0 /\ r2 <> 0 -> r1 * r2 <> 0 *)
  cos_acos              (* cos (acos x) = x *)
  : fcs.

(* Some lemmas which about eqaulitions of real number from Standard Library *)
Hint Rewrite 
  Rinv_r_simpl_m        (* r1 <> 0 -> r1 * r2 * / r1 = r2 *)
  Rsqr_sqrt             (* 0 <= x -> (sqrt x)² = x *)
  sqrt_pow2             (* 0 <= x -> sqrt (x ^ 2) = x *)
  Rsqr_pow2             (* x² = x ^ 2 *)
  : fcs.

(* Hint Rewrite -> Rsqr_pow2 : fcs.      (* x² = x ^ 2 *)
Hint Rewrite <- Rsqr_pow2 : fcs.      (* x² = x ^ 2 *)
 *)

(** Some extra lemmas defined by myself *)

Lemma inv_gt0 (r:R) : 0 < r -> 0 < /r.
  Proof.
  intros. apply Rinv_0_lt_compat. trivial.
  Qed.
Global Hint Resolve inv_gt0 : fcs.

Lemma inv_ge0 (r:R) : 0 < r -> 0 <= /r. 
  Proof. auto with fcs. Qed.
Global Hint Resolve inv_ge0 : fcs.

Lemma pow2_sqrt (r:R) : 0 <= r -> (sqrt r) ^ 2 = r.
  Proof.
  intros. rewrite <- Rsqr_pow2. rewrite Rsqr_sqrt; auto.
  Qed.
Hint Rewrite pow2_sqrt : fcs.


(** Some use-defined tactics *)

(* a tactic that help solve the equation for flight contrl. *)
Ltac simple_equation :=
  intros;                           (* import hypothesis *)
  repeat autounfold with fcs;       (* unfold definitions *)
  auto with fcs;                    (* solve trivial *)
  unfold Rdiv;                      (* unfold the divide operator *)
  autorewrite with fcs;             (* try to rewrite and simple *)
  try field;                        (* solve an equation *)
  try lra;                          (* solve an inequation, instead fourier *)
  auto with fcs;                    (* solve trivial again *)
  (* handle: 0 <= A * B *)
  try apply Rmult_le_pos; auto with fcs;
  (* handle: A * B * C <> 0 *)
  try apply Rmult_integral_contrapositive; auto with fcs;
  (* handle: P1 /\ P2 /\ P3 *)
  repeat try split; auto with fcs.
