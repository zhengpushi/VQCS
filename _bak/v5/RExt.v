(*
  purpose   : auxiliary library for Coq.Reals.
  author    : Zhengpu SHI
  date      : 2021.05
  
  remark    :
  1. possible reason of "field" failure
    a. notation "/", need unfold Rdiv first.
    b. unknown variable name, need be rewrite first.
*)


Require Export Reals.
Require Export Psatz.
Require Export Lra.

Open Scope R_scope.


(** * More properties for Coq.Reals.R *)


(** ** Expand the database of Automatic Tactics *)

(** autounfold with R *)

Global Hint Unfold
  Rminus        (* a - b = a + - b *)
  Rdiv          (* a / b = a * / b *)
  : R.

(** autorewrite with R *)

Hint Rewrite
  Ropp_0            (* - 0 = 0 *)
  Rminus_0_r        (* r - 0 = r *)
  Rplus_0_l         (* 0 + r = r *)
  Rplus_0_r         (* r + 0 = r *)
  Rmult_0_l         (* 0 * r = 0 *)
  Rmult_0_r         (* r * 0 = 0 *)
  Rmult_1_l         (* 1 * r = r *)
  Rmult_1_r         (* r * 1 = r *)
  Ropp_involutive   (* - - r = r *)
  : R.

(** auto with R *)

Global Hint Resolve
  Rplus_lt_0_compat   (* 0 < r1 -> 0 < r2 -> 0 < r1 + r2 *)
  Rmult_lt_0_compat   (* 0 < r1 -> 0 < r2 -> 0 < r1 * r2 *)
  Rinv_0_lt_compat    (* 0 < r -> 0 < / r *)
  Rlt_gt              (* r1 < r2 -> r2 > r1 *)
  Rgt_lt              (* r1 > r2 -> r2 < r1 *)
  Rgt_not_eq          (* r1 > r2 -> r1 <> r2 *)
  PI_RGT_0            (* PI > 0 *)
  : R.


(** ** Control Opaque / Transparent *)

(** mathmatical functions *)
Global Opaque PI.
Global Opaque sqrt.
Global Opaque Rpower.
Global Opaque sin.
Global Opaque cos.
Global Opaque tan.
Global Opaque asin.
Global Opaque atan.
Global Opaque acos.


(** ** Customized Tactics *)

(** a + b <> 0 *)
Ltac plus_neq0 :=
  match goal with
  | |- ?a + ?b <> 0 => apply Rgt_not_eq,Rlt_gt,Rplus_lt_0_compat; 
    auto with R fcs
  end.

(** 0 < a *)
Ltac zero_lt :=
  repeat match goal with
  (* 0 *)
  | H: ?a <> 0 |- 0 < ?a * ?a => apply Rlt_0_sqr; apply H
  | |- 0 < ?a + ?b => apply Rplus_lt_0_compat
  | |- 0 < ?a * ?b => apply Rmult_lt_0_compat
  | |- 0 < sqrt ?a => apply sqrt_lt_R0
  | |- 0 < ?a / ?b => unfold Rdiv
  | |- 0 < / ?a => apply Rinv_0_lt_compat
  | |- 0 < ?a ^ _ => simpl
  | |- 0 < (?a)² => unfold Rsqr
  | |- 0 < ?a => auto with R fcs; try lra
  (* R0 *)
  | |- R0 < ?a * ?b => apply Rmult_lt_0_compat; try lra; auto with R fcs
  | |- R0 < sqrt ?a => apply sqrt_lt_R0
  | |- R0 < ?a / ?b => unfold Rdiv
  | |- R0 < / ?a => apply Rinv_0_lt_compat
  | |- R0 < ?a ^ _ => simpl
  | |- R0 < (?a)² => unfold Rsqr
  | |- R0 < ?a => auto with R fcs; try lra
  end.


(** ( √ r1 * √ r2)^2 = r1 * r2 *)
Lemma sqrt_mult_sqrt : forall (r1 r2 : R), 
  0 <= r1 -> 0 <= r2 ->
  ((sqrt r1) * (sqrt r2)) * ((sqrt r1) * (sqrt r2)) = r1 * r2.
Proof.
  intros. ring_simplify. repeat rewrite pow2_sqrt; auto.
Qed.

(** simplify expression has sqrt and pow2 *)
Ltac simpl_sqrt_pow2 :=
  repeat (
  (* (_²) -> x * x *)
  unfold Rsqr;
  (* (sqrt r1 * sqrt r2)^2 = r1 * r2 *)
  try rewrite sqrt_mult_sqrt;
  (* (sqrt x) ^ 2 = x *)
  try rewrite pow2_sqrt;
  (* sqrt (x ^ 2) = x *)
  try rewrite sqrt_pow2;
  (* (sqrt x * sqrt x) = x *)
  try rewrite sqrt_sqrt
  ).

(** 0 <= a *)
Ltac zero_le :=
  (* simplify sqrt+pow2 *)
  repeat (
  try simpl_sqrt_pow2;
  try match goal with
  (* 0 <= sqrt x *)
  | |- 0 <= sqrt _ => apply sqrt_pos
  (* 0 <= a * a *)
  | |- 0 <= ?a * ?a => apply Rle_0_sqr
  (* 0 <= a -> 0 <= b -> 0 <= a + b *) 
  | |- 0 <= ?a + ?b => apply Rplus_le_le_0_compat
  (* 0 <= a -> 0 <= b -> 0 <= a * b *)
  | |- 0 <= ?a * ?b => apply Rmult_le_pos
  (* if fail, proof < again *)
(*   | |- 0 <= ?a => apply Rlt_le; zero_le
  | |- R0 <= ?a => apply Rlt_le; zero_le *)
  end).

(** a * b <> 0 *)
Ltac mult_neq0 :=
  match goal with
  | |- ?a * ?b <> 0 => apply Rgt_not_eq,Rlt_gt;zero_le
  end.

(** a <> 0 *)
Ltac neq0 :=
  repeat match goal with
  | |- ?a /\ ?b => repeat split
  | |- ?a <> 0 => apply Rgt_not_eq,Rlt_gt; zero_le
  end.


(** ** Customized Definitions *)

(** PI *)
Definition π := PI.

(** ** Proposional Equality o two Real Numbers *)

(** Equality Decidability of Real Number *)
(* Check Req_EM_T. *)


(** ** Boolean Comparison of two Real Numbers *)

(** r1 =? r2 *)
Definition Reqb (r1 r2 : R) : bool :=
  if Req_EM_T r1 r2 then true else false.

Infix "=?" := (Reqb) : R_scope.

(** r1 <=? r2 *)
Definition Rleb (r1 r2 : R) : bool :=
  if Rle_lt_dec r1 r2 then true else false.
Infix "<=?" := (Rleb) : R_scope.

(** r1 <? r2 *)
Definition Rltb (r1 r2 : R) : bool :=
  if Rlt_le_dec r1 r2 then true else false.
Infix "<?" := (Rltb) : R_scope.


Lemma Reqb_comm : forall r1 r2, Reqb r1 r2 = Reqb r2 r1.
Proof.
  intros r1 r2. unfold Reqb.
  destruct (Req_EM_T r1 r2), (Req_EM_T r2 r1); auto. subst. easy.
Qed.

Lemma Reqb_true_iff : forall r1 r2, Reqb r1 r2 = true <-> r1 = r2.
Proof.
  intros r1 r2. split; unfold Reqb; intros; destruct Req_EM_T; auto; lra.
Qed.
 
Lemma Reqb_false_iff : forall r1 r2, Reqb r1 r2 = false <-> r1 <> r2.
Proof.
  intros r1 r2. split; unfold Reqb; intros; destruct Req_EM_T; auto; lra.
Qed. 

Lemma Reqb_refl : forall r, Reqb r r = true.
Proof. intros. unfold Reqb. destruct Req_EM_T; auto. Qed.

Lemma Reqb_trans : forall r1 r2 r3, Reqb r1 r2 = true -> 
  Reqb r2 r3 = true -> Reqb r1 r3 = true.
Proof.
  intros. apply Reqb_true_iff in H,H0. apply Reqb_true_iff. subst; auto.
Qed.

(** r * r = 0 <-> r = 0 *)
Lemma Rmult_eq0_iff_eq0 : forall r, r * r = 0 <-> r = 0.
Proof.
  intros. split; intros.
  - apply Rmult_integral in H. lra. 
  - rewrite H. ring.
Qed.

Global Hint Resolve Rmult_eq0_iff_eq0 : R.

(** r * r <> 0 <-> r <> 0 *)
Lemma Rsqr_neq0_iff_neq0 : forall r, r * r <> 0 <-> r <> 0.
Proof.
  intros. split; intros; intro.
  - rewrite H0 in H. lra.
  - apply Rmult_integral in H0. lra. 
Qed.

Global Hint Resolve Rsqr_neq0_iff_neq0 : R.

(** 0 <= r1*r1 + r2*r2 *)
Lemma Rplus_sqr_sqr_ge0 : forall r1 r2 : R, 0 <= r1 * r1 + r2 * r2.
Proof.
  intros. apply Rplus_le_le_0_compat; zero_le.
Qed.

(** r1 <> 0 \/ r2 <> 0 <-> r1 * r1 + r2 * r2 <> 0 *)
Lemma Rplus_sqr_neq0_iff2 : forall r1 r2 : R,
  r1 <> 0 \/ r2 <> 0 <-> r1 * r1 + r2 * r2 <> 0.
Proof.
  intros. split; intro H.
  - destruct H.
    + rewrite Rplus_comm. apply tech_Rplus; zero_le; zero_lt.
    + apply tech_Rplus; zero_le; zero_lt.
  - destruct (Req_EM_T (r1 * r1) 0) as [E1|E1].
    + rewrite Rmult_eq0_iff_eq0 in E1. right. subst.
      ring_simplify (0 * 0 + r2 * r2) in H. intro. subst. lra.
    + rewrite Rsqr_neq0_iff_neq0 in E1. auto.
Qed.


(** r1*r1 + r2*r2 <> 0 -> 0 < r1*r1 + r2*r2 *)
Lemma Rplus_sqr_sqr_neq0_iff_Rplus_sqr_sqr_gt0 : forall r1 r2 : R,
  r1 * r1 + r2 * r2 <> 0 <-> 0 < r1 * r1 + r2 * r2.
Proof.
  intros. split; intros.
  - apply Rplus_sqr_neq0_iff2 in H. destruct H.
    + apply Rplus_lt_le_0_compat. zero_lt. zero_le.
    + apply Rplus_le_lt_0_compat. zero_le. zero_lt.
  - lra.
Qed.

Global Hint Resolve Rplus_sqr_sqr_neq0_iff_Rplus_sqr_sqr_gt0 : R.

(** r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 <-> r1 * r1 + r2 * r2 + r3 * r3 <> 0 *)
Lemma Rplus_sqr_neq0_iff3 : forall r1 r2 r3 : R,
  r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 <-> r1 * r1 + r2 * r2 + r3 * r3 <> 0.
Proof.
  intros. split; intros.
  - destruct H.
    + rewrite Rplus_assoc. rewrite Rplus_comm. apply tech_Rplus.
      * zero_le.
      * zero_lt.
    + rewrite Rplus_sqr_neq0_iff2 in H.
      rewrite Rplus_assoc. apply tech_Rplus. zero_le.
      auto with R. (* why fail? *)
      apply Rplus_sqr_sqr_neq0_iff_Rplus_sqr_sqr_gt0; auto.
  - rewrite Rplus_sqr_neq0_iff2.
    destruct (Req_EM_T r1 0),(Req_EM_T r2 0),(Req_EM_T r3 0); subst; 
    auto; try lra.
Qed.

(** r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 \/ r4 <> 0 <-> 
    r1 * r1 + r2 * r2 + r3 * r3 + r4 * r4 <> 0 *)
Lemma Rplus_sqr_neq0_iff4 : forall r1 r2 r3 r4 : R,
  r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 \/ r4 <> 0 <-> 
  r1 * r1 + r2 * r2 + r3 * r3 + r4 * r4 <> 0.
Proof.
  intros. split; intro H.
  - destruct H.
    + rewrite Rplus_comm. rewrite Rplus_comm with (r1 := r1*r1).
      rewrite Rplus_assoc. rewrite Rplus_comm with (r1 := r1*r1).
      repeat rewrite <- Rplus_assoc. apply tech_Rplus; zero_le; zero_lt.
    + destruct H.
      * rewrite Rplus_comm. rewrite Rplus_assoc. 
        rewrite Rplus_comm with (r1 := r2 * r2).
        repeat rewrite <- Rplus_assoc. apply tech_Rplus; zero_le; zero_lt.
      * destruct H.
        { repeat rewrite Rplus_assoc. rewrite Rplus_comm with (r2 := r4 * r4).
          repeat rewrite <- Rplus_assoc. apply tech_Rplus; zero_le; zero_lt. }
        { apply tech_Rplus; zero_le; zero_lt. }
  - destruct (r1 * r1 =? 0) eqn : E1.
    + apply Reqb_true_iff in E1. destruct (r2 * r2 =? 0) eqn : E2.
      * apply Reqb_true_iff in E2. destruct (r3 * r3 =? 0) eqn : E3.
        { apply Reqb_true_iff in E3. rewrite E1,E2,E3 in H.
          repeat rewrite Rplus_0_l in H. right;right;right.
          apply Rsqr_neq0_iff_neq0; auto. }
        { apply Reqb_false_iff in E3. right; right; left.
          apply Rsqr_neq0_iff_neq0; auto. }
      * apply Reqb_false_iff in E2. right; left.
          apply Rsqr_neq0_iff_neq0; auto.
    + apply Reqb_false_iff in E1. left. apply Rsqr_neq0_iff_neq0; auto.
Qed.


(** ** Simplification for trigonometric functions *)

Lemma xx_sqr : forall x:R, x * x = Rsqr x.
Proof. auto. Qed.

Lemma cos2_sin2 : forall x:R, Rsqr (cos x) + Rsqr (sin x) = 1.
Proof. intros. rewrite Rplus_comm. apply sin2_cos2. Qed.

Lemma cos_sin : forall x:R, cos x * sin x = sin x * cos x.
Proof. intros. lra. Qed.

Lemma x_neg_x : forall x:R, x + - x = 0.
Proof. intros. lra. Qed.

Lemma neg_x_x : forall x:R, -x + x = 0.
Proof. intros. lra. Qed.

Lemma x_mul_neg_x : forall x y : R, y * -x = - (x * y).
Proof. intros. lra. Qed.

Lemma neg_x_mul_x : forall x y : R, -y * x = - (y * x).
Proof. intros. lra. Qed.

Lemma sqrR1_R1 : R1² = R1.
Proof. unfold Rsqr. ring. Qed.

Lemma one_R1 : 1 = R1.
Proof. ring. Qed.

Lemma inv1_R1 : /1 = R1.
Proof. field. Qed.

Lemma invR1_R1 : /R1 = R1.
Proof. field. Qed.

Lemma sqrtR1_R1 : sqrt R1 = R1.
Proof. apply Rsqr_inj. zero_le. lra. rewrite Rsqr_sqrt.
  rewrite sqrR1_R1. auto. lra.
Qed.

Lemma sqrt1_R1 : sqrt 1 = R1.
Proof. rewrite one_R1. apply sqrtR1_R1. Qed.

Lemma coscos_sinsin : forall x : R, (cos x * cos x + sin x * sin x) = 1.
Proof. intros. rewrite ?xx_sqr. rewrite ?cos2_sin2. auto. Qed.

Lemma sinsin_coscos : forall x : R, (sin x * sin x + cos x * cos x) = 1.
Proof. intros. rewrite ?xx_sqr. rewrite ?sin2_cos2. auto. Qed.

(** r1 - (-r2) = r1 + r2 *)
Lemma Rsub_Rneg : forall (r1 r2 : R), r1 - (- r2) = r1 + r2.
Proof. intros. ring. Qed.

(** Simplify trigonometric function and expression of real number *)
Ltac trigo_simp := 
  rewrite ?Rmult_opp_opp;   (* -x * -x = x * x *)
(*   rewrite ?xx_sqr;          (* x * x = Rsqr x  *) *)
  rewrite ?Rsub_Rneg,       (* r1 - (-r2) = r1 + r2 *)
          ?sin2_cos2,       (* sin^2 + cos^2 = 1 *)
          ?cos2_sin2,       (* cos^2 + sin^2 = 1 *)
          ?coscos_sinsin,   (* cos*cos + sin*sin = 1 *)
          ?sinsin_coscos,   (* sin*sin + cos*cos = 1 *)
          ?cos_sin,         (* cos * sin = sin * cos *)
          ?x_mul_neg_x,     (* y * -x = - (x * y) *)
          ?neg_x_mul_x,     (* -y * x = - (x * y) *)
          ?x_neg_x,         (* x + -x = 0 *)
          ?neg_x_x,         (* -x + x = 0 *)
          ?sqrtR1_R1,       (* sqrt R1 = R1 *)
          ?sqrt1_R1,        (* sqrt 1 = 1 *)
          ?sqrR1_R1,        (* R1² = R1 *)
(*           ?Rinv_1,           (* /1 = 1 *) *)
          ?inv1_R1,         (* /1 = R1 *)
          ?invR1_R1,        (* /R1 = R1 *)
          ?one_R1           (* 1 = R1 *)
  ;
  autorewrite with R;       (* +0, 0+, *0, 0*, *1, 1* *)
  try field;
  auto.


(** ** Properties about sqrt *)

(** x < 0 -> sqrt x = 0 *)
Lemma le0_imply_sqrt_eq0 : forall (x : R), x < 0 -> sqrt x = 0.
Proof.
  intros. Transparent sqrt. unfold sqrt. destruct (Rcase_abs x). auto.
  (* although, x < 0, x >= 0, all appear, lra fail to solve it. *)
  exfalso. lra.
Qed.

(** 0 < sqrt x -> 0 < x *)
Lemma sqrt_gt0_imply_gt0 : forall (x : R), 0 < sqrt x -> 0 < x.
Proof.
  intros. replace 0 with (sqrt 0) in H.
  - apply sqrt_lt_0_alt in H. auto.
  - apply sqrt_0.
Qed.

(* sqrt x = R1 -> x = R1 *)
Lemma sqrt_eqR1_imply_R1 : forall (x : R), sqrt x = R1 -> x = R1.
Proof.
  intros.
  assert ((sqrt x)² = R1). rewrite H. unfold Rsqr. lra. rewrite <- H0.
  rewrite Rsqr_sqrt; auto.
  assert (0 < sqrt x). rewrite H. lra. 
  apply sqrt_gt0_imply_gt0 in H1. lra.
Qed.


(** ** Approximate of two real numbers *)

(** r1 ≈ r2, that means |r1 - r2| <= diff *)
Definition Rapprox (r1 r2 diff : R) : Prop := Rabs (r1 - r2) <= diff.

(** boolean version of approximate function *)
Definition Rapproxb (r1 r2 diff : R) : bool := Rleb (Rabs (r1 - r2)) diff.


