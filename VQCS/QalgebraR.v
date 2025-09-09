(*
  Copyright 2024 ***
  This file is part of VQCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Algebra of Quantities on R type
  author    : ***
  date      : 2024.06
*)

From FinMatrix Require Export RExt.
Require Import SI.
Import SI_Accepted SI_Prefix.
From FinMatrix Require Import MyExtrOCamlR.

Require Export Qalgebra.

Declare Scope QuR_scope.
Delimit Scope QuR_scope with QR.

Open Scope Unit_scope.
Open Scope Quantity_scope.
Open Scope QuR_scope.


(* ######################################################################### *)
(** * Algebraic operations for quantities of type R, derived from the Qalgebra *)

Definition QuR := @Quantity R.

Definition u2qR (x : R) (u : Unit) : QuR := @u2q R x u.
Definition r2q (r : R) : QuR := a2q r.
Coercion r2q : R >-> QuR.

Definition qoneR : QuR := qone 1.

Definition qcvtbleR (q1 q2 : QuR) : Prop := qcvtble q1 q2.
Definition qcvtblebR (q1 q2 : QuR) : bool := qcvtbleb q1 q2.
Definition q2qnR (q : QuR) (nref : Nunit) : QuR  := q2qn Rmult q nref.
Definition q2quR (q : QuR) (uref : Unit) : QuR := q2qu Rmult q uref.
Definition q2qR (q qref : QuR) : QuR := q2q Rmult q qref.

Definition qaddR (q1 q2 : QuR) : QuR := qadd Rplus q1 q2.
Definition qaddlR (q1 q2 : QuR) : QuR := qaddl Rmult Rplus q1 q2.
Definition qaddrR (q1 q2 : QuR) : QuR := qaddr Rmult Rplus q1 q2.
Definition qoppR (q : QuR) : QuR := qopp Ropp q.
Definition qsubR (q1 q2 : QuR) : QuR := qsub Rplus Ropp q1 q2.
Definition qsublR (q1 q2 : QuR) : QuR := qsubl Rmult Rplus Ropp q1 q2.
Definition qsubrR (q1 q2 : QuR) : QuR := qsubr Rmult Rplus Ropp q1 q2.
Definition qmulR (q1 q2 : QuR) : QuR := qmul Rmult q1 q2.
Definition qpowR (q : QuR) (z : Z) : QuR := qpow powerRZ q z.
Definition qinvR (q : QuR) : QuR := qinv Rinv q.
Definition qdivR (q1 q2 : QuR) : QuR := qdiv Rmult Rinv q1 q2.

Infix "+" := qaddR : QuR_scope.
Infix "'+" := qaddlR : QuR_scope.
Infix "+'" := qaddrR : QuR_scope.
Notation "- q" := (qoppR q) : QuR_scope.
Infix "-" := qsubR : QuR_scope.
Infix "'-" := qsublR : QuR_scope.
Infix "-'" := qsubrR : QuR_scope.
Infix "*" := qmulR : QuR_scope.
Infix "^" := qpowR : QuR_scope.
Notation " q ² " := (q ^ 2) : QuR_scope.
Notation " q ³ " := (q ^ 3) : QuR_scope.
Notation " q ⁴ " := (q ^ 4) : QuR_scope.
Notation " q ⁵ " := (q ^ 5) : QuR_scope.
Notation "/ q" := (qinvR q) : QuR_scope.
Infix "/" := qdivR : QuR_scope.


(** Absolute value function *)
Definition qabs (q : QuR) : QuR := qop1 Rabs q.

(** Any power of quantity which the unit of base and exponent both are 1 *)
Definition qpower (base exp : QuR) : QuR := qdim0op2 Rpower base exp.

(** Trigonometric functions or its inverse require the dimensionless unit, where
    1. trigometric functions need input unit 1 and output unit radian,
    2. inverse trigometric functions require input unit radian and output 1.
    Moreover, radian is equal to 1 *)
Definition qsin (q : QuR) : QuR := qdim0op1 sin q.
Definition qcos (q : QuR) : QuR := qdim0op1 cos q.
Definition qtan (q : QuR) : QuR := qdim0op1 tan q.
Definition qasin (q : QuR) : QuR := qdim0op1 asin q.
Definition qacos (q : QuR) : QuR := qdim0op1 acos q.
Definition qatan (q : QuR) : QuR := qdim0op1 atan q.

Notation "''sin' x" := (qsin x) (at level 10) : QuR_scope.
Notation "''cos' x" := (qcos x) (at level 10) : QuR_scope.
Notation "''tan' x" := (qtan x) (at level 10) : QuR_scope.
Notation "''asin' x" := (qasin x) (at level 10) : QuR_scope.
Notation "''acos' x" := (qacos x) (at level 10) : QuR_scope.
Notation "''atan' x" := (qatan x) (at level 10) : QuR_scope.

(** Automation for quantity equality of R type *)
Ltac qeqR :=
  (* simplify *)
  intros; cbv;
  (* help to solve eq/ineq contains PI *)
  try match goal with
  | H:context[PI] |- _ => pose proof (PI_bound)
  | |- context[PI] => pose proof (PI_bound)
  end;
  (* elim Rbool, solve R contracdiction *)
  autoRbool; auto; try lra;
  (* elim Qmake, option, tuple, not *)
  try match goal with | |- Qmake _ _ = Qmake _ _ => f_equal end;
  try match goal with | |- Some _ = Some _ => f_equal end;
  try match goal with | |- (_, _) = (_, _) => f_equal end;
  try match goal with | |- _ -> False => intro end;
  (* solve simple cases, such contracdiction *)
  try easy;
  (* elim R *)
  try lra.


(* ######################################################################### *)
(** * Specific operations for quantities of type R *)

(** z-th root of a [Quantity] `q` *)
Definition qrootR (q : QuR) (z : Z) : QuR :=
  match q with
  | Qmake v n => Qmake (Rpower v (/Z2R z)) (nroot n z)
  | _ => !!
  end.

(** The condition of [qroot]
  1. q is valid
  2. the value of the quantity q must be positive
  3. the coefficient of the unit of q must be positive
  4. [nrootCondb] also hold, i.e., z must be positive, and the dimension 
  of `q` is divisible by z *)
Definition qrootCondR (q : QuR) (z : Z) : Prop :=
  match q with
  | Qmake v n => (0 < v) /\ (0 < (ncoef n)) /\ nrootCond n z
  | _ => False
  end.

Definition qrootCondbR (q : QuR) (z : Z) : bool :=
  match q with
  | Qmake v n => (0 <? v) && (0 <? (ncoef n)) && nrootCondb n z
  | _ => false
  end.

(** sqrt *)
Definition qsqrt (q : QuR) : QuR := qrootR q 2.

Lemma qrootR_qsqr : forall q, qrootCondR q 2 -> qrootR (q * q) 2 = q.
Proof.
  intros. unfold qrootR, qrootCondR, nrootCond in *.
  destruct q; simpl; auto. logic. f_equal.
  rewrite Rpower_inv2. ra. rewrite nroot2_nmul; auto.
Qed.

Lemma qsqr_qrootR : forall q, qrootCondR q 2 -> (qrootR q 2)² = q.
Proof.
  intros. unfold qrootR, qrootCondR, nrootCond in *.
  destruct q; simpl; auto. logic. f_equal.
  rewrite Rpower_inv2. ra. rewrite npow_nroot2; auto.
  unfold nrootCond. logic.
Qed.

(** boolean comparison: q1 equal to q2 *)
Definition qeqbR (q1 q2 : QuR) : bool := qcmpb Rmult Reqb q1 q2.
(** boolean comparison: q1 less than q2 *)
Definition qltbR (q1 q2 : QuR) : bool := qcmpb Rmult Rltb q1 q2.
(** boolean comparison: q1 less than or equal to q2 *)
Definition qlebR (q1 q2 : QuR) : bool := qcmpb Rmult Rleb q1 q2.

Infix "=?"  := qeqbR : QuR_scope.
Infix "<?"  := qltbR : QuR_scope.
Infix "<=?" := qlebR : QuR_scope.

(** [qeqbR] is true, it is reflexive. *)
Lemma qeqbR_true_refl q : q =? q = true.
Proof.
  (* Note, if q is !!, then it is not true, *)
Abort.

(** [qeqbR] is commutative *)
Lemma qeqbR_comm q1 q2 : (q1 =? q2) = (q2 =? q1).
Proof.
Abort.


(* ######################################################################### *)
(** * Examples *)
Section test.

  (* ---------------------------------------------------- *)
  (* plus *)

  (* plus with same Unit *)

  (* 3 s + 2 s = 1 s + 4 s *)
  Goal (u2qR 3 's) + (u2qR 2 's) = (u2qR 1 's) + (u2qR 4 's).
  Proof. qeqR. Qed.
  
  (* plus with different Unit directly is wrong *)
  
  (* 1 min + 60 s = !! *)
  Goal (u2qR 1 'min) + (u2qR 60 's) = !!.
  Proof. qeqR. Qed.

  (* we can manually make a unit conversion *)

  (* q2q (1 min) s + 60 s = 120 s *)
  Goal q2quR (u2qR 1 'min) 's + (u2qR 60 's) = u2qR 120 's.
  Proof. qeqR. Qed.

  (* 1 min + q2q (60 s) min = 2 min *)
  Goal u2qR 1 'min + q2quR (u2qR 60 's) 'min = u2qR 2 'min.
  Proof. qeqR. Qed.

  (* we also provided the auto conversion based on left/right units using '+ or +' *)

  (* 1 min '+ 60 s = 2 min *)
  Goal (u2qR 1 'min) '+ (u2qR 60 's) = u2qR 2 'min.
  Proof. qeqR. Qed.

  (* 1 min +' 60 s = 120 s *)
  Goal (u2qR 1 'min) +' (u2qR 60 's) = u2qR 120 's.
  Proof. qeqR. Qed.

  (* ---------------------------------------------------- *)
  (* multiplication *)

  (* 2 'A * 3 'Ω = 6 'V *)
  Goal (u2qR 2 'A) * u2qR 3 'Ω = u2qR 6 'V.
  Proof. qeqR. Qed.

  (* 2 'A * 3 'Ω = q2q (6000 'mV) 'V *)
  Goal (u2qR 2 'A) * u2qR 3 'Ω = q2quR (u2qR 6000 _m 'V) 'V.
  Proof. qeqR. Qed.

  (* q2q (6000 'mV) 'V = 6 'V *)
  Goal q2quR (u2qR 6000 _m 'V) 'V = (u2qR 6 'V).
  Proof. qeqR. Qed.
  
  (* (4 m) ^ 3 = 64 m³  *)
  Goal (u2qR 4 'm)³ = u2qR 64 ('m³)%U.
  Proof. qeqR. Qed.

  (* ---------------------------------------------------- *)
  (* inversion *)

  (* q2q (/ (3 min)) Hz = (1/180) Hz *)
  Goal (q2quR (/(u2qR 3 'min)) 'Hz) = u2qR (1/180)%R 'Hz.
  Proof. qeqR. Qed.

  (* ---------------------------------------------------- *)
  (* division *)

  (* (10 m) / (5 m/s) = 2 s *)
  Goal (u2qR 10 'm) / (u2qR 5 ('m/'s)%U) = u2qR 2 's.
  Proof. qeqR. Qed.

  (* ---------------------------------------------------- *)
  (* boolean comparison *)
  Goal u2qR 3 'N <? u2qR 5 'N = true. Proof. qeqR. Qed.
  Goal u2qR 3 'A <? u2qR 5 'N = false. Proof. qeqR. Qed.
  Goal u2qR 3 ('N*'m)%U <? u2qR 5 ('m²*'N*/'m)%U = true. Proof. qeqR. Qed.

  (* ---------------------------------------------------- *)
  (* 三角函数 *)
  
  (* sin²θ + cos²θ = 1 *)
  Goal forall r, let theta := u2qR r 'rad in
            ('sin theta)² + ('cos theta)² = qoneR.
  Proof. qeqR. ra. Qed.
  
  (* ---------------------------------------------------- *)
  (* 开n次方 *)

  (* √(4 m⁶) = 2 m³ *)
  Goal qrootR (u2qR 4 ('m⁶)) 2 = u2qR 2 ('m³)%U.
  Proof.
    qeqR.
    - field_simplify. rewrite Rpower_inv2. ra. apply Rabs_right; lra.
    - field_simplify. rewrite Rpower_inv2. ra.
  Qed.

  (* ∛(1000 cm³) = 10 cm *)
  Goal qrootR (u2qR 1000 (_c 'm ^ 3)%U) 3 = (u2qR 10 _c 'm).
  Proof.
    qeqR.
    - field_simplify. pose proof (Rpower_invn 3). cbv in H. apply H; try lra; try lia.
    - field_simplify. pose proof (Rpower_invn 3). cbv in H. apply H; try lra; try lia.
  Qed.
  
End test.

Module ex_QuR.
  
  (* ---------------------------------------------------- *)
  (* 自由落体运动 *)
  Section ex1.
    (* 自由落体运动，从t0时刻开始下落，求t1,t2时刻的速度、距离:
       已知：
          重力加速度 g = 9.8 m/s^2
          时间 t1 = 30 s
          时间 t2 = 1 min
       则：
          在t1时刻的速度 v1 = g*t1 = 294 m/s
          在t2时刻的速度 v2 = g*t2 = 588 m/s
          在t1时刻的距离 s1 = (1/2)*g*t1^2 = 4410 m
          在t2时刻的距离 s2 = (1/2)*g*t2^2 = 17640 m *)
    Let g := u2qR 9.8 ('m/('s^2))%U.
    Let t1 := u2qR 30 's.
    Let t2 := u2qR 1 'min.
    Let v1 := t1 * g.
    Let v2 := t1 * g.
    Let s1 := (1/2)%R * g * t1 ^ 2.
    Let s2 := (1/2)%R * g * t2 ^ 2.

    (* v1 = 294 m/s *)
    Goal v1 = u2qR 294 ('m/'s)%U.
    Proof. qeqR. Qed.

    (* s1 = 4410 m *)
    Goal s1 = u2qR 4410 'm.
    Proof. qeqR. Qed.
    
    Example v1_m_per_s := qval v1.
    Example s1_s := qval s1.
    
    Goal qval v1 = Some 294. Proof. qeqR. Qed.
    Goal qval s1 = Some 4410. Proof. qeqR. Qed.
  End ex1.

  (* ---------------------------------------------------- *)
  (* 流速与时间的问题 *)
  Section ex2.
    (* two taps(水龙头), one 36.7cm^3/s, another 2.1L/min, need to fill 
       300cm^3 cup, how long?
       答：1L/min=1dm^3/min=1000/60 (cm^3/s) = 50/3 (cm^3/s)
       所以，300 / (36.7+2.1*50/3) s ≈ 4.18 s ≈ 0.0697 min *)
    Let f1 := u2qR 36.7 ((_c 'm)³/'s)%U.
    Let f2 := u2qR 2.1 ('L/'min)%U.
    Let V := u2qR 300 ((_c 'm)³)%U.
    
    Example fill_time_s := V / (f1 '+ f2).
    Example fill_time_min := q2quR (V / (f1 +' f2)) 'min.

    Goal qval fill_time_s = Some (300/(36.7+2.1*50/3))%R.
    Proof. qeqR. Qed.

    Goal qval (f1 '+ f2) = Some (36.7+2.1*50/3)%R. qeqR. Qed.
    Goal qval (f1 +' f2) = Some (36.7*3/50+2.1)%R. qeqR. Qed.
    Goal qdims (fill_time_s) = Some (udims 's). qeqR. Qed.
    Goal qdims (fill_time_min) = Some (udims 's). qeqR. Qed.
    Goal qcoef (fill_time_s) = Some (ucoef 's). qeqR. Qed.
    Goal qcoef (fill_time_min) = Some (ucoef 'min). qeqR. Qed.
    Goal qcoef (f1 '+ f2) = Some (ucoef ((_c 'm)^3/'s)%U). qeqR. Qed.
    Goal qcoef (f1 +' f2) = Some (ucoef ('L/'min)%U). qeqR. Qed.
    Goal qcoef (f1 '+ f2) = Some (1e-6). qeqR. Qed.
    Goal qcoef (f1 +' f2) = Some (1e-3/60)%R. qeqR. Qed.
    Goal qval fill_time_min = qval (fill_time_s / 60). qeqR. Qed.
  End ex2.

  (* ---------------------------------------------------- *)
  (* K_T与K_E的问题 *)
  Section ex3.
    Let coef_955 : R := 60 / (2 * PI).  (* 60 / (2π) ≈ 9.55 *)
    Let u1 : Unit := ('V / 'rpm)%U.
    Let u2 : Unit := ('N * 'm / 'A)%U.
    
    Variable val_K_E : R.
    Let K_E := u2qR val_K_E u1. (* K_E 的单位是 V/rpm *)
    Let K_T1 := q2quR K_E u1. (* K_T与K_E相等，且 K_T 的单位是 V/rpm *)
    Let K_T2 := q2quR K_E u2. (* K_T与K_E相等，且 K_T 的单位是 N*m/A *)

    (* 当 K_T 单位是 N*m/A 时才符合教材中的公式，即 K_T = 9.55 * K_E *)
    Goal qval K_T2 = Some (coef_955 * val_K_E)%R.
    Proof. qeqR; ra. Qed.

    (* 当 K_T 单位是 V/rpm 时，不符合教材中的公式 *)
    Goal qval K_T1 = Some val_K_E.
    Proof. qeqR; ra. Qed.
  End ex3.
  
End ex_QuR.

(* Extraction "ocaml_qalgebraR_ex.ml" ex_QuR. *)

(* 
utop[2]> ex_QuR.v1_m_per_s;;
- : float option = Some 294.
utop[3]> ex_QuR.s1_s;;
- : float option = Some 4410.
utop[4]> ex_QuR.fill_time_s;;
- : float quantity =
Qmake (4.18410041841004166,
 (1., ((((((Zpos XH, Z0), Z0), Z0), Z0), Z0), Z0)))
utop[5]> ex_QuR.fill_time_min;;
- : float quantity =
Qmake (0.0697350069735007,
 (60., ((((((Zpos XH, Z0), Z0), Z0), Z0), Z0), Z0)))
 *)
