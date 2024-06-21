(*
  Copyright 2024 ZhengPu Shi
  This file is part of VQCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Algebra of Quantities on R type
  author    : Zhengpu Shi
  date      : 2024.06
*)


From FinMatrix Require Export RExt.
Require Import SI.
Import SI_Accepted SI_Prefix.
From FinMatrix Require Import MyExtrOCamlR.

Require Export Qalgebra.

Open Scope Unit_scope.
Open Scope Quantity_scope.


(* ######################################################################### *)
(** * Algebraic operations for quantities of type R, derived from the Qalgebra *)

Notation Quantity := (@Quantity R).
Notation qmakeU := (@qmakeU R).

Definition qmakeByR (r : R) : Quantity := qmakeA r.
Coercion qmakeByR : R >-> Quantity.

Notation qone := (qone 1).

Notation qcvtble := (@qcvtble R).
Notation qconv := (qconv Rmult).

Notation qadd := (qadd Rplus).
Notation qmul := (qmul Rmult).
Notation qpow := (qpow powerRZ).
Notation qinv := (qinv Rinv).
Notation qdiv := (qdiv Rmult Rinv).

Infix "+" := qadd : Quantity_scope.
Infix "*" := qmul : Quantity_scope.
Infix "^" := qpow : Quantity_scope.
Notation " q ² " := (q ^ 2) : Quantity_scope.
Notation " q ³ " := (q ^ 3) : Quantity_scope.
Notation " q ⁴ " := (q ^ 4) : Quantity_scope.
Notation " q ⁵ " := (q ^ 5) : Quantity_scope.
Notation "/ q" := (qinv q) : Quantity_scope.
Infix "/" := qdiv : Quantity_scope.


(** Absolute value function *)
Definition qabs (q : Quantity) : Quantity := qop1 Rabs q.

(** Any power of quantity which the unit of base and exponent both are 1 *)
Definition qpower (base exp : Quantity) : Quantity := qdim0op2 Rpower base exp.

(** Trigonometric functions or its inverse require the dimensionless unit, where
    1. trigometric functions need input unit 1 and output unit radian,
    2. inverse trigometric functions require input unit radian and output 1.
    Moreover, radian is equal to 1 *)
Definition qsin q := qdim0op1 sin q.
Definition qcos q := qdim0op1 cos q.
Definition qtan q := qdim0op1 tan q.
Definition qasin q := qdim0op1 asin q.
Definition qacos q := qdim0op1 acos q.
Definition qatan q := qdim0op1 atan q.

(** Automation for quantity equality of R type *)
Ltac qeqR :=
  (* simplify *)
  intros; cbv;
  (* elim Rbool, solve R contracdiction *)
  autoRbool; auto; try lra;
  (* elim Qmake *)
  try match goal with | |- Quantity.Qmake _ _ = Quantity.Qmake _ _ => f_equal end;
  try match goal with | |- (_, _) = (_, _) => f_equal end;
  (* elim R *)
  try lra.


(* ######################################################################### *)
(** * Specific operations for quantities of type R *)

(** z-th root of a [Quantity] `q` *)
Definition qroot (q : Quantity) (z : Z) : Quantity :=
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
Definition qrootCond (q : Quantity) (z : Z) : Prop :=
  match q with
  | Qmake v n => (0 < v) /\ (0 < (ncoef n)) /\ nrootCond n z
  | _ => False
  end.

Definition qrootCondb (q : Quantity) (z : Z) : bool :=
  match q with
  | Qmake v n => (0 <? v) && (0 <? (ncoef n)) && nrootCondb n z
  | _ => false
  end.

Lemma qroot_qsqr : forall q, qrootCond q 2 -> qroot (q * q) 2 = q.
Proof.
  intros. unfold qroot, qrootCond, nrootCond in *.
  destruct q; simpl; auto. logic. f_equal.
  rewrite Rpower_inv2. ra. rewrite nroot2_nmul; auto.
Qed.

Lemma qsqr_qroot : forall q, qrootCond q 2 -> (qroot q 2)² = q.
Proof.
  intros. unfold qroot, qrootCond, nrootCond in *.
  destruct q; simpl; auto. logic. f_equal.
  rewrite Rpower_inv2. ra. rewrite npow_nroot2; auto.
  unfold nrootCond. logic.
Qed.


(* ######################################################################### *)
(** * Examples *)
Section test.

  (* ---------------------------------------------------- *)
  (* plus *)

  (* plus with same Unit *)

  (* 3 s + 2 s = 1 s + 4 s *)
  Goal (qmakeU 3 's) + (qmakeU 2 's) = (qmakeU 1 's) + (qmakeU 4 's).
  Proof. qeqR. Qed.
  
  (* plus with different Unit is not supported, need manual convertion *)
  
  (* 1 min + 60 s = !! *)
  Goal (qmakeU 1 'min) + (qmakeU 60 's) = !!.
  Proof. qeqR. Qed.

  (* qconv (1 min) s + 60 s = 120 s *)
  Goal qconv (qmakeU 1 'min) 's + (qmakeU 60 's) = qmakeU 120 's.
  Proof. qeqR. Qed.

  (* ---------------------------------------------------- *)
  (* multiplication *)

  (* 2 'A * 3 'Ω = 6 'V *)
  Goal (qmakeU 2 'A) * qmakeU 3 'Ω = qmakeU 6 'V.
  Proof. qeqR. Qed.

  (* 2 'A * 3 'Ω = qconv (6000 'mV) 'V *)
  Goal (qmakeU 2 'A) * qmakeU 3 'Ω = qconv (qmakeU 6000 _m 'V) 'V.
  Proof. qeqR. Qed.

    (* (4 m) ^ 3 = 64 m³  *)
  Goal (qmakeU 4 'm) ^ 3 = qmakeU 64 ('m³)%U.
  Proof. cbv. f_equal; try lra. f_equal. lra. Qed.

  (* ---------------------------------------------------- *)
  (* inversion *)

  (* qconv (/ (3 min)) Hz = (1/180) Hz *)
  Goal (qconv (/(qmakeU 3 'min)) 'Hz) = qmakeU (1/180)%R 'Hz.
  Proof. qeqR. Qed.

  (* ---------------------------------------------------- *)
  (* division *)

  (* (10 m) / (5 m/s) = 2 s *)
  Goal (qmakeU 10 'm) / (qmakeU 5 ('m/'s)%U) = qmakeU 2 's.
  Proof. qeqR. Qed.
  
  (* ---------------------------------------------------- *)
  (* 运动学中的一个场景：自由落体运动 *)
  Section Motion.
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
    Let g : Quantity := qmakeU 9.8 ('m/('s^2))%U.
    Let t1 := qmakeU 30 's.
    Let t2 := qmakeU 1 'min.
    Let v1 := t1 * g.
    Let v2 := t1 * g.
    Let s1 := (1/2)%R * g * t1 ^ 2.
    Let s2 := (1/2)%R * g * t2 ^ 2.

    (* v1 = 294 m/s *)
    Goal v1 = qmakeU 294 ('m/'s)%U.
    Proof. qeqR. Qed.

    (* s1 = 4.41 km *)
    Goal s1 = qconv (qmakeU 4.41 'km) 'm.
    Proof. qeqR. Qed.
  End Motion.

  (* ---------------------------------------------------- *)
  (* 动力学中的简单问题 *)
  
  Section test1.
    (** example2: two taps(水龙头), one 36.7cm^3/s, another 2.1L/min, need to fill 
        300cm^3 cup, how long? *)
    Example f1 := qmakeU 36.7 ((_c 'm)³/'s)%U.
    Example f2 := qmakeU 2.1 ('L/'min)%U.
    Example V := qmakeU 300 ((_c 'm)³)%U.

    Example fill_time1 := (qconv (V / (f1 + f2)) 's).
    Eval cbv in (qval fill_time1).

  End test1.

  (* ---------------------------------------------------- *)
  (* 三角函数 *)
  
  (* sin²θ + cos²θ = 1 *)
  Goal forall r, let theta := qmakeU r 'rad in
            (qsin theta)² + (qcos theta)² = qone.
  Proof. qeqR. ra. Qed.
  
  (* ---------------------------------------------------- *)
  (* 开n次方 *)

  (* √(4 m⁶) = 2 m³ *)
  Goal qroot (qmakeU 4 ('m⁶)) 2 = qmakeU 2 ('m³)%U.
  Proof.
    qeqR.
    - field_simplify. rewrite Rpower_inv2. ra. apply Rabs_right; lra.
    - field_simplify. rewrite Rpower_inv2. ra.
  Qed.

  (* ∛(1000 cm³) = 10 cm *)
  Goal qroot (qmakeU 1000 (_c 'm ^ 3)%U) 3 = (qmakeU 10 _c 'm).
  Proof.
    qeqR.
    - field_simplify. pose proof (Rpower_invn 3). cbv in H. apply H; try lra; try lia.
    - field_simplify. pose proof (Rpower_invn 3). cbv in H. apply H; try lra; try lia.
  Qed.
End test.

(* Extraction "ocaml_test_fill_time.ml" fill_time1. *)
