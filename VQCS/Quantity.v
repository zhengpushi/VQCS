(*
  Copyright 2024 ***
  This file is part of VQCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : (Physical) Quantity
  author    : ***
  date      : 2022.04
  
  remark    :
  * Quantity的设计有几种不同的做法：
    1. R * Unit
       * 保留了用户输入的的Unit的AST，也许在某些场合有用（比如字符串输出时可保留用户
         给定的单位构造），但该功能不是必须的。
       * 使得两个Quantity的比较要用等价关系。
    2. R * Nunit = R * (R * Dims)
       * 单位被规范化为 (R*Dims)，使得 3 kg*m*s 和 3 s*kg*m 都归约为 3 s*m*kg，
         因此可以用eq来表示相等。
       * 区分 'min 和 's，所以要手动转换：30 'min, 0.5 'hrs 和 1800 's
    3. R * Dims
       * 将单位 hr, min, s 统一为量(3600,s), (60,s), (1,s)，并且量 2'min 成为(120,'s)
         因此可以用eq来表示量的相等。
       * 不区分 'min 和 's，自动化进行单位转换，但是可能带来设计上的不确定性。
       * 每个量都失去了用户指定单位的能力，虽然能够手动取出每个单位下的值。
    我们选择 R * Nunit 的设计，即能使用 eq，又能区分单位。

  * The value of [Quantity] is polymorphic, such as R, vector, and matrix.

  * qcvtble/qcvtbleb/qconv : two [Quantity] are convertible, or convert it.
    For example:
    q1 = 2 minutes   = (2,'min)  ==> (2,60,'s)
    q2 = 60 seconds  = (60,'s)   ==> (60,1,'s)
    q3 = 2 Ampere    = (2,'A)    ==> (2,1,'A)
    Here,
    1. q1 and q2 are [Unit] of `Time`, and they are convertible.
    2. q3 is [Unit] of `Electronic Current`, and not convertible to q1 or q2

  * If we need to printing Quantity to string? later work.
*)

Require Export Unit Nunit Nconv Uconv.

From FinMatrix Require Import Matrix.
Require Import SI.
Import SI_Accepted SI_Prefix.

Declare Scope Quantity_scope.
Delimit Scope Quantity_scope with QU.
Open Scope Quantity_scope.

(* ######################################################################### *)
(** * Quantity type *)

(* ======================================================================= *)
(** ** Definition and basic operatios of [Quantity] *)

(** Definition of [Quantity] *)
Inductive Quantity {tA : Type} :=
| Qmake (v : tA) (n : Nunit)
| Qinvalid.

Bind Scope Quantity_scope with Quantity.

Notation "!!" := Qinvalid (at level 3) : Quantity_scope.

(** Make a [Quantity] from [Unit] *)
Definition u2q {tA} (v : tA) (u : Unit) := Qmake v (u2n u).

(** Make a dimensionless [Quantity] from tA type *)
Definition a2q {tA} (v : tA) := Qmake v nunitOne.

(** quantity one which its value is 1 and has dimensionless unit *)
(* Definition qone {tA} (Aone : tA) := a2q Aone. *)
Definition qone {tA} (Aone : tA) : @Quantity tA := Qmake Aone nunitOne.

(* 关于K_T和K_E的单位问题 *)
(* Eval cbv in u2q 1 (('N * 'm) / 'A). *)
(* = Qmake R1 ((R1 * R1 * / (R1 * R1) * R1 * / R1)%R, ((-2)%Z, 2%Z, 1%Z, (-1)%Z, 0%Z, 0%Z, 0%Z)) *)
(* Eval cbv in u2q 1 ('V / 'rpm). *)
(* 
  = Qmake R1
    ((R1 * (R1 * R1) * / (R1 * (R1 * R1)) * / R1 *
     / ((R1 + R1) * PI * / ((R1 + R1) * ((R1 + R1) * (R1 + (R1 + R1) * (R1 + (R1 + R1) * (R1 + (R1 + R1))))) * R1)))%R,
    ((-2)%Z, 2%Z, 1%Z, (-1)%Z, 0%Z, 0%Z, 0%Z))
 *)


(** Get the value of a [Quantity] with its own [Unit] *)
Definition qval {tA} (q : Quantity) : option tA :=
  match q with
  | Qmake v n => Some v
  | _ => None
  end.

(** Get coefficent of a [Quantity] *)
Definition qcoef {tA} (q : @Quantity tA) : option R :=
  match q with
  | Qmake _ (c, _) => Some c
  | _ => None
  end.

(** Get dimensions of a [Quantity] *)
Definition qdims {tA} (q : @Quantity tA) : option Dims :=
  match q with
  | Qmake _ (_, d) => Some d
  | _ => None
  end.

Lemma qeq_if_qval_qcof_qdims : forall {tA} (q1 q2 : @Quantity tA),
    qval q1 = qval q2 -> qcoef q1 = qcoef q2 -> qdims q1 = qdims q2 -> q1 = q2.
Proof.
  intros. destruct q1, q2; simpl in *; try easy. inv H. f_equal.
  destruct n,n0. inv H0; inv H1. auto.
Qed.

(** Get [Unit] of a [Quantity] `q` *)
Definition qunit {tA} (q : @Quantity tA) : option Unit :=
  match q with
  | Qmake v n => Some (n2u n)
  | _ => None
  end.

(** Check that if the [Quantity] `q` has same [Unit] with `u` (proposition version) *)
Definition qsameu {tA} (q : @Quantity tA) (u : Unit) : Prop :=
  match q with
  | Qmake v n => n = (u2n u)
  | _ => False
  end.

(** Check that if the [Quantity] `q` has same [Unit] with `u` (boolean version) *)
Definition qsameub {tA} (q : @Quantity tA) (u : Unit) : bool :=
  match q with
  | Qmake v n => neqb n (u2n u)
  | _ => false
  end.

Lemma qsameub_reflect : forall {tA} (q : @Quantity tA) u,
    reflect (qsameu q u) (qsameub q u).
Proof.
  intros. unfold qsameu, qsameub. destruct q; try constructor; auto.
  bdestruct (neqb n (u2n u)); constructor; auto.
Qed.
Hint Resolve qsameub_reflect : bdestruct.

Lemma qsameub_true_iff : forall {tA} (q : @Quantity tA) u,
    qsameub q u = true <-> qsameu q u.
Proof. intros. bdestruct (qsameub q u); try tauto. easy. Qed.

Lemma qsameub_false_iff : forall {tA} (q : @Quantity tA) u,
    qsameub q u = false <-> ~ qsameu q u.
Proof. intros. bdestruct (qsameub q u); try tauto. easy. Qed.


(** Two [Quantity]s are convertible (proposition version *)
Definition qcvtble {tA} (q1 q2 : @Quantity tA) : Prop :=
  match q1, q2 with
  | Qmake v1 n1, Qmake v2 n2 => ndims n1 = ndims n2
  | _, _ => False
  end.

(** Two [Quantity]s are convertible (boolean version) *)
Definition qcvtbleb {tA} (q1 q2 : @Quantity tA) : bool :=
  match q1, q2 with
  | Qmake v1 n1, Qmake v2 n2 => deqb (ndims n1) (ndims n2)
  | _, _ => false
  end.

(* more operations or properties for [Quantity] if we have ARmul: R -> tA -> tA  *)
Section more_ARmul.
  Context {tA} (ARmul : R -> tA -> tA).

  (** Convert a [Quantity] `q` with [Nunit] `nref` *)
  Definition q2qn (q : @Quantity tA) (nref : Nunit) : Quantity :=
    match q with
    | Qmake v n =>
        match nconvRate n nref with
        | Some rate => Qmake (ARmul rate v) nref
        | _ => !!
        end
    | _ => !!
    end.

  (** Convert a [Quantity] `q` with [Unit] `uref` *)
  Definition q2qu (q : @Quantity tA) (uref : Unit) : Quantity := q2qn q (u2n uref).

  (** Convert a [Quantity] `q` with [Quantity] `qref` *)
  Definition q2q (q : @Quantity tA) (qref : @Quantity tA) : Quantity :=
    match qref with
    | Qmake v n => q2qn q n
    | _ => !!
    end.

  (** qsameu (q2qu q u) u *)
  Lemma qsameu_q2qu : forall q u, qsameu q u -> ucoef u <> 0 -> qsameu (q2qu q u) u.
  Proof.
    intros. unfold qsameu in *. unfold q2qu, q2qn in *. destruct q; auto.
    rewrite H. rewrite nconvRate_eq; auto.
  Qed.

  (** qsameub (q2qu q u) u = true *)
  Lemma qsameub_q2qu : forall q u, qsameu q u -> ucoef u <> 0 -> qsameub (q2qu q u) u = true.
  Proof. intros. apply qsameub_true_iff. apply qsameu_q2qu; auto. Qed.
  
  (** Get the value of a [Quantity] `q` respect to [Nunit] `nref` *)
  Definition qvaln (q : @Quantity tA) (nref : Nunit) : option tA :=
    qval (q2qn q nref).

  (** Get the value of a [Quantity] `q` respect to [Unit] `uref` *)
  Definition qvalu (q : @Quantity tA) (uref : Unit) : option tA :=
    qvaln q (u2n uref).

  (** Boolean comparison of two quantities *)
  Definition qcmpb (Acmpb : tA -> tA -> bool) (q1 q2 : @Quantity tA) : bool :=
    match q1, q2 with
    | Qmake v1 n1, Qmake v2 n2 =>
        match nconv n1 n2 with
        | Some (k, _) => Acmpb (ARmul k v1) v2
        | _ => false
        end
    (* note that, if any input quantity is invalid, the result is false *)
    | _, _ => false
    end.
  
End more_ARmul.

(* 示例：标量 *)
Section ex_salar.
  Notation qvalu := (qvalu Rmult).
  Notation q2qu := (q2qu Rmult).

  (* 时间，0.5 hrs = 30 min *)
  Section time.
    Let t1 := u2q 0.5 'hrs.
    Let t2 := u2q 30 'min.

    (* Compute qcvtbleb t1 t2. *)
    
    Goal qvalu t1 'hrs = Some 0.5.
    Proof. cbn. f_equal. lra. Qed.

    (* Eval cbn in qconv t1 'min. *)

    Goal q2qu t1 'min = t2.
    Proof. cbv. f_equal. lra. Qed.
  End time.

End ex_salar.
  
(* 示例：向量 *)
Section ex_vector.
  Notation qvalu := (qvalu vscal).
  Notation q2qu := (q2qu (vscal (Amul:=Rmult))).
  Notation l2v := (@l2v R 0).

  (* 位移矢量，[px py pz] meter = [100*px 100*py 100*pz] cm *)
  Section displacement.
    Variable px py pz : R.
    Let p1 := u2q (@l2v 3 [px;py;pz]) 'm.

    Notation "'厘米" := (_c 'm).

    (* Eval cbn in qvalByU p1 '厘米. *)
    
    Goal q2qu p1 '厘米 = u2q (l2v [100*px;100*py;100*pz]%R) '厘米.
    Proof. cbv. f_equal. veq; lra. Qed.
  End displacement.
End ex_vector.
