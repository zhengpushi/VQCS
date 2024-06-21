(*
  Copyright 2024 ZhengPu Shi
  This file is part of VQCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : (Physical) Quantity
  author    : ZhengPu Shi
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

From FinMatrix Require Import MatrixR.
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
Inductive Quantity {A : Type} :=
| Qmake (v : A) (n : Nunit)
| Qinvalid.

Bind Scope Quantity_scope with Quantity.

Notation "!!" := Qinvalid (at level 3) : Quantity_scope.

(** quantity one which its value is 1 and has dimensionless unit *)
Definition qone {A} (Aone : A) : @Quantity A := Qmake Aone nunitOne.

(** Make a [Quantity] from [Unit] *)
Definition qmakeU {A} (v : A) (u : Unit) := Qmake v (u2n u).

(** Make a dimensionless [Quantity] from A type *)
Definition qmakeA {A} (v : A) := Qmake v nunitOne.


(** Get the value of a [Quantity] with its own [Unit] *)
Definition qval {A} (q : Quantity) : option A :=
  match q with
  | Qmake v n => Some v
  | _ => None
  end.

(** Get coefficent of a [Quantity] *)
Definition qcoef {A} (q : @Quantity A) : option R :=
  match q with
  | Qmake v (c, d) => Some c
  | _ => None
  end.

(** Get dimensions of a [Quantity] *)
Definition qdims {A} (q : @Quantity A) : option Dims :=
  match q with
  | Qmake v (c, d) => Some d
  | _ => None
  end.

(** Two [Quantity]s are convertible (proposition version *)
Definition qcvtble {A} (q1 q2 : @Quantity A) : Prop :=
  match q1, q2 with
  | Qmake v1 n1, Qmake v2 n2 => ndims n1 = ndims n2
  | _, _ => False
  end.

(** Two [Quantity]s are convertible (boolean version) *)
Definition qcvtbleb {A} (q1 q2 : @Quantity A) : bool :=
  match q1, q2 with
  | Qmake v1 n1, Qmake v2 n2 => deqb (ndims n1) (ndims n2)
  | _, _ => false
  end.

Section more.
  Context {A : Type}.
  Context (Ascal : R -> A -> A).
  Infix "s*" := Ascal.
  
  (** Get the value of a [Quantity] `q` respect to [Nunit] `nref` *)
  Definition qvalByN (q : @Quantity A) (nref : Nunit) : option A :=
    match q with
    | Qmake v n =>
        match nconvRate n nref with
        | Some rate => Some (rate s* v)
        | _ => None
        end
    | _ => None
    end.

  (** Get the value of a [Quantity] `q` respect to [Unit] `uref` *)
  Definition qvalByU (q : Quantity) (uref : Unit) : option A :=
    qvalByN q (u2n uref).

  (** Convert a [Quantity] `q` with [Unit] `uref` *)
  Definition qconv (q : @Quantity A) (uref : Unit) : Quantity :=
    let nref := u2n uref in
    match q with
    | Qmake v n =>
        match nconvRate n nref with
        | Some rate => Qmake (rate s* v) nref
        | _ => !!
        end
    | _ => !!
    end.
End more.

(* 示例：标量 *)
Section ex_salar.
  Notation qvalByU := (qvalByU Rmult).
  Notation qconv := (qconv Rmult).

  (* 时间，0.5 hrs = 30 min *)
  Section time.
    Let t1 := qmakeU 0.5 'hrs.
    Let t2 := qmakeU 30 'min.

    (* Compute qcvtbleb t1 t2. *)
    
    Goal qvalByU t1 'hrs = Some 0.5.
    Proof. simpl; f_equal; lra. Qed.

    (* Eval cbn in qconv t1 'min. *)

    Goal qconv t1 'min = t2.
    Proof. cbv. f_equal. lra. Qed.
  End time.

End ex_salar.
  
(* 示例：向量 *)
Section ex_vector.
  Notation qvalByU := (qvalByU vscal).
  Notation qconv := (qconv vscal).

  (* 位移矢量，[px py pz] meter = [100*px 100*py 100*pz] cm *)
  Section displacement.
    Variable px py pz : R.
    Let p1 := qmakeU (@l2v 3 [px;py;pz]) 'm.

    Notation "'厘米" := (_c 'm).

    (* Eval cbn in qvalByU p1 '厘米. *)
    
    Goal qconv p1 '厘米 = qmakeU (l2v [100*px;100*py;100*pz]%R) '厘米.
    Proof. cbv. f_equal. veq; lra. Qed.
  End displacement.
End ex_vector.
