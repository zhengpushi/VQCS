(*
  Copyright 2024 ***
  This file is part of VQCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Imperial Units
  author    : ***
  date      : 2024.12

  remark    :
  1. 英制单位的wiki页面
     https://en.wikipedia.org/wiki/Imperial_units
     https://zh.wikipedia.org/wiki/英制单位
     https://mathpedia.miraheze.org/wiki/英制单位
     https://mathpedia.huijiwiki.com/wiki/英制单位
  2. 公制-英制转换表
     https://www.shuxuele.com/metric-imperial-conversion-charts.html
  3. 
*)

Require Export Nunit.

(* Imperial units is based on SI *)
Require Export SI.
Import SI_Prefix.
Export SI_Accepted.

Declare Scope IU_scope.
Delimit Scope IU_scope with IU.
Open Scope IU.

(* ======================================================================= *)
(** ** Length units *)

(** 英寸 *)
Definition inch := 2.54 * 'cm.
Notation "'in" := (inch) (at level 5) : SI_scope.

(** 英尺 *)
Definition foot := 12 * 'in.
Notation "'ft" := (foot) (at level 5) : SI_scope.

(** 1 foot = 0.3048 meter  *)
Lemma foot_spec1 : 'ft == 0.3048 * 'm.
Proof. ueq. Qed.
  
(** 码 *)
Definition yard := 3 * 'ft.
Notation "'yd" := (yard) (at level 5) : SI_scope.

(** 1 yard = 0.9144 meter  *)
Lemma yard_spec1 : 'yd == 0.9144 * 'm.
Proof. ueq. Qed.

(** 英里 *)
Definition mile := 5280 * 'ft.
Notation "'mi" := (mile) (at level 5) : SI_scope.

(** 1 mile = 1609.344 meter  *)
Lemma mile_spec1 : 'mi == 1609.344 * 'm.
Proof. ueq. Qed.

(** 海里 *)
Definition nauticalMile := 1852 * 'm.
Notation "'nmi" := (nauticalMile) (at level 5) : SI_scope.

(* 海里的传统定义：子午线1角分的长度。
   子午线是地表连接南北两极的大圆线上的半圆弧，为180度；而1度是60角分。
   即：子午线长度/180/60。
   由于地球非标准球体，1度的距离不完全相当，所以海里的长度理论上不固定。
   
   若以“1.852公里*60*180”得到子午线长度，则可得到地球半周长，周长，半径。
   如何验证这一问题及单位？
   可反算地球半径，在6300到6310公里之间。
 *)
(* Lemma earthRadius_by_nauticalMile : *)
(*   let r := 'nmi * 60 * 180 * 2 / (2 * PI) in r > 0 *)
(* Proof. ueq. Qed. *)

(* ======================================================================= *)
(** ** Area units *)

(** 平方英寸 *)
(** 平方英尺 *)
(** 平方英里 *)

(* ======================================================================= *)
(** ** Volume units *)

(** 立方英寸 *)
(** 立方英尺 *)
(** 立方英里 *)
  

Section test.

  Import SI_Derived.
  Import SI_Accepted.
  Import SI_Prefix.
  Import SI_Constants.
  
End test.
