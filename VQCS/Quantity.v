(*
  Copyright 2024 ZhengPu Shi
  This file is part of VQCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : (Physical) Quantity
  author    : ZhengPu Shi
  date      : 2022.04
  
  remark    :
  
  * Syntax of [Quantity] : (A * Unit)

  * Semantics of [Quantity] : A * Dims
     (1). A * Unit ==> (A * (R * Dims)) ==> (A * Dims)

  * [Qcvtible q1 q2]: A proposition means two [Quantity]s are convertible.
    It is defined as the equality of [Dims] of [Quantity].

  * For example
    q1 = 30 minutes  = (30,'min)  ==> (30,60,'s)    ==> (1800,'s)
    q2 = 0.5 hours   = (0.5,'hrs) ==> (0.5,3600,'s) ==> (1800,'s)
    q3 = 900 seconds = (900,'s)   ==> (900,1,'s)    ==> (900,'s)
    q4 = 2 Ampere    = (2,'A)     ==> (2,1,'A)      ==> (2,'A)

    Here,
    1. q1, q2 and q3 are [Unit] of `Time`, and they are convertible.
    2. q1 and q2 are equal
    3. q4 is [Unit] of `Electronic Current`, and not convertible to 
       [Unit] of `Time`.

  * Dimension laws
    1. q1 {*,/,+,-,==,<=,<} q2, only if [Qcvtible q1 q2]
    2. {sin,cos,tan,exp,log} q, only if [Dims q] = 0

  * Suport in function
    Example 1:

    Definition OhmsLaw (i r : Quantity) : Quantity :=
      i <- Qval i 'A;
      r <- Qval r 'ohm;
        (i * r, 'V)
    Here,
    1. The input parameter i and r have `Unit` constraint,
       `i` could be 'A, 'kA, ...
       `r` could be 'ohms, 'mohms, 'kohms ...
    2. The output has `Unit` constraint too.
    3. The inner calculation is correct.
    4. User needn't to care about the factor of the argument.
       He could safely use 'ohms, 'kohms as the `Unit` of `r`.
    5. We should support extraction to normal value-function.
       Definition QfunExtract1 (f : Quantity -> Quantity) 
          (u1 u : Unit) : option (R -> R)
       Definition QfunExtract2 (f : Quantity -> Quantity -> Quantity) 
          (u1 u2 u : Unit) : R -> R -> R
       etc.

   * Quantity的设计有几种不同的做法：
     * R * Unit
       1. 保留了用户输入的的Unit的AST，也许在某些场合有用（比如字符串输出时可保留用户
          给定的单位构造），但该功能不是必须的。
       2. 使得两个Quantity的比较要用等价关系。
     * R * Nunit = R * R * Dims
       1. 单位被规范化为 (R*Dims)，使得 3 kg*m*s 和 3 kg*m*s 都归约为 3 s*m*kg，
          因此可以用eq来表示相等。
       2. 但还是要处理 30 'min, 0.5 'hrs 和 1800 's 的相等性问题。
       3. 保留了 'min 和 's 的区别（暂时不知道有什么用途）
     * R * Dims
       1. 可以完全用eq来表示量的相等。
       2. 无法表示 'min 和 's 的区别，需要额外的 Qval:Q->Unit->option R 来取出值。
*)

Require Export RExt.
Require Export Unit Nunit Uconv.
Require Import SI.

Declare Scope Quantity_scope.
Delimit Scope Quantity_scope with Q.
Open Scope Quantity_scope.


(** ** Definition of [Quantity] *)
Section def.

  Context {A : Type}.
  Context {Azero : A}.
  Context (RmulA : R -> A -> A).

  (* [Quantity] is defined as a option type. *)
  Inductive Quantity : Type :=
  | Qmake (v : A) (d : Dims)
  | Qinvalid.


  (** Make a [Quantity] from [Nunit] *)
  Definition QmakeN (v : A) (n : Nunit) :=
    let (c,d) := n in Qmake (RmulA c v) d.
  
  (** Make a [Quantity] from [Unit] *)
  Definition QmakeU (v : A) (u : Unit) := QmakeN v (u2n u).

  (* Bind Scope Quantity_scope with Quantity. *)

  (** Get value of a [Quantity] *)
  Definition Qval (q : Quantity) : option A :=
    match q with
    | Qmake v d => Some v
    | _ => None
    end.

  (** The value of a [Quantity] is zero  *)
  Definition QvalZero (q : Quantity) : Prop :=
    match q with
    | Qmake v d => v = Azero
    | _ => False
    end.

  (** Get value of a [Quantity] respect to [Unit] `u` *)
  Definition QvalRef (q : Quantity) (u : Unit) : option A :=
    match q with
    | Qmake v d =>
        let (c, d') := u2n u in
        if Deqb d d' then Some (RmulA (R1/c) v) else None
    | _ => None
    end.
  
End def.

Notation "!!" := (Qinvalid) (at level 3) : Quantity_scope.


(** ** Value-function Extraction *)
Section extract.
  Context {A : Type}.
  Context (RmulA : R -> A -> A).
  
  Notation Q := (@Quantity A).
  Notation QmakeU := (QmakeU RmulA).
  
  (* Extraction for unary function (A -> option A) *)
  Definition Qextract1 (f : Q -> Q) (u1 u : Unit) : A -> option A :=
    fun x1 : A =>
      match f (QmakeU x1 u1) with
      | Qmake v d' =>
          let (c,d) := u2n u in
          if Deqb d d'
          then Some (RmulA (1/c) v)
          else None
      | _ => None
      end.

  (* Extraction for unary function (option (A->A)) *)
  (* Definition Qextract1_full (f : Q -> Q) (u1 u : Unit) : option (A -> A) := *)
  (* Problem:
     We cannot construct the Unit information from a function.
     For example: given a function `f : Q -> Q`, we canot get `_u1,_u : Unit`,
     so we cannot check the matching of `u1,u` and `_u1,_u`.
     Thus, we canont construct `option (A->A)` easily now. *)

  (* Extraction for binary function *)
  Definition Qextract2 (f : Q -> Q -> Q) (u1 u2 u : Unit) : A -> A -> option A :=
    fun x1 x2 : A =>
      match f (QmakeU x1 u1) (QmakeU x2 u2) with
      | Qmake v d' =>
          let (c,d) := u2n u in
          if Deqb d d'
          then Some (RmulA (1/c) v)
          else None
      | _ => None
      end.

End extract.


Section test.
  Import SI_Accepted.
  Import SI_Prefix.

  Notation QmakeU := (QmakeU Rmult).
  Notation QvalRef := (QvalRef Rmult).
  
  (* 时间单位：0.5 hrs = 30 min *)
  Section Time_Problem.
    Let q1 := QmakeU 0.5 'hrs.
    Let q2 := QmakeU 30 'min.
    
    Goal QvalRef q1 'hrs = Some 0.5.
    Proof. simpl; f_equal. field. Qed.

    Goal QvalRef q1 's = Some 1800.
    Proof. simpl; f_equal. lra. Qed.

    Goal q1 = q2. cbn. f_equal. lra. Qed.
  End Time_Problem.

  (* 电学，数值函数抽取，以 U = I * R 为例 *)
  Section Qextract.
    Let U_by_I_and_R (i r : Quantity) : Quantity :=
          match QvalRef i 'A with
          | Some i =>
              match QvalRef r ohm with
              | Some r => QmakeU (i*r)%R 'V
              | _ => !!
              end
          | _ => !!
          end.
    
    (* x mA * y MΩ = (x*y) kV *)
    Goal forall x y : R,
        U_by_I_and_R (QmakeU x (_m 'A)) (QmakeU y (_M 'Ω)) = QmakeU (x*y)%R (_k 'V).
    Proof. intros. cbn; simpl. f_equal. lra. Qed.

    (* 如果单位兼容，提取出正确处理了单位的函数 *)
    Let U_by_I_and_R_2 := Eval cbv in Qextract2 Rmult U_by_I_and_R (_k 'A) 'Ω 'V.

    Goal forall x y : R, U_by_I_and_R_2 x y = Some (1000 * x * y)%R.
    Proof. intros. cbv. f_equal. field. Qed.
    
    (* 如果单位不兼容，提取的函数无效 *)
    Let U_by_I_and_R_3 := Eval cbv in Qextract2 Rmult U_by_I_and_R (_k 'A) 'Ω 'g.
    
    Goal forall x y : R, U_by_I_and_R_3 x y = None.
    Proof. intros. cbv. auto. Qed.
  End Qextract.
  
  (* 运动学，自由落体运动 *)
  Section Motion.
    (* 自由落体运动，从t0时刻开始下落，求t1,t2时刻的速度、距离。
       重力加速度 g = 9.8 m/s^2
       时间 t1 = 30 s
       时间 t2 = 1 min
       在t1时刻的速度 v1 = g*t1 = 294 m/s
       在t2时刻的速度 v2 = g*t2 = 588 m/s
       在t1时刻的距离 s1 = (1/2)*g*t1^2 = 4410 m
       在t2时刻的距离 s2 = (1/2)*g*t2^2 = 17640 m
     *)
    Let g : Quantity := QmakeU 9.8 ('m/'s^2).
    Let t1 := QmakeU 30 's.
    Let t2 := QmakeU 1 'min.
    (* Let v1 := t1 * g. *)
    (* Let v2 := t1 * g. *)
    (* Let s1 := (1/2) * g * t1 ^ 2. *)
    (* Let s2 := (1/2) * g * t2 ^ 2. *)
    
    (* Compute Qeval s1. *)
    
    (* Let ex1 : Qeq v1 (genQ 294 ('m/'s)%U) = true. *)
    (* Proof. cbv. destruct Req_EM_T as [E1|E1]; auto. lra. Qed. *)
    
    (* Let ex2 : Qeq s2 (genQ 17640 'm) = true. *)
    (* Proof. cbv. destruct Req_EM_T as [E1|E1]; auto. lra. Qed. *)

    (* (* Compute Qconv t1 ('min). *) *)
    (* Let ex3 : Qconv t1 ('min) = Some (0.5, 'min). *)
    (* Proof. cbv. f_equal. f_equal. field. Qed. *)
    
    (* Compute s2. *)
  End Motion.
End test.


(* (** ** Comparison of two [Quantity]s *) *)
(* Section Qcmp. *)
(*   Context {A} *)
(*     (cmp : A -> A -> Prop) *)
(*     (cmpb : A -> A -> bool) *)
(*     (cmpb_reflect : forall a b : A, reflect (cmp a b) (cmpb a b)). *)

(*   (** Comprasion of two [Quantity]s (Prop version) *) *)
(*   Definition Qcmp (q1 q2 : Quantity) : Prop := *)
(*     match q1, q2 with *)
(*     | Qmake v1 n1, Qmake v2 n2 => *)
(*         if Neqb n1 n2 *)
(*         then cmp v1 v2 *)
(*         else False *)
(*     | !!, !! => True (* take care! *) *)
(*     | _, _ => False *)
(*     end. *)

(*   Lemma Qcmp_refl : forall q (cmp_refl:forall a, cmp a a), q <> !! -> Qcmp q q. *)
(*   Proof. intros; destruct q; simpl; try easy. rewrite Neqb_refl. auto. Qed. *)

(*   (** Comprasion of two [Quantity]s (bool version) *) *)
(*   Definition Qcmpb (q1 q2 : Quantity) : bool := *)
(*     match q1, q2 with *)
(*     | Qmake v1 n1, Qmake v2 n2 => (cmpb v1 v2) && (Neqb n1 n2) *)
(*     | !!, !! => true (* take care! *) *)
(*     | _, _ => false *)
(*     end. *)

(*   Lemma Qcmpb_true_iff : forall q1 q2, Qcmpb q1 q2 = true <-> Qcmp q1 q2. *)
(*   Proof. *)
(*     intros. destruct q1,q2; simpl; try easy. *)
(*     rewrite andb_true_iff. split; intros. *)
(*     - destruct H. rewrite H0. *)
(*       destruct (cmpb_reflect val val0); auto. easy. *)
(*     - bdestruct (Neqb n n0); auto. split; auto. *)
(*       pose proof (reflect_iff _ _ (cmpb_reflect val val0)). apply H1; auto. *)
(*   Qed. *)

(*   Lemma Qcmpb_false_iff : forall q1 q2, Qcmpb q1 q2 = false <-> ~(Qcmp q1 q2). *)
(*   Proof. intros. rewrite <- Qcmpb_true_iff. split; solve_bool. Qed. *)
  
(*   Lemma Qcmpb_reflect : forall q1 q2, reflect (Qcmp q1 q2) (Qcmpb q1 q2). *)
(*   Proof. *)
(*     intros. destruct (Qcmpb q1 q2) eqn:Eq; constructor. *)
(*     apply Qcmpb_true_iff; auto. apply Qcmpb_false_iff; auto. *)
(*   Qed. *)
  
(* End Qcmp. *)


(* (** Equal,Less Than, Less Equal of two quantities *) *)

(* Definition Qeq (q1 q2 : Quantity) : Prop := q1 =? q2 = true. *)
(* Definition Qlt (q1 q2 : Quantity) : Prop := q1 <? q2 = true. *)
(* Definition Qle (q1 q2 : Quantity) : Prop := q1 <=? q2 = true. *)

(* Infix "==" := Qeq : Quantity_scope. *)
(* (* Infix "<>" := (not Qeq) : Quantity_scope. *) (* easy to get a ambiguous! *) *)
(* Infix "<" := Qlt : Quantity_scope. *)
(* Infix "<=" := Qle : Quantity_scope. *)


(* Definition Qeqb (q1 q2 : Quantity) : bool := Qcmpb q1 q2 Reqb. *)
(* Definition Qltb (q1 q2 : Quantity) : bool := Qcmpb q1 q2 Rltb. *)
(* Definition Qleb (q1 q2 : Quantity) : bool := Qcmpb q1 q2 Rleb. *)

(* Infix "=?"  := Qeqb : Quantity_scope. *)
(* Infix "<?"  := Qltb : Quantity_scope. *)
(* Infix "<=?" := Qleb : Quantity_scope. *)


(* (** ** Equality of two [Quantity]s *) *)
(* Section Qeq. *)
(*   Context {A : Type} *)
(*     (Aeqb : A -> A -> bool) *)
(*     (Aeqb_reflect : forall a b : A, reflect (a = b) (Aeqb a b)). *)
    
(*   Definition Qeqb (q1 q2 : @Quantity A) : bool := Qcmpb Aeqb q1 q2. *)
(*   Infix "=?" := Qeqb : Quantity_scope. *)

(*   Lemma Qeqb_true_iff : forall q1 q2, q1 =? q2 = true <-> q1 = q2. *)
(*   Proof. *)
(*     intros. unfold Qeqb. rewrite (Qcmpb_true_iff eq); auto. *)
(*     unfold Qcmp. destruct q1, q2; split; intros; try easy. *)
(*     - bdestruct (Neqb n n0); subst; try easy. *)
(*     - inversion H. rewrite Neqb_refl. auto. *)
(*   Qed. *)

(*   Lemma Qeqb_false_iff : forall q1 q2, q1 =? q2 = false <-> q1 <> q2. *)
(*   Proof. intros. rewrite <- Qeqb_true_iff. split; solve_bool. Qed. *)

(*   Lemma Qeqb_refl : forall q, q =? q = true. *)
(*   Proof. *)
(*     destruct q; auto; simpl. apply andb_true_iff. split. *)
(*     - apply (reflect_iff _ _ (Aeqb_reflect val val)). auto. *)
(*     - apply Neqb_refl. *)
(*   Qed. *)
  
(* End Qeq. *)


(** Examples *)
(* Compute (genQ 5 'min) =? (genQ (1+2*2) ('min *'N *'m / ('N * 'm))).
Compute (genQ 3 'N) <? (genQ 5 'N).
Compute (genQ 3 ('N*'m)%U) <? (genQ 5 ('m²*'N*/'m)%U).
Compute (genQ 3 'A) <? (genQ 5 'N). (* the result is false definitely! *) *)
