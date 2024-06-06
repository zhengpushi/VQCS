(*
  purpose   : (Physical) Quantity
  author    : ZhengPu Shi
  date      : 2022.04
  
  remark    :
  1. Quantity : (val:A, coef:R, dims:Dims)
     * The pair (coef,dims) determine the [Unit] of a [Quantity]
     * For example
       q1 = 30 minutes = (30, 60, s),
       q2 = 0.5 hrs = (0.5, 3600, s),
       q3 = 2 A = (2, 1, A)
       Note, 
       * q1 and q2 have different [Unit], they cannot operate directly,
         but they are convertible;
       * q3 is different from q1 and q2, and cannot be converted to q1 or q1.
     * The value types in [Quantity] are polymorphic, such as R and vector are valid
  2. dimension laws
     * q1 {*,/,+,-,==,<=,<} q2, only if [unit(q1) = unit(q2)]
     * {sin,cos,tan,exp,log} q, only if dims(q) = 0
  3. If we need to printing Quantity to string? later work.
*)

(* Require Import String. *)
Require Export RExt.
Require Export Unit Nunit Uconv.
Require Import SI.

Declare Scope Quantity_scope.
Delimit Scope Quantity_scope with Q.
Open Scope Quantity_scope.

(** ** Definition of [Quantity] *)
Section def.

  Context {A : Type}.

  (* [Quantity] is defined as a option type. *)
  Inductive Quantity : Type :=
  | Qmake (val : A) (n : Nunit)
  | Qinvalid.

  (** Qmake is injective. *)
  (* Lemma Qmake_inj u1 u2 : Qmake u1 = Qmake u2 <-> u1 = u2. *)
  (* Proof. split; intro H; inversion H; auto. Qed. *)
  

  (** Make a [Quantity] from [Unit] *)
  Definition QmakeU (val : A) (u : Unit) := Qmake val (u2n u).

  (* Bind Scope Quantity_scope with Quantity. *)

  (** Convert real number to Quantity with Unit 1. *)
  (* Definition real2QU (val : R) := genQU val #1. *)
  (* Coercion real2QU : R >-> Quantity. *)

  (** Convert [Unit] to Quantity with value 1. *)
  (* Definition unit2QU (u : Unit) := genQU 1 u. *)
  (* Note that, this coercion shouldno't open, it will disturb the real2QU.
     We need to distinguish value and coefficient. *)
  (* Coercion unit2QU : Unit >-> Quantity. *)
  (* Notation "$1 u" := (unit2QU u) (at level 10) : QU_scope. *)

  (** Get value of a [Quantity] *)
  Definition Qval (q : Quantity) : option A :=
    match q with
    | Qmake v (mkNunit c d) => Some v
    | _ => None
    end.
  
  (** Get coefficent of a [Quantity] *)
  Definition Qcoef (q : Quantity) : option R :=
    match q with
    | Qmake v (mkNunit c d) => Some c
    | _ => None
    end.
  
  (** Get dimensions of a [Quantity] *)
  Definition Qdims (q : Quantity) : option Dims :=
    match q with
    | Qmake v (mkNunit c d) => Some d
    | _ => None
    end.

End def.

(* Notation "! q" := (q <> QUinvalid)) (at level 3) : Quantity_scope. *)
Notation "!!" := (Qinvalid) (at level 3) : Quantity_scope.


(** ** (SemEquality of two [Quantity]s *)
Section Qcmp.
  Context {A}
    (cmp : A -> A -> Prop)
    (cmpb : A -> A -> bool)
    (cmpb_reflect : forall a b : A, reflect (cmp a b) (cmpb a b)).

  (** Comprasion of two [Quantity]s (Prop version) *)
  Definition Qcmp (q1 q2 : Quantity) : Prop :=
    match q1, q2 with
    | Qmake v1 n1, Qmake v2 n2 =>
        if Neqb n1 n2
        then cmp v1 v2
        else False
    | !!, !! => True (* take care! *)
    | _, _ => False
    end.


(** ** Comparison of two [Quantity]s *)
Section Qcmp.
  Context {A}
    (cmp : A -> A -> Prop)
    (cmpb : A -> A -> bool)
    (cmpb_reflect : forall a b : A, reflect (cmp a b) (cmpb a b)).

  (** Comprasion of two [Quantity]s (Prop version) *)
  Definition Qcmp (q1 q2 : Quantity) : Prop :=
    match q1, q2 with
    | Qmake v1 n1, Qmake v2 n2 =>
        if Neqb n1 n2
        then cmp v1 v2
        else False
    | !!, !! => True (* take care! *)
    | _, _ => False
    end.

  Lemma Qcmp_refl : forall q (cmp_refl:forall a, cmp a a), q <> !! -> Qcmp q q.
  Proof. intros; destruct q; simpl; try easy. rewrite Neqb_refl. auto. Qed.

  (** Comprasion of two [Quantity]s (bool version) *)
  Definition Qcmpb (q1 q2 : Quantity) : bool :=
    match q1, q2 with
    | Qmake v1 n1, Qmake v2 n2 => (cmpb v1 v2) && (Neqb n1 n2)
    | !!, !! => true (* take care! *)
    | _, _ => false
    end.

  Lemma Qcmpb_true_iff : forall q1 q2, Qcmpb q1 q2 = true <-> Qcmp q1 q2.
  Proof.
    intros. destruct q1,q2; simpl; try easy.
    rewrite andb_true_iff. split; intros.
    - destruct H. rewrite H0.
      destruct (cmpb_reflect val val0); auto. easy.
    - bdestruct (Neqb n n0); auto. split; auto.
      pose proof (reflect_iff _ _ (cmpb_reflect val val0)). apply H1; auto.
  Qed.

  Lemma Qcmpb_false_iff : forall q1 q2, Qcmpb q1 q2 = false <-> ~(Qcmp q1 q2).
  Proof. intros. rewrite <- Qcmpb_true_iff. split; solve_bool. Qed.
  
  Lemma Qcmpb_reflect : forall q1 q2, reflect (Qcmp q1 q2) (Qcmpb q1 q2).
  Proof.
    intros. destruct (Qcmpb q1 q2) eqn:Eq; constructor.
    apply Qcmpb_true_iff; auto. apply Qcmpb_false_iff; auto.
  Qed.
  
End Qcmp.


(* (** Equal,Less Than, Less Equal of two quantities *) *)

(* Definition Qeq (q1 q2 : Quantity) : Prop := q1 =? q2 = true. *)
(* Definition Qlt (q1 q2 : Quantity) : Prop := q1 <? q2 = true. *)
(* Definition Qle (q1 q2 : Quantity) : Prop := q1 <=? q2 = true. *)

(* Infix "==" := Qeq : Qu_scope. *)
(* (* Infix "<>" := (not Qeq) : Qu_scope. *) (* easy to get a ambiguous! *) *)
(* Infix "<" := Qlt : Qu_scope. *)
(* Infix "<=" := Qle : Qu_scope. *)


(* Definition Qeqb (q1 q2 : Quantity) : bool := Qcmpb q1 q2 Reqb. *)
(* Definition Qltb (q1 q2 : Quantity) : bool := Qcmpb q1 q2 Rltb. *)
(* Definition Qleb (q1 q2 : Quantity) : bool := Qcmpb q1 q2 Rleb. *)

(* Infix "=?"  := Qeqb : Qu_scope. *)
(* Infix "<?"  := Qltb : Qu_scope. *)
(* Infix "<=?" := Qleb : Qu_scope. *)


(** ** Equality of two [Quantity]s *)
Section Qeq.
  Context {A : Type}
    (Aeqb : A -> A -> bool)
    (Aeqb_reflect : forall a b : A, reflect (a = b) (Aeqb a b)).
    
  Definition Qeqb (q1 q2 : @Quantity A) : bool := Qcmpb Aeqb q1 q2.
  Infix "=?" := Qeqb : Quantity_scope.

  Lemma Qeqb_true_iff : forall q1 q2, q1 =? q2 = true <-> q1 = q2.
  Proof.
    intros. unfold Qeqb. rewrite (Qcmpb_true_iff eq); auto.
    unfold Qcmp. destruct q1, q2; split; intros; try easy.
    - bdestruct (Neqb n n0); subst; try easy.
    - inversion H. rewrite Neqb_refl. auto.
  Qed.

  Lemma Qeqb_false_iff : forall q1 q2, q1 =? q2 = false <-> q1 <> q2.
  Proof. intros. rewrite <- Qeqb_true_iff. split; solve_bool. Qed.

  Lemma Qeqb_refl : forall q, q =? q = true.
  Proof.
    destruct q; auto; simpl. apply andb_true_iff. split.
    - apply (reflect_iff _ _ (Aeqb_reflect val val)). auto.
    - apply Neqb_refl.
  Qed.
  
End Qeq.


(** Examples *)
(* Compute (genQ 5 'min) =? (genQ (1+2*2) ('min *'N *'m / ('N * 'm))).
Compute (genQ 3 'N) <? (genQ 5 'N).
Compute (genQ 3 ('N*'m)%U) <? (genQ 5 ('m²*'N*/'m)%U).
Compute (genQ 3 'A) <? (genQ 5 'N). (* the result is false definitely! *) *)



(** ** Convert the [Unit] of a [Quantity] *)
Section conversion.
  Context {A : Type} (AmulR : A -> R -> A).
  
  (** Check if two quantities have same unit.  *)
  Definition Qsameunit (q1 q2 : @Quantity A) : Prop :=
    match q1, q2 with
    | Qmake _ (mkNunit _ d1), Qmake _ (mkNunit _ d2) => d1 = d2
    | _, _ => False
    end.

  Definition Qsameunitb (q1 q2 : @Quantity A) : bool :=
    match q1, q2 with
    | Qmake _ (mkNunit _ d1), Qmake _ (mkNunit _ d2) => Deqb d1 d2
    | _, _ => false
    end.

  (* Compute Qusameunitb (genQ 1 'min) (genQ 60 's). *)

  
  (** Convert the [Unit] of a [Qantity] `q` to [Nunit] `ref`.
      Return a valid [Quantity] only when `q` is convertible to `ref`.
      (v,c1,d) with (c2,d) ==> (v*c1/c2,c2,d) *)
  Definition Qconv (q : Quantity) (ref : Nunit) : Quantity :=
    let '(mkNunit c2 d2) := ref in
    match q with
    | Qmake v (mkNunit c1 d1) =>
        if Deqb d1 d2
        then Qmake (AmulR v (c1/c2)) ref
        else !!
    | _ => !!
    end.
  
End conversion.

Section test.
  Import SI_Accepted.

  (* 0.5 hrs = 30 min *)
  Goal Qconv Rmult (QmakeU 0.5 'hrs) (u2n 'min) = QmakeU 30 'min.
  Proof. cbv. f_equal. field. Qed.

  (* 0.5 hrs = 1800 s *)
  Goal Qconv Rmult (QmakeU 0.5 'hrs) (u2n 's) = QmakeU 1800 's.
  Proof. cbv. f_equal. field. Qed.

  
  (* 一个专门的问题：
    自由落体运动，从t0时刻开始下落，求t1,t2时刻的速度、距离。
    重力加速度 g = 9.8 m/s^2
    时间 t1 = 30 s
    时间 t2 = 1 min
    在t1时刻的速度 v1 = g*t1 = 294 m/s
    在t2时刻的速度 v2 = g*t2 = 588 m/s
    在t1时刻的距离 s1 = (1/2)*g*t1^2 = 4410 m
    在t2时刻的距离 s2 = (1/2)*g*t2^2 = 17640 m
   *)
  Let g : Quantity := QmakeU 9.8 ('m/'s^2)%U.
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
End test.
