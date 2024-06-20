(*
  purpose   : Unit, syntax of unit.
  author    : Zhengpu Shi
  date      : 2021.05
  reference : 
  1. SI-Brochure-9-EN.pdf
  
  remark    :
  1. Basic Unit and derived Unit
    There are 7 basic unit. eg., Time, Length, Mass, etc.
    basic unit can be composed to construct derived unit, and the coefficient 
    could be added. eg., 1min=60's, 1N=1kg*m/s².
*)

Require Export RExt. 

Open Scope R_scope.


Declare Scope Unit_scope.
Delimit Scope Unit_scope with U.
Open Scope Unit_scope.



(** * BasicUnit: seven basic unit come from SI *)



(** ** Definition of BasicUnit *)
(* every name represent a basic unit. *)
Inductive BasicUnit : Set :=
  | BUTime
  | BULength
  | BUMass
  | BUElectricCurrent
  | BUThermodynamicTemperature
  | BUAmountOfSubstance
  | BULuminousIntensity.

Notation "&T" := (BUTime) (at level 0).
Notation "&L" := (BULength) (at level 0).
Notation "&M" := (BUMass) (at level 0).
Notation "&I" := (BUElectricCurrent) (at level 0).
Notation "&O" := (BUThermodynamicTemperature) (at level 0).
Notation "&N" := (BUAmountOfSubstance) (at level 0).
Notation "&J" := (BULuminousIntensity) (at level 0).  



(** ** Equality of BasicUnit *)
Section BasicUnit_eq.

  (** Generate some simple functions and propertie:
<<
    BasicUnit_beq : BasicUnit -> BasicUnit -> bool
    BasicUnit_eq_dec : forall x y : BasicUnit, {x = y} + {x <> y}
>>
  *)
  Scheme Equality for BasicUnit.

  (** BasicUnit_beq is reflexive. *)
  Lemma BasicUnit_beq_refl b : BasicUnit_beq b b = true.
  Proof.
    destruct b; auto.
  Qed.

  (** BasicUnit_beq is true，iff b1 = b2. *)
  Lemma BasicUnit_beq_true_iff : forall b1 b2, 
    BasicUnit_beq b1 b2 = true <-> b1 = b2.
  Proof.
    intros. split; intros.
    - destruct b1,b2; simpl; simpl; easy.
    - subst. apply BasicUnit_beq_refl.
  Qed.

  (** BasicUnit_beq is false, iff b1 <> b2. *)
  Lemma BasicUnit_beq_false_iff : forall b1 b2, 
    BasicUnit_beq b1 b2 = false <-> b1 <> b2.
  Proof.
    intros. split; intros.
    - destruct (BasicUnit_beq b1 b2) eqn : E1. easy.
      intro H1. apply BasicUnit_beq_true_iff in H1. rewrite E1 in H1. easy.
    - destruct b1,b2; simpl; auto; destruct H; auto.
  Qed.

End BasicUnit_eq.



(** * Unit: syntax representation of a unit *)



(** ** Definition of Unit *)

(** Unit is an AST that can represent any unit. *)
Inductive Unit : Set :=
  | Unone (coef : R)        (* a unit with no dimension. eg: a number *)
  | Ubu (bu : BasicUnit)    (* a unit with single dimension. eg: m *)
  | Uinv (u : Unit)         (* inversion of a unit. eg: Hz = /s *)
  | Umul (u1 u2 : Unit).    (* multiplication of two units. eg: m*s *)

Notation "$ coef" := (Unone coef) (at level 0) : Unit_scope. 
Notation "[ kind ]" := (Ubu kind) (at level 0) : Unit_scope.
Notation " / u" := (Uinv u) : Unit_scope.
Notation "u1 / u2" := (Umul u1 (Uinv u2)) : Unit_scope.
Notation "u1 * u2" := (Umul u1 u2) : Unit_scope.

(** A value of R type is a Unit. *)
Coercion Unone : R >-> Unit.



(** ** Natual powers of a Unit *)
Fixpoint Upown (u : Unit) (n : nat) : Unit :=
  match n with
  | O => Unone 1
  | 1 => u
  | S n' => Umul u (Upown u n')
  end.



(** ** Integer powers of a Unit  *)
Definition Upow (u : Unit) (z : Z) : Unit :=
  match z with
  | Z0 => Unone 1
  | Zpos p => Upown u (Pos.to_nat p)
  | Zneg p => Uinv (Upown u (Pos.to_nat p))
  end.

Notation " a ^ z " := (Upow a z) (at level 30, right associativity) :Unit_scope.
Notation " a ² " := (a ^ 2) (at level 1) : Unit_scope.
Notation " a ³ " := (a ^ 3) (at level 1) : Unit_scope.
Notation " a ⁴ " := (a ^ 4) (at level 1) : Unit_scope.
Notation " a ⁵ " := (a ^ 5) (at level 1) : Unit_scope.
Notation " a ⁶ " := (a ^ 6) (at level 1) : Unit_scope.
Notation " a ⁷ " := (a ^ 7) (at level 1) : Unit_scope.

(* examples *)
Example m := [BULength].
Example kg :=  [BUMass].
Example s := [BUTime].
Example hour := 3600 * [BUTime].
Example km := 1000 * m.
Example N := 2 * (kg * m) / (s * s).
Example N' := (2 * kg / s) * (m / s).

(** A question, how to make sure N == N'? we need semantics of Unit. *)


Lemma Upow_eq_0 u : Upow u 0 = 1.
Proof. auto. Qed.

Lemma Upow_eq_1 u : Upow u 1 = u.
Proof. auto. Qed.

Lemma Upow_eq_2 u : Upow u 2 = u².
Proof. auto. Qed.

Example Upow_plus u n1 n2 : (Upow u n1) * (Upow u n2) = Upow u (n1 + n2).
Abort.  (* need semantics equal, not syntax equal *)



(** ** Get coefficient of a Unit *)
Fixpoint Ugetcoef (u : Unit) : R :=
  match u with
  | Unone c => c
  | Ubu bu => R1
  | Uinv u1 => Rinv (Ugetcoef u1)
  | Umul u1 u2 => Rmult (Ugetcoef u1) (Ugetcoef u2)
  end.

(* examples *)
(* Compute Ugetcoef (kg * m / (s * s)).
Compute Ugetcoef N.
Compute Ugetcoef N'. *)


(** [Ugetcoef] for [Uinv] is commutative. *)
Lemma Ugetcoef_Uinv : forall u, Ugetcoef (/ u) = Rinv (Ugetcoef u).
Proof. intros. auto. Qed.

(** [Ugetcoef] for [Umul] is distributive. *)
Lemma Ugetcoef_Umul : forall u1 u2, Ugetcoef (u1 * u2) = 
  Rmult (Ugetcoef u1) (Ugetcoef u2).
Proof. intros. auto. Qed.



(** ** Get dimension of the BasicUnit from a Unit *)

Fixpoint Ugetdim (u : Unit) (b : BasicUnit) : Z :=
  match u with
  | Unone c => 0
  | Ubu bu => if (BasicUnit_eq_dec bu b) then 1 else 0
  | Uinv u1 => Z.opp (Ugetdim u1 b)
  | Umul u1 u2 => Z.add (Ugetdim u1 b) (Ugetdim u2 b)
  end.

(* examples *)
(* Compute Ugetdim (kg * m / (s * s)) &T.
Compute Ugetdim (100*kg) &M. *)

(** [Ugetdim] of [Ubu] with same key equal 1. *)
Lemma Ugetdim_Ubu_same : forall b, Ugetdim [b] b = Z.of_nat 1.
Proof. destruct b; simpl; auto. Qed.

(** [Ugetdim] of [Ubu] with different key equal 0. *)
Lemma Ugetdim_Ubu_diff : forall b b', b <> b' -> Ugetdim [b] b' = 0%Z.
Proof. intros. destruct b,b'; simpl; auto; destruct H; auto. Qed.

(** [Ugetdim] of [Uinv] equal to [Z.opp]. *)
Lemma Ugetdim_Uinv : forall u b, 
  Ugetdim (/u) b =  Z.opp (Ugetdim u b).
Proof. intros; destruct b; auto. Qed.

(** [Ugetdim] of [Umul] equal to [Ugetdim] + [Ugetdim]. *)
Lemma Ugetdim_Umul : forall u1 u2 b, 
  Ugetdim (u1 * u2) b = Z.add (Ugetdim u1 b) (Ugetdim u2 b).
Proof. intros. auto. Qed.

(** [Ugetdim] of [Upown] equal to nat.mult. *)
Lemma Ugetdim_Upown : forall u bu a n, 
  Ugetdim u bu = a -> Ugetdim (Upown u n) bu = (Z.of_nat n * a)%Z.
Proof.
  intros. induction n; simpl; auto. destruct n.
  - destruct a; auto.
  - rewrite Ugetdim_Umul. rewrite H,IHn.
    destruct a; auto with zarith.
Qed.
 
(** [Ugetdim] of [Upow] equal to Z.mult. *)
Lemma Ugetdim_Upow : forall u bu a z, 
  Ugetdim u bu = a -> Ugetdim (u ^ z) bu = (z * a)%Z.
Proof.
  intros.
  unfold Upow. destruct z; auto.
  - rewrite (Ugetdim_Upown _ _ a); auto.
    auto with zarith.
  - rewrite Ugetdim_Uinv. rewrite (Ugetdim_Upown _ _ a); auto.
    auto with zarith.
Qed.


(** ** Generate a Unit by natural powers of a BasicUnit *)
Fixpoint Ugenpown (b : BasicUnit) (n : nat) : Unit :=
  match n with
  | O => $1
  | S O => [b]
  | S n' => (Ugenpown b n') * [b]
  end.

(* examples *)
(* Compute Ugenpown BUTime 3.
Compute Ugenpown BUTime 2.
Compute Ugenpown BUTime 1.
Compute Ugenpown BUTime 0. *)

(** Get coefficient of a Unit generated by [Ugenpown] will get 1. *)
Lemma Ugetcoef_Ugenpown : forall (b : BasicUnit) (n : nat),
  Ugetcoef (Ugenpown b n) = R1.
Proof.
  intros b n. induction n; auto.
  destruct n; auto.
  replace (Ugenpown b (S (S n))) with (Ugenpown b (S n) * [b]); auto.
  rewrite Ugetcoef_Umul. rewrite IHn. simpl. ring.
Qed.

(** Get dimension of the BasicUnit b from a Unit generated by [Ugenpown b n] 
  will get n. *)
Lemma Ugetdim_Ugenpown_same : forall (b : BasicUnit) (n : nat),
  Ugetdim (Ugenpown b n) b = Z.of_nat n.
Proof.
  induction n; auto. destruct n; auto.
  - replace (Ugenpown b 1) with [b]; auto. apply Ugetdim_Ubu_same.
  - replace (Ugenpown b (S (S n))) with
    (Ugenpown b (S n) * [b]); auto.
    rewrite Ugetdim_Umul. rewrite IHn. rewrite Ugetdim_Ubu_same. simpl. f_equal.
    remember (Pos.of_succ_nat n).
    rewrite Pos.add_comm. rewrite Pos.add_1_l. auto.
Qed.

(** Get dimension of the BasicUnit b from a Unit generated by [Ugenpown b' n] 
  will get 0. *)
Lemma Ugetdim_Ugenpown_diff : forall (b1 b2 : BasicUnit) (n : nat),
  b1 <> b2 -> Ugetdim (Ugenpown b1 n) b2 = 0%Z.
Proof.
  intros. induction n; auto. destruct n; auto.
  - replace (Ugenpown b1 1) with [b1]; auto. rewrite Ugetdim_Ubu_diff; auto.
  - replace (Ugenpown b1 (S (S n))) with
    (Ugenpown b1 (S n) * [b1]); auto.
    rewrite Ugetdim_Umul. rewrite IHn. rewrite Ugetdim_Ubu_diff; auto.
Qed.



(** ** Generate a Unit by integer powers of the BasicUnit *)
Definition Ugenpow (b : BasicUnit) (dim : Z) : Unit :=
  match Z_dec 0 dim with  (* {0 < dim} + {0 > dim} + {0 = dim} *)
  | inleft dec2 => match dec2 with
    | left _ => Ugenpown b (Z.to_nat dim)
    | right _ => / (Ugenpown b (Z.to_nat (Z.opp dim)))
    end
  | inright _ => $1
  end.

(* examples *)
Compute Ugenpow BUTime 2.
Compute Ugenpow BUTime 1.
Compute Ugenpow BUTime 0.
Compute Ugenpow BUTime (-1).
Compute Ugenpow BUTime (-2).

(** Get coefficient of a Unit generate by [Ugenpow b dim] will get 1. *)
Lemma Ugetcoef_Ugenpow : forall (b : BasicUnit) (dim : Z),
  Ugetcoef (Ugenpow b dim) = R1.
Proof.
  destruct dim; auto.
  - replace (Ugenpow b (Z.pos p))
    with (Ugenpown b (Z.to_nat (Z.pos p))); auto.
    apply Ugetcoef_Ugenpown.
  - replace (Ugenpow b (Z.neg p))
    with (/ (Ugenpown b (Z.to_nat (Z.pos p)))); auto.
    rewrite Ugetcoef_Uinv.
    rewrite Ugetcoef_Ugenpown. field.
Qed.

(** Get dimension of the BasicUnit b from a Unit generate by [Ugenpow b dim] 
  will get dim. *)
Lemma Ugetdim_Ugenpow_same : forall (b : BasicUnit) (dim : Z),
  Ugetdim (Ugenpow b dim) b = dim.
Proof.
  destruct dim; auto.
  - replace (Ugenpow b (Z.pos p))
    with (Ugenpown b (Z.to_nat (Z.pos p))); auto.
    rewrite Ugetdim_Ugenpown_same. auto with zarith.
  - replace (Ugenpow b (Z.neg p))
    with (/ (Ugenpown b (Z.to_nat (Z.pos p)))); auto.
    simpl. rewrite Ugetdim_Ugenpown_same. auto with zarith.
Qed.

(** Get dimension of the BasicUnit b from a Unit generate by [Ugenpow b' dim] 
  will get 0. *)
Lemma Ugetdim_Ugenpow_diff : forall (b b' : BasicUnit) (dim : Z),
  b <> b' ->
  Ugetdim (Ugenpow b dim) b' = 0%Z.
Proof.
  induction dim; auto; intros H.
  - replace (Ugenpow b (Z.pos p))
    with (Ugenpown b (Z.to_nat (Z.pos p))); auto.
    rewrite Ugetdim_Ugenpown_diff; auto.
  - replace (Ugenpow b (Z.neg p))
    with (/ (Ugenpown b (Z.to_nat (Z.pos p)))); auto.
    simpl. rewrite Ugetdim_Ugenpown_diff; auto.
Qed.



(** ** Generate a Unit with a base unit and a integer powers of a BasicUnit. *)
Definition Ucons (base : Unit) (b : BasicUnit) (dim : Z) : Unit :=
  if (dim =? 0)%Z 
  then base
  else base * (Ugenpow b dim).
  
(** Get coefficient of a Unit generated by [Ucons base b dim], return the 
 coefficient of [base]. *)
Lemma Ugetcoef_Ucons : forall (base : Unit) (b : BasicUnit) (dim : Z),
  Ugetcoef (Ucons base b dim) = Ugetcoef base.
Proof.
  intros base b. destruct b; intros;
  unfold Ucons; destruct (dim =? 0)%Z eqn:E1; auto;
  rewrite Ugetcoef_Umul, Ugetcoef_Ugenpow, Rmult_1_r; auto.
Qed.

(** Get dimension of the BasicUnit b2 from a Unit generated by 
  [Ucons base b1 dim]. *)
Lemma Ugetdim_Ucons : forall (base : Unit) (b1 b2 : BasicUnit) (dim : Z),
  Ugetdim (Ucons base b1 dim) b2 = ((Ugetdim base b2) + 
    (if (BasicUnit_beq b1 b2) then dim else 0))%Z.
Proof.
  intros.
  destruct (BasicUnit_beq b1 b2) eqn : E1 ; simpl.
  - apply BasicUnit_beq_true_iff in E1. subst. 
    unfold Ucons. induction dim; simpl; try ring.
    + rewrite Ugetdim_Ugenpow_same. auto.
    + rewrite Ugetdim_Ugenpown_same. auto with zarith.
  - unfold Ucons. induction dim; simpl; auto with zarith.
    + rewrite Ugetdim_Ugenpow_diff; auto.
      apply BasicUnit_beq_false_iff. auto.
    + rewrite Ugetdim_Ugenpown_diff; auto.
      apply BasicUnit_beq_false_iff. auto.
Qed.


