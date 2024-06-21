(*
  Copyright 2024 ZhengPu Shi
  This file is part of VQCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Utilities
  author    : ZhengPu Shi
  date      : 2021.05
  
 *)


Require Export Coq.Setoids.Setoid.     (* for rewriting A <-> B *)
Require Export Coq.Logic.Decidable.
Require Export Coq.Logic.Classical.    (* powerful tauto *)
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.PropExtensionality.
Require Export Coq.Bool.Bool.          (* reflect *)
Require Export ZArith Lia Reals Lra.
Require Export Extraction.

From FinMatrix Require Export RExt.


(* ======================================================================= *)
(** ** Reserved notations *)

Reserved Notation "a ^ z" (at level 30, right associativity).
Reserved Notation "a ²" (at level 1, format "a ²").
Reserved Notation "a ³" (at level 1, format "a ³").
Reserved Notation "a ⁴" (at level 1, format "a ⁴").
Reserved Notation "a ⁵" (at level 1, format "a ⁵").
Reserved Notation "a ⁶" (at level 1, format "a ⁶").

(* ======================================================================= *)
(** ** Tactics *)

(** inversion and subst *)
Ltac inv H := inversion H; subst; clear H.

(** destruct by sumbool comparison procedure.
    Note that we should register the reflection to "bdestruct" database *)
Ltac bdestruct X :=
  let H := fresh in
  let e := fresh "e" in
  evar (e: Prop);
  assert (H: reflect e X); subst e;
  [ try eauto with bdestruct
  | destruct H as [H|H]].

(** Z.eqb reflects Z.eq *)
Hint Resolve Z.eqb_spec : bdestruct.

(** simplify the logic expressions *)
Ltac logic :=
  repeat
    (match goal with
     (* solve it *)
     | [H : ?P |- ?P] => exact H
     | [|- True] => constructor
     | [H : False |- _] => destruct H

     (* simplify it *)
     | [|- _ /\ _ ] => constructor
     | [|- _ -> _] => intro
     | [|- not _ ] => intro
     | [|- _ <-> _ ] => split; intros
     | [H : _ /\ _ |- _] => destruct H
     | [H : _ \/ _ |- _] => destruct H

     (* rewriting *)
     (* | [H1 : ?P -> ?Q, H2 : ?P |- _] => pose proof (H1 H2) *)
     (* | [H : ?a = ?b |- _ ]  => try progress (rewrite H) *)
     | [H : ?a <> ?b |- False]   => destruct H
     end;
     try congruence).

(** Solve simple logic about "bool" *)
Ltac autoBool :=
  repeat
    let H := fresh "H" in 
    match goal with
    (* b = false <-> b <> true *)
    | |- ?b = false <-> ?b <> true => split
    (* b = true <-> b <> false *)
    | |- ?b = false <-> ?b <> true => split
    (* b = false -> b <> true *)
    | H: ?b = false |- ?b <> true => rewrite H
    (* b <> true -> b = false *)
    | H: ?b <> true |- ?b = false => apply not_true_is_false
    (* a && b = true |- _ ==> a = true, b = true |- _ *)
    | H: ?a && ?b = true |- _ => apply andb_prop in H
    end;
    logic.


(* ======================================================================= *)
(** ** Properties for even numbers of Z type *)
Section Z.
  Open Scope Z_scope.

  (** a <> 0 -> (a * b) / a = b *)
  Lemma z_div_mul_alt : forall a b : Z, a <> 0 -> (a * b) / a = b.
  Proof. intros. rewrite Z.mul_comm. apply Z.div_mul. auto. Qed.

  (** a mod b = 0 -> b * (a / b) = a *)
  Lemma z_mul_div : forall a b : Z, a mod b = 0 -> b * (a / b) = a.
  Proof.
    intros. pose proof (Z_div_mod_eq_full a b). rewrite H0 at 2. rewrite H. lia.
  Qed.
  
  (** (2 * z) / 2 = z *)
  Lemma zdiv2_mul2 : forall z : Z, (2 * z) / 2 = z.
  Proof. intros. apply z_div_mul_alt. lia. Qed.

  (** 2 * (z / 2) = z *)
  Lemma zmul2_div2 : forall z : Z, Z.Even z -> 2 * (z / 2) = z.
  Proof.
    intros. rewrite z_mul_div; auto.
    rewrite Zmod_even. apply Z.even_spec in H. rewrite H. auto.
  Qed.

  (** (z + z) / 2 = z *)
  Lemma zdiv2_add : forall z : Z, (z + z) / 2 = z.
  Proof. intros. rewrite Z.add_diag. rewrite zdiv2_mul2. auto. Qed.
  
End Z.

Hint Resolve
  Z.div_mul                (* b <> 0 -> (a * b) / b = a *)
  z_div_mul_alt            (* a <> 0 -> (a * b) / a = b *)
  z_mul_div                (* a mod b = 0 -> b * (a / b) = a *)
  zmul2_div2               (* Z.Even z -> 2 * (z / 2) = z *)
  zdiv2_mul2               (* (2 * z) / 2 = z *)
  zdiv2_add                (* (z + z) / 2 = z *)
  : Z.


(* ======================================================================= *)
(** ** properties for prod *)

(* ----------------------------------------------------- *)
(** *** pair equality *)
(** pair equality *)
Section pair_eq.
  Context {T1 T2 T3 T4 T5 T6 T7 : Type}.

  Variable a1 b1 : T1.
  Variable a2 b2 : T2.
  Variable a3 b3 : T3.
  Variable a4 b4 : T4.
  Variable a5 b5 : T5.
  Variable a6 b6 : T6.
  Variable a7 b7 : T7.

  Lemma pair_eq2 :
    (a1,a2) = (b1,b2) <-> 
    a1 = b1 /\ a2 = b2.
  Proof. repeat rewrite pair_equal_spec. tauto. Qed.
  
  Lemma pair_eq3 :
    (a1,a2,a3) = (b1,b2,b3) <-> 
    a1 = b1 /\ a2 = b2 /\ a3 = b3.
  Proof. repeat rewrite pair_equal_spec. tauto. Qed.

  Lemma pair_eq4 :
    (a1,a2,a3,a4) = (b1,b2,b3,b4) <-> 
    a1 = b1 /\ a2 = b2 /\ a3 = b3 /\ a4 = b4.
  Proof. repeat rewrite pair_equal_spec. tauto. Qed.
  
  Lemma pair_eq5 :
    (a1,a2,a3,a4,a5) = (b1,b2,b3,b4,b5) <-> 
    a1 = b1 /\ a2 = b2 /\ a3 = b3 /\ a4 = b4 /\ a5 = b5.
  Proof. repeat rewrite pair_equal_spec. tauto. Qed.
  
  Lemma pair_eq6 :
    (a1,a2,a3,a4,a5,a6) = (b1,b2,b3,b4,b5,b6) <-> 
    a1 = b1 /\ a2 = b2 /\ a3 = b3 /\ a4 = b4 /\ a5 = b5 /\ a6 = b6.
  Proof. repeat rewrite pair_equal_spec. tauto. Qed.
  
  Lemma pair_eq7 :
    (a1,a2,a3,a4,a5,a6,a7) = (b1,b2,b3,b4,b5,b6,b7) <-> 
    a1 = b1 /\ a2 = b2 /\ a3 = b3 /\ a4 = b4 /\ a5 = b5 /\ a6 = b6 /\ a7 = b7.
  Proof. repeat rewrite pair_equal_spec. tauto. Qed.
End pair_eq.

(* ----------------------------------------------------- *)
(** *** pair inequality *)
Section pair_neq.
  Context {T1 T2 T3 T4 T5 T6 T7 : Type}.

  Variable a1 b1 : T1.
  Variable a2 b2 : T2.
  Variable a3 b3 : T3.
  Variable a4 b4 : T4.
  Variable a5 b5 : T5.
  Variable a6 b6 : T6.
  Variable a7 b7 : T7.

  Lemma pair_neq2 :
    (a1,a2) <> (b1,b2) <-> 
    a1 <> b1 \/ a2 <> b2.
  Proof. rewrite pair_eq2. tauto. Qed.
  
  Lemma pair_neq3 :
    (a1,a2,a3) <> (b1,b2,b3) <-> 
    a1 <> b1 \/ a2 <> b2 \/ a3 <> b3.
  Proof. rewrite pair_eq3. tauto. Qed.

  Lemma pair_neq4 :
    (a1,a2,a3,a4) <> (b1,b2,b3,b4) <-> 
    a1 <> b1 \/ a2 <> b2 \/ a3 <> b3 \/ a4 <> b4.
  Proof. rewrite pair_eq4. tauto. Qed.

  Lemma pair_neq5 :
    (a1,a2,a3,a4,a5) <> (b1,b2,b3,b4,b5) <-> 
    a1 <> b1 \/ a2 <> b2 \/ a3 <> b3 \/ a4 <> b4 \/ a5 <> b5.
  Proof. rewrite pair_eq5. tauto. Qed.
  
  Lemma pair_neq6 :
    (a1,a2,a3,a4,a5,a6) <> (b1,b2,b3,b4,b5,b6) <-> 
    a1 <> b1 \/ a2 <> b2 \/ a3 <> b3 \/ a4 <> b4 \/ a5 <> b5 \/ a6 <> b6.
  Proof. rewrite pair_eq6. tauto. Qed.

  Lemma pair_neq7 :
    (a1,a2,a3,a4,a5,a6,a7) <> (b1,b2,b3,b4,b5,b6,b7) <-> 
    a1 <> b1 \/ a2 <> b2 \/ a3 <> b3 \/ a4 <> b4 \/ a5 <> b5 \/ a6 <> b6 \/ a7 <> b7.
  Proof. rewrite pair_eq7. tauto. Qed.
End pair_neq.

(* ----------------------------------------------------- *)
(** *** pair decidable *)
Section pair_dec.
  Context {T1 T2 T3 T4 T5 T6 T7 : Type}.
  Context {T1dec : forall a b : T1, {a = b} + {a <> b}}.
  Context {T2dec : forall a b : T2, {a = b} + {a <> b}}.
  Context {T3dec : forall a b : T3, {a = b} + {a <> b}}.
  Context {T4dec : forall a b : T4, {a = b} + {a <> b}}.
  Context {T5dec : forall a b : T5, {a = b} + {a <> b}}.
  Context {T6dec : forall a b : T6, {a = b} + {a <> b}}.
  Context {T7dec : forall a b : T7, {a = b} + {a <> b}}.

  Variable a1 b1 : T1.
  Variable a2 b2 : T2.
  Variable a3 b3 : T3.
  Variable a4 b4 : T4.
  Variable a5 b5 : T5.
  Variable a6 b6 : T6.
  Variable a7 b7 : T7.
  
  Lemma pair_dec2 : {(a1,a2) = (b1,b2)} + {(a1,a2) <> (b1,b2)}.
  Proof.
    destruct (T1dec a1 b1) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    destruct (T2dec a2 b2) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    all: right; apply pair_neq2; auto.
  Defined.

  Lemma pair_dec3 : {(a1,a2,a3) = (b1,b2,b3)} + {(a1,a2,a3) <> (b1,b2,b3)}.
  Proof.
    destruct (T1dec a1 b1) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    destruct (T2dec a2 b2) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    destruct (T3dec a3 b3) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    all: right; apply pair_neq3; auto.
  Defined.

  Lemma pair_dec4 :
    {(a1,a2,a3,a4) = (b1,b2,b3,b4)} + {(a1,a2,a3,a4) <> (b1,b2,b3,b4)}.
  Proof.
    destruct (T1dec a1 b1) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    destruct (T2dec a2 b2) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    destruct (T3dec a3 b3) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    destruct (T4dec a4 b4) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    all: right; apply pair_neq4; auto.
  Defined.

  Lemma pair_dec5 :
    {(a1,a2,a3,a4,a5) = (b1,b2,b3,b4,b5)} +
      {(a1,a2,a3,a4,a5) <> (b1,b2,b3,b4,b5)}.
  Proof.
    destruct (T1dec a1 b1) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    destruct (T2dec a2 b2) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    destruct (T3dec a3 b3) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    destruct (T4dec a4 b4) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    destruct (T5dec a5 b5) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    all: right; apply pair_neq5; auto.
  Defined.

  Lemma pair_dec6 :
    {(a1,a2,a3,a4,a5,a6) = (b1,b2,b3,b4,b5,b6)} +
      {(a1,a2,a3,a4,a5,a6) <> (b1,b2,b3,b4,b5,b6)}.
  Proof.
    destruct (T1dec a1 b1) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    destruct (T2dec a2 b2) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    destruct (T3dec a3 b3) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    destruct (T4dec a4 b4) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    destruct (T5dec a5 b5) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    destruct (T6dec a6 b6) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    all: right; apply pair_neq6; auto 6.
  Defined.

  Lemma pair_dec7 :
    {(a1,a2,a3,a4,a5,a6,a7) = (b1,b2,b3,b4,b5,b6,b7)} +
      {(a1,a2,a3,a4,a5,a6,a7) <> (b1,b2,b3,b4,b5,b6,b7)}.
  Proof.
    destruct (T1dec a1 b1) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    destruct (T2dec a2 b2) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    destruct (T3dec a3 b3) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    destruct (T4dec a4 b4) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    destruct (T5dec a5 b5) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    destruct (T6dec a6 b6) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    destruct (T7dec a7 b7) as [H1|H1]; [rewrite H1; clear H1|]; auto.
    all: right; apply pair_neq7; auto 7.
  Defined.

End pair_dec.
