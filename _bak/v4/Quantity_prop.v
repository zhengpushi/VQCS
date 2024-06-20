(*
  Properties of Quantity
*)

From FCS Require Export Unit_prop.
From FCS Require Export Quantity.


(** Unit运算的规范 *)

Open Scope Unit_scope.

Lemma unit_op2_plus_spec_old : forall u,
  let (b,u0) := unit_op2_plus u u in
    b = true /\ u == u0.
Proof.
  intros. unfold unit_op2_plus. rewrite Unit_beq_refl. split; auto.
  apply unorm_spec.
Qed.

Lemma unit_op2_plus_spec : forall b u0 u,
  (b,u0) = unit_op2_plus u u -> b = true /\ u == u0.
Proof.
  intros b u0 u H. unfold unit_op2_plus in H. rewrite Unit_beq_refl in H.
  inversion H. split; auto. apply unorm_spec.
Qed.

(** Quantity运算的规范 *)

Open Scope Quantity_scope.

Lemma Qadd_ok : forall (u : Unit) (r1 r2 : R),
  (r1 & u) + (r2 & u) == (r1 + r2) & u.
Proof.
  induction u.
  - simpl. destruct unit_op2_plus eqn : E1.
    symmetry in E1. apply unit_op2_plus_spec in E1. inversion E1.
    intros. subst. simpl. unfold Quantity_eq.
    unfold Quantity_beq. apply andb_true_iff. split.
    + apply R_beq_refl.
    + apply Unit_beq_true_iff. auto.
  - Abort.

(** Operation Properties of Quantity *)

Lemma Qadd_comm : forall (q1 q2 : Qu), q1 + q2 = q2 + q1.
Proof.
  intros.
  Abort.  
