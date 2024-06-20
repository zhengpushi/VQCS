(*
  Properties of Unit
*)

Require Export Unit.

(** ** UnitKind_beq *)

Lemma UnitKind_beq_refl : forall k, UnitKind_beq k k = true.
Proof. destruct k; auto. Qed.

Lemma UnitKind_beq_sym : forall k1 k2, 
  UnitKind_beq k1 k2 = true -> UnitKind_beq k2 k1 = true.
Proof. destruct k1,k2; auto. Qed.

Lemma UnitKind_beq_trans : forall k1 k2 k3, 
  UnitKind_beq k1 k2 = true -> 
  UnitKind_beq k2 k3 = true -> 
  UnitKind_beq k1 k3 = true.
Proof. destruct k1,k2,k3; auto. Qed.

Lemma UnitKind_beq_true_iff : forall k1 k2,
  UnitKind_beq k1 k2 = true <-> k1 = k2.
Proof. split; intros H1; destruct k1,k2; inversion H1; auto. Qed.

Lemma UnitKind_beq_false_iff : forall k1 k2,
  UnitKind_beq k1 k2 = false <-> k1 <> k2.
Proof. 
  split; intros H1.
  - destruct k1,k2; inversion H1; discriminate.
  - destruct k1,k2; compute; auto; destruct H1; auto.
Qed.

Global Hint Resolve
  UnitKind_beq_refl
  UnitKind_beq_sym
  UnitKind_beq_trans
  UnitKind_beq_true_iff
  UnitKind_beq_false_iff
  : unit.

(** ** ElementUnit_beq *)

Open Scope ElementUnit_scope.

Lemma ElementUnit_beq_refl : forall u, ElementUnit_beq u u = true.
Proof.
  destruct u; simpl.
  rewrite UnitKind_beq_refl. rewrite Qeq_bool_refl. auto.
Qed.

Lemma ElementUnit_beq_sym : forall u1 u2, 
  ElementUnit_beq u1 u2 = true -> ElementUnit_beq u2 u1 = true.
Proof.
  destruct u1, u2; simpl;
  destruct (UnitKind_beq EUkind EUkind0) eqn : E1;
  destruct (Qeq_bool EUcoef EUcoef0) eqn : E2;
  intros H1; inversion H1.
  apply UnitKind_beq_sym in E1; rewrite E1.
  apply Qeq_bool_sym in E2; rewrite E2. auto.
Qed.

Lemma ElementUnit_beq_trans : forall u1 u2 u3, 
  ElementUnit_beq u1 u2 = true -> 
  ElementUnit_beq u2 u3 = true -> 
  ElementUnit_beq u1 u3 = true.
Proof.
  destruct u1, u2, u3; simpl;
  destruct (UnitKind_beq EUkind EUkind0) eqn : E1;
  destruct (Qeq_bool EUcoef EUcoef0) eqn : E2;
  intros H1; inversion H1.
  destruct (UnitKind_beq EUkind0 EUkind1) eqn : E3;
  destruct (Qeq_bool EUcoef0 EUcoef1) eqn : E4;
  intros H2; inversion H2.
  apply (UnitKind_beq_trans EUkind EUkind0 EUkind1) in E1;auto;rewrite E1.
  apply (Qeq_bool_trans EUcoef EUcoef0 EUcoef1) in E2;auto.
Qed.

Lemma ElementUnit_beq_true_iff : forall u1 u2,
  ElementUnit_beq u1 u2 = true <-> u1 == u2.
Proof.
  split; intros H1; destruct u1,u2; inversion H1;
  apply andb_true_iff in H0; destruct H0;
  unfold ElementUnit_eq, ElementUnit_beq;
  rewrite H,H0; auto.
Qed.

Lemma ElementUnit_beq_false_iff : forall u1 u2,
  ElementUnit_beq u1 u2 = false <-> not (u1 == u2).
Proof. 
  split; intros H1.
  - destruct u1,u2; inversion H1;
    unfold ElementUnit_eq, ElementUnit_beq;
    apply andb_false_iff in H0.
    destruct H0 as [H0|H0]; rewrite H0.
    + simpl; auto.
    + rewrite andb_comm; simpl; auto.
  - unfold ElementUnit_eq in H1.
    apply not_true_is_false. auto.
Qed.

Lemma ElementUnit_eq_refl : forall u, ElementUnit_eq u u.
Proof. unfold ElementUnit_eq. apply ElementUnit_beq_refl. Qed.

Lemma ElementUnit_eq_sym : forall u1 u2, 
  ElementUnit_eq u1 u2 -> ElementUnit_eq u2 u1.
Proof. unfold ElementUnit_eq. apply ElementUnit_beq_sym. Qed.

Lemma ElementUnit_eq_trans : forall u1 u2 u3, 
  ElementUnit_eq u1 u2 -> 
  ElementUnit_eq u2 u3 -> 
  ElementUnit_eq u1 u3.
Proof. unfold ElementUnit_eq. apply ElementUnit_beq_trans. Qed.

Global Hint Resolve
  ElementUnit_beq_refl
  ElementUnit_beq_sym
  ElementUnit_beq_trans
  ElementUnit_beq_true_iff
  ElementUnit_beq_false_iff
  ElementUnit_eq_refl
  ElementUnit_eq_sym
  ElementUnit_eq_trans
  : unit.

(** ** BasicUnit_beq *)

Open Scope BasicUnit_scope.

Lemma BasicUnit_beq_refl : forall u, BasicUnit_beq u u = true.
Proof. destruct u; auto; apply ElementUnit_beq_refl. Qed.

Lemma BasicUnit_beq_sym : forall u1 u2, 
  BasicUnit_beq u1 u2 = true ->
  BasicUnit_beq u2 u1 = true.
Proof. destruct u1,u2; auto; apply ElementUnit_beq_sym. Qed.

Lemma BasicUnit_beq_trans : forall u1 u2 u3, 
  BasicUnit_beq u1 u2 = true ->
  BasicUnit_beq u2 u3 = true ->
  BasicUnit_beq u1 u3 = true.
Proof. 
  destruct u1,u2,u3; auto;simpl;intros H1 H2; try discriminate H1;
  apply (ElementUnit_beq_trans eu eu0 eu1); auto.
Qed.

Lemma BasicUnit_beq_true_iff : forall u1 u2,
  BasicUnit_beq u1 u2 = true <-> u1 == u2.
Proof. split; intros H1; destruct u1,u2; inversion H1;auto. Qed.

Lemma Basic : forall u1 u2,
  BasicUnit_beq u1 u2 = false <-> not (u1 == u2).
Proof.
  split; intros H1.
  - destruct u1,u2; try discriminate;
    intros H2; apply BasicUnit_beq_true_iff in H2;
    rewrite H1 in H2; discriminate.
  - unfold BasicUnit_eq in H1.
    apply not_true_is_false; auto.
Qed.

Lemma BasicUnit_eq_refl : forall u, BasicUnit_eq u u.
Proof. unfold BasicUnit_eq. apply BasicUnit_beq_refl. Qed.

Lemma BasicUnit_eq_sym : forall u1 u2, 
  BasicUnit_eq u1 u2 ->
  BasicUnit_eq u2 u1.
Proof. unfold BasicUnit_eq. apply BasicUnit_beq_sym. Qed.

Lemma BasicUnit_eq_trans : forall u1 u2 u3, 
  BasicUnit_eq u1 u2 ->
  BasicUnit_eq u2 u3 ->
  BasicUnit_eq u1 u3.
Proof. unfold BasicUnit_eq. apply BasicUnit_beq_trans. Qed.

Global Hint Resolve
  BasicUnit_beq_refl
  BasicUnit_beq_sym
  BasicUnit_beq_trans
  BasicUnit_beq_true_iff
  Basic
  BasicUnit_eq_refl
  BasicUnit_eq_sym
  BasicUnit_eq_trans
  : unit.

(** * Unit *)

Open Scope Unit_scope.


(** ** uflat_aux *)
(* 
Lemma uflat_aux_spec : forall u,  uflat_aux 
uflat (/ u)
 *)

(** ** uflat *)
(* 
Lemma uflat_spec : forall u, uflat 
uflat (/ u) *)

(** ** u2list *)

(** ** ulinsert *)

(** ** ulclean *)

(** ** list2u *)

(** ** unorm *)

Lemma unorm_spec_basicUnit : forall u, ub u == (unorm u).
Proof. destruct u; compute; auto. Qed.
(* 
Lemma unorm_spec_inv : forall u, / u == (unorm (/ u)).
Proof.
  intros. unfold unorm.
  induction u.
  - destruct u; compute; auto.
  -  simpl. apply unorm_spec_basicUnit.
 destruct u; compute; auto. Qed. *)

Lemma unorm_spec : forall u, u == (unorm u).
Proof.
  induction u.
  - apply unorm_spec_basicUnit.
  - destruct u.
    + unfold unorm.
      destruct u; compute; auto.
    + Admitted.
  
(** ** ueq *)

(** ** Unit_beq_aux *)

(* Lemma Unit_inv_inv : forall u, unorm (/ / u) = unorm u.
Proof. 
  induction u.
  - destruct u; unfold unorm; auto.
  - compute. destruct u.
    + unfold unorm; auto.
    + destruct u.
      * unfold unorm; auto.
      * 
    + unfold unorm. auto.
    + unfold unorm. simpl.
     simpl.
Admitted.
 *)

Lemma Unit_beq_aux_refl : forall u, Unit_beq_aux u u = true.
Proof.
  induction u; simpl; auto with unit.
  rewrite IHu1,IHu2. auto.
Qed.

Lemma Unit_beq_aux_sym : forall u1 u2, 
  Unit_beq_aux u1 u2 = true ->
  Unit_beq_aux u2 u1 = true.
Proof.
  induction u1,u2; simpl; auto with unit.
  destruct (Unit_beq_aux u1_1 u2_1) eqn : E1,
  (Unit_beq_aux u1_2 u2_2) eqn : E2.
  - apply IHu1_1 in E1. rewrite E1.
    apply IHu1_2 in E2. rewrite E2. auto.
  - intros H; inversion H.
  - intros H; inversion H.
  - intros H; inversion H.
Qed.

Lemma Unit_beq_aux_trans : forall u1 u2 u3, 
  Unit_beq_aux u1 u2 = true ->
  Unit_beq_aux u2 u3 = true ->
  Unit_beq_aux u1 u3 = true.
Proof.
  induction u1,u2,u3; simpl; auto with unit;
  intros H1 H2; try discriminate.
  - apply (BasicUnit_beq_trans u u0 u1); auto.
  - apply (IHu1 u2 u3 H1 H2).
  - apply andb_true_iff in H1,H2.
    destruct H1 as [H10 H11], H2 as [H20 H21].
    assert (Unit_beq_aux u1_1 u3_1 = true).
    { apply (IHu1_1 u2_1); auto. }
    assert (Unit_beq_aux u1_2 u3_2 = true).
    { apply (IHu1_2 u2_2); auto. }
    rewrite H,H0. auto.
Qed.

Lemma Unit_beq_aux_true_iff : forall u1 u2,
  Unit_beq_aux u1 u2 = true <-> u1 == u2.
Proof. 
  split; intros H1; destruct u1,u2.
  - destruct u,u0; try discriminate; auto with unit; simpl in H1.
    + rewrite ElementUnit_beq_true_iff in H1.
  Admitted.

Lemma Unit_beq_aux_false_iff : forall u1 u2,
  Unit_beq_aux u1 u2 = false <-> not (u1 == u2).
Proof.
  Admitted.

(** ** Unit_beq *)

(* 这些性质好像很简单，不需要说明 *)
(* Lemma ueq_refl : forall u, ueq u u.
Proof. intros. unfold ueq. auto. Qed.

Lemma ueq_sym : forall u1 u2, ueq u1 u2 -> ueq u2 u1.
Proof. intros. unfold ueq. destruct u1,u2; auto. Qed.

Lemma ueq_trans : forall u1 u2 u3, ueq u1 u2 -> ueq u2 u3 -> ueq u1 u3.
Proof. 
  intros. unfold ueq. destruct u1,u2,u3; 
  inversion H; inversion H0; auto; subst; auto.
Qed.
 *)
(* Add Parametric Relation : (Unit) (ueq)
  reflexivity proved by (ueq_refl)
  symmetry proved by (ueq_sym)
  transitivity proved by (ueq_trans)
  as eq_set_rel.
   *)

Lemma Unit_beq_refl : forall u, Unit_beq u u = true.
Proof. unfold Unit_beq. intros. apply Unit_beq_aux_refl. Qed.

Lemma Unit_beq_sym : forall u1 u2, 
  Unit_beq u1 u2 = true ->
  Unit_beq u2 u1 = true.
Proof. unfold Unit_beq. intros. apply Unit_beq_aux_sym; auto. Qed.

Lemma Unit_beq_trans : forall u1 u2 u3, 
  Unit_beq u1 u2 = true ->
  Unit_beq u2 u3 = true ->
  Unit_beq u1 u3 = true.
Proof.
  unfold Unit_beq. intros.
  apply (Unit_beq_aux_trans (unorm u1) (unorm u2)); auto.
Qed.

Lemma Unit_beq_true_iff : forall u1 u2,
  Unit_beq u1 u2 = true <-> u1 == u2.
Proof.
  intros. unfold Unit_beq. split.
  - rewrite Unit_beq_aux_true_iff.
  Admitted.

Lemma Unit_beq_false_iff : forall u1 u2,
  Unit_beq u1 u2 = false <-> not (u1 == u2).
Proof.
  Admitted.
