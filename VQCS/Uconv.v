(*
  Copyright 2024 ZhengPu Shi
  This file is part of VQCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Conversion between units.
  author    : ZhengPu Shi
  date      : 2022.04
*)

Require Export Unit Nunit.
Require Import SI.

Open Scope Unit_scope.


(* We prefer DONT expand [n2u] *)
Opaque n2u.


(** * Conversion between [Unit] *)

(** ** Two units are convertible *)

(** Two units are convertible only when they have same dimensions *)
Definition Ucvtible (u1 u2 : Unit) : Prop :=
  Ndims (u2n u1) = Ndims (u2n u2).

(* Ucvtible is equivalence relation *)
Lemma Ucvtible_refl : forall u, Ucvtible u u.
Proof. intros. hnf. auto. Qed.

Lemma Ucvtible_sym : forall u1 u2, Ucvtible u1 u2 -> Ucvtible u2 u1.
Proof. intros. hnf. auto. Qed.

Lemma Ucvtible_trans : forall u1 u2 u3,
    Ucvtible u1 u2 -> Ucvtible u2 u3 -> Ucvtible u1 u3.
Proof. intros. hnf. rewrite H. auto. Qed.

#[export] Instance Ucvtible_equiv : Equivalence Ucvtible.
Proof.
  constructor; hnf; intros; auto.
  apply Ucvtible_refl. apply Ucvtible_sym; auto. apply Ucvtible_trans with y; auto.
Qed.

(** Similar units imply a coefficient relation. *)
Lemma Ucvtible_imply_coef : forall u1 u2 : Unit,
    Ucvtible u1 u2 -> Ucoef u2 <> 0 -> { k | u1 == (k : R) * u2}.
Proof.
  intros. unfold Ucvtible, Ueq in *; simpl in *.
  exists ((Ucoef u1) / (Ucoef u2))%R.
  rewrite u2n_Umult; simpl. apply Neq_iff; simpl. split.
  - field; auto.
  - rewrite H. auto.
Qed.

(** Two units are similar only when they have same dimensions (bool version) *)
Definition Ucvtibleb (u1 u2 : Unit) : bool :=
  Deqb (Ndims (u2n u1)) (Ndims (u2n u2)).

Lemma Ucvtibleb_true_iff : forall u1 u2, Ucvtibleb u1 u2 = true <-> Ucvtible u1 u2.
Proof. intros. unfold Ucvtibleb, Ucvtible. rewrite Deqb_true_iff. simpl. easy. Qed.
  
Lemma Ucvtibleb_false_iff : forall u1 u2, Ucvtibleb u1 u2 = false <-> ~(Ucvtible u1 u2).
Proof. intros. rewrite <- Ucvtibleb_true_iff. split; solve_bool. Qed.
  
Lemma Ucvtibleb_reflect : forall u1 u2, reflect (Ucvtible u1 u2) (Ucvtibleb u1 u2).
Proof.
  intros. destruct (Ucvtibleb u1 u2) eqn:E1; constructor.
  apply Ucvtibleb_true_iff; auto. apply Ucvtibleb_false_iff; auto.
Qed.

#[export] Hint Resolve Ucvtibleb_reflect : bdestruct.


(** ** Convert a unit with given reference unit. *)

(**
<<
  For example:
    src = 2*hours, ref = 30*minutes, return (4, 30*minutes).
  Conversion step
  1. check that src and ref is convertible
  2. calc coefficient
    src == (coef_src, dims)
    ref == (coef_ref, dims)
    coef = coef_src / coef_ref
  3. return result
    dst = (coef, ref)
>>
 *)

Definition Uconv (src ref : Unit) : option (R * Unit) :=
  if Ucvtibleb src ref
  then Some ((Ncoef (u2n src) / Ncoef (u2n ref))%R, ref)
  else None.

Section test.
  Import SI_Accepted.

  (* Compute (Uconv (2 * 'hrs) (30*'min)). *)
  (* Compute (Uconv (2 * 'hrs) (20*'A)). *)

  Let uconv_ex1 : Uconv (2 * 'hrs) (30*'min) = Some (4, 30*'min).
  Proof. cbv. f_equal. f_equal. field. Qed.
End test.

(* [Uconv] got [None], iff, [Ucvtible] not holds  *)
Lemma Uconv_None_iff : forall (src ref : Unit),
    Uconv src ref = None <-> ~Ucvtible src ref.
Proof. intros. unfold Uconv. bdestruct (Ucvtibleb src ref); try easy. Qed.

(* If [Uconv src ref] got [Some (k, u)], then [Ucvtible src ref] holds *)
Lemma Uconv_imply_Ucvtible_src_ref : forall (src ref : Unit) k u,
    Uconv src ref = Some (k,u) -> Ucvtible src ref.
Proof. intros. unfold Uconv in H. bdestruct (Ucvtibleb src ref); try easy. Qed.

(* If [Uconv src ref] got [Some (k,u)], then [Ucvtible src u] holds *)
Lemma Uconv_imply_Ucvtible_src_u : forall (src ref : Unit) k u,
    Uconv src ref = Some (k,u) -> Ucvtible src u.
Proof.
  intros. unfold Uconv in H. bdestruct (Ucvtibleb src ref); try easy.
  inversion H. apply Ucvtible_trans with ref; auto. congruence.
Qed.

(* If [Uconv src ref] got [Some (k,u)], then [Ucvtible ref u] holds *)
Lemma Uconv_imply_Ucvtible_ref_u : forall (src ref : Unit) k u,
    Uconv src ref = Some (k,u) -> Ucvtible ref u.
Proof.
  intros. unfold Uconv in H. bdestruct (Ucvtibleb src ref); try easy.
  inversion H. apply Ucvtible_refl.
Qed.

(* If [Uconv src ref] got [Some (k,u)], then `src = k * u` *)
Lemma Uconv_Some : forall (src ref : Unit) k u,
    Uconv src ref = Some (k,u) ->
    Ucoef ref <> 0 -> src == k * u.
Proof.
  intros.
  pose proof (Uconv_imply_Ucvtible_src_ref src ref _ _ H).
  unfold Uconv in *; simpl in *. apply Ucvtibleb_true_iff in H1. rewrite H1 in H.
  inversion H. hnf. subst. rewrite u2n_Umult. simpl. apply Neq_iff; simpl. split.
  - field; auto.
  - apply Ucvtibleb_true_iff in H1. hnf in H1; simpl in H1. rewrite H1. auto.
Qed.



(** ** Unify two [Unit]s *)

(**
<<
  For example:
    src = 2*hours, ref = 30*minutes, return (7200, 1800, secons)
  Steps:
  1. normalize
    u1 == (c1, d1), u2 == (c2, d2)
  2. check if `u1` and `u2` are convertible, that is `d1 =? d2`.
     If not return None, otherwise retrun (c1,c2,d).
     Here, d == (1, d1) = (1, d2)
>>
 *)

Definition Uunify (u1 u2 : Unit) : option (R * R * Unit) :=
  let c1 := Ncoef (u2n u1) in
  let d1 := Ndims (u2n u1) in
  let c2 := Ncoef (u2n u2) in
  let d2 := Ndims (u2n u2) in
  if Deqb d1 d2
  then Some (c1,c2, n2u (1, d1))
  else None.

  (* let (c1,d1) := u2n u1 in *)
  (* let (c2,d2) := u2n u2 in *)
  (* if Deqb d1 d2 *)
  (* then Some (c1,c2, n2u (1, d1)) *)
  (* else None. *)

Section test.
  Import SI_Accepted.

  (* Compute (Uunify (2 * 'hrs) (30*'min)). *)

  Goal Uunify (2 * 'hrs) (30*'min) = Some (7200,1800, Unorm ('s)).
  Proof. cbv. f_equal. f_equal. f_equal; field. Qed.
End test.

(* [Uunify] of same [Unit] `u`, got a known form *)
Lemma Uunify_same : forall u,
    let (c,d) := (Ncoef (u2n u), Ndims (u2n u)) in
    Uunify u u = Some (c,c, n2u(1,d)).
Proof. intros. unfold Uunify. rewrite Deqb_refl. auto. Qed.
  
(* [Uunify] got [None], iff, [Ucvtible] not holds  *)
Lemma Uunify_None_iff : forall (u1 u2 : Unit),
    Uunify u1 u2 = None <-> ~Ucvtible u1 u2.
Proof.
  intros. unfold Uunify, Ucvtible.
  destruct (u2n u1) as [c1 d1], (u2n u2) as [c2 d2]; simpl.
  bdestruct (Deqb d1 d2); subst; try easy.
Qed.

(* If [Uunify u1 u2] got [Some (k1,k2,u)], then `u` is normalized *)
Lemma Uunify_imply_Unormalized_u : forall (u1 u2 : Unit) u k1 k2,
    Uunify u1 u2 = Some (k1,k2,u) -> Unormalized u.
Proof.
  intros. unfold Uunify in *.
  destruct (u2n u1) as [c1 d1], (u2n u2) as [c2 d2]. simpl in H.
  bdestruct (Deqb d1 d2); subst; try easy.
  inversion H. apply n2u_coef1_Unormalized.
Qed.

(* If [Uunify u1 u2] got [Some (k1,k2,u)], then [Ucvtible u1 u2] holds *)
Lemma Uunify_imply_Ucvtible_u1_u2 : forall (u1 u2 : Unit) k1 k2 u,
    Uunify u1 u2 = Some (k1,k2,u) -> Ucvtible u1 u2.
Proof.
  intros. unfold Uunify, Ucvtible in *.
  destruct (u2n u1) as [c1 d1], (u2n u2) as [c2 d2]; simpl in *.
  bdestruct (Deqb d1 d2); subst; try easy.
Qed.

(* If [Uunify u1 u2] got [Some (k1,k2,u)], then [Ucvtible u1 u] holds *)
Lemma Uunify_imply_Ucvtible_u1_u : forall (u1 u2 : Unit) k1 k2 u,
    Uunify u1 u2 = Some (k1,k2,u) -> Ucvtible u1 u.
Proof.
  intros. unfold Uunify, Ucvtible in *.
  destruct (u2n u1) as [c1 d1], (u2n u2) as [c2 d2]; simpl in *.
  bdestruct (Deqb d1 d2); subst; try easy. inversion H. rewrite Udims_n2u; auto.
Qed.

(* If [Uunify u1 u2] got [Some (k1,k2,u)], then [Ucvtible u2 u] holds *)
Lemma Uunify_imply_Ucvtible_u2_u : forall (u1 u2 : Unit) k1 k2 u,
    Uunify u1 u2 = Some (k1,k2,u) -> Ucvtible u2 u.
Proof.
  intros.
  apply Ucvtible_trans with u1.
  apply symmetry. eapply Uunify_imply_Ucvtible_u1_u2; apply H.
  eapply Uunify_imply_Ucvtible_u1_u; apply H.
Qed.

(* If [Uunify u1 u2] got [Some (k1,k2,u)], then `u1 = k1 * u` *)
Lemma Uunify_imply_u1_u : forall (u1 u2 : Unit) k1 k2 u,
    Uunify u1 u2 = Some (k1,k2,u) -> u1 == k1 * u.
Proof.
  intros. unfold Uunify, Ueq in *. apply Neq_iff. rewrite u2n_Umult.
  destruct (u2n u1) as [c1 d1], (u2n u2) as [c2 d2]; simpl in *.
  bdestruct (Deqb d1 d2); subst; try easy. inversion H. split.
  - rewrite Ucoef_n2u. cbn. ring.
  - simp_Udim. rewrite !Udim_n2u. simpl. des_dims1 d2; auto.
Qed.

(* If [Uunify u1 u2] got [Some (k1,k2,u)], then `u2 = k2 * u` *)
Lemma Uunify_imply_u2_u : forall (u1 u2 : Unit) k1 k2 u,
    Uunify u1 u2 = Some (k1,k2,u) -> u2 == k2 * u.
Proof.
  intros. unfold Uunify, Ueq in *. apply Neq_iff. rewrite u2n_Umult.
  destruct (u2n u1) as [c1 d1], (u2n u2) as [c2 d2]; simpl in *.
  bdestruct (Deqb d1 d2); subst; try easy. inversion H. split.
  - rewrite Ucoef_n2u. cbn. ring.
  - simp_Udim. rewrite !Udim_n2u. simpl. des_dims1 d2; auto.
Qed.

(* [Uunify] is commutative when got [None] *)
Lemma Uunify_comm_None : forall u1 u2, Uunify u1 u2 = None -> Uunify u2 u1 = None.
Proof.
  intros. rewrite Uunify_None_iff in *. intro. apply Ucvtible_sym in H0. easy.
Qed.

(* [Uunify] is commutative when got [Some] *)
Lemma Uunify_comm_Some : forall u1 u2 k1 k2 u,
    Uunify u1 u2 = Some (k1,k2,u) -> Uunify u2 u1 = Some (k2,k1,u).
Proof.
  intros. unfold Uunify in *.
  destruct (u2n u1) as [c1 d1], (u2n u2) as [c2 d2]; simpl in *.
  rewrite Deqb_comm. bdestruct (Deqb d1 d2); subst; try easy. inversion H. auto.
Qed.

(* Specification of [Uunify] if got [Some] *)
Lemma Uunify_spec_Some : forall u1 u2 k1 k2 u,
    Uunify u1 u2 = Some (k1,k2,u) ->
    Ucoef u1 = k1 /\ Ucoef u2 = k2 /\
      u = n2u (1, Ndims (u2n u1)) /\
      u = n2u (1, Ndims (u2n u2)).
Proof.
  intros. unfold Uunify in H.
  destruct (u2n u1) as [c1 d1] eqn:E1, (u2n u2) as [c2 d2] eqn:E2; simpl in *.
  bdestruct (Deqb d1 d2); subst; try easy. inversion H; subst.
  rewrite <- Ncoef_u2n; rewrite E1; simpl.
  rewrite <- Ncoef_u2n; rewrite E2; simpl. auto.
Qed.

(* if (u1.u2=Some u12) and (u2.u3=Some ?), then (u12.u3) <> None *)
Lemma Uunify_SSN_contr : forall u1 u2 u3 u12 k1 k2 k3 k4 u23,
    Uunify u1 u2 = Some (k1,k2,u12) ->
    Uunify u2 u3 = Some (k3,k4,u23) ->
    Uunify u12 u3 <> None.
Proof.
  intros. apply Uunify_spec_Some in H,H0. simp_logic. subst.
  simpl in *. rewrite H6. rewrite H3. clear.
  unfold Uunify. rewrite u2n_n2u. simpl. rewrite !Z.eqb_refl. simpl. easy.
Qed.

(* if (u1.u2=u12) and (u12.u3=?), then (u1.u3) <> None *)
Lemma Uunify_SNS_contr : forall u1 u2 u3 u12 k1 k2 k3 k4 u23,
    Uunify u1 u2 = Some (k1,k2,u12) ->
    Uunify u12 u3 = Some (k3,k4,u23) ->
    Uunify u1 u3 <> None.
Proof.
  intros. apply Uunify_spec_Some in H,H0. simp_logic. subst.
  simpl in *. apply n2u_eq_iff in H6, H3.
  unfold Uunify. simpl. inversion H6. inversion H3.
  rewrite !Udim_n2u in *; simpl in *. rewrite !Z.eqb_refl; simpl. easy.
Qed.



(* destruct `Uunify u1 u2` *)
Ltac des_Uunify u1 u2 :=
  destruct (Uunify u1 u2) as [((?k,?k),?u)|] eqn:?E; auto.

(* Solve: Uunify u1 u2 =? |- Uunify u1 u2 =? or Uunify u2 u1 =? *)
Ltac solve_Unify_eq :=
  repeat
    match goal with
    | H: Uunify ?u1 ?u2 = _ |- Uunify ?u1 ?u2 = _ => apply H
    | H: Uunify ?u1 ?u2=Some _ |- Uunify ?u2 ?u1=Some _ => apply Uunify_comm_Some
    | H: Uunify ?u1 ?u2 = None |- Uunify ?u2 ?u1 = None => apply Uunify_comm_None
    end.

(* Simplify promise of form (Unify u1 u2 = Some ?) to `atom` equations *)
Ltac simp_Uunify_eq_Some :=
  repeat
    match goal with
    | H: Uunify ?u1 ?u2 = Some _ |- _ =>
        apply Uunify_spec_Some in H; simp_logic
    end.

(* Solve {Unify _ _ = Some _, Unify _ _ = Some, Unify _ _ = None} |- _ *)
Ltac solve_Unify_contro :=
  exfalso;
  match goal with
  | H1:Uunify ?u1 ?u2 = Some _,
      H2:Uunify ?u2 ?u3 = Some (_,_,?u23),
        H3: Uunify ?u1 ?u23 = None |- _ =>
      eapply (Uunify_SSN_contr u3 u2 u1 u23); solve_Unify_eq
  | H1:Uunify ?u1 ?u2 = Some (_,_,?u12),
      H2:Uunify ?u2 ?u3 = Some _,
        H3: Uunify ?u12 ?u3 = None |- _ =>
      eapply (Uunify_SSN_contr u1 u2 u3 u12); solve_Unify_eq
  | H1:Uunify ?u1 ?u2 = Some (_,_,?u12),
      H2:Uunify ?u2 ?u3 = None,
        H3: Uunify ?u12 ?u3 = Some _ |- _ =>
      eapply (Uunify_SNS_contr u2 u1 u3 u12); solve_Unify_eq
  | H1:Uunify ?u1 ?u2 = None,
      H2:Uunify ?u2 ?u3 = Some (_,_,?u23),
        H3: Uunify ?u1 ?u23 = Some _ |- _ =>
      eapply (Uunify_SNS_contr u2 u3 u1 u23); solve_Unify_eq
  end.

Definition UunifyN (u1 u2 : Unit) : option (R * R * Dims) :=
  let c1 := Ncoef (u2n u1) in
  let d1 := Ndims (u2n u1) in
  let c2 := Ncoef (u2n u2) in
  let d2 := Ndims (u2n u2) in if Deqb d1 d2 then Some (c1, c2, d1) else None.
