(*
  Copyright 2024 ***
  This file is part of VQCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Conversion between normalized units
  author    : ***
  date      : 2022.04
*)

Require Export Unit Nunit.
Require Import SI.
Import SI_Accepted.

Open Scope Unit_scope.

(* we prefer DO NOT expand it *)
#[global] Opaque n2u.


(* ######################################################################### *)
(** * Conversion between normalized units *)

(* ======================================================================= *)
(** ** Two normalized units are convertible *)

(** Two Nunits are convertible only when they have same dimensions *)
Definition ncvtble (n1 n2 : Nunit) : Prop := ndims n1 = ndims n2.

(** ncvtble is equivalence relation *)
Lemma ncvtble_refl : forall n, ncvtble n n.
Proof. intros. hnf. auto. Qed.

Lemma ncvtble_sym : forall n1 n2, ncvtble n1 n2 -> ncvtble n2 n1.
Proof. intros. hnf. auto. Qed.

Lemma ncvtble_trans : forall n1 n2 n3, ncvtble n1 n2 -> ncvtble n2 n3 -> ncvtble n1 n3.
Proof. intros. hnf. rewrite H. auto. Qed.

#[export] Instance ncvtble_equiv : Equivalence ncvtble.
Proof.
  constructor; hnf; intros; auto.
  apply ncvtble_refl. apply ncvtble_sym; auto. apply ncvtble_trans with y; auto.
Qed.

(* (** Similar units imply a coefficient relation. *) *)
(* Lemma ncvtble_imply_coef : forall n1 n2 : Unit, *)
(*     ncvtble n1 n2 -> ncoef n2 <> 0 -> { k | n1 == (k : R) * n2}. *)
(* Proof. *)
(*   intros. unfold ncvtble, ueq in *; simpl in *. *)
(*   exists ((ucoef n1) / (ucoef n2))%R. *)
(*   rewrite u2n_Umult; simpl. apply neq_iff; simpl. split. *)
(*   - field; auto. *)
(*   - rewrite H. auto. *)
(* Qed. *)

(** Two normalized units are similar only when they have same dimensions (bool version) *)
Definition ncvtbleb (n1 n2 : Nunit) : bool := deqb (ndims n1) (ndims n2).

Lemma ncvtbleb_refl : forall n, ncvtbleb n n = true.
Proof. intros. unfold ncvtbleb. rewrite deqb_refl. auto. Qed.

Lemma ncvtbleb_true_iff : forall n1 n2, ncvtbleb n1 n2 = true <-> ncvtble n1 n2.
Proof. intros. unfold ncvtbleb, ncvtble. rewrite deqb_true_iff. simpl. easy. Qed.
  
Lemma ncvtbleb_false_iff : forall n1 n2, ncvtbleb n1 n2 = false <-> ~(ncvtble n1 n2).
Proof. intros. rewrite <- ncvtbleb_true_iff. split; solve_bool. Qed.
  
Lemma ncvtbleb_reflect : forall n1 n2, reflect (ncvtble n1 n2) (ncvtbleb n1 n2).
Proof.
  intros. destruct (ncvtbleb n1 n2) eqn:E1; constructor.
  apply ncvtbleb_true_iff; auto. apply ncvtbleb_false_iff; auto.
Qed.

#[export] Hint Resolve ncvtbleb_reflect : bdestruct.

(** Get ratio factor from [Nunit] `src` to [Nunit] `ref` *)
Definition nconvRate (src ref : Nunit) : option R :=
  if ncvtbleb src ref
  then Some (ncoef src / ncoef ref)%R
  else None.

Lemma nconvRate_eq : forall n, ncoef n <> 0 -> nconvRate n n = Some 1.
Proof. intros. unfold nconvRate. rewrite ncvtbleb_refl. f_equal. ra. Qed.

(** Convert a [Nunit] `src` to [Nunit] `ref` *)
Definition nconv (src ref : Nunit) : option (R * Nunit) :=
  if ncvtbleb src ref
  then Some ((ncoef src / ncoef ref)%R, ref)
  else None.

Section test.
  (* Eval cbn in nconvRate (u2n 'hrs) (u2n 'min). (* Some 60 *) *)
  (* Eval cbn in nconv (u2n 'hrs) (u2n 's). (* Some (60, u2n 's) *) *)
  
  Goal nconvRate (u2n 'hrs) (u2n 'min) = Some 60.
  Proof. cbv. f_equal. lra. Qed.

  Goal nconv (u2n 'hrs) (u2n 's) = Some (3600, (u2n 's)).
  Proof. cbv. f_equal. f_equal. lra. Qed.
End test.


(* (** [uconv] got [None], iff, [ncvtble] not holds  *) *)
(* Lemma uconv_None_iff : forall (src ref : Unit), *)
(*     uconv src ref = None <-> ~ncvtble src ref. *)
(* Proof. intros. unfold uconv. bdestruct (ncvtbleb src ref); try easy. Qed. *)

(* (** If [uconv src ref] got [Some (k, u)], then [ncvtble src ref] holds *) *)
(* Lemma uconv_imply_ncvtble_src_ref : forall (src ref : Unit) k u, *)
(*     uconv src ref = Some (k,u) -> ncvtble src ref. *)
(* Proof. intros. unfold uconv in H. bdestruct (ncvtbleb src ref); try easy. Qed. *)

(* (** If [uconv src ref] got [Some (k,u)], then [ncvtble src u] holds *) *)
(* Lemma uconv_imply_ncvtble_src_u : forall (src ref : Unit) k u, *)
(*     uconv src ref = Some (k,u) -> ncvtble src u. *)
(* Proof. *)
(*   intros. unfold uconv in H. bdestruct (ncvtbleb src ref); try easy. *)
(*   inversion H. apply ncvtble_trans with ref; auto. congruence. *)
(* Qed. *)

(* (** If [uconv src ref] got [Some (k,u)], then [ncvtble ref u] holds *) *)
(* Lemma uconv_imply_ncvtble_ref_u : forall (src ref : Unit) k u, *)
(*     uconv src ref = Some (k,u) -> ncvtble ref u. *)
(* Proof. *)
(*   intros. unfold uconv in H. bdestruct (ncvtbleb src ref); try easy. *)
(*   inversion H. apply ncvtble_refl. *)
(* Qed. *)

(* (** If [uconv src ref] got [Some (k,u)], then `src = k * u` *) *)
(* Lemma uconv_Some : forall (src ref : Unit) k u, *)
(*     uconv src ref = Some (k,u) -> *)
(*     ucoef ref <> 0 -> src == k * u. *)
(* Proof. *)
(*   intros. *)
(*   pose proof (uconv_imply_ncvtble_src_ref src ref _ _ H). *)
(*   unfold uconv in *; simpl in *. apply ncvtbleb_true_iff in H1. rewrite H1 in H. *)
(*   inversion H. hnf. subst. rewrite u2n_Umult. simpl. apply neq_iff; simpl. split. *)
(*   - field; auto. *)
(*   - apply ncvtbleb_true_iff in H1. hnf in H1; simpl in H1. rewrite H1. auto. *)
(* Qed. *)


(* (** ** Unify two [Unit]s *) *)

(* (** *)
(* << *)
(*   For example: *)
(*     src = 2*hours, ref = 30*minutes, return (7200, 1800, secons) *)
(*   Steps: *)
(*   1. normalize *)
(*      u1 == (c1, d1), u2 == (c2, d2) *)
(*   2. check if `u1` and `u2` are convertible, that is `d1 =? d2`. *)
(*      If not return None, otherwise retrun (c1,c2,d). *)
(*      Here, d == (1, d1) = (1, d2) *)
(* >> *)
(*  *) *)

(* Definition uunify (u1 u2 : Unit) : option (R * R * Unit) := *)
(*   let (c1,d1) := u2n u1 in *)
(*   let (c2,d2) := u2n u2 in *)
(*   if deqb d1 d2 *)
(*   then Some (c1,c2, n2u (1, d1)) *)
(*   else None. *)

(* Section test. *)
(*   Import SI_Accepted. *)

(*   (* Eval cbn in (uunify (2 * 'hrs) (30*'min)). *) *)

(*   Goal uunify (2 * 'hrs) (30*'min) = Some (7200,1800, unorm ('s)). *)
(*   Proof. cbn. f_equal. f_equal. f_equal; lra. Qed. *)
(* End test. *)

(* (** [uunify] of same [Unit] `u`, got a known form *) *)
(* Lemma uunify_same : forall u, *)
(*     let (c,d) := (u2n u) in *)
(*     uunify u u = Some (c,c, n2u(1,d)). *)
(* Proof. intros. unfold uunify. lazy [u2n]. rewrite deqb_refl. auto. Qed. *)
  
(* (** [uunify] got [None], iff, [ncvtble] not holds  *) *)
(* Lemma uunify_None_iff : forall (u1 u2 : Unit), *)
(*     uunify u1 u2 = None <-> ~ncvtble u1 u2. *)
(* Proof. *)
(*   intros. unfold uunify, ncvtble. *)
(*   destruct (u2n u1) as [c1 d1], (u2n u2) as [c2 d2]; simpl. *)
(*   bdestruct (deqb d1 d2); subst; try easy. *)
(* Qed. *)

(* (** If [uunify u1 u2] got [Some (k1,k2,u)], then `u` is normalized *) *)
(* Lemma uunify_imply_unormed : forall (u1 u2 : Unit) u k1 k2, *)
(*     uunify u1 u2 = Some (k1,k2,u) -> unormed u. *)
(* Proof. *)
(*   intros. unfold uunify in *. *)
(*   destruct (u2n u1) as [c1 d1], (u2n u2) as [c2 d2]. simpl in H. *)
(*   bdestruct (deqb d1 d2); subst; try easy. *)
(*   inversion H. apply n2u_coef1_unormed. *)
(* Qed. *)

(* (** If [uunify u1 u2] got [Some (k1,k2,u)], then [ncvtble u1 u2] holds *) *)
(* Lemma uunify_imply_ncvtble_u1_u2 : forall (u1 u2 : Unit) k1 k2 u, *)
(*     uunify u1 u2 = Some (k1,k2,u) -> ncvtble u1 u2. *)
(* Proof. *)
(*   intros. unfold uunify, ncvtble in *. *)
(*   destruct (u2n u1) as [c1 d1], (u2n u2) as [c2 d2]; simpl in *. *)
(*   bdestruct (deqb d1 d2); subst; try easy. *)
(* Qed. *)

(* (** If [uunify u1 u2] got [Some (k1,k2,u)], then [ncvtble u1 u] holds *) *)
(* Lemma uunify_imply_ncvtble_u1_u : forall (u1 u2 : Unit) k1 k2 u, *)
(*     uunify u1 u2 = Some (k1,k2,u) -> ncvtble u1 u. *)
(* Proof. *)
(*   intros. unfold uunify, ncvtble in *. *)
(*   destruct (u2n u1) as [c1 d1], (u2n u2) as [c2 d2]. *)
(*   lazy [ndims]. bdestruct (deqb d1 d2); subst; try easy. inv H. simpl. *)
(*   rewrite udims_n2u; auto. *)
(* Qed. *)

(* (* If [uunify u1 u2] got [Some (k1,k2,u)], then [ncvtble u2 u] holds *) *)
(* Lemma uunify_imply_ncvtble_u2_u : forall (u1 u2 : Unit) k1 k2 u, *)
(*     uunify u1 u2 = Some (k1,k2,u) -> ncvtble u2 u. *)
(* Proof. *)
(*   intros. *)
(*   apply ncvtble_trans with u1. *)
(*   apply symmetry. eapply uunify_imply_ncvtble_u1_u2; apply H. *)
(*   eapply uunify_imply_ncvtble_u1_u; apply H. *)
(* Qed. *)

(* (* If [uunify u1 u2] got [Some (k1,k2,u)], then `u1 = k1 * u` *) *)
(* Lemma uunify_imply_u1_u : forall (u1 u2 : Unit) k1 k2 u, *)
(*     uunify u1 u2 = Some (k1,k2,u) -> u1 == k1 * u. *)
(* Proof. *)
(*   intros. unfold uunify, ueq in *. apply neq_iff. rewrite u2n_Umult. *)
(*   destruct (u2n u1) as [c1 d1], (u2n u2) as [c2 d2]; simpl in *. *)
(*   bdestruct (deqb d1 d2); subst; try easy. inv H. split. *)
(*   - rewrite ucoef_n2u. cbn. ring. *)
(*   - des_dims1 d2. rewrite !udim_n2u. simpl. auto. *)
(* Qed. *)

(* (* If [uunify u1 u2] got [Some (k1,k2,u)], then `u2 = k2 * u` *) *)
(* Lemma uunify_imply_u2_u : forall (u1 u2 : Unit) k1 k2 u, *)
(*     uunify u1 u2 = Some (k1,k2,u) -> u2 == k2 * u. *)
(* Proof. *)
(*   intros. unfold uunify, ueq in *. apply neq_iff. rewrite u2n_Umult. *)
(*   destruct (u2n u1) as [c1 d1], (u2n u2) as [c2 d2]; simpl in *. *)
(*   bdestruct (deqb d1 d2); subst; try easy. inversion H. split. *)
(*   - rewrite ucoef_n2u. cbn. ring. *)
(*   - des_dims1 d2. rewrite !udim_n2u. simpl. auto. *)
(* Qed. *)

(* (* [uunify] is commutative when got [None] *) *)
(* Lemma uunify_comm_None : forall u1 u2, uunify u1 u2 = None -> uunify u2 u1 = None. *)
(* Proof. *)
(*   intros. rewrite uunify_None_iff in *. intro. apply ncvtble_sym in H0. easy. *)
(* Qed. *)

(* (* [uunify] is commutative when got [Some] *) *)
(* Lemma uunify_comm_Some : forall u1 u2 k1 k2 u, *)
(*     uunify u1 u2 = Some (k1,k2,u) -> uunify u2 u1 = Some (k2,k1,u). *)
(* Proof. *)
(*   intros. unfold uunify in *. *)
(*   destruct (u2n u1) as [c1 d1], (u2n u2) as [c2 d2]; simpl in *. *)
(*   rewrite deqb_comm. bdestruct (deqb d1 d2); subst; try easy. inversion H. auto. *)
(* Qed. *)

(* (* Specification of [uunify] if got [Some] *) *)
(* Lemma uunify_spec_Some : forall u1 u2 k1 k2 u, *)
(*     uunify u1 u2 = Some (k1,k2,u) -> *)
(*     ucoef u1 = k1 /\ ucoef u2 = k2 /\ *)
(*       u = n2u (1, ndims (u2n u1)) /\ *)
(*       u = n2u (1, ndims (u2n u2)). *)
(* Proof. *)
(*   intros. unfold uunify in H. *)
(*   destruct (u2n u1) as [c1 d1] eqn:E1, (u2n u2) as [c2 d2] eqn:E2; simpl in *. *)
(*   bdestruct (deqb d1 d2); subst; try easy. inversion H; subst. *)
(*   rewrite <- ncoef_u2n; rewrite E1; simpl. *)
(*   rewrite <- ncoef_u2n; rewrite E2; simpl. auto. *)
(* Qed. *)

(* (* if (u1.u2=Some u12) and (u2.u3=Some ?), then (u12.u3) <> None *) *)
(* Lemma uunify_SSN_contr : forall u1 u2 u3 u12 k1 k2 k3 k4 u23, *)
(*     uunify u1 u2 = Some (k1,k2,u12) -> *)
(*     uunify u2 u3 = Some (k3,k4,u23) -> *)
(*     uunify u12 u3 <> None. *)
(* Proof. *)
(*   intros. apply uunify_spec_Some in H,H0. logic. subst. *)
(*   simpl in *. rewrite H6. rewrite H3. clear. *)
(*   unfold uunify. rewrite u2n_n2u. simpl. rewrite !Z.eqb_refl. simpl. easy. *)
(* Qed. *)

(* (* if (u1.u2=u12) and (u12.u3=?), then (u1.u3) <> None *) *)
(* Lemma uunify_SNS_contr : forall u1 u2 u3 u12 k1 k2 k3 k4 u23, *)
(*     uunify u1 u2 = Some (k1,k2,u12) -> *)
(*     uunify u12 u3 = Some (k3,k4,u23) -> *)
(*     uunify u1 u3 <> None. *)
(* Proof. *)
(*   intros. apply uunify_spec_Some in H,H0. logic. subst. *)
(*   simpl in *. apply n2u_eq_iff in H6, H3. *)
(*   unfold uunify. simpl. inversion H6. inversion H3. *)
(*   rewrite !udim_n2u in *; simpl in *. rewrite !Z.eqb_refl; simpl. easy. *)
(* Qed. *)



(* (* destruct `uunify u1 u2` *) *)
(* Ltac des_uunify u1 u2 := *)
(*   destruct (uunify u1 u2) as [((?k,?k),?u)|] eqn:?E; auto. *)

(* (* Solve: uunify u1 u2 =? |- uunify u1 u2 =? or uunify u2 u1 =? *) *)
(* Ltac solve_Unify_eq := *)
(*   repeat *)
(*     match goal with *)
(*     | H: uunify ?u1 ?u2 = _ |- uunify ?u1 ?u2 = _ => apply H *)
(*     | H: uunify ?u1 ?u2=Some _ |- uunify ?u2 ?u1=Some _ => apply uunify_comm_Some *)
(*     | H: uunify ?u1 ?u2 = None |- uunify ?u2 ?u1 = None => apply uunify_comm_None *)
(*     end. *)

(* (* Simplify promise of form (Unify u1 u2 = Some ?) to `atom` equations *) *)
(* Ltac simp_uunify_eq_Some := *)
(*   repeat *)
(*     match goal with *)
(*     | H: uunify ?u1 ?u2 = Some _ |- _ => *)
(*         apply uunify_spec_Some in H; logic *)
(*     end. *)

(* (* Solve {Unify _ _ = Some _, Unify _ _ = Some, Unify _ _ = None} |- _ *) *)
(* Ltac solve_Unify_contro := *)
(*   exfalso; *)
(*   match goal with *)
(*   | H1:uunify ?u1 ?u2 = Some _, *)
(*       H2:uunify ?u2 ?u3 = Some (_,_,?u23), *)
(*         H3: uunify ?u1 ?u23 = None |- _ => *)
(*       eapply (uunify_SSN_contr u3 u2 u1 u23); solve_Unify_eq *)
(*   | H1:uunify ?u1 ?u2 = Some (_,_,?u12), *)
(*       H2:uunify ?u2 ?u3 = Some _, *)
(*         H3: uunify ?u12 ?u3 = None |- _ => *)
(*       eapply (uunify_SSN_contr u1 u2 u3 u12); solve_Unify_eq *)
(*   | H1:uunify ?u1 ?u2 = Some (_,_,?u12), *)
(*       H2:uunify ?u2 ?u3 = None, *)
(*         H3: uunify ?u12 ?u3 = Some _ |- _ => *)
(*       eapply (uunify_SNS_contr u2 u1 u3 u12); solve_Unify_eq *)
(*   | H1:uunify ?u1 ?u2 = None, *)
(*       H2:uunify ?u2 ?u3 = Some (_,_,?u23), *)
(*         H3: uunify ?u1 ?u23 = Some _ |- _ => *)
(*       eapply (uunify_SNS_contr u2 u3 u1 u23); solve_Unify_eq *)
(*   end. *)

(* (** unify two [Unit]s to normalized unit *) *)
(* Definition uunifyN (u1 u2 : Unit) : option (R * Nunit) := *)
(*   let (c1,d1) := u2n u1 in *)
(*   let (c2,d2) := u2n u2 in *)
(*   if deqb d1 d2 then Some (c1, (c2, d1)) else None. *)
