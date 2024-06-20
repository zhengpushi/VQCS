(*
  purpose   : Convertion between units.
  author    : Zhengpu Shi
  date      : 2022.04
*)

Require Export Unit NUnit SI.

Open Scope Unit_scope.


(** * Convertion between [Unit] *)

(** ** Check that if two units are similar (i.e., convertible ) *)

(** Two units are similar only when they have same dimensions *)
Definition Usimb (u1 u2 : Unit) : bool :=
  let (_,d1) := u2n u1 in
  let (_,d2) := u2n u2 in
    Dims_eqb d1 d2.

(** Similar units imply a coefficient. *)
Lemma Usimb_true_imply_coef (src ref : Unit) (H1 : Usimb src ref = true)
  (H2 : Ugetcoef ref <> R0)  :
  { k  | src == (k:R) * ref}.
Proof.
  unfold Usimb in *.
  destruct (u2n src) eqn:E1, (u2n ref) eqn:E2.
  apply Dims_eqb_true_iff in H1. subst.
  exists (r/r0)%R.
  apply Ueq_iff_coef_dims.
  rewrite u2n_Umul_rew. rewrite E1,E2. simpl. split.
  - apply Reqb_true_iff. field. intro.
    symmetry in E2. apply Ugetcoef_u2n in E2. subst. easy.
  - destruct d0 as [[[[[[a1 a2] a3] a4] a5] a6] a7].
    apply Dims_eqb_true_refl.
Qed.


(** ** Convert a unit with given reference unit. *)

(**
<<
  For example:
    src = 2*hours, ref = 30*minutes, return (4, 30*minutes).
  Convertion step
  1. judge that src and ref is convertible
  2. calc some coefficients
    src == (coef_src, dims)
    ref == (coef_ref, dims)
    coef = coef_src / coef_ref
  3. return result
    dst = (coef, ref)
>>
*)
Definition Uconv (src ref : Unit) : option (R * Unit) :=
  let '(c1,d1) := u2n src in
  let (c2,d2) := u2n ref in
    if (Dims_eqb d1 d2) 
    then Some ((c1/c2)%R, ref)
    else None.

(* example *)
Example uconv_ex1 : Uconv (2 * 'hrs) (30*'min) = Some (4, (30*'min)).
Proof.
  compute. f_equal. f_equal. field.
Qed.

