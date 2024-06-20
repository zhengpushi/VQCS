(*
  category:     Utilities
  filename:     Unit_props.v
  author:       Zhengpu Shi
  date:         2021.05.08
  purpose:      Properities of the Unit System.

  copyright:    Formalized Engineering Mathematics team of NUAA.
  website:      http://fem-nuaa.cn/FML4FCS
*)

Require Import Lra.

Require Import Unit.
Import DerivedUnits.


(** unit function's semantic correctness *)

Lemma Rpower_neq0 : forall base exp, base <> 0 -> exp <> 0 -> 
  Rpower base exp <> 0.
Admitted.

Lemma unit_calc_coef_neq0 : forall (u:Unit), u <> 0 -> unit_calc_coef u <> 0.
Proof.
  intros u H. induction u; compute.
  - assert (n <> 0). { intros H1. rewrite H1 in H. destruct H. auto. } auto.
  - lra.
  - Search (Unit -> _). apply Rpower_neq0. apply IHu1. 2:{ apply IHu2.
     subst. elim H. destruct H.
   induction u1,u2; compute; try lra.
   Abort.

(* 准备用一些小的引理来逐步实现 *)
Lemma unit_coef_ucoef : forall r, unit_calc_coef (# r) = r.
Proof. compute. auto. Qed.

Lemma unit_coef_ukind : forall k, unit_calc_coef ($ k) = 1.
Proof. compute. auto. Qed.

Lemma unit_coef_uopp : forall u, 
  unit_calc_coef ( - u) = (- (unit_calc_coef u))%R.
Proof.
  induction u.
  - compute; field.
  - compute; field.
  - compute; field.
  - compute; field.
  - compute; field.
  - compute; field.
  - unfold unit_calc_coef. fold (unit_calc_coef).
    Abort.




