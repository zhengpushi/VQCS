(*
  purpose   : auxiliary library for Z.
  author    : Zhengpu SHI
  date      : 2022.04
*)

Require Export ZArith.

Open Scope Z.


(** Boolean equality of Zadd satisfy right cancelling rule *)
Lemma Zadd_eqb_cancel_r : forall (z1 z2 a : Z),
  (z1 + a =? z2 + a)%Z = (z1 =? z2)%Z.
Proof.
  intros.
  remember (z1 =? z2)%Z as b1 eqn : H1.
  remember (z1 + a =? z2 + a)%Z as b2 eqn : H2.
  destruct b1,b2; auto.
  - apply eq_sym in H1,H2. apply Z.eqb_eq in H1. apply Z.eqb_neq in H2.
    subst. auto.
  - apply eq_sym in H1,H2. apply Z.eqb_neq in H1. apply Z.eqb_eq in H2.
    apply Z.add_cancel_r in H2. apply H1 in H2. easy.
Qed.

