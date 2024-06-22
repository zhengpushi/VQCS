(*
  purpose   : Derivative of quantity (experimental).
  author    : ZhengPu Shi
  date      : 2022.04

*)

From MyStdLibExt Require Export RExt.

Require Export Qalgebra.


(** * Quantity上的微积分 *)

Declare Scope Qfun_scope.
Delimit Scope Qfun_scope with Qfun.
Open Scope Qfun_scope.

Definition Qfun := option Quantity -> option Quantity.

(** 函数的算术运算 *)

Definition Qfadd (f g : Qfun) t := f t + g t.
Definition Qfsub (f g : Qfun) t := f t - g t.
Definition Qfmul (f g : Qfun) t := f t * g t.
Definition Qfdiv (f g : Qfun) t := f t / g t.
Definition Qfcnst (f : Qfun) c t := c * (f t).

Infix "+" := Qfadd : Qfun_scope.
Infix "-" := Qfsub : Qfun_scope.
Infix "*" := Qfmul : Qfun_scope.
Infix "/" := Qfdiv : Qfun_scope.
Infix "*c" := Qfcnst (at level 40, left associativity) : Qfun_scope.

Check Qfadd Qsin Qopp (Some (3,'m)).
Compute Qfadd Qopp Qopp (Some (3,'m)).

(** 函数算术运算的合法性 *)
Lemma Qfadd_ok : forall (f g : Qfun) t, (f + g) t = (f t + g t)%q.
Proof. intros. auto. Qed.

(** 函数加乘运算的结合律和交换律 *)

(* f + g = g + f *)
Lemma Qfadd_comm : forall (f g : Qfun), f + g = g + f.
Proof. 
  intros. apply functional_extensionality. intros.
  repeat rewrite Qfadd_ok.
  rewrite Qadd_comm. auto.
Qed.

(* (f + g) + h = f + (g + h)  *)
Lemma Qfadd_assoc : forall (f g h : Qfun), (f + g) + h = f + (g + h).
Proof. 
  intros. apply functional_extensionality. intros.
  repeat rewrite Qfadd_ok.
  rewrite Qadd_assoc. auto.
Qed.












