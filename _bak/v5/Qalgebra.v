(*
  purpose   : Arithmetic of Units.
  author    : Zhengpu Shi
  date      : 2022.04
  
  remark    :
  1. differences between arithmetic and algebra
  (1). arithmetic means add,sub,mul,div of numbers
  (2). algebra use numbers and variables sametime, and mainly use laws to 
    deal with the problem, not only calculate.
  (3). algebra include power, algorithm and complex numbers too.
  
  2. u1 +/- u2, only if dims(u1) == dims(u2)

*)

Require Export RExt.

Require Export Unit NUnit SI.


(** * Quantity *)


(** ** Definitions *)

Declare Scope Qu_scope.
Delimit Scope Qu_scope with Qu.
Open Scope Qu_scope.

(** A quantity is an option type that contains the unit type, and None means an 
  invalid quantity type. 
  For example, add with different unit type will invalid. *)
Definition Quantity : Set := option Unit.

Bind Scope Qu_scope with Quantity.

(** Get numerical value of a quantity *)
Definition Qval_opt (q : Quantity) : option R :=
  match q with
  | Some u => let (c,d) := u2n u in Some c
  | _ => None
  end.

Definition Qval (q : Quantity) (H : q <> None) : R.
Proof.
  destruct q; try easy. exact (let (c,d) := u2n u in c).
Defined.

(** Get dimension of a quantity *)
Definition Qdim_opt (q : Quantity) : option Dims :=
  match q with
  | Some u => let (c,d) := u2n u in Some d
  | _ => None
  end.

Definition Qdim (q : Quantity) (H : q <> None) : Dims.
Proof.
  destruct q; try easy. exact (let (c,d) := u2n u in d).
Defined.

(** Get unit of a quantity *)
Definition Qunit (q : Quantity) (H : q <> None) : Unit.
Proof.
  destruct q; try easy.
Defined.


(** ** Properties *)

(** Qunit is equal to a unit created by n2u with Qval and Qdim. *)
Lemma Qunit_eq_Qval_Qdim (q : Quantity) (H : q <> None) : 
  Qunit q H == n2u (Qval q H, Qdim q H).
Proof.
  destruct q; try easy. unfold Qval, Qdim, Qunit.
  destruct (u2n u) eqn:E1. unfold Ueq. rewrite u2n_n2u. auto.
Qed.


(** * Equality of dimensions of two quantities *)

(** Definitions *)

Definition Qdimeq (q1 q2 : Quantity) : Prop :=
  match q1, q2 with
  | Some u1, Some u2 =>
    let (c1,d1) := u2n u1 in
    let (c2,d2) := u2n u2 in
      d1 = d2
  | _, _ => False
  end.


(** ** Properties *)



(** * Comparison of two quantities *)


(** Definitions *)

(** Boolean comparison of two quantities *)
Definition Qcmpb (q1 q2 : Quantity) (Rcmpb : R -> R -> bool) : bool :=
  match q1,q2 with
  | Some u1, Some u2 =>
    let '(c1, d1) := u2n u1 in
    let '(c2, d2) := u2n u2 in
      if (Dims_eqb d1 d2)
      then (Rcmpb c1 c2)
      else false
  | _, _ => false
  end.

(** Equal,Less Than, Less Equal of two quantities *)
Definition Qeqb (q1 q2 : Quantity) : bool := Qcmpb q1 q2 Reqb.
Definition Qltb (q1 q2 : Quantity) : bool := Qcmpb q1 q2 Rltb.
Definition Qleb (q1 q2 : Quantity) : bool := Qcmpb q1 q2 Rleb.

Infix "=?"  := Qeqb : Qu_scope.
Infix "<?"  := Qltb : Qu_scope.
Infix "<=?" := Qleb : Qu_scope.

(** Proposition comparison of two quantities *)
Definition Qeq (q1 q2 : Quantity) : Prop := q1 =? q2 = true.
Definition Qlt (q1 q2 : Quantity) : Prop := q1 <? q2 = true.
Definition Qle (q1 q2 : Quantity) : Prop := q1 <=? q2 = true.

Infix "==" := Qeq : Qu_scope.
Infix "<" := Qlt : Qu_scope.
Infix "<=" := Qle : Qu_scope.


(** ** Properties *)

(** Qeqb got true, iff coefficient and dimensions are equal *)
Lemma Qeqb_true_iff u1 u2 :
    (Some u1 =? Some u2 = true) <->
    let (r1,d1) := u2n u1 in
    let (r2,d2) := u2n u2 in
      (r1 =? r2)%R && (Dims_eqb d1 d2) = true.
Proof.
  unfold Qeqb,Qcmpb.
  split; intros; destruct (u2n u1) eqn:E1,(u2n u2) eqn:E2.
  - destruct (Dims_eqb d d0). rewrite H; auto. easy.
  - apply andb_true_iff in H. destruct H.
    rewrite H, H0. auto.
Qed.

(** Qeqb is reflexive *)
Lemma Qeqb_refl q : (q <> None) -> q =? q = true.
Proof.
  intros. unfold Qeqb,Qcmpb. destruct q; auto.
  destruct (u2n u). rewrite Dims_eqb_refl. rewrite Reqb_refl. auto.
Qed.

(** Qeqb is commutative *)
Lemma Qeqb_comm q1 q2 : (q1 =? q2) = (q2 =? q1).
Proof.
  unfold Qeqb,Qcmpb. destruct q1,q2; auto.
  destruct (u2n u),(u2n u0).
  destruct (Dims_eqb d d0) eqn : E1.
  - rewrite Dims_eqb_comm in E1; rewrite E1. rewrite Reqb_comm; auto.
  - rewrite Dims_eqb_comm in E1; rewrite E1. auto.
Qed.

(** Qeqb is transitive *)
Lemma Qeqb_trans q1 q2 q3 : (q1 =? q2 = true) -> (q2 =? q3 = true) ->
  (q1 =? q3 = true).
Proof.
  intros. destruct q1,q2,q3; auto; try easy.
  unfold Qeqb,Qcmpb in *.
  destruct (u2n u),(u2n u0),(u2n u1).
  destruct (Dims_eqb d d0) eqn:E1, (Dims_eqb d0 d1) eqn:E2; try easy.
  rewrite (Dims_eqb_trans d d0 d1); auto.
  rewrite (Reqb_trans r r0 r1); auto.
Qed.

(** Qeq is reflexive *)
Lemma Qeq_refl q : (q <> None) -> q == q.
Proof.
  unfold Qeq. apply Qeqb_refl.
Qed.

(** Qeq is commutative *)
Lemma Qeq_comm q1 q2 : q1 == q2 -> q2 == q1.
Proof.
  unfold Qeq. rewrite Qeqb_comm. auto.
Qed.

(** Qeq is transitive *)
Lemma Qeq_trans q1 q2 q3 : q1 == q2 -> q2 == q3 -> q1 == q3.
Proof.
  unfold Qeq. apply (Qeqb_trans q1 q2 q3).
Qed.

(** Equality of two quantities, iff Qunit of them are equal *)
Lemma Qeq_iff_Qunit_eq (q1 q2 : Quantity) (H1 : q1 <> None) (H2 : q2 <> None) :
  q1 == q2 <-> (Qunit q1 H1 == Qunit q2 H2)%U.
Proof.
  destruct q1,q2; try easy.
  unfold Qeq,Qeqb,Qcmpb,Qunit,Ueq.
  destruct (u2n u) eqn:E1, (u2n u0) eqn:E2.
  split; intros.
  - destruct (Dims_eqb d d0) eqn:E3; try easy.
    apply Reqb_true_iff in H; apply Dims_eqb_true_iff in E3. subst; auto.
  - inversion H.
    rewrite Reqb_refl, Dims_eqb_refl. auto.
Qed.



(** * Quantity Arithmetic Operations *)

(** ** Definitions *)

(** Quantity addition *)
Definition Qplus (q1 q2 : Quantity) : Quantity :=
  match q1,q2 with
  | Some u1, Some u2 =>
    let '(c1, d1) := u2n u1 in
    let '(c2, d2) := u2n u2 in
      if (Dims_eqb d1 d2)
      then Some (n2u (Rplus c1 c2, d1))
      else None
  | _, _ => None
  end.

(* (** Test examples *)
Example Qplus_ex1 : Qplus (Some ($1*'min)) (Some ($30*'s)) = Some ($90*'s).
Proof. compute. f_equal. f_equal. f_equal. field. Qed. *)

(** Quantity opposition *)
Definition Qopp (q : Quantity) : Quantity :=
  match q with
  | Some u =>
    let '(c, d) := u2n u in Some (n2u (Ropp c, d))
  | _ => None
  end.

(** Quantity substraction *)
Definition Qsub (q1 q2 : Quantity) : Quantity := Qplus q1 (Qopp q2).

(** Quantity multiplication *)
Definition Qmult (q1 q2 : Quantity) : Quantity :=
  match q1,q2 with
  | Some u1, Some u2 =>
    let '(c1, d1) := u2n u1 in
    let '(c2, d2) := u2n u2 in
      Some (n2u (Rmult c1 c2, Dims_plus d1 d2))
  | _, _ => None
  end.

(** Quantity inversion *)
Definition Qinv (q : Quantity) : Quantity :=
  match q with
  | Some u =>
    let '(c, d) := u2n u in Some (n2u (Rinv c, Dims_opp d))
  | _ => None
  end.

(** Quantity division *)
Definition Qdiv (q1 q2 : Quantity) : Quantity := Qmult q1 (Qinv q2).

(** Symbols *)
Notation "- q" := (Qopp q) : Qu_scope.
Notation "/ q" := (Qinv q) : Qu_scope.
Infix "+" := Qplus : Qu_scope.
Infix "-" := Qsub : Qu_scope.
Infix "*" := Qmult : Qu_scope.
Infix "/" := Qdiv : Qu_scope.


(** ** Tactic for solving equality of quantities *)

(** Solve Q1 == Q2 *)
Ltac pfqeq :=
  compute;
  destruct Req_EM_T as [H1|H2]; auto;
  destruct H2; field.


(** ** Arithmetic Examples *)

(* direct compare *)
Goal Some ($1000 * 'g)%U == Some ($1 * 'kg)%U.
Proof. pfqeq. Qed.

(* plus with same Unit *)
Goal Some ($3 * 's)%U + Some ($2 * 's)%U == Some ($1*'s)%U + Some ($4*'s)%U.
Proof. pfqeq. Qed.

(* plus with different Unit *)
Goal Some ($10*'s)%U + Some ($1*'min)%U == Some ($70*'s)%U.
Proof. pfqeq. Qed.

Goal Some ($3*'kg)%U + Some ($1000*'g)%U == Some ($4*'kg)%U.
Proof. pfqeq. Qed.

(* opposition *)
Goal - (Some ($3*'min)%U) == Some ($(-180)%R*'s)%U.
Proof. pfqeq. Qed.

(* multiply with different Unit *)
Goal Some ($3*'km)%U * Some ($2*'s)%U == Some ($6000*('m*'s))%U.
Proof. pfqeq. Qed.

(* inversion *)
Goal / (Some ($3*'min)%U) == Some ($(1/180)%R*'Hz)%U.
Proof. pfqeq. Qed.

(* divide with different Unit *)
Goal Some ($6000*('m*'s))%U / Some ($3*'m)%U == Some ($2000*'s)%U.
Proof. pfqeq. Qed.


(** ** Properties *)

(** Qplus is commutative *)
Lemma Qplus_comm (q1 q2 : Quantity) :
  Qdimeq q1 q2 -> q1 + q2 == q2 + q1.
Proof.
  unfold Qeq, Qplus, Qdimeq.
  destruct q1,q2; try easy.
  destruct (u2n u) eqn:E1, (u2n u0) eqn:E2.
  intros H; rewrite H.
  repeat rewrite ?Dims_eqb_refl,?u2n_n2u.
  apply Qeqb_true_iff. repeat rewrite u2n_n2u.
  apply andb_true_intro; split.
  apply Reqb_true_iff; ring. rewrite Dims_eqb_refl; auto.
Qed.

(** Qplus is associative *)
Lemma Qplus_assoc (q1 q2 q3 : Quantity) :
  Qdimeq q1 q2 -> Qdimeq q2 q3 -> 
  (q1 + q2) + q3 == q1 + (q2 + q3).
Proof.
  unfold Qeq, Qplus, Qdimeq.
  destruct q1,q2,q3; try easy.
  destruct (u2n u) eqn:E1, (u2n u0) eqn:E2, (u2n u1) eqn:E3.
  intros H1 H2; rewrite H1,H2.
  repeat rewrite ?Dims_eqb_refl,?u2n_n2u.
  apply Qeqb_true_iff. repeat rewrite u2n_n2u.
  apply andb_true_intro; split.
  apply Reqb_true_iff; ring. rewrite Dims_eqb_refl; auto.
Qed.
  
(** Qmult is commutative *)
Lemma Qmult_comm (q1 q2 : Quantity) :
  q1 <> None -> q2 <> None ->
  q1 * q2 == q2 * q1.
Proof.
  intros HQ1 HQ2.
  unfold Qeq, Qmult, Qdimeq.
  destruct q1,q2; try easy.
  destruct (u2n u) eqn:E1, (u2n u0) eqn:E2.
  apply Qeqb_true_iff. repeat rewrite u2n_n2u.
  apply andb_true_intro; split.
  apply Reqb_true_iff; ring.
  rewrite Dims_plus_comm. apply Dims_eqb_refl.
Qed.

(** Qplus is Qmult *)
Lemma Qmult_assoc (q1 q2 q3 : Quantity) :
  Qdimeq q1 q2 -> Qdimeq q2 q3 -> 
  (q1 * q2) * q3 == q1 * (q2 * q3).
Proof.
  unfold Qeq, Qmult, Qdimeq.
  destruct q1,q2,q3; try easy.
  destruct (u2n u) eqn:E1, (u2n u0) eqn:E2, (u2n u1) eqn:E3.
  intros H1 H2; rewrite H1,H2.
  repeat rewrite ?Dims_eqb_refl,?u2n_n2u.
  apply Qeqb_true_iff. repeat rewrite u2n_n2u.
  apply andb_true_intro; split.
  apply Reqb_true_iff; ring.
  rewrite Dims_plus_assoc. rewrite Dims_eqb_refl; auto.
Qed.



(** * Complex operations of quantities *)


(** ** Definitions *)

(** Power of quantity with natural numbers *)
Definition Qpow (q : Quantity) (n : nat) : Quantity :=
  match q with
  | Some u => Some (Upow u n)
  | None => None
  end.

(** Symbos for Qpow *)
Notation " q ² " := (Qpow q 2) (at level 1) : Qu_scope.
Notation " q ³ " := (Qpow q 3) (at level 1) : Qu_scope.
Notation " q ⁴ " := (Qpow q 4) (at level 1) : Qu_scope.
Notation " q ⁵ " := (Qpow q 5) (at level 1) : Qu_scope.
Notation "q ^ n" := (Qpow q n) : Qu_scope.

(** General unary operation of a quantity which won't change it's unit *)
Definition Qop1 (q : Quantity) (f : R -> R) : Quantity :=
  match q with
  | Some u =>
    let '(c, d) := u2n u in Some (n2u (f c, d))
  | _ => None
  end.

(** Several unary operations of quantity *)
Definition Qsin q := Qop1 q sin.
Definition Qcos q := Qop1 q cos.
Definition Qtan q := Qop1 q tan.
Definition Qatan q := Qop1 q atan.
Definition Qacos q := Qop1 q acos.
Definition Qsqrt q := Qop1 q sqrt.


(** Examples *)

(* Check Qsin (Some ($1*'m)%U).
Compute ((Some ($1*'m)%U) ^ 5). *)

Goal ((Some ($1*'m)%U) ^ 5) == Some ($1*'m⁵)%U.
Proof. pfqeq. Qed.

