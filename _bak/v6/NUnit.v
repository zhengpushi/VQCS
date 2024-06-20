(*
  purpose   : Normalized Unit, semantics of unit.
  author    : Zhengpu Shi
  date      : 2021.05
  
  reference :
  1. https://en.wikipedia.org/wiki/Dimensional_analysis
  
  remark    :
  1. Dimension & dimension exponent.
    every Unit could be represented with 7 dimension exponent,
    for example, A = L^a * M^b * T^c ...
    these units are called coherent units. But there are some units are not 
    coherent, like minute, it need a coefficient, i.e., 1min = 60s.
  2. How to unify these two different types of units?
    we use a coefficient and dimensions (7 corresponding dimension) of a Unit 
    to be considered as the semantics of the unit.
  3. What are dimensions used for?
    (a). an intermediary when converting two different units
    (b). to verify an equation by checking left and right has same dimensions.
    (c). to find relation between physical quantity.
      for example, if we know a quantity X is related to Length and Time, but 
      we don't know how, then an assumption equation X = L^a * T^b could be 
      used to find the real relation after lots of experiments and guessed the 
      suitable dimension exponent a and b.
  4. Dimension rule
    two quantity could be compare or plus or subtract only when they have 
    same dimensions.
*)


Require Export BoolExt ZExt. 
Require Export Unit. 


(** * Dimensions: coefficients that show how a unit is made up of basic units. 
*)

(** ** Difinition of dimensions *)

(** A tuple of 7 integers which each one means the dimension of a [BasicUnit]. 
*)
Definition Dims := (Z * Z * Z * Z * Z * Z * Z)%type.

(** Zero dimensions, means a pure number value. *)
Definition Dims_zero : Dims := (0,0,0,0,0,0,0)%Z.

(** Equality of Dims is decidable.  *)
Lemma Dims_eq_dec : forall (da db : Dims), {da = db} + {da <> db}.
Proof.
  intros da db.
  destruct da as [[[[[[a1 a2] a3] a4] a5] a6] a7].
  destruct db as [[[[[[b1 b2] b3] b4] b5] b6] b7].
  destruct (Z.eq_dec a1 b1); [idtac | right; intros H; inversion H; auto].
  destruct (Z.eq_dec a2 b2); [idtac | right; intros H; inversion H; auto].
  destruct (Z.eq_dec a3 b3); [idtac | right; intros H; inversion H; auto].
  destruct (Z.eq_dec a4 b4); [idtac | right; intros H; inversion H; auto].
  destruct (Z.eq_dec a5 b5); [idtac | right; intros H; inversion H; auto].
  destruct (Z.eq_dec a6 b6); [idtac | right; intros H; inversion H; auto].
  destruct (Z.eq_dec a7 b7); [idtac | right; intros H; inversion H; auto].
  subst; auto.
Qed.

(** Inequality of Dims, iff at least one of the dimension is not equal. *)
Lemma Dims_neq_iff : forall (da db : Dims),
  da <> db <->
  let '(a1,a2,a3,a4,a5,a6,a7) := da in
  let '(b1,b2,b3,b4,b5,b6,b7) := db in
    (a1 <> b1) \/ (a2 <> b2) \/ (a3 <> b3) \/ (a4 <> b4) \/
    (a5 <> b5) \/ (a6 <> b6) \/ (a7 <> b7).
Proof.
  intros da db.
  destruct da as [[[[[[a1 a2] a3] a4] a5] a6] a7].
  destruct db as [[[[[[b1 b2] b3] b4] b5] b6] b7].
  split; intros H.
  - assert (not (a1 = b1 /\ a2 = b2 /\ a3 = b3 /\ 
    a4 = b4 /\ a5 = b5 /\ a6 = b6 /\ a7 = b7)); try tauto.
    intros H1. repeat (destruct H1 as [?H H1]; subst).
    destruct H. auto.
  - intros H1; inversion H1. subst. repeat destruct H; auto.
Qed.



(** ** Boolean equality of [Dims] *)

(** Boolean equality of [Dims] is defined as the equality of each component. *)
Definition Dims_eqb (da db : Dims) : bool :=
  let '(a1,a2,a3,a4,a5,a6,a7) := da in
  let '(b1,b2,b3,b4,b5,b6,b7) := db in
    Z.eqb a1 b1 
    && Z.eqb a2 b2 
    && Z.eqb a3 b3 
    && Z.eqb a4 b4 
    && Z.eqb a5 b5 
    && Z.eqb a6 b6 
    && Z.eqb a7 b7.

(** [Dims_eqb] is true, iff propositonal equal. *)
Lemma Dims_eqb_true_iff (da db : Dims) : Dims_eqb da db = true <-> da = db.
Proof.
  repeat destruct da as [da ?].
  repeat destruct db as [db ?].
  unfold Dims_eqb. split; intros H.
  - repeat (rewrite Bool.andb_true_iff in H; destruct H as [H H1]; 
    apply Z.eqb_eq in H1; subst). apply Z.eqb_eq in H; subst. auto.
  - inversion H. subst. rewrite ?Bool.andb_true_iff. 
    repeat split; try rewrite Z.eqb_eq; auto.
Qed.


(** [Dims_eqb] is false, iff propositonal not equal. *)
Lemma Dims_eqb_false_iff (da db : Dims) : 
  Dims_eqb da db = false <-> da <> db.
Proof.
  split; intros H.
  - intros H1. apply Dims_eqb_true_iff in H1. rewrite H in H1. lra.
  - repeat destruct da as [da ?].
    repeat destruct db as [db ?].
    apply Dims_neq_iff in H. unfold Dims_eqb.
    repeat (destruct H; try (apply Z.eqb_neq in H; rewrite H; 
      rewrite ?andb_false_l,?andb_false_r; auto)).
Qed.

(** [Dims_eqb] is true, it is reflexive. *)
Lemma Dims_eqb_true_refl (d : Dims) : Dims_eqb d d = true.
Proof.
  destruct (Dims_eqb d d) eqn:E1; auto.
  apply Dims_eqb_false_iff in E1; easy.
Qed.

(** [Dims_eqb] is commutative. *)
Lemma Dims_eqb_comm (da db : Dims) : Dims_eqb da db = Dims_eqb db da.
Proof.
  destruct (Dims_eqb da db) eqn:E1, (Dims_eqb db da) eqn:E2; auto.
  - apply Dims_eqb_true_iff in E1; apply Dims_eqb_false_iff in E2. subst;easy.
  - apply Dims_eqb_true_iff in E2; apply Dims_eqb_false_iff in E1. subst;easy.
Qed.

(** [Dims_eqb] is true, it is transitive. *)
Lemma Dims_eqb_true_trans (da db dc : Dims) : Dims_eqb da db = true ->
  Dims_eqb db dc = true -> Dims_eqb da dc = true.
Proof.
  intros.
  destruct (Dims_eqb da db) eqn:E1, (Dims_eqb db dc) eqn:E2, 
    (Dims_eqb da dc) eqn:E3; auto.
  apply Dims_eqb_true_iff in E1,E2; apply Dims_eqb_false_iff in E3. subst;easy.
Qed.



(** ** Addition of [Dims] *)

(** Addition of [Dims] is defined as the addition of each component. *)
Definition Dims_plus (da db : Dims) : Dims :=
  let '(a1,a2,a3,a4,a5,a6,a7) := da in
  let '(b1,b2,b3,b4,b5,b6,b7) := db in
    (a1 + b1, a2 + b2, a3 + b3, a4 + b4, a5 + b5, a6 + b6, a7 + b7)%Z.

(** [Dims_plus] is commutative. *)
Lemma Dims_plus_comm : forall (da db : Dims),
  Dims_plus da db = Dims_plus db da.
Proof.
  intros.
  destruct da as [[[[[[a1 a2] a3] a4] a5] a6] a7].
  destruct db as [[[[[[b1 b2] b3] b4] b5] b6] b7].
  simpl. repeat (f_equal; try ring).
Qed.

(** [Dims_plus] is associative. *)
Lemma Dims_plus_assoc : forall (da db dc : Dims),
  Dims_plus (Dims_plus da db) dc = Dims_plus da (Dims_plus db dc).
Proof.
  intros.
  destruct da as [[[[[[a1 a2] a3] a4] a5] a6] a7].
  destruct db as [[[[[[b1 b2] b3] b4] b5] b6] b7].
  destruct dc as [[[[[[c1 c2] c3] c4] c5] c6] c7].
  simpl. repeat (f_equal; try ring).
Qed.

Lemma Dims_plus_0_l : forall d, Dims_plus Dims_zero d = d.
Proof.
  intros.
  destruct d as [[[[[[a1 a2] a3] a4] a5] a6] a7].
  simpl. repeat (f_equal; try ring).
Qed.

Lemma Dims_plus_0_r : forall d, Dims_plus d Dims_zero = d.
Proof.
  intros. rewrite Dims_plus_comm. apply Dims_plus_0_l.
Qed.



(** ** Negation of a [Dims] *)

(** Negation of a [Dims] is defined as the negation of each component. *)
Definition Dims_opp (da : Dims) : Dims :=
  let '(a1,a2,a3,a4,a5,a6,a7) := da in
    (-a1, -a2, -a3, -a4, -a5, -a6, -a7)%Z.

Lemma Dims_plus_opp_r (d : Dims) : Dims_plus d (Dims_opp d) = Dims_zero.
Proof.
  destruct d as [[[[[[a1 a2] a3] a4] a5] a6] a7].
  unfold Dims_plus,Dims_opp,Dims_zero.
  repeat f_equal; try ring.
Qed.



(** ** Subtraction of [Dims] *)

(** A - B is defined as the A + (-B) *)
Definition Dims_sub (da db : Dims) : Dims :=
  Dims_plus da (Dims_opp db).



(** ** Scale multiplication of [Dims] *)
Definition Dims_cmul (z : Z) (d : Dims) : Dims :=
  let '(a1,a2,a3,a4,a5,a6,a7) := d in
    (z*a1, z*a2, z*a3, z*a4, z*a5, z*a6, z*a7)%Z.



(** ** Square root of a [Dims] *)

(** Check that if a dimensions can be sqrt. *)
Definition Dims_sqrt_cond (d : Dims) : bool :=
  let '(a1,a2,a3,a4,a5,a6,a7) := d in
    ((Z.even a1) && (Z.even a2) && (Z.even a3) && (Z.even a4) && 
    (Z.even a5) && (Z.even a6) && (Z.even a7)).

(** Square root of a [Dims] is valid only when each dimension is an even 
  number. *)
Definition Dims_sqrt (da : Dims) : option Dims :=
  if Dims_sqrt_cond (da) then
    let '(a1,a2,a3,a4,a5,a6,a7) := da in
      Some (a1/2, a2/2, a3/2, a4/2, a5/2, a6/2, a7/2)%Z
  else None.

Lemma Dims_sqrt_cond_imply_Dims_sqrt_not_None d : 
  Dims_sqrt_cond d = true -> Dims_sqrt d <> None.
Proof.
  destruct d as [[[[[[a1 a2] a3] a4] a5] a6] a7].
  unfold Dims_sqrt. intros H; rewrite H. easy.
Qed.

Lemma Dims_sqrt_Dims_cmul_2 d : 
  Dims_sqrt (Dims_cmul 2 d) = Some d.
Proof.
  destruct d as [[[[[[a1 a2] a3] a4] a5] a6] a7].
  unfold Dims_sqrt. unfold Dims_sqrt_cond, Dims_cmul.
  assert (forall (z : Z), Z.even (2 * z) = true).
  { intros. induction z; auto. }
  repeat rewrite H.
(*   simpl. *)
  lazy [andb]. (* simpl will expand more, let's control. *)
  assert (forall z, 2 * z / 2 = z)%Z.
  { intros. rewrite Z.mul_comm. apply Z_div_mult. auto with zarith. }
  repeat rewrite H0. auto.
Qed.



(** * Normalized unit: the semantics of a Unit *)


(** ** Definitions of normalized unit *)

(** A normalized unit is a pair of a coefficient and a dimensions. *) 
Definition NUnit : Set := R * Dims.

(** NUnit equal, iff coefficient and dimensions both equal. *)
Lemma NUnit_eq_iff : forall (na nb : NUnit),
  na = nb <->
  let '(ca, da) := na in
  let '(cb, db) := nb in
    (ca = cb) /\ (da = db).
Proof.
  intros.
  destruct na as [ca da], nb as [cb db]. split; intro H;
  inversion H; subst; easy.
Qed.

(** NUnit not equal, iff coefficient or dimensions not equal. *)
Lemma NUnit_neq_iff : forall (na nb : NUnit),
  na <> nb <->
  let '(ca, da) := na in
  let '(cb, db) := nb in
    (ca <> cb) \/ (da <> db).
Proof.
  intros.
  destruct na as [ca da], nb as [cb db]. split; intros H.
  - assert (not (ca = cb /\ da = db)); try tauto.
    intros H1. destruct H1; subst. destruct H; auto.
  - intros H1; inversion H1; clear H1; auto. subst.
    destruct H; auto.
Qed.



(** ** Boolean Equality of NUnit *)

(** Boolean equality of NUnit is defined as the [andb] of two corresponding 
  equality. *)
Definition NUeqb (na nb : NUnit) : bool :=
  let '(ca, da) := na in
  let '(cb, db) := nb in
     (ca =? cb)%R && Dims_eqb da db.

(** [NUeqb] is true, it is reflexive *)
Lemma NUeqb_true_refl : forall u, NUeqb u u = true.
Proof.
  destruct u. simpl. rewrite andb_true_intro; auto.
  rewrite Reqb_true_refl, Dims_eqb_true_iff. easy.
Qed.

(** [NUeqb] is commutative. *)
Lemma NUeqb_comm : forall na nb, NUeqb na nb = NUeqb nb na.
Proof.
  intros. destruct na, nb. simpl.
  rewrite Reqb_comm. rewrite Dims_eqb_comm. auto.
Qed.

(** [NUeqb] is true, it is transitive *)
Lemma NUeqb_true_trans : forall na nb nc, NUeqb na nb = true ->
  NUeqb nb nc = true -> NUeqb na nc = true.
Proof.
  intros. destruct na,nb,nc. simpl in *.
  apply andb_true_iff. apply andb_true_iff in H,H0.
  rewrite Reqb_true_iff, Dims_eqb_true_iff in *.
  destruct H,H0; subst; easy.
Qed.

(** [NUeqb] is true, iff propositonal equal. *)
Lemma NUeqb_true_iff : forall (na nb : NUnit), 
  NUeqb na nb = true <-> na = nb.
Proof.
  destruct na,nb; simpl.
  rewrite andb_true_iff.
  rewrite Reqb_true_iff, Dims_eqb_true_iff.
  split; intro H; inversion H; subst; auto.
Qed.

(** [NUeqb] is false, iff propositonal not equal *)
Lemma NUeqb_false_iff : forall na nb, 
  NUeqb na nb = false <-> na <> nb.
Proof.
  intros na nb. split; intros.
  - intro H1. apply NUeqb_true_iff in H1. rewrite H in H1. easy.
  - assert (~(NUeqb na nb = true)).
    + intro H1. apply NUeqb_true_iff in H1. easy.
    + apply not_true_is_false; auto.
Qed.


(** ** NUnit equality is decidable *)

Lemma NUnit_eq_dec (na nb : NUnit) : {na = nb} + {na <> nb}.
Proof.
  destruct (NUeqb na nb) eqn : E1.
  - left. apply NUeqb_true_iff in E1. auto.
  - right. apply NUeqb_false_iff in E1. auto.
Qed.



(** ** Convert from [Unit] to [NUnit]. *)

Definition u2n (u : Unit) : NUnit :=
  let coef := Ugetcoef u in
  let ds := Ugetdim u BUTime in
  let dm := Ugetdim u BULength in
  let dkg := Ugetdim u BUMass in
  let dA := Ugetdim u BUElectricCurrent in
  let dK := Ugetdim u BUThermodynamicTemperature in
  let dmol := Ugetdim u BUAmountOfSubstance in
  let dcd := Ugetdim u BULuminousIntensity in
    (coef, (ds,dm,dkg,dA,dK,dmol,dcd)).

(* examples *)
(* Compute u2n (m * 1 * s * s).
Compute u2n N.
Compute u2n N'.
Compute NUeqb (u2n(1 * m * s)) (u2n (s * m * 1)). *)


(** u2n of $r. *)
Lemma u2n_Unone r : u2n $r = (r, Dims_zero).
Proof. compute. auto. Qed.

(* (** u2n of [b]. *)
Lemma u2n_Ub b : u2n [b] = (1, ?).
Proof. compute. auto. Qed. *)

(** Coefficient of u is the coefficient of [u2n u]. *)
Lemma Ugetcoef_u2n : forall u coef dims,
  (coef, dims) = u2n u -> Ugetcoef u = coef.
Proof.
  induction u; intros; simpl in *;
  unfold u2n in H; inversion H; auto.
Qed.

(** A rewriting of [u2n] [Umul]. *)
Lemma u2n_Umul_rew (u1 u2 : Unit) : u2n (u1 * u2) =
  let (c1,d1) := u2n u1 in
  let (c2,d2) := u2n u2 in
    ((c1*c2)%R, Dims_plus d1 d2).
Proof.
  apply NUnit_eq_iff. simpl. split; auto.
Qed.

(** [u2n] is compatible for [Umul] left. *)
Lemma u2n_Umul_l u1 u2 u : u2n u1 = u2n u2 ->
  u2n (u1 * u) = u2n (u2 * u).
Proof.
  intros. rewrite ?u2n_Umul_rew.
  destruct (u2n u1), (u2n u2), (u2n u). inversion H. auto.
Qed.

(** [u2n] is compatible for [Umul] right. *)
Lemma u2n_Umul_elim_r u1 u2 u : u2n u1 = u2n u2 ->
  u2n (u * u1) = u2n (u * u2).
Proof.
  intros. rewrite ?u2n_Umul_rew.
  destruct (u2n u1), (u2n u2), (u2n u). inversion H. auto.
Qed.

(** [u2n] is compatible for [Umul]. *)
Lemma u2n_Umul u1a u1b u2a u2b : u2n u1a = u2n u2a -> 
  u2n u1b = u2n u2b -> u2n (u1a * u1b) = u2n (u2a * u2b).
Proof.
  intros. rewrite ?u2n_Umul_rew.
  destruct (u2n u1a), (u2n u1b), (u2n u2a), (u2n u2b). 
  inversion H. inversion H0. auto.
Qed.

(** A rewriting of [u2n] [Uinv]. *)
Lemma u2n_Uinv_rew u1 : u2n (/u1) =
  let (c1,d1) := u2n u1 in
    ((/c1)%R, Dims_opp d1).
Proof.
  apply NUnit_eq_iff. simpl. split; auto.
Qed.

(** [u2n] is compatible for [Uinv]. *)
Lemma u2n_Uinv u1 u2 : u2n u1 = u2n u2 -> u2n (/u1) = u2n (/u2).
Proof.
  intros. rewrite ?u2n_Uinv_rew.
  destruct (u2n u1), (u2n u2). 
  inversion H. auto.
Qed.

(** [u2n] is compatible for [Upown]. *)
Lemma u2n_Upown u1 u2 n : u2n u1 = u2n u2 -> u2n (Upown u1 n) = u2n (Upown u2 n).
Proof.
  intros. induction n; auto. simpl. destruct n; auto.
  apply u2n_Umul; auto.
Qed.

(** [u2n] is compatible for [Upow]. *)
Lemma u2n_Upow u1 u2 n : u2n u1 = u2n u2 -> u2n (u1 ^ n) = u2n (u2 ^ n).
Proof.
  intros. unfold Upow. destruct n; auto.
  apply u2n_Upown; auto.
  apply u2n_Uinv.
  apply u2n_Upown; auto.
Qed.

(** A rewriting of [Ugetcoef] [Upown]. *)
Lemma Ugetcoef_Upown u n c d : u2n u = (c, d) -> 
  Ugetcoef (Upown u n) = pow c n.
Proof.
  intros. induction n; auto.
  assert (Ugetcoef u = c). { apply (Ugetcoef_u2n _ _ d); auto. }
  simpl. destruct n.
  - autorewrite with R; auto.
  - rewrite Ugetcoef_Umul. rewrite H0,IHn. auto.
Qed.

(** A rewriting of [Ugetcoef] [Upow]. *)
Lemma Ugetcoef_Upow u z c d : u2n u = (c, d) -> 
  Ugetcoef (u ^ z) = powerRZ c z.
Proof.
  intros. unfold Upow. unfold powerRZ. destruct z; auto.
  - rewrite (Ugetcoef_Upown u _ c d); auto.
  - rewrite Ugetcoef_Uinv.
    rewrite (Ugetcoef_Upown u _ c d); auto.
Qed.

(** Dimension of [n2u n] is the dimension of the n. *)
Lemma Ugetdim_u2n : forall u coef ds dm dkg dA dK dmol dcd,
  u2n u = (coef, (ds,dm,dkg,dA,dK,dmol,dcd)) ->
  Ugetdim u BUTime = ds /\
  Ugetdim u BULength = dm /\
  Ugetdim u BUMass = dkg /\
  Ugetdim u BUElectricCurrent = dA /\
  Ugetdim u BUThermodynamicTemperature = dK /\
  Ugetdim u BUAmountOfSubstance = dmol /\
  Ugetdim u BULuminousIntensity = dcd.
Proof.
  intros. inversion H. repeat split; auto.
Qed.

(** A rewriting of [u2n] [upow]. *)
Lemma u2n_Upow_rew u z c d : u2n u = (c,d) -> 
  u2n (u ^ z) = (powerRZ c z, Dims_cmul z d).
Proof.
  intros. apply NUnit_eq_iff. destruct (u2n u) eqn: E1.
  inversion H. split; auto.
  - apply (Ugetcoef_Upow _ _ _ d). rewrite E1; auto.
  - unfold Dims_cmul.
    destruct d as [[[[[[a1 a2] a3] a4] a5] a6] a7].
    rewrite H in E1.
    apply (Ugetdim_u2n u c a1 a2 a3 a4 a5 a6 a7) in E1; auto.
    do 6 destruct E1 as [? E1]. do 6 f_equal.
    rewrite (Ugetdim_Upow _ _ a1); auto.
    rewrite (Ugetdim_Upow _ _ a2); auto.
    rewrite (Ugetdim_Upow _ _ a3); auto.
    rewrite (Ugetdim_Upow _ _ a4); auto.
    rewrite (Ugetdim_Upow _ _ a5); auto.
    rewrite (Ugetdim_Upow _ _ a6); auto.
    rewrite (Ugetdim_Upow _ _ a7); auto.
Qed.



(** ** Convert from [NUnit] to [Unit]. *)
Definition n2u (n : NUnit) : Unit :=
  let '(coef, (ds,dm,dkg,dA,dK,dmol,dcd)) := n in
  let u := $coef in
  let u := Ucons u BUTime ds in
  let u := Ucons u BULength dm in
  let u := Ucons u BUMass dkg in
  let u := Ucons u BUElectricCurrent dA in
  let u := Ucons u BUThermodynamicTemperature dK in
  let u := Ucons u BUAmountOfSubstance dmol in
  let u := Ucons u BULuminousIntensity dcd in
    u.

(** Coefficient of [n2u n] is the coefficient of [n]. *)
Lemma Ugetcoef_n2u : forall n coef dims,
  (coef, dims) = n -> Ugetcoef (n2u n) = coef.
Proof.
  intros. induction n as [coef1 dims1]. inversion H; subst.
  destruct dims1 as [[[[[[ds dm] dkg] dA] dK] dmol] dcd]. simpl.
  rewrite ?Ugetcoef_Ucons. auto.
Qed.

(** Dimension of [n2u n] is the dimension of the n. *)
Lemma Ugetdim_n2u : forall n coef ds dm dkg dA dK dmol dcd,
  (coef, (ds,dm,dkg,dA,dK,dmol,dcd)) = n ->
  Ugetdim (n2u n) BUTime = ds /\
  Ugetdim (n2u n) BULength = dm /\
  Ugetdim (n2u n) BUMass = dkg /\
  Ugetdim (n2u n) BUElectricCurrent = dA /\
  Ugetdim (n2u n) BUThermodynamicTemperature = dK /\
  Ugetdim (n2u n) BUAmountOfSubstance = dmol /\
  Ugetdim (n2u n) BULuminousIntensity = dcd.
Proof.
  intros.
  induction n as [coef1 dims1].
  destruct dims1 as [[[[[[ds1 dm1] dkg1] dA1] dK1] dmol1] dcd1].
  inversion H; subst. simpl.
  rewrite ?Ugetdim_Ucons; simpl. repeat split;
  try ring.
Qed.

(** [n2u] is injective about coefficient. *)
Lemma n2u_inj_coef : forall coef1 coef2 d1 d2, 
  n2u (coef1, d1) = n2u (coef2, d2) -> coef1 = coef2.
Proof.
  intros.
  assert (forall u1 u2, u1 = u2 -> Ugetcoef u1 = Ugetcoef u2);
  intros; subst; auto.
  apply H0 in H. simpl in H.
  destruct d1 as [[[[[[ds1 dm1] dkg1] dA1] dK1] dmol1] dcd1].
  destruct d2 as [[[[[[ds2 dm2] dkg2] dA2] dK2] dmol2] dcd2].
  rewrite ?Ugetcoef_Ucons in H. simpl in H. auto.
Qed.

(** [n2u] is injective about dimensions. *)
Lemma n2u_inj_dims : forall coef1 coef2 d1 d2, 
  n2u (coef1, d1) = n2u (coef2, d2) -> d1 = d2.
Proof.
  intros.
  assert (forall u1 u2 k, u1 = u2 -> Ugetdim u1 k = Ugetdim u2 k);
  intros; subst; auto. simpl in H.
  destruct d1 as [[[[[[ds1 dm1] dkg1] dA1] dK1] dmol1] dcd1].
  destruct d2 as [[[[[[ds2 dm2] dkg2] dA2] dK2] dmol2] dcd2].
  (* BUTime *)
  remember H as H1 eqn : E1; clear E1;
  apply (H0 _ _ &T) in H1; rewrite ?Ugetdim_Ucons in H1; simpl in H1;
  rewrite ?Z.add_0_r,?Z.add_0_l in H1; subst.
  (* BULength *)
  remember H as H1 eqn : E1; clear E1;
  apply (H0 _ _ &L) in H1; rewrite ?Ugetdim_Ucons in H1; simpl in H1;
  rewrite ?Z.add_0_r,?Z.add_0_l in H1; subst.
  (* BUMass *)
  remember H as H1 eqn : E1; clear E1;
  apply (H0 _ _ &M) in H1; rewrite ?Ugetdim_Ucons in H1; simpl in H1;
  rewrite ?Z.add_0_r,?Z.add_0_l in H1; subst.
  (* BUElectricCurrent *)
  remember H as H1 eqn : E1; clear E1;
  apply (H0 _ _ &I) in H1; rewrite ?Ugetdim_Ucons in H1; simpl in H1;
  rewrite ?Z.add_0_r,?Z.add_0_l in H1; subst.
  (* BUThermodynamicTemperature *)
  remember H as H1 eqn : E1; clear E1;
  apply (H0 _ _ &O) in H1; rewrite ?Ugetdim_Ucons in H1; simpl in H1;
  rewrite ?Z.add_0_r,?Z.add_0_l in H1; subst.
  (* BUAmountOfSubstance *)
  remember H as H1 eqn : E1; clear E1;
  apply (H0 _ _ &N) in H1; rewrite ?Ugetdim_Ucons in H1; simpl in H1;
  rewrite ?Z.add_0_r,?Z.add_0_l in H1; subst.
  (* BULuminousIntensity *)
  remember H as H1 eqn : E1; clear E1;
  apply (H0 _ _ &J) in H1; rewrite ?Ugetdim_Ucons in H1; simpl in H1;
  rewrite ?Z.add_0_r,?Z.add_0_l in H1; subst.
  auto.
Qed.

(** [n2u] is injective. *)
Lemma n2u_inj : forall n1 n2, n2u n1 = n2u n2 -> n1 = n2.
Proof.
  intros n1 n2 H. remember H as H1 eqn: E1; clear E1.
  destruct n1 as (coef1, d1). destruct n2 as (coef2, d2).
  apply n2u_inj_coef in H.
  apply n2u_inj_dims in H1. subst. auto.
Qed.

(** Converting from [NUnit] to [Unit], and then again to [NUnit], will return 
  to beginning. *)
Lemma u2n_n2u : forall (n : NUnit), u2n (n2u n) = n.
Proof.
  intros n. unfold u2n. induction n as [coef dims].
  destruct dims as [[[[[[d1 d2] d3] d4] d5] d6] d7]. simpl.
  rewrite ?Ugetcoef_Ucons,?Ugetdim_Ucons; simpl. repeat f_equal; ring.
Qed.




(** * Comparison of [Unit]: use corresponding [NUnit] comparison. *)


(** ** Boolean Equality of [Unit] *)
Definition Ueqb (u1 u2 : Unit) : bool := NUeqb (u2n u1) (u2n u2).

Notation "u1 =? u2" := (Ueqb u1 u2) (at level 70) : Unit_scope.

(** Boolean equality of two initial units, imply boolean equality of two units 
  constructed from them. *)
Lemma Ueqb_iff_Ueqb_of_Ucons : forall u1 u2 b dim,
  Ueqb (Ucons u1 b dim) (Ucons u2 b dim) = Ueqb u1 u2.
Proof.
  intros. unfold Ueqb in *. unfold u2n in *.
  rewrite ?Ugetcoef_Ucons, ?Ugetdim_Ucons.
  unfold NUeqb.
  repeat apply andb_eq_inv; auto;
  rewrite Zadd_eqb_cancel_r; auto.
Qed.


(** [Ueqb] is true, it is reflexive *)
Lemma Ueqb_true_refl : forall u, u =? u = true.
Proof. intros. unfold Ueqb. apply NUeqb_true_iff. auto. Qed.

(** [Ueqb] is commutative. *)
Lemma Ueqb_comm : forall (u1 u2 : Unit), (u1 =? u2) = (u2 =? u1).
Proof.
  intros. unfold Ueqb in *. apply NUeqb_comm.
Qed.

(** [Ueqb] is true, it is transitive *)
Lemma Ueqb_true_trans : forall (u1 u2 u3 : Unit), 
  u1 =? u2 = true -> u2 =? u3 = true -> u1 =? u3 = true.
Proof.
  intros. unfold Ueqb in *. apply NUeqb_true_trans with (u2n u2); auto.
Qed.

(** [Ueqb] is true, iff their coefficients and dimensions all equal. *)
Lemma Ueqb_true_iff_coef_dims : forall u1 u2,
  (u1 =? u2 = true) <-> 
    let (c1,d1) := u2n u1 in
    let (c2,d2) := u2n u2 in
      Reqb c1 c2 = true /\ Dims_eqb d1 d2 = true.
Proof.
  intros. unfold Ueqb.
  rewrite NUeqb_true_iff.
  destruct (u2n u1) eqn: E1, (u2n u2) eqn: E2.
  split; intros H; inversion H; subst.
  - rewrite Reqb_true_iff, Dims_eqb_true_iff. easy.
  - rewrite Reqb_true_iff in H0.
    rewrite Dims_eqb_true_iff in H1. subst; easy.
Qed.

(** [Ueqb] with n2u is true, iff their coefficients and dimensions all equal. *)
Lemma Ueqb_n2u_true_iff_coef_dims : forall c1 c2 d1 d2,
  (n2u (c1,d1) =? n2u (c2,d2) = true) <-> c1 = c2 /\ d1 = d2.
Proof.
  intros. rewrite Ueqb_true_iff_coef_dims. repeat rewrite u2n_n2u.
  rewrite Reqb_true_iff, Dims_eqb_true_iff. tauto.
Qed.



(** ** Proposional euqality of [Unit] *)

Definition Ueq (u1 u2 : Unit) : Prop := u2n u1 = u2n u2.

Notation "u1 == u2" := (Ueq u1 u2) (at level 70) : Unit_scope.

(** Equality of two initial units, imply equality of two units constructed from 
  them. *)
Lemma Ueq_imply_Ueq_of_Ucons : forall u1 u2 b dim,
  Ueq u1 u2 -> Ueq (Ucons u1 b dim) (Ucons u2 b dim).
Proof.
  intros. unfold Ueq in *. unfold u2n in *.
  inversion H.
  rewrite ?Ugetcoef_Ucons,?Ugetdim_Ucons.
  rewrite H1,H2,H3,H4,H5,H6,H7,H8. auto.
Qed.

(** Equality of two units, iff their coefficients and dimensions all equal. *)
Lemma Ueq_iff_coef_dims : forall u1 u2,
  u1 == u2 <-> 
    let (c1,d1) := u2n u1 in
    let (c2,d2) := u2n u2 in
      Reqb c1 c2 = true /\ Dims_eqb d1 d2 = true.
Proof.
  intros. unfold Ueq. split; intros;
  destruct (u2n u1) eqn:E1, (u2n u2) eqn:E2.
  - inversion H.
    rewrite Reqb_true_iff, Dims_eqb_true_iff. auto.
  - rewrite Reqb_true_iff, Dims_eqb_true_iff in H. destruct H; subst; easy.
Qed.

(** [Ueq] is an equivalence relation. *)
Lemma Ueq_refl : forall (u : Unit), u == u.
Proof.
  intros. unfold Ueq. auto.
Qed.

Lemma Ueq_sym : forall (u1 u2 : Unit), u1 == u2 -> u2 == u1.
Proof.
  intros. unfold Ueq, u2n in *. inversion H. auto.
Qed.

Lemma Ueq_trans : forall (u1 u2 u3 : Unit), 
  u1 == u2 -> u2 == u3 -> u1 == u3.
Proof.
  intros. unfold Ueq, u2n in *. inversion H. inversion H0.
  repeat (f_equal; auto).
Qed.

Lemma Ueq_equiv : equivalence Unit Ueq.
Proof.
  intros. refine (Build_equivalence _ _ _ _ _); unfold Ueq.
  - intros x. auto.
  - intros x1 x2 x3. intros. rewrite H; auto.
  - intros x1 x2. intros. rewrite H; auto.
Qed.

Add Parametric Relation : Unit Ueq
  reflexivity proved by (equiv_refl Unit Ueq Ueq_equiv)
  symmetry proved by (equiv_sym Unit Ueq Ueq_equiv)
  transitivity proved by (equiv_trans Unit Ueq Ueq_equiv)
  as Ueq_rel.

(** [Ueq] iff [Ueqb]. *)
Lemma Ueq_iff_Ueqb u1 u2 : (u1 == u2) <-> (u1 =? u2 = true).
Proof.
  rewrite Ueq_iff_coef_dims.
  rewrite Ueqb_true_iff_coef_dims. split; easy.
Qed.



(** ** Approximate relation of [Unit] *)

(** Check if two units is approximate, propositional version. *)
Definition Unit_approx (u1 u2 : Unit) (diff : R) : Prop :=
  let (c1, d1) := u2n u1 in
  let (c2, d2) := u2n u2 in
    (d1 = d2) /\ (Rapprox c1 c2 diff).

(** Check if two units is approximate, boolean version. *)
Definition Unit_approxb (u1 u2 : Unit) (diff : R) : bool :=
  let (c1, d1) := u2n u1 in
  let (c2, d2) := u2n u2 in
    (Dims_eqb d1 d2) && (Rapproxb c1 c2 diff).



(** * Square root of a Unit *)

(** Square root of a Unit defined as sqrt of coefficient and dimensions. *)
Definition Unit_sqrt (u : Unit) : option Unit :=
  let (c, d) := u2n u in
    match (Dims_sqrt d) with
    | Some d' => Some (n2u (sqrt c, d'))
    | None => None
    end.

(** Examples *)
(* Compute Unit_sqrt (4*[BUTime]²).
Compute Unit_sqrt (4*[BUTime]²*[BULength]).
 *)



(** * Normalization of [Unit] (won't use) *)

Definition Unorm (u : Unit) : Unit := n2u (u2n u).

(* examples *)
(* Compute Unorm (kg * m * s).
Compute Unorm (kg * s * m).
Compute Unorm (s * m * kg * $3 ).
Compute Unorm (unorm (s * m * kg * $3 )).
 *)

(** unorm operation is fixpoint. *)
Lemma Unorm_fixpoint : forall (u : Unit),
  let u' := Unorm u in Unorm u' = u'.
Proof.
  intros u. unfold Unorm. rewrite u2n_n2u. auto.
Qed.

