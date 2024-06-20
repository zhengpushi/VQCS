(*
  purpose   : Convertion between units.
  author    : Zhengpu Shi
  date      : 2022.04
*)

Require Export Unit NUnit SI.

Open Scope Unit_scope.


(** * Convertion from one unit to another specified Unit *)

(** ** Definitions *)

(** Convert a unit with given unit. eg: 30 min with hour get 0.5 hour *)
(*
  第一步，判断 src 和 ref 是否可转换？并得到共同的 dims
  第二步，得到转换系数 coef_src coef_ref coef_src2ref : 
    src == (coef_src, dims)
    ref == (coef_ref, dims)
    coef = coef_src / coef_ref
  第三步，构造出目标单位 dst
    dst = coef * ref
*)
Definition Uconv (src : Unit) (ref : Unit) : option (R * Unit) :=
  let '(c1,d1) := u2n src in
  let (c2,d2) := u2n ref in
    if (Dims_eqb d1 d2) 
    then Some ((c1/c2)%R, ref)
    else None.


(** Examples *)
Example uconv_ex1 : Uconv ($30 * 'min) ('hrs) = Some (0.5, 'hrs).
Proof.
  compute. f_equal. f_equal. field.
Qed.

