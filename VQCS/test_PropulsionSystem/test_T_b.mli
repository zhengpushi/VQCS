
type __ = Obj.t

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



val add : int -> int -> int

module Nat :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val pow : int -> int -> int
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val size_nat : positive -> int

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool

  val ggcdn : int -> positive -> positive -> positive * (positive * positive)

  val ggcd : positive -> positive -> positive * (positive * positive)

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> int

  val of_nat : int -> positive

  val of_succ_nat : int -> positive
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val pow_pos : z -> positive -> z

  val compare : z -> z -> comparison

  val sgn : z -> z

  val eqb : z -> z -> bool

  val max : z -> z -> z

  val min : z -> z -> z

  val abs : z -> z

  val to_nat : z -> int

  val of_nat : int -> z

  val to_pos : z -> positive

  val ggcd : z -> z -> z * (z * z)
 end

type q = { qnum : z; qden : positive }

type cReal = { seq : (z -> q); scale : z }

type dReal = (q -> bool)

module type RbaseSymbolsSig =
 sig
  type coq_R

  val coq_Rabst : cReal -> coq_R

  val coq_Rrepr : coq_R -> cReal

  val coq_R0 : coq_R

  val coq_R1 : coq_R

  val coq_Rplus : coq_R -> coq_R -> coq_R

  val coq_Rmult : coq_R -> coq_R -> coq_R

  val coq_Ropp : coq_R -> coq_R
 end

module RbaseSymbolsImpl :
 RbaseSymbolsSig

val iPR_2 : positive -> RbaseSymbolsImpl.coq_R

val iPR : positive -> RbaseSymbolsImpl.coq_R

val iZR : z -> RbaseSymbolsImpl.coq_R

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl :
 RinvSig

val rdiv :
  RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val req_dec_T : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

val reqb : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

type baseUnit =
| BUTime
| BULength
| BUMass
| BUElectricCurrent
| BUThermodynamicTemperature
| BUAmountOfSubstance
| BULuminousIntensity

val baseUnit_beq : baseUnit -> baseUnit -> bool

val bueqb : baseUnit -> baseUnit -> bool

type unit0 =
| Unone of RbaseSymbolsImpl.coq_R
| Ubu of baseUnit
| Uinv of unit0
| Umul of unit0 * unit0

val ucoef : unit0 -> RbaseSymbolsImpl.coq_R

val udim : unit0 -> baseUnit -> z

type dims = (((((z * z) * z) * z) * z) * z) * z

val dzero : dims

val deqb : dims -> dims -> bool

val dmap : dims -> (z -> z) -> dims

val dmap2 : dims -> dims -> (z -> z -> z) -> dims

val dplus : dims -> dims -> dims

val dopp : dims -> dims

val udims : unit0 -> dims

type nunit = RbaseSymbolsImpl.coq_R * dims

val ncoef : nunit -> RbaseSymbolsImpl.coq_R

val ndims : nunit -> dims

val nunitOne : nunit

val neqb : nunit -> nunit -> bool

val nmul : nunit -> nunit -> nunit

val ninv : nunit -> nunit

val u2n : unit0 -> nunit

module SI_Basic :
 sig
  val second : baseUnit

  val ampere : baseUnit
 end

module SI_Accepted :
 sig
  val milliampere : unit0

  val minute : unit0

  val hour : unit0

  val milli_amper_hour : unit0
 end

val ncvtbleb : nunit -> nunit -> bool

val nconvRate : nunit -> nunit -> RbaseSymbolsImpl.coq_R option

type 'tA quantity =
| Qmake of 'tA * nunit
| Qinvalid

val u2q : 'a1 -> unit0 -> 'a1 quantity

val a2q : 'a1 -> 'a1 quantity

val qval : 'a1 quantity -> 'a1 option

val qsameub : 'a1 quantity -> unit0 -> bool

val q2qn :
  (RbaseSymbolsImpl.coq_R -> 'a1 -> 'a1) -> 'a1 quantity -> nunit -> 'a1
  quantity

val q2qu :
  (RbaseSymbolsImpl.coq_R -> 'a1 -> 'a1) -> 'a1 quantity -> unit0 -> 'a1
  quantity

val qop1 : ('a1 -> 'a1) -> 'a1 quantity -> 'a1 quantity

val qop2 : ('a1 -> 'a1 -> 'a1) -> 'a1 quantity -> 'a1 quantity -> 'a1 quantity

val qadd : ('a1 -> 'a1 -> 'a1) -> 'a1 quantity -> 'a1 quantity -> 'a1 quantity

val qopp : ('a1 -> 'a1) -> 'a1 quantity -> 'a1 quantity

val qsub :
  ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> 'a1 quantity -> 'a1 quantity -> 'a1
  quantity

val qinv : ('a1 -> 'a1) -> 'a1 quantity -> 'a1 quantity

val qmul : ('a1 -> 'a2 -> 'a2) -> 'a1 quantity -> 'a2 quantity -> 'a2 quantity

val qdiv :
  ('a1 -> 'a2 -> 'a2) -> ('a2 -> 'a2) -> 'a1 quantity -> 'a2 quantity -> 'a2
  quantity

type quR = RbaseSymbolsImpl.coq_R quantity

val u2qR : RbaseSymbolsImpl.coq_R -> unit0 -> quR

val r2q : RbaseSymbolsImpl.coq_R -> quR

val q2quR : quR -> unit0 -> quR

val qsubR : quR -> quR -> quR

val qmulR : quR -> quR -> quR

val qdivR : quR -> quR -> quR

val val_0_06 : RbaseSymbolsImpl.coq_R

val val_C_b : RbaseSymbolsImpl.coq_R

val val_C_min : RbaseSymbolsImpl.coq_R

val c_b : quR

val c_min : quR

val cHK_UNIT : quR -> unit0 -> quR

val cVT_UNIT : quR -> unit0 -> quR

val get_T_b_by_I_b : quR -> quR

module T_b_ex :
 sig
  val val_T_b_1 : RbaseSymbolsImpl.coq_R option

  val val_T_b_2 : RbaseSymbolsImpl.coq_R option
 end
