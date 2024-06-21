
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



module Coq__1 = struct
 (** val add : int -> int -> int **)

 let rec add = (+)
end
include Coq__1

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> Stdlib.Int.succ (add p m))
      n

  (** val mul : int -> int -> int **)

  let rec mul n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n

  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Stdlib.Int.succ 0)
      (fun m0 -> mul n (pow n m0))
      m
 end

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p -> (match y with
               | XI q0 -> XI (add p q0)
               | XO q0 -> XO (add p q0)
               | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH -> (match y with
             | XI q0 -> XI (succ q0)
             | XO q0 -> XO (succ q0)
             | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double_mask (sub_mask p q0)
       | XO q0 -> succ_double_mask (sub_mask p q0)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p q0)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val size_nat : positive -> int **)

  let rec size_nat = function
  | XI p0 -> Stdlib.Int.succ (size_nat p0)
  | XO p0 -> Stdlib.Int.succ (size_nat p0)
  | XH -> Stdlib.Int.succ 0

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q0 =
    match p with
    | XI p0 -> (match q0 with
                | XI q1 -> eqb p0 q1
                | _ -> false)
    | XO p0 -> (match q0 with
                | XO q1 -> eqb p0 q1
                | _ -> false)
    | XH -> (match q0 with
             | XH -> true
             | _ -> false)

  (** val ggcdn : int -> positive -> positive -> positive * (positive * positive) **)

  let rec ggcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (XH, (a, b)))
      (fun n0 ->
      match a with
      | XI a' ->
        (match b with
         | XI b' ->
           (match compare a' b' with
            | Eq -> (a, (XH, XH))
            | Lt ->
              let (g, p) = ggcdn n0 (sub b' a') a in
              let (ba, aa) = p in (g, (aa, (add aa (XO ba))))
            | Gt ->
              let (g, p) = ggcdn n0 (sub a' b') b in
              let (ab, bb) = p in (g, ((add bb (XO ab)), bb)))
         | XO b0 -> let (g, p) = ggcdn n0 a b0 in let (aa, bb) = p in (g, (aa, (XO bb)))
         | XH -> (XH, (a, XH)))
      | XO a0 ->
        (match b with
         | XI _ -> let (g, p) = ggcdn n0 a0 b in let (aa, bb) = p in (g, ((XO aa), bb))
         | XO b0 -> let (g, p) = ggcdn n0 a0 b0 in ((XO g), p)
         | XH -> (XH, (a, XH)))
      | XH -> (XH, (XH, b)))
      n

  (** val ggcd : positive -> positive -> positive * (positive * positive) **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> int **)

  let to_nat x =
    iter_op Coq__1.add x (Stdlib.Int.succ 0)

  (** val of_nat : int -> positive **)

  let rec of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> XH)
        (fun _ -> succ (of_nat x))
        x)
      n

  (** val of_succ_nat : int -> positive **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x -> succ (of_succ_nat x))
      n
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double (pos_sub p q0)
       | XO q0 -> succ_double (pos_sub p q0)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Coq_Pos.pred_double q0)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val pow_pos : z -> positive -> z **)

  let pow_pos z0 =
    Coq_Pos.iter (mul z0) (Zpos XH)

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Coq_Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' -> (match y with
                  | Zneg y' -> compOpp (Coq_Pos.compare x' y')
                  | _ -> Lt)

  (** val sgn : z -> z **)

  let sgn = function
  | Z0 -> Z0
  | Zpos _ -> Zpos XH
  | Zneg _ -> Zneg XH

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos q0 -> Coq_Pos.eqb p q0
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg q0 -> Coq_Pos.eqb p q0
                 | _ -> false)

  (** val max : z -> z -> z **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val min : z -> z -> z **)

  let min n m =
    match compare n m with
    | Gt -> m
    | _ -> n

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val to_nat : z -> int **)

  let to_nat = function
  | Zpos p -> Coq_Pos.to_nat p
  | _ -> 0

  (** val of_nat : int -> z **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Z0)
      (fun n0 -> Zpos (Coq_Pos.of_succ_nat n0))
      n

  (** val to_pos : z -> positive **)

  let to_pos = function
  | Zpos p -> p
  | _ -> XH

  (** val ggcd : z -> z -> z * (z * z) **)

  let ggcd a b =
    match a with
    | Z0 -> ((abs b), (Z0, (sgn b)))
    | Zpos a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zneg bb))))
    | Zneg a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zneg bb))))
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

module RbaseSymbolsImpl =
 struct
  type coq_R = float

  (** val coq_Rabst : cReal -> dReal **)

  let coq_Rabst = __

  (** val coq_Rrepr : dReal -> cReal **)

  let coq_Rrepr = __

  (** val coq_Rquot1 : __ **)

  let coq_Rquot1 =
    __

  (** val coq_Rquot2 : __ **)

  let coq_Rquot2 =
    __

  (** val coq_R0 : coq_R **)

  let coq_R0 = 0.0

  (** val coq_R1 : coq_R **)

  let coq_R1 = 1.0

  (** val coq_Rplus : coq_R -> coq_R -> coq_R **)

  let coq_Rplus = (+.)

  (** val coq_Rmult : coq_R -> coq_R -> coq_R **)

  let coq_Rmult = ( *. )

  (** val coq_Ropp : coq_R -> coq_R **)

  let coq_Ropp = fun a -> (0.0 -. a)

  type coq_Rlt = __

  (** val coq_R0_def : __ **)

  let coq_R0_def =
    __

  (** val coq_R1_def : __ **)

  let coq_R1_def =
    __

  (** val coq_Rplus_def : __ **)

  let coq_Rplus_def =
    __

  (** val coq_Rmult_def : __ **)

  let coq_Rmult_def =
    __

  (** val coq_Ropp_def : __ **)

  let coq_Ropp_def =
    __

  (** val coq_Rlt_def : __ **)

  let coq_Rlt_def =
    __
 end

(** val iPR_2 : positive -> RbaseSymbolsImpl.coq_R **)

let rec iPR_2 = function
| XI p0 ->
  RbaseSymbolsImpl.coq_Rmult
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 RbaseSymbolsImpl.coq_R1)
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 (iPR_2 p0))
| XO p0 ->
  RbaseSymbolsImpl.coq_Rmult
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 RbaseSymbolsImpl.coq_R1) (iPR_2 p0)
| XH -> RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 RbaseSymbolsImpl.coq_R1

(** val iPR : positive -> RbaseSymbolsImpl.coq_R **)

let iPR = function
| XI p0 -> RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 (iPR_2 p0)
| XO p0 -> iPR_2 p0
| XH -> RbaseSymbolsImpl.coq_R1

(** val iZR : z -> RbaseSymbolsImpl.coq_R **)

let iZR = function
| Z0 -> RbaseSymbolsImpl.coq_R0
| Zpos n -> iPR n
| Zneg n -> RbaseSymbolsImpl.coq_Ropp (iPR n)

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl =
 struct
  (** val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

  let coq_Rinv = fun a -> (1.0 /. a)

  (** val coq_Rinv_def : __ **)

  let coq_Rinv_def =
    __
 end

(** val rdiv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let rdiv r1 r2 =
  RbaseSymbolsImpl.coq_Rmult r1 (RinvImpl.coq_Rinv r2)

(** val q2R : q -> RbaseSymbolsImpl.coq_R **)

let q2R x =
  RbaseSymbolsImpl.coq_Rmult (iZR x.qnum) (RinvImpl.coq_Rinv (iZR (Zpos x.qden)))

(** val req_dec_T : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let req_dec_T = fun r1 r2 ->
  let c = Float.compare r1 r2 in
  if c = 0 then true
  else false

(** val reqb : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let reqb r1 r2 =
  if req_dec_T r1 r2 then true else false

type baseUnit =
| BUTime
| BULength
| BUMass
| BUElectricCurrent
| BUThermodynamicTemperature
| BUAmountOfSubstance
| BULuminousIntensity

(** val baseUnit_beq : baseUnit -> baseUnit -> bool **)

let baseUnit_beq x y =
  match x with
  | BUTime -> (match y with
               | BUTime -> true
               | _ -> false)
  | BULength -> (match y with
                 | BULength -> true
                 | _ -> false)
  | BUMass -> (match y with
               | BUMass -> true
               | _ -> false)
  | BUElectricCurrent -> (match y with
                          | BUElectricCurrent -> true
                          | _ -> false)
  | BUThermodynamicTemperature ->
    (match y with
     | BUThermodynamicTemperature -> true
     | _ -> false)
  | BUAmountOfSubstance -> (match y with
                            | BUAmountOfSubstance -> true
                            | _ -> false)
  | BULuminousIntensity -> (match y with
                            | BULuminousIntensity -> true
                            | _ -> false)

(** val bueqb : baseUnit -> baseUnit -> bool **)

let bueqb =
  baseUnit_beq

type unit0 =
| Unone of RbaseSymbolsImpl.coq_R
| Ubu of baseUnit
| Uinv of unit0
| Umul of unit0 * unit0

(** val upowNat : unit0 -> int -> unit0 **)

let rec upowNat u n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Unone (iZR (Zpos XH)))
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> u)
      (fun _ -> Umul (u, (upowNat u n')))
      n')
    n

(** val upow : unit0 -> z -> unit0 **)

let upow u = function
| Z0 -> Unone (iZR (Zpos XH))
| Zpos p -> upowNat u (Coq_Pos.to_nat p)
| Zneg p -> Uinv (upowNat u (Coq_Pos.to_nat p))

(** val ucoef : unit0 -> RbaseSymbolsImpl.coq_R **)

let rec ucoef = function
| Unone c -> c
| Ubu _ -> iZR (Zpos XH)
| Uinv u1 -> RinvImpl.coq_Rinv (ucoef u1)
| Umul (u1, u2) -> RbaseSymbolsImpl.coq_Rmult (ucoef u1) (ucoef u2)

(** val udim : unit0 -> baseUnit -> z **)

let rec udim u b =
  match u with
  | Unone _ -> Z0
  | Ubu bu -> if bueqb bu b then Zpos XH else Z0
  | Uinv u1 -> Z.opp (udim u1 b)
  | Umul (u1, u2) -> Z.add (udim u1 b) (udim u2 b)

type dims = (((((z * z) * z) * z) * z) * z) * z

(** val deqb : dims -> dims -> bool **)

let deqb d1 d2 =
  let (p, z0) = d1 in
  let (p0, z1) = p in
  let (p1, z2) = p0 in
  let (p2, z3) = p1 in
  let (p3, z4) = p2 in
  let (z5, z6) = p3 in
  let (p4, z7) = d2 in
  let (p5, z8) = p4 in
  let (p6, z9) = p5 in
  let (p7, z10) = p6 in
  let (p8, z11) = p7 in
  let (z12, z13) = p8 in
  (&&)
    ((&&)
      ((&&) ((&&) ((&&) ((&&) (Z.eqb z5 z12) (Z.eqb z6 z13)) (Z.eqb z4 z11)) (Z.eqb z3 z10))
        (Z.eqb z2 z9)) (Z.eqb z1 z8)) (Z.eqb z0 z7)

(** val dmap : dims -> (z -> z) -> dims **)

let dmap d f =
  let (p, z0) = d in
  let (p0, z1) = p in
  let (p1, z2) = p0 in
  let (p2, z3) = p1 in
  let (p3, z4) = p2 in
  let (z5, z6) = p3 in (((((((f z5), (f z6)), (f z4)), (f z3)), (f z2)), (f z1)), (f z0))

(** val dmap2 : dims -> dims -> (z -> z -> z) -> dims **)

let dmap2 d1 d2 f =
  let (p, z0) = d1 in
  let (p0, z1) = p in
  let (p1, z2) = p0 in
  let (p2, z3) = p1 in
  let (p3, z4) = p2 in
  let (z5, z6) = p3 in
  let (p4, z7) = d2 in
  let (p5, z8) = p4 in
  let (p6, z9) = p5 in
  let (p7, z10) = p6 in
  let (p8, z11) = p7 in
  let (z12, z13) = p8 in
  (((((((f z5 z12), (f z6 z13)), (f z4 z11)), (f z3 z10)), (f z2 z9)), (f z1 z8)), (f z0 z7))

(** val dplus : dims -> dims -> dims **)

let dplus d1 d2 =
  dmap2 d1 d2 Z.add

(** val dopp : dims -> dims **)

let dopp d =
  dmap d Z.opp

(** val udims : unit0 -> dims **)

let udims u =
  (((((((udim u BUTime), (udim u BULength)), (udim u BUMass)), (udim u BUElectricCurrent)),
    (udim u BUThermodynamicTemperature)), (udim u BUAmountOfSubstance)),
    (udim u BULuminousIntensity))

type nunit = RbaseSymbolsImpl.coq_R * dims

(** val ncoef : nunit -> RbaseSymbolsImpl.coq_R **)

let ncoef =
  fst

(** val ndims : nunit -> dims **)

let ndims =
  snd

(** val neqb : nunit -> nunit -> bool **)

let neqb n1 n2 =
  (&&) (reqb (ncoef n1) (ncoef n2)) (deqb (ndims n1) (ndims n2))

(** val nmul : nunit -> nunit -> nunit **)

let nmul n1 n2 =
  ((RbaseSymbolsImpl.coq_Rmult (ncoef n1) (ncoef n2)), (dplus (ndims n1) (ndims n2)))

(** val ninv : nunit -> nunit **)

let ninv n1 =
  ((RinvImpl.coq_Rinv (ncoef n1)), (dopp (ndims n1)))

(** val u2n : unit0 -> nunit **)

let u2n u =
  ((ucoef u), (udims u))

module SI_Prefix =
 struct
  (** val centi : unit0 -> unit0 **)

  let centi u =
    Umul ((Unone (rdiv (iZR (Zpos XH)) (iZR (Z.pow_pos (Zpos (XO (XI (XO XH)))) (XO XH))))),
      u)
 end

module SI_Basic =
 struct
  (** val second : baseUnit **)

  let second =
    BUTime

  (** val metre : baseUnit **)

  let metre =
    BULength
 end

module SI_Accepted =
 struct
  (** val minute : unit0 **)

  let minute =
    Umul ((Unone (iZR (Zpos (XO (XO (XI (XI (XI XH)))))))), (Ubu SI_Basic.second))

  (** val litre : unit0 **)

  let litre =
    Umul ((Unone (rdiv (iZR (Zpos XH)) (iZR (Z.pow_pos (Zpos (XO (XI (XO XH)))) (XI XH))))),
      (upow (Ubu SI_Basic.metre) (Zpos (XI XH))))
 end

(** val ncvtbleb : nunit -> nunit -> bool **)

let ncvtbleb n1 n2 =
  deqb (ndims n1) (ndims n2)

(** val nconvRate : nunit -> nunit -> RbaseSymbolsImpl.coq_R option **)

let nconvRate src ref =
  if ncvtbleb src ref then Some (rdiv (ncoef src) (ncoef ref)) else None

type 'a quantity =
| Qmake of 'a * nunit
| Qinvalid

(** val qmakeU : 'a1 -> unit0 -> 'a1 quantity **)

let qmakeU v0 u =
  Qmake (v0, (u2n u))

(** val qconv :
    (RbaseSymbolsImpl.coq_R -> 'a1 -> 'a1) -> 'a1 quantity -> unit0 -> 'a1 quantity **)

let qconv ascal q0 uref =
  let nref = u2n uref in
  (match q0 with
   | Qmake (v0, n) ->
     (match nconvRate n nref with
      | Some rate -> Qmake ((ascal rate v0), nref)
      | None -> Qinvalid)
   | Qinvalid -> Qinvalid)

(** val qop2 : ('a1 -> 'a1 -> 'a1) -> 'a1 quantity -> 'a1 quantity -> 'a1 quantity **)

let qop2 f q1 q2 =
  match q1 with
  | Qmake (v1, n1) ->
    (match q2 with
     | Qmake (v2, n2) -> if neqb n1 n2 then Qmake ((f v1 v2), n1) else Qinvalid
     | Qinvalid -> Qinvalid)
  | Qinvalid -> Qinvalid

(** val qadd : ('a1 -> 'a1 -> 'a1) -> 'a1 quantity -> 'a1 quantity -> 'a1 quantity **)

let qadd =
  qop2

(** val qinv : ('a1 -> 'a1) -> 'a1 quantity -> 'a1 quantity **)

let qinv ainv = function
| Qmake (v0, n) -> Qmake ((ainv v0), (ninv n))
| Qinvalid -> Qinvalid

(** val qmul : ('a1 -> 'a2 -> 'a2) -> 'a1 quantity -> 'a2 quantity -> 'a2 quantity **)

let qmul amulB q1 q2 =
  match q1 with
  | Qmake (v1, n1) ->
    (match q2 with
     | Qmake (v2, n2) -> Qmake ((amulB v1 v2), (nmul n1 n2))
     | Qinvalid -> Qinvalid)
  | Qinvalid -> Qinvalid

(** val qdiv :
    ('a1 -> 'a2 -> 'a2) -> ('a2 -> 'a2) -> 'a1 quantity -> 'a2 quantity -> 'a2 quantity **)

let qdiv amulB binv q1 q2 =
  qmul amulB q1 (qinv binv q2)

(** val f1 : RbaseSymbolsImpl.coq_R quantity **)

let f1 =
  qmakeU
    (q2R { qnum = (Zpos (XI (XI (XI (XI (XO (XI (XI (XO XH))))))))); qden = (XO (XI (XO
      XH))) }) (Umul ((upow (SI_Prefix.centi (Ubu SI_Basic.metre)) (Zpos (XI XH))), (Uinv
    (Ubu SI_Basic.second))))

(** val f2 : RbaseSymbolsImpl.coq_R quantity **)

let f2 =
  qmakeU (q2R { qnum = (Zpos (XI (XO (XI (XO XH))))); qden = (XO (XI (XO XH))) }) (Umul
    (SI_Accepted.litre, (Uinv SI_Accepted.minute)))

(** val v : RbaseSymbolsImpl.coq_R quantity **)

let v =
  qmakeU (iZR (Zpos (XO (XO (XI (XI (XO (XI (XO (XO XH))))))))))
    (upow (SI_Prefix.centi (Ubu SI_Basic.metre)) (Zpos (XI XH)))

(** val fill_time1 : RbaseSymbolsImpl.coq_R quantity **)

let fill_time1 =
  qconv RbaseSymbolsImpl.coq_Rmult
    (qdiv RbaseSymbolsImpl.coq_Rmult RinvImpl.coq_Rinv v
      (qadd RbaseSymbolsImpl.coq_Rplus f1 f2)) (Ubu SI_Basic.second)
