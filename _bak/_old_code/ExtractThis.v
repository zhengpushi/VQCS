
Require Import SI.
Require Import QUalgebra.

Require Import Extraction.



From Coq Require Extraction.


(** Give some conversion rules manually *)

(* the command provided by std library will generate warning *)
(* Require Import extraction.ExtrOcamlBasic.
Require Import extraction.ExtrOcamlNatInt.
Require Import extraction.ExtrOcamlZInt. *)
 

(* some inductive datatypes *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive nat => "int" [ "0" "Int.succ" ] 
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

(* constant - Real number and operations *)
Extract Constant R => float.

(* patch for coq 8.11 and newer *)
Extract Constant Rabst => "__".
Extract Constant Rrepr => "__".

Extract Constant R0 => "0.0".
Extract Constant R1 => "1.0".
Extract Constant PI => "Float.pi".
Extract Constant Rplus => "(+.)".
Extract Constant Rmult => "( *. )".
Extract Constant Rminus => "(-.)".
Extract Constant Ropp => "fun a -> (0.0 -. a)".
Extract Constant Rinv => "fun a -> (1.0 /. a)".
Extract Constant Rpower => "Float.pow".
Extract Constant sin => "Float.sin".
Extract Constant cos => "Float.cos".
Extract Constant sqrt => "Float.sqrt".
Extract Constant atan => "Float.atan".
Extract Constant acos => "Float.acos".
(* Extract Constant pow => 
  "fun r0 n -> if n=0 then 1.0 else (r0 *. (pow r0 (n-1)))". *)

  
(* Recursive Extraction SI. *)
Recursive Extraction Qmult.
Recursive Extraction QUmult QUplus QUinv QUconv.


Section test1.

  (** example2: two taps, one 36.7cm^3/s, another 2.1L/min, need to fill 
  300cm^3 cup, how long? *)
  Let f1 := genQU 36.7 ('cm³/'s)%U.
  Let f2 := genQU 2.1 ('L/'min)%U.
  Let V := genQU 300 ('cm³)%U.
  
  Definition fill_time := (QUconv (V / (f1 + f2)) 's).
  Eval compute in fill_time.
  
  Definition fill_time_val := QUvalue fill_time.

End test1.

Extract Constant QUvalueERR => "infinity".
Extract Constant QUdimERR => "{ d1 = Z0; d2 = Z0; d3 = Z0; d4 = Z0; d5 = Z0; d6 = Z0; d7 = Z0; d8 = Z0 }".


Recursive Extraction mkDims Dzero fill_time fill_time_val.
Extraction "test1.ml" QUvalue QUdim fill_time fill_time_val .

(** OCaml测试步骤
$ utop
>> #use "test1.ml";;
>> fill_time;;
>> exit 0;;
*)
