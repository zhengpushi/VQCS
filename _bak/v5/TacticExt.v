(*
  purpose   : auxiliary library for tactic.
  author    : Zhengpu SHI
  date      : 2022.04
*)


(** ** Tactics with a short name *)

Global Ltac gd k := generalize dependent k.
