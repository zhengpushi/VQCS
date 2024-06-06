
(* n-th Power of m*)
let rec power_aux m n ret =
  if n < 1 then ret else power_aux m (n-1) (ret * m)

let power m n = power_aux m n 1


(* Generate a string like (1,1^n); (2,2^n); ...; (max,max^n) *)
let gen_power_numbers max n = 
  let pad1_max_len = String.length (string_of_int max) in
  let pad2_max_len = String.length (string_of_int (power max n)) in
  for i = 1 to max do
    let cr = if (i mod 5 = 0) then "\n" else "" in
    let num1 = string_of_int i in
    let num2 = string_of_int (power i n) in
    let pad1 = String.make (pad1_max_len- String.length num1) ' ' in
    let pad2 = String.make (pad2_max_len - String.length num2) ' ' in
    let all = "(" ^ pad1 ^ num1 ^ "," ^ pad2 ^ num2 ^ "); " ^ cr in
    print_string all
  done;
  print_string "\n"

let cfg_MIN_max = 1
let cfg_MAX_max = 1000
let cfg_MAX_n = 6
let cfg_MIN_n = 1

let fix_min_max x min max =
  if x < min
  then min
  else if x > max
  then max
  else x

let main() =
  let max = int_of_string Sys.argv.(1) in
  let n = int_of_string Sys.argv.(2) in
  let max = fix_min_max max cfg_MIN_max cfg_MAX_max in
  let n = fix_min_max n cfg_MIN_n cfg_MAX_n in
  Printf.printf ("generate [(%d^%d); (%d^%d); ...; (%d^%d)]\n") 1 n 2 n (max) n ;
  gen_power_numbers max n;;

main()