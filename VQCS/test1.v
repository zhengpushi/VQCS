
Require Import QUalgebra.
  

Section test1.

  (** example2: two taps, one 36.7cm^3/s, another 2.1L/min, need to fill 
  300cm^3 cup, how long? *)
  Let f1 := genQU 36.7 ('cm³/'s)%U.
  Let f2 := genQU 2.1 ('L/'min)%U.
  Let V := genQU 300 ('cm³)%U.
  
  Definition fill_time := (QUconv (V / (f1 + f2)) 's).
  Eval compute in fill_time.

End test1.

Require Import 