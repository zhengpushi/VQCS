(*
  问题：一个简化的模型，用于规范化一个单位。
  比如，s * m * /A, m * /A * s, m * m */m * s * /A 都应该规范化为 m * s * /A
  
  解决：
  1. 表达一个单位
  首先单位系统的基本类别是 Kind, 有7种。
  然后是UnitBasic作为基本单位，可表达 m, km, 等单个单位，没有乘法，
    之所以保留这一层，是为了方便程序编写。
    后来增加了 /m, /km 的表达能力。
  然后是 Unit，包含了 ub 基本构造, inv, mul 这两种操作，可以构造所有的单位表达式。
  2. 如何规范化单位
  (1) 方法一：利用列表作为线性的中间媒介，简化处理，逐个取出 UnitBasic 单位并合并
  首先去掉 inv 操作，仅保留 ub, mul。目的是简化数据。
  然后处理成 list UnitBasic
  然后规范化该 list
  最后重新合并成一个 Unit
  (2) 其他方法：
  之前的Unit3.v中，使用了提取coef，统计Kind个数为Z，然后重新生成单位的方法。
  还可以用模式匹配，写一个复杂的函数，一步化简到位，但比较难写。
  还可以用二叉树的变换来实现，但没想清楚怎么处理。
  还有个思路，利用 permutation 谓词来判断两个表达式相同，
  不过先要处理为list，而且list两边元素数量可能不同，虽然一个表达式相同。
  为防止错误的单位相加，可以考虑使用 option 类型。
*)


(** Import necessary libraries *)

Require Import Permutation.
Require Import ZArith.


(** * Definition and operations of Unit *)

(** Declare a scope for Unit *)
Declare Scope unit_scope.
Open Scope unit_scope.


(** ** Unit Kind,
 there are seven basic unit kind in SI. *)

(** Definition of Unit Kind *)
Inductive Kind :=
  | ka
  | kb
  | kc
  | kd
  | ke
  | kf
  | kg.

(** Convert Kind to nat *)
Definition Kind_ord (k : Kind) : nat :=
  match k with
  | ka => 1 | kb => 2 | kc => 3 | kd => 4
  | ke => 5 | kf => 6 | kg => 7
  end.

Coercion Kind_ord : Kind >-> nat.

(** Automatic generate xx_beq, xx_eq_dec *)
Scheme Equality for Kind.


(** ** Unit Basic,
 represent a basic unit element *)
 
Inductive UnitBasic : Set :=
  | ubone               (* 1 *)
  | ubk (k : Kind)      (* normal *)
  | ubki (k : Kind)     (* inverse *)
  .

(** Automatic generate xx_beq, xx_eq_dec *)
Scheme Equality for UnitBasic.

Notation "1" := (ubone) : unit_scope.
Notation "$ k" := (ubk k) (at level 0) : unit_scope.
Notation "$' k" := (ubki k) (at level 0) : unit_scope.

(** Convert UnitBasic to Z *)
Definition UnitBasic_ord (u : UnitBasic) : Z :=
  match u with
  | 1 => 0
  | $ k => Z.of_nat k
  | $' k => Z.opp (Z.of_nat k)
  end.

Search (Z -> Z -> bool).
Compute Z.eqb 3 3.
Compute Z.leb 3 3.
Compute Z.ltb 3 3.
Compute Z.gtb 3 3.
Compute Z.geb 3 3.


(** ** Unit,
 it could be used to represent any Unit expression *)
Inductive Unit : Set :=
  | ub (u : UnitBasic)
  | uinv (u : Unit)
  | umul (u1 u2 : Unit).

Bind Scope unit_scope with Kind UnitBasic Unit.

Coercion ub : UnitBasic >-> Unit.

Notation " / u" := (uinv u) : unit_scope.
Notation "u1 * u2" := (umul u1 u2) : unit_scope.
(* Notation "u1 / u2" := (umul u1 (uinv u2)) : unit_scope. *)

Example ex1 : Unit := 1 * 1.
Example ex2 : Unit := $ka * $kb * 1.
Example ex3 : Unit := 1 * $kb * $ka.
Example ex4 : Unit := 1 * $kb * $'ka.




(** 以下算法，只是测试用，已经丢弃  *)

(** 计算复杂度，方便递归处理 *)
Fixpoint ulevel (u : Unit) : nat :=
  match u with
  | ub _ => 0
  | / u => (ulevel u) + 1
  | u1 * u2 => (ulevel u1) + (ulevel u2) + 1
  end.

(* 处理方法：
  输入：Unit，输出：Unit (规范化的）
  uflat: 消除 uinv 操作，仅得到UnitBasic的乘法形式，目的是降低复杂度。
  u2list: 将 Unit 转化为 list
  ulinsert: 逐步插入一个 UnitBasic，最核心的一步，消除冗余和规范化。
  list2u: 将 list 转化为 Unit
*)

(* 化简
 1. 消除所有 / 运算
    /(u1*u2) => $a * $'b * ...
    /1 => 1
 2. 1消除，至多保留1个
*)
Fixpoint uflat_aux (n : nat) (u : Unit) : Unit :=
  match n, u with
  | 0, _ => u
  | S n, / (ub b) => match b with
    | 1 => 1
    | $ k => ub ($' k)
    | $' k => ub ($ k)
    end
  | S n, / / u => uflat_aux n u
  | S n, / (u1 * u2) => uflat_aux n
    ((uflat_aux n (/(uflat_aux n u1))) *
    (uflat_aux n (/(uflat_aux n u2))))
  | S n, u1 * u2 => match u1, u2 with
    | /u1, _ => uflat_aux n ((uflat_aux n u1) * u2)
    | _, /u2 => uflat_aux n (u1 * (uflat_aux n u2))
    | 1, 1 => 1
    | 1, _ => uflat_aux n u2
    | _, 1 => uflat_aux n u1
    | _, _ => (* uflat_inv_aux n  *)
      (uflat_aux n u1) * (uflat_aux n u2)
    end
  | S n, _ => u
  end.
  
Definition uflat (u : Unit) : Unit := uflat_aux (ulevel u) u.

(* 从测试可以看出，这个函数没那么容易实现 *)
Compute uflat (1*1*1*1).
Compute uflat (/(1*1)).
Compute uflat (/ (1 * $ (ka))).
Compute uflat (/(1*$ka*(/($ka*$kb)))).
Compute uflat ( /($ka*$kb) * /($ka*$kb)).
Compute uflat ( /($ka*$kb) * /($ka*$kb)).
Compute uflat ( /($ka*$kb) * /($ka*$kb) * / ($'ka * $'kb)).

Check $ka*$ka*$kc*$'ka.




(** 尝试用新的方法 *)

Require Import List.
Import ListNotations.

(** 本考虑用 permutation 来表达两个 Unit 等价，但实际上单位的构成比较复杂，
 两边的元素个数可能也不相同。不合适。 *)
#[export] Hint Constructors Permutation :  sort.

Goal (3 <= 5)%Z. auto with zarith. Qed.

Example exlst1 := [$ka;$kb;$ka].
Example exlst2 := [$kb;$ka;$ka].
Example exlst3 : Permutation exlst1 exlst2.
unfold exlst1,exlst2.
constructor.
Qed.

(* 稍复杂一点时，permutation就不能自动证明了 *)
Example exlst4 : Permutation [2;7;3;4;5] [3;2;7;4;5].
Fail constructor.
Abort.

(** Unit to list *)
Fixpoint u2list (u : Unit) : list UnitBasic :=
  match u with
  | ub b => [b]
  | / u0 => []
  | u1 * u2 => match u1, u2 with
    | _, _ => (u2list u1) ++ (u2list u2)
    end
  end.

Eval compute in u2list ($ka * $kb * $kc * $ka).

(* 向 list UnitBasic 插入元素，自动规范化。 *)
Fixpoint ulinsert (ls : list UnitBasic) (u2 : UnitBasic) 
  : list UnitBasic :=
  match ls with
  | [] => [u2]
  | u1 :: tl => match u1, u2 with
    | 1, 1 => ls
    | 1, _ => u1 :: (ulinsert tl u2)
    | _, 1 => ls
    | $k1, $k2 => if (leb k1 k2)
      then u1 :: (ulinsert tl u2)
      else u2 :: (ulinsert tl u1)
    | $k1, $'k2 => if (Nat.eqb k1 k2)
      then tl
      else if (leb k1 k2)
        then u1 :: (ulinsert tl u2)
        else u2 :: (ulinsert tl u1)
    | $'k1, $k2 => if (Nat.eqb k1 k2)
      then tl
      else if (leb k1 k2)
        then u1 :: (ulinsert tl u2)
        else u2 :: (ulinsert tl u1)
    | $'k1, $'k2 => if (leb k1 k2)
      then u1 :: (ulinsert tl u2)
      else u2 :: (ulinsert tl u1)
    end
  end.

Example ul1 : list UnitBasic := [].
Example ul2 := Eval compute in ulinsert ul1 $'kc. Print ul2.
Example ul3 := Eval compute in ulinsert ul2 $'kb. Print ul3.
Example ul4 := Eval compute in ulinsert ul3 $ka. Print ul4.
Example ul5 := Eval compute in ulinsert ul4 $kb. Print ul5.
Example ul6 := Eval compute in ulinsert ul5 $ka. Print ul6. (* 高次还是有问题，
  所以，下一步，我们将次数抽象出来。 *)

(* 将 UnitBasic 构造成 Unit *)
Fixpoint list2u (ls : list UnitBasic) : Unit :=
  match ls with
  | [] => 1
  | [hd] => hd
  | hd :: tl => (list2u tl) * hd
  end.

Eval compute in list2u [$ka;$ka;$kb;$kb;$kc].
(* ？这里处理的不好，需要处理成 左结合！ *)

(* 可以换个思路，由于 list 难于处理成左结合，
  可以进行 rev 操作一次，
  还可以对原始数据构造时就逆着构造。
*)
Eval compute in list2u (rev [$ka;$ka;$kb;$kb;$kc]).


(** 以下是临时代码，不再使用 *)

(* 问题，写一个递归函数，判断两个 Unit 是否相等 *)
(* 1. 乘法是可以交换，可以结合的
   2. 1可以任意多次的相乘
   
   例如： 
    $ka * $kb * 1 / $kb 
    = $ka 
    = 1 * $ka 
    = $ka * 1 * 1
    = ($ka * 1) * (1 * 1)
    
  参考：perm, 可以把乘法的语法树转换成 list，然后判断两个 list 是否同排列
*)
Check Unit.
(* Fixpoint ueq (u1 u2 : Unit) : bool :=
  match u1 with
  | 1 => match u2 with 
    | 1 => true 
    | _ => false 
    end
  | _ => false
  end.
  | $k1 => match u2 with 
    | $k2 => kind_beq k1 k2 
    | _ => false 
    end
  | _ => false
  end.
  | / u10 => match u2 with
    | / u20 => ueq u10 u20
    | _ => false 
    end
  | _ => false
  end.
  | u11 * u12 => match u2 with
    | u21 * u22 => andb (ueq u11 u21) (ueq u12 u22)
    | _  => false
    end
  end.
  . *)
