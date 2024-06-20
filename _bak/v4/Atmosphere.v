(*
  Atmosphere parameters relation
  
  1. 大气中的关系式推导过程
*)

Require Import Quantity.


(* 国际标准大气 (International Standard Atmosphere, ISA),
 人为规定的一个不变的大气环境。
 由来：飞机及发动机的性能取决于气体的气压、密度和气温，飞机的最大速度、爬升率和升限等都会
 随气压、密度和温度发生改变，并随着高度层和时间的不同而不同，因此，同一架飞机在不同地点、
 不同高度、不同季节或时间做飞行试验会得到不同的结果。
 为便于比较飞机的飞行性能，必须以一定的大气状态作为衡量的标准。*)

Module ISA.
  (** ** 标准大气 *)
    
  (** 标准海平面 *)
  Definition H0 := 0 & 'm.
  
  (** 标准空气温度 *)
  Definition T0 := 288.15 & 'K.
  
  (** 标准大气压强 *)
  Definition p0 := 101325 & 'Pa.
  
  (** 标准空气密度 *)
  Definition ρ0 := 1.225 & ('kg/'m³).
  
  (** * 标准温度分布规律 *)
  
  (** 不同的高度类型 *)
  Inductive HeightType : Set :=
    | HT_NotSupport             (* 不支持的类型 *)
    | HT_Troposphere            (* 对流层（0-11km) *)
    | HT_Stratosphere_le20      (* 平流层 (1-20km) *)
    | HT_Stratosphere_le32      (* 平流层 (20-32km) *)
    .
  
  (** 将高度转换为高度类型 *)
  Definition HeightType_ofH (h : Quantity) : HeightType :=
    match h with
    | Qinvalid => HT_NotSupport
    | Qbasic r u =>
      if (Unit_beq u 'km) 
      then 
        if (r <? 0) 
        then HT_NotSupport
        else
          if (r <=? 11)
          then HT_Troposphere
          else
            if (r <=? 20)
            then HT_Stratosphere_le20
            else
              if (r <=? 32)
              then HT_Stratosphere_le32
              else HT_NotSupport
      else HT_NotSupport
    end.
    
  Compute HeightType_ofH (0 & 'km).

  (** 温度递减规律 *)
  (* 
    在对流层：每上升1km，温度下降 6.5℃
    在平流层(11-20km)：温度保持常数
    在平流层(20-32km)：高度每上升1km，温度上升1℃
   *)
  Open Scope Quantity_scope.
  Definition T (h : Quantity) : Quantity :=
    let ht := HeightType_ofH h in
      match ht with
      | HT_NotSupport => Qinvalid
      | HT_Troposphere => T0 - (0.0065 & ('K/'km)) * h
      | HT_Stratosphere_le20 => 216.65 & 'K
      | HT_Stratosphere_le32 => 216.65 & 'K + (0.001&('K/'km)) * (h - 20000&'km)
      end.
  Print T.
  (** 压强公式、密度公式的推导 *)
  
  (** 需要用到微分 *)
  Definition Qfun := Quantity -> Quantity.
  Parameter Qdifferential : Qfun -> Qfun.
End ISA.

Require Import Extraction.

Recursive Extraction ISA.T.


Import ISA.
