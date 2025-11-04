(* # SelfContainedLib/Geometry.v *)
(* 模块定位：一级基础模块，提供离散几何核心定义（点、距离、共线性），无外部依赖，支撑下游场景模块 *)
From Coq Require Import Utf8.
From Coq Require Import Arith.Arith.

(* ======================== 核心定义 ======================== *)
Module Type BasicGeometry.
  Parameter Point : Type.
  Parameter distance : Point -> Point -> nat.
  Parameter collinear : Point -> Point -> Point -> Prop.
End BasicGeometry.

Module DiscreteGeometry <: BasicGeometry.
  (* 使用显式类型注释避免解析歧义 *)
  Definition Point : Type := prod nat nat.
  
  Definition distance (p q : Point) : nat :=
    match p, q with
    | (x1, y1), (x2, y2) =>
        Nat.max (Nat.abs (x2 - x1)) (Nat.abs (y2 - y1))
    end.
    
  Definition collinear (p q r : Point) : Prop :=
    match p, q, r with
    | (x1, y1), (x2, y2), (x3, y3) =>
        (x2 - x1) * (y3 - y1) = (x3 - x1) * (y2 - y1)
    end.
End DiscreteGeometry.

(* ======================== 验证定理 ======================== *)
Theorem geometry_test : DiscreteGeometry.distance (0, 0) (3, 4) = 4.
Proof. reflexivity. Qed.

(* ======================== 模块导出 ======================== *)
Export BasicGeometry DiscreteGeometry geometry_test.