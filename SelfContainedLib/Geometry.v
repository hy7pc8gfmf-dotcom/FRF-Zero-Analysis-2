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
  Definition Point := nat * nat.
  
  Definition distance (p q : Point) : nat :=
    let (x1, y1) := p in
    let (x2, y2) := q in
    Nat.max (Nat.abs (Nat.sub x2 x1)) (Nat.abs (Nat.sub y2 y1)).
    
  Definition collinear (p q r : Point) : Prop :=
    let (x1, y1) := p in
    let (x2, y2) := q in
    let (x3, y3) := r in
    Nat.mul (Nat.sub x2 x1) (Nat.sub y3 y1) = Nat.mul (Nat.sub x3 x1) (Nat.sub y2 y1).
End DiscreteGeometry.

(* ======================== 验证定理 ======================== *)
Theorem geometry_test : DiscreteGeometry.distance (0, 0) (3, 4) = 4.
Proof. reflexivity. Qed.

(* ======================== 模块导出 ======================== *)
Export BasicGeometry DiscreteGeometry geometry_test.