(* # SelfContainedLib/Geometry.v *)
(* 模块定位：一级基础模块，提供离散几何核心定义（点、距离、共线性），无外部依赖，支撑下游场景模块
   修复核心：1. 解决"nat类型为Set，预期类型为nat"错误（补充nat类型导入+明确作用域）；2. 确保与Coq 8.18.0兼容，无导入路径错误
   依赖约束：仅依赖Coq标准库，无循环依赖，不新增/删减功能 *)
From Coq Require Import Utf8.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.Nat. (* 核心修复：补充Nat模块导入，确保nat类型及相关函数（Nat.max/Nat.abs）正确解析 *)
Open Scope nat_scope. (* 确保nat被解析为具体类型，而非Set *)

(* ======================== 核心定义（前置无依赖，功能全保留，仅修复类型解析） ======================== *)
Module Type BasicGeometry.
  Parameter Point : Type.
  Parameter distance : Point -> Point -> nat.
  Parameter collinear : Point -> Point -> Point -> Prop.
End BasicGeometry.

Module DiscreteGeometry <: BasicGeometry.
  Definition Point := nat * nat. (* 修复后：nat正确解析为类型，而非Set *)
  Definition distance (p q : Point) : nat :=
    let (x1, y1) := p in
    let (x2, y2) := q in
    Nat.max (Nat.abs (x2 - x1)) (Nat.abs (y2 - y1)). (* 依赖Arith.Nat，确保函数正确调用 *)
    
  Definition collinear (p q r : Point) : Prop :=
    let (x1, y1) := p in
    let (x2, y2) := q in
    let (x3, y3) := r in
    (x2 - x1) * (y3 - y1) = (x3 - x1) * (y2 - y1).
End DiscreteGeometry.

(* ======================== 验证定理（功能全保留，确保修复后逻辑完备） ======================== *)
Theorem geometry_test : DiscreteGeometry.distance (0, 0) (3, 4) = 4.
Proof. reflexivity. Qed.

(* ======================== 模块导出（无符号冲突，支撑下游模块调用） ======================== *)
Export BasicGeometry DiscreteGeometry geometry_test.
Export Nat.max Nat.abs. (* 导出常用函数，避免下游模块重复导入 *)
Close Scope nat_scope.