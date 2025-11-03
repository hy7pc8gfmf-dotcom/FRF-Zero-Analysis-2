(* SelfContainedLib/Geometry.v *)
From Coq Require Import Utf8.
From Coq Require Import Arith.Arith.

Open Scope nat_scope. (* 核心修复：打开nat作用域，确保nat被正确解析为类型而非Set *)

Module Type BasicGeometry.
  Parameter Point : Type.
  Parameter distance : Point -> Point -> nat.
  Parameter collinear : Point -> Point -> Point -> Prop.
End BasicGeometry.

Module DiscreteGeometry <: BasicGeometry.
  Definition Point := nat * nat. (* 修复后：nat正确解析为具体类型，而非Set *)
  Definition distance (p q : Point) : nat :=
    let (x1, y1) := p in
    let (x2, y2) := q in
    Nat.max (Nat.abs (x2 - x1)) (Nat.abs (y2 - y1)).
    
  Definition collinear (p q r : Point) : Prop :=
    let (x1, y1) := p in
    let (x2, y2) := q in
    let (x3, y3) := r in
    (x2 - x1) * (y3 - y1) = (x3 - x1) * (y2 - y1).
End DiscreteGeometry.

Theorem geometry_test : DiscreteGeometry.distance (0, 0) (3, 4) = 4.
Proof. reflexivity. Qed.