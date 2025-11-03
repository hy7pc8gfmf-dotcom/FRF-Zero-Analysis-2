(* SelfContainedLib/Geometry.v *)
From Coq Require Import Utf8.
From Coq Require Import Arith.Arith.

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
    Nat.max (Nat.abs (x2 - x1)) (Nat.abs (y2 - y1)).
    
  Definition collinear (p q r : Point) : Prop :=
    let (x1, y1) := p in
    let (x2, y2) := q in
    let (x3, y3) := r in
    (x2 - x1) * (y3 - y1) = (x3 - x1) * (y2 - y1).
End DiscreteGeometry.

Theorem geometry_test : DiscreteGeometry.distance (0, 0) (3, 4) = 4.
Proof. reflexivity. Qed.