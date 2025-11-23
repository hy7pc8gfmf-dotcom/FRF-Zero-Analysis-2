(* SelfContainedLib/Geometry.v *)
From Coq Require Import Utf8.
From Coq Require Import Arith.Arith.

Module Type BasicGeometry.
  Parameter Point : Type.
  Parameter distance : Point -> Point -> nat.
  Parameter collinear : Point -> Point -> Point -> Prop.
End BasicGeometry.

Module DiscreteGeometry <: BasicGeometry.
  (* 首先定义具体的点类型 *)
  Inductive ConcretePoint : Type :=
  | make_point : nat -> nat -> ConcretePoint.

  (* 然后将模块类型中的Parameter映射到这个具体类型 *)
  Definition Point := ConcretePoint.

  Definition abs_diff (a b : nat) : nat :=
    if a <=? b then b - a else a - b.

  Definition distance (p q : Point) : nat :=
    match p, q with
    | make_point x1 y1, make_point x2 y2 =>
        Nat.max (abs_diff x1 x2) (abs_diff y1 y2)
    end.

  Definition collinear (p q r : Point) : Prop :=
    match p, q, r with
    | make_point x1 y1, make_point x2 y2, make_point x3 y3 =>
        (x2 - x1) * (y3 - y1) = (x3 - x1) * (y2 - y1)
    end.

End DiscreteGeometry.

Theorem geometry_test :
  let p := DiscreteGeometry.make_point 0 0 in
  let q := DiscreteGeometry.make_point 3 4 in
  DiscreteGeometry.distance p q = 4.
Proof. reflexivity. Qed.