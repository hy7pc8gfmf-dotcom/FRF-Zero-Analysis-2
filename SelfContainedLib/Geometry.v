(* SelfContainedLib/Geometry.v *)

From Coq Require Import Utf8.
From Coq Require Import Reals.
From Coq Require Import Psatz.

(** 几何基础模块 *)

(** 二维点定义 *)
Record Point : Type := {
  x : R;
  y : R
}.

(** 二维向量定义 *)
Record Vector : Type := {
  vx : R;
  vy : R
}.

(** 线段定义 *)
Record Segment : Type := {
  start : Point;
  end_ : Point
}.

(** 三角形定义 *)
Record Triangle : Type := {
  vertexA : Point;
  vertexB : Point;
  vertexC : Point
}.

(** 几何运算模块类型 *)
Module Type BasicGeometry.
  Parameter Point : Type.
  Parameter Vector : Type.
  
  (* 基本构造 *)
  Parameter origin : Point.
  Parameter make_point : R -> R -> Point.
  Parameter make_vector : R -> R -> Vector.
  
  (* 向量运算 *)
  Parameter vector_add : Vector -> Vector -> Vector.
  Parameter vector_scale : R -> Vector -> Vector.
  Parameter vector_dot : Vector -> Vector -> R.
  Parameter vector_cross : Vector -> Vector -> R.
  Parameter vector_norm : Vector -> R.
  
  (* 点与向量运算 *)
  Parameter point_to_vector : Point -> Vector.
  Parameter vector_to_point : Vector -> Point.
  Parameter point_add_vector : Point -> Vector -> Point.
  
  (* 距离和度量 *)
  Parameter distance : Point -> Point -> R.
  Parameter midpoint : Point -> Point -> Point.
  
  (* 几何关系 *)
  Parameter collinear : Point -> Point -> Point -> Prop.
  Parameter perpendicular : Vector -> Vector -> Prop.
  Parameter parallel : Vector -> Vector -> Prop.
  
  (* 公理和定理 *)
  Axiom distance_symmetric : forall p q, distance p q = distance q p.
  Axiom distance_nonnegative : forall p q, distance p q >= 0.
  Axiom distance_zero : forall p q, distance p q = 0 <-> p = q.
  Axiom triangle_inequality : 
    forall p q r, distance p r <= distance p q + distance q r.
  
  Axiom vector_add_comm : forall u v, vector_add u v = vector_add v u.
  Axiom vector_add_assoc : forall u v w, 
    vector_add (vector_add u v) w = vector_add u (vector_add v w).
  
  Axiom dot_product_comm : forall u v, vector_dot u v = vector_dot v u.
  Axiom cross_product_antisym : forall u v, vector_cross u v = - vector_cross v u.
End BasicGeometry.

(** 二维欧几里得几何实现 *)
Module Euclidean2DGeometry <: BasicGeometry.
  Definition Point := Point.
  Definition Vector := Vector.
  
  Definition origin : Point := {| x := 0; y := 0 |}.
  
  Definition make_point (a b : R) : Point := {| x := a; y := b |}.
  
  Definition make_vector (a b : R) : Vector := {| vx := a; vy := b |}.
  
  Definition vector_add (u v : Vector) : Vector :=
    {| vx := vx u + vx v; vy := vy u + vy v |}.
  
  Definition vector_scale (k : R) (v : Vector) : Vector :=
    {| vx := k * vx v; vy := k * vy v |}.
  
  Definition vector_dot (u v : Vector) : R :=
    vx u * vx v + vy u * vy v.
  
  Definition vector_cross (u v : Vector) : R :=
    vx u * vy v - vy u * vx v.
  
  Definition vector_norm (v : Vector) : R :=
    sqrt (vector_dot v v).
  
  Definition point_to_vector (p : Point) : Vector :=
    {| vx := x p; vy := y p |}.
  
  Definition vector_to_point (v : Vector) : Point :=
    {| x := vx v; y := vy v |}.
  
  Definition point_add_vector (p : Point) (v : Vector) : Point :=
    {| x := x p + vx v; y := y p + vy v |}.
  
  Definition distance (p q : Point) : R :=
    sqrt ((x q - x p) ^ 2 + (y q - y p) ^ 2).
  
  Definition midpoint (p q : Point) : Point :=
    {| x := (x p + x q) / 2; y := (y p + y q) / 2 |}.
  
  Definition collinear (p q r : Point) : Prop :=
    vector_cross (point_to_vector {| x := x q - x p; y := y q - y p |})
                (point_to_vector {| x := x r - x p; y := y r - y p |}) = 0.
  
  Definition perpendicular (u v : Vector) : Prop :=
    vector_dot u v = 0.
  
  Definition parallel (u v : Vector) : Prop :=
    vector_cross u v = 0.
  
  Lemma distance_symmetric : forall p q, distance p q = distance q p.
  Proof.
    intros p q.
    unfold distance.
    f_equal.
    - ring.
    - ring.
  Qed.
  
  Lemma distance_nonnegative : forall p q, distance p q >= 0.
  Proof.
    intros p q.
    unfold distance.
    apply sqrt_pos.
  Qed.
  
  Lemma distance_zero : forall p q, distance p q = 0 <-> p = q.
  Proof.
    intros p q.
    unfold distance.
    split.
    - intro H.
      apply sqrt_eq_0 in H.
      + assert (Hx : (x q - x p) ^ 2 = 0).
        * nra.
        * assert (Hy : (y q - y p) ^ 2 = 0).
          -- nra.
          -- destruct p as [px py], q as [qx qy].
          simpl in *.
          f_equal; nra.
      + nra.
    - intro H.
      rewrite H.
      simpl.
      compute.
      reflexivity.
  Qed.
  
  Lemma triangle_inequality : 
    forall p q r, distance p r <= distance p q + distance q r.
  Proof.
    intros p q r.
    unfold distance.
    (* 使用柯西-施瓦茨不等式和平方和展开 *)
    set (a := x q - x p).
    set (b := y q - y p).
    set (c := x r - x q).
    set (d := y r - y q).
    replace (x r - x p) with (a + c) by (unfold a, c; ring).
    set (e := y r - y p).
    replace e with (b + d) by (unfold b, d, e; ring).
    rewrite <- sqrt_mult.
    - apply sqrt_le_1_alt.
      rewrite <- Rsqr_plus.
      apply Rsqr_incr_1.
      + nra.
      + rewrite <- sqrt_Rsqr_abs.
        * apply Rle_trans with (sqrt (a^2 + b^2) + sqrt (c^2 + d^2).
          -- apply Rplus_le_compat; apply sqrt_Rsqr_abs; nra.
          -- nra.
        * apply Rabs_pos.
    - nra.
    - nra.
  Qed.
  
  Lemma vector_add_comm : forall u v, vector_add u v = vector_add v u.
  Proof.
    intros u v.
    destruct u as [ux uy], v as [vx vy].
    unfold vector_add.
    f_equal; ring.
  Qed.
  
  Lemma vector_add_assoc : forall u v w, 
    vector_add (vector_add u v) w = vector_add u (vector_add v w).
  Proof.
    intros u v w.
    destruct u as [ux uy], v as [vx vy], w as [wx wy].
    unfold vector_add.
    f_equal; ring.
  Qed.
  
  Lemma dot_product_comm : forall u v, vector_dot u v = vector_dot v u.
  Proof.
    intros u v.
    destruct u as [ux uy], v as [vx vy].
    unfold vector_dot.
    ring.
  Qed.
  
  Lemma cross_product_antisym : forall u v, vector_cross u v = - vector_cross v u.
  Proof.
    intros u v.
    destruct u as [ux uy], v as [vx vy].
    unfold vector_cross.
    ring.
  Qed.
End Euclidean2DGeometry.

(** 圆定义 *)
Record Circle : Type := {
  center : Point;
  radius : R
}.

(** 矩形定义 *)
Record Rectangle : Type := {
  bottom_left : Point;
  top_right : Point
}.

(** 几何变换模块 *)
Module Type GeometricTransformations.
  Parameter translate : Vector -> Point -> Point.
  Parameter rotate : R -> Point -> Point -> Point.
  Parameter reflect : Point -> Point -> Point -> Point.
  
  Axiom translation_preserves_distance : 
    forall v p q, Euclidean2DGeometry.distance (translate v p) (translate v q) = 
    Euclidean2DGeometry.distance p q.
  
  Axiom rotation_preserves_distance : 
    forall angle center p q, 
    Euclidean2DGeometry.distance (rotate angle center p) (rotate angle center q) = 
    Euclidean2DGeometry.distance p q.
End GeometricTransformations.

Module EuclideanTransformations <: GeometricTransformations.
  Definition translate (v : Vector) (p : Point) : Point :=
    Euclidean2DGeometry.point_add_vector p v.
  
  Definition rotate (angle : R) (center : Point) (p : Point) : Point :=
    let dx := x p - x center in
    let dy := y p - y center in
    let cos_a := cos angle in
    let sin_a := sin angle in
    {| x := x center + dx * cos_a - dy * sin_a;
       y := y center + dx * sin_a + dy * cos_a |}.
  
  Definition reflect (line_p1 line_p2 : Point) (p : Point) : Point :=
    (* 简化实现：关于x轴反射 *)
    {| x := x p; y := - y p |}.
  
  Lemma translation_preserves_distance : 
    forall v p q, Euclidean2DGeometry.distance (translate v p) (translate v q) = 
    Euclidean2DGeometry.distance p q.
  Proof.
    intros v p q.
    destruct p as [px py], q as [qx qy], v as [vx vy].
    unfold translate, Euclidean2DGeometry.point_add_vector, Euclidean2DGeometry.distance.
    simpl.
    f_equal; ring.
  Qed.
  
  Lemma rotation_preserves_distance : 
    forall angle center p q, 
    Euclidean2DGeometry.distance (rotate angle center p) (rotate angle center q) = 
    Euclidean2DGeometry.distance p q.
  Proof.
    intros angle center p q.
    destruct p as [px py], q as [qx qy], center as [cx cy].
    unfold rotate, Euclidean2DGeometry.distance.
    simpl.
    set (dx1 := px - cx).
    set (dy1 := py - cy).
    set (dx2 := qx - cx).
    set (dy2 := qy - cy).
    repeat rewrite Rmult_plus_distr_r.
    repeat rewrite Rmult_plus_distr_l.
    rewrite <- Rplus_assoc.
    f_equal.
    (* 使用三角恒等式：cos² + sin² = 1 *)
    rewrite <- (cos2 angle + sin2 angle) at 1.
    ring_simplify.
    f_equal.
    - rewrite Rmult_1_r.
      ring.
    - rewrite Rmult_1_r.
      ring.
  Qed.
End EuclideanTransformations.

(** 几何定理证明 *)

Section GeometryTheorems.
  Import Euclidean2DGeometry.
  
  (** 中点定理 *)
  Lemma midpoint_theorem : forall p q,
    distance p (midpoint p q) = distance (midpoint p q) q.
  Proof.
    intros p q.
    destruct p as [px py], q as [qx qy].
    unfold distance, midpoint.
    simpl.
    f_equal; field.
  Qed.
  
  (** 等腰三角形定理 *)
  Lemma isosceles_triangle_theorem : 
    forall A B C,
    distance A B = distance A C ->
    collinear A B C = False ->
    exists M, distance B M = distance C M /\ collinear A M B.
  Proof.
    intros A B C Hdist Hnot_coll.
    destruct A as [ax ay], B as [bx by], C as [cx cy].
    unfold distance, midpoint, collinear, point_to_vector, vector_cross in *.
    simpl in *.
    (* 简化假设 *)
    assert (H : (bx - ax) ^ 2 + (by - ay) ^ 2 = (cx - ax) ^ 2 + (cy - ay) ^ 2).
    { simpl in Hdist. nra. }
    exists (midpoint A B).
    split.
    - unfold distance, midpoint.
      simpl.
      f_equal; field.
    - unfold collinear, point_to_vector, vector_cross.
      simpl.
      (* 由于A, B, C不共线，中点M在AB上 *)
      ring_simplify.
      reflexivity.
  Qed.
  
  (** 勾股定理 *)
  Theorem pythagorean_theorem : 
    forall A B C,
    let vAB := make_vector (x B - x A) (y B - y A) in
      let vAC := make_vector (x C - x A) in
      perpendicular vAB vAC ->
    distance B C ^ 2 = distance A B ^ 2 + distance A C ^ 2.
  Proof.
    intros A B C vAB vAC Hperp.
    destruct A as [ax ay], B as [bx by], C as [cx cy].
    unfold distance, perpendicular, vector_dot in *.
    simpl in *.
    nra.
  Qed.
  
  (** 平行四边形对角线定理 *)
  Lemma parallelogram_diagonals : 
    forall A B C D,
    let vAB := make_vector (x B - x A) (y B - y A) in
      let vDC := make_vector (x C - x D) (y C - y D) in
      vector_add (point_to_vector A) (point_to_vector C) = 
      vector_add (point_to_vector B) (point_to_vector D) ->
    midpoint A C = midpoint B D.
  Proof.
    intros A B C D vAB vDC H.
    destruct A as [ax ay], B as [bx by], C as [cx cy], D as [dx dy].
    unfold midpoint.
    f_equal; simpl; field.
  Qed.
End GeometryTheorems.

(** 导出模块 *)
Export Euclidean2DGeometry.
Export EuclideanTransformations.