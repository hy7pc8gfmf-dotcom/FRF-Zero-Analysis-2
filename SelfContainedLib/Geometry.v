(* # SelfContainedLib/Geometry.v *)
(* 完全自包含的离散几何模块，无外部依赖 *)

(* ======================== 基础定义 ======================== *)

(* 定义点为一对自然数 *)
Inductive Point : Type :=
| point : nat -> nat -> Point.

(* 获取点的x坐标 *)
Definition get_x (p : Point) : nat :=
  match p with
  | point x _ => x
  end.

(* 获取点的y坐标 *)
Definition get_y (p : Point) : nat :=
  match p with
  | point _ y => y
  end.

(* 自然数小于等于比较 *)
Fixpoint leb (n m : nat) : bool :=
  match n, m with
  | O, _ => true
  | S _, O => false
  | S n', S m' => leb n' m'
  end.

(* 绝对值差函数 *)
Definition abs_diff (a b : nat) : nat :=
  if leb a b then b - a else a - b.

(* 最大值函数 *)
Definition max (a b : nat) : nat :=
  if leb a b then b else a.

(* ======================== 几何操作 ======================== *)

(* 距离函数：切比雪夫距离 *)
Definition distance (p q : Point) : nat :=
  let x1 := get_x p in
  let y1 := get_y p in
  let x2 := get_x q in
  let y2 := get_y q in
  max (abs_diff x1 x2) (abs_diff y1 y2).

(* 共线性判断 *)
Definition collinear (p q r : Point) : Prop :=
  let x1 := get_x p in
  let y1 := get_y p in
  let x2 := get_x q in
  let y2 := get_y q in
  let x3 := get_x r in
  let y3 := get_y r in
  (x2 - x1) * (y3 - y1) = (x3 - x1) * (y2 - y1).

(* ======================== 验证 ======================== *)

(* 创建点 (0,0) 和 (3,4) *)
Definition origin : Point := point 0 0.
Definition test_point : Point := point 3 4.

(* 验证距离计算 *)
Theorem geometry_test : distance origin test_point = 4.
Proof.
  simpl. reflexivity.
Qed.

(* ======================== 模块接口 ======================== *)

Module Type BasicGeometry.
  Parameter Point : Type.
  Parameter distance : Point -> Point -> nat.
  Parameter collinear : Point -> Point -> Point -> Prop.
End BasicGeometry.

Module DiscreteGeometry <: BasicGeometry.
  Definition Point := Point.
  Definition distance := distance.
  Definition collinear := collinear.
End DiscreteGeometry.

(* ======================== 导出 ======================== *)
Export DiscreteGeometry geometry_test.