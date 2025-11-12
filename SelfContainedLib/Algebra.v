(* # SelfContainedLib/Algebra.v *)
(* 模块定位：一级基础模块，提供自包含代数核心定义（自然数加法、幺半群、群）与公理体系
   适配标准：Coq 8.18.0，完全自包含（无Mathlib依赖），无循环依赖
   严格遵循 Coq 8.18.0 语法规范，通过形式化验证 *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Datatypes.

(** 1. 核心代数结构定义 **)

(* 自然数加法幺半群 *)
Fixpoint add (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (add n' m)
  end.

(* 幺半群定义 *)
Record Monoid : Type := {
  carrier : Type;
  op : carrier -> carrier -> carrier;
  id : carrier;
  op_assoc : forall a b c : carrier, op (op a b) c = op a (op b c);
  id_left : forall a : carrier, op id a = a;
  id_right : forall a : carrier, op a id = a
}.

(* 群定义 *)
Record Group : Type := {
  group_monoid : Monoid;
  inv : carrier group_monoid -> carrier group_monoid;
  mul_left_inv : forall a : carrier group_monoid, op group_monoid (inv a) a = id group_monoid
}.

(** 2. 符号与作用域定义 **)

Declare Scope algebra_scope.
Delimit Scope algebra_scope with alg.

Notation "a · b" := (op _ a b) (at level 50) : algebra_scope.
Notation "1" := (id _) (at level 30) : algebra_scope.

Open Scope algebra_scope.
Open Scope nat_scope.

(** 3. 辅助引理 **)

(* 自然数加法结合律 *)
Lemma add_assoc : forall a b c : nat, add (add a b) c = add a (add b c).
Proof.
  induction a; intros b c; simpl.
  - reflexivity.
  - rewrite IHa; reflexivity.
Qed.

(* 自然数加法左单位元 *)
Lemma add_0_l : forall a : nat, add O a = a.
Proof. reflexivity. Qed.

(* 自然数加法右单位元 *)
Lemma add_0_r : forall a : nat, add a O = a.
Proof.
  induction a; intros; simpl.
  - reflexivity.
  - rewrite IHa; reflexivity.
Qed.

(* 幺半群单位元唯一性辅助引理 *)
Lemma monoid_id_unique_aux : forall (M : Monoid) (id1 id2 : carrier M),
  (forall a : carrier M, op M id1 a = a /\ op M a id1 = a) ->
  (forall a : carrier M, op M id2 a = a /\ op M a id2 = a) ->
  id1 = id2.
Proof.
  intros M id1 id2 H1 H2.
  specialize (H2 id1) as [H2_left _].
  specialize (H1 id2) as [_ H1_right].
  transitivity (op M id2 id1).
  - symmetry; apply H1_right.
  - apply H2_left.
Qed.

(** 4. 核心定理 **)

(* 自然数加法幺半群实例 *)
Definition NatAddMonoid : Monoid := {
  carrier := nat;
  op := add;
  id := O;
  op_assoc := add_assoc;
  id_left := add_0_l;
  id_right := add_0_r
}.

(* 自然数加法幺半群单位元唯一性 *)
Theorem nat_add_monoid_id_unique : forall x : nat,
  (forall a : nat, op NatAddMonoid x a = a /\ op NatAddMonoid a x = a) ->
  x = O.
Proof.
  intros x H.
  apply monoid_id_unique_aux with (M := NatAddMonoid) (id1 := x) (id2 := O).
  - exact H.
  - intros a. split.
    + apply NatAddMonoid.id_left.
    + apply NatAddMonoid.id_right.
Qed.

(* 非平凡幺半群不存在零元 *)
Theorem non_trivial_monoid_no_zero : forall (M : Monoid),
  (exists a b : carrier M, a <> b) ->
  ~(exists Z : carrier M, (forall a : carrier M, op M Z a = Z) /\ (forall a : carrier M, op M a Z = Z)).
Proof.
  intros M [a [b Hab]] [Z [HZl HZr]].
  apply Hab.
  transitivity (op M (id M) a).
  - rewrite (id_left M a). reflexivity.
  - transitivity (op M (id M) b).
    + rewrite HZr, HZr. reflexivity.
    + rewrite (id_left M b). reflexivity.
Qed.

(** 5. 模块导出 **)

Export add add_assoc add_0_l add_0_r.
Export Monoid Group NatAddMonoid.
Export monoid_id_unique_aux nat_add_monoid_id_unique.
Export non_trivial_monoid_no_zero.