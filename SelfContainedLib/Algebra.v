(* # SelfContainedLib/Algebra.v *)
(* 模块定位：一级基础模块，提供自包含代数核心定义（自然数加法、幺半群、群）与公理体系
适配标准：Coq 8.18.0，完全自包含（无Mathlib依赖），无循环依赖 *)

(* 仅导入最基础的Coq标准库模块 *)
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Datatypes.

(* ======================== 核心定义（完全自包含） ======================== *)

(* 1. 自然数加法 *)
Fixpoint add (n m : nat) : nat := 
  match n with
  | O => m
  | S n' => S (add n' m)
  end.

(* 2. 幺半群定义 *)
Record Monoid : Type := {
  carrier : Type;
  op : carrier -> carrier -> carrier;
  id : carrier;
  op_assoc : forall a b c : carrier, op (op a b) c = op a (op b c);
  id_left : forall a : carrier, op id a = a;
  id_right : forall a : carrier, op a id = a
}.

(* 3. 群定义 *)
Record Group : Type := {
  group_monoid : Monoid;
  inv : carrier group_monoid -> carrier group_monoid;
  mul_left_inv : forall a : carrier group_monoid, op group_monoid (inv a) a = id group_monoid
}.

(* 符号记法 *)
Declare Scope algebra_scope.
Delimit Scope algebra_scope with alg.
Notation "a · b" := (op _ a b) (at level 50) : algebra_scope.
Notation "1" := (id _) (at level 30) : algebra_scope.
Open Scope algebra_scope.
Open Scope nat_scope.

(* ======================== 辅助引理 ======================== *)

Lemma add_assoc : forall a b c : nat, add (add a b) c = add a (add b c).
Proof.
  induction a; intros b c; simpl.
  - reflexivity.
  - rewrite IHa; reflexivity.
Qed.

Lemma add_0_l : forall a : nat, add O a = a.
Proof. reflexivity. Qed.

Lemma add_0_r : forall a : nat, add a O = a.
Proof.
  induction a; intros; simpl.
  - reflexivity.
  - rewrite IHa; reflexivity.
Qed.

(* 修复 monoid_id_unique_aux 证明 *)
Lemma monoid_id_unique_aux : forall (M : Monoid) (id2 id1 : carrier M), 
  (forall a : carrier M, op M id2 a = a /\ op M a id2 = a) ->
  (forall a : carrier M, op M id1 a = a /\ op M a id1 = a) ->
  id2 = id1.
Proof.
  intros M id2 id1 H2 H1.
  (* 使用正确的字段访问语法 *)
  specialize (H2 id1) as [H2_left _].
  specialize (H1 id2) as [_ H1_right].
  (* 现在可以直接使用这些等式 *)
  transitivity (op M id2 id1).
  - symmetry; exact H1_right.
  - exact H2_left.
Qed.

(* ======================== 核心定理 ======================== *)

Definition NatAddMonoid : Monoid := {|
  carrier := nat;
  op := add;
  id := O;
  op_assoc := add_assoc;
  id_left := add_0_l;
  id_right := add_0_r
|}.

Theorem nat_add_monoid_id_unique : forall x : nat, 
  (forall a : nat, op NatAddMonoid x a = a /\ op NatAddMonoid a x = a) -> 
  x = O.
Proof.
  intros x H.
  apply monoid_id_unique_aux with (M := NatAddMonoid) (id2 := x) (id1 := O).
  - exact H.
  - intros a. split; [apply NatAddMonoid.(id_left) | apply NatAddMonoid.(id_right)].
Qed.

(* 修复 non_trivial_monoid_no_zero 证明 *)
Theorem non_trivial_monoid_no_zero : forall (M : Monoid),
  (exists a b : carrier M, a <> b) ->
  ~(exists Z : carrier M, (forall a : carrier M, op M Z a = Z) /\ (forall a : carrier M, op M a Z = Z)).
Proof.
  intros M [a b Hab] [Z [HZl HZr]].
  apply Hab.
  (* 使用幺半群公理 *)
  transitivity (op M (id M) a).
  - rewrite (id_left M a). reflexivity.
  - transitivity (op M (id M) b).
    + rewrite HZr, HZr. reflexivity.
    + rewrite (id_left M b). reflexivity.
Qed.

(* ======================== 模块导出 ======================== *)
(* 导出所有定义和定理供其他模块使用 *)
Export add add_assoc add_0_l add_0_r.
Export Monoid Group NatAddMonoid.
Export monoid_id_unique_aux nat_add_monoid_id_unique.
Export non_trivial_monoid_no_zero.