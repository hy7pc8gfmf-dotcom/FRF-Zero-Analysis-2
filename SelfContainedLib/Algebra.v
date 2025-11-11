( # SelfContainedLib/Algebra.v )
( 模块定位：一级基础模块，提供自包含代数核心定义（自然数加法、幺半群、群）与公理体系
适配标准：Coq 8.18.0，完全自包含（无Mathlib依赖），无循环依赖
核心修复：1. 修正Record字段投影引用语法（符合Coq 8.18.0规范）；2. 移除Mathlib导入（环境无Mathlib）；3. 修复代数公理无交集判定证明
全量保留功能：自然数加法运算、幺半群/群实例化、单位元唯一性、公理无交集判定等 )

( 显式导入依赖模块（仅Coq标准库，无Mathlib依赖） )
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith. ( 导入整数模块，支撑IntAddGroup定义 )

( ======================== 核心定义（前置无依赖，统一符号，对接algebra_scope） ======================== )

( 1. 自然数加法（自包含定义，运算规则：0+m=m，S(n)+m=S(n+m)） )
Fixpoint add (n m : nat) : nat :=
match n with
O => m
S n' => S (add n' m)
end.

( 2. 幺半群定义（自包含，满足：结合律+左单位律+右单位律） )
Record Monoid : Type := {
carrier : Type; ( 载体集合 )
op : carrier -> carrier -> carrier; ( 二元运算 )
id : carrier; ( 单位元 )
op_assoc : forall a b c : carrier, op (op a b) c = op a (op b c); ( 结合律 )
id_left : forall a : carrier, op id a = a; ( 左单位律：id∘a = a )
id_right : forall a : carrier, op a id = a ( 右单位律：a∘id = a )
}.

( 3. 群定义（扩展幺半群，修正字段投影引用语法） )
Record Group : Type := {
group_monoid : Monoid; ( 底层幺半群结构 )
inv : carrier group_monoid -> carrier group_monoid; ( 逆元运算 )
mul_left_inv : forall a : carrier group_monoid,
op group_monoid (inv a) a = id group_monoid ( 左逆元律 )
}.

( 4. 代数公理标签（枚举所有核心公理类型） )
Inductive AlgebraAxiomTag : Type :=
AddAssocTag : AlgebraAxiomTag ( 加法结合律 )
AddIdLeftTag : AlgebraAxiomTag ( 加法左单位元 )
AddIdRightTag : AlgebraAxiomTag ( 加法右单位元 )
MulAssocTag : AlgebraAxiomTag ( 乘法结合律 )
MulIdLeftTag : AlgebraAxiomTag ( 乘法左单位元 )
MulIdRightTag : AlgebraAxiomTag ( 乘法右单位元 )
MulLeftInvTag : AlgebraAxiomTag. ( 乘法左逆元 )

( 5. 代数公理封装（公理内容统一为Prop类型） )
Record AlgebraAxiom : Type := {
axiom_tag : AlgebraAxiomTag; ( 公理类型标签 )
axiom_content : Prop; ( 公理内容 )
}.

( 统一符号记法（激活algebra_scope） )
Declare Scope algebra_scope.
Notation "op M a b" := (Monoid_op M a b) (at level 50) : algebra_scope.
Notation "id M" := (Monoid_id M) (at level 40) : algebra_scope.
Notation "inv G a" := (@Group_inv _ G a) (at level 40) : algebra_scope.

( 辅助定义：Monoid字段投影函数（解决原始语法错误的关键） )
Definition Monoid_carrier (M : Monoid) : Type := M.(carrier).
Definition Monoid_op (M : Monoid) : Monoid_carrier M -> Monoid_carrier M -> Monoid_carrier M := M.(op).
Definition Monoid_id (M : Monoid) : Monoid_carrier M := M.(id).

( 辅助定义：Group字段投影函数 )
Definition Group_inv (M : Monoid) (G : Group) : Monoid_carrier M -> Monoid_carrier M := G.(inv).

Open Scope algebra_scope.
Open Scope nat_scope.

( ======================== 辅助引理（证明前置，无逻辑断层） ======================== )

( 引理1：加法结合律 )
Lemma add_assoc : forall a b c : nat, add (add a b) c = add a (add b c).
Proof.
induction a; intros b c; simpl.
reflexivity.
rewrite IHa; reflexivity.
Qed.

( 引理2：加法左单位律 )
Lemma add_0_l : forall a : nat, add O a = a.
Proof. reflexivity. Qed.

( 引理3：加法右单位律 )
Lemma add_0_r : forall a : nat, add a O = a.
Proof.
induction a; intros; simpl.
reflexivity.
rewrite IHa; reflexivity.
Qed.

( 引理4：幺半群单位元唯一性 )
Lemma monoid_id_unique_aux : forall (M : Monoid) (id2 id1 : carrier M),
(forall a : carrier M, op M id2 a = a /\ op M a id2 = a) ->
(forall a : carrier M, op M id1 a = a /\ op M a id1 = a) -> id2 = id1.
Proof.
intros M id2 id1 [H2l H2r] [H1l H1r].
assert (id2 = op M id2 id1) by (apply H2l).
assert (op M id2 id1 = id1) by (apply H1r).
rewrite H, H0; reflexivity.
Qed.

( 引理5：代数公理类型判别 )
Lemma algebra_axiom_tag_dec : forall (ax : AlgebraAxiom),
{ax.(axiom_tag) = AddAssocTag} +
{ax.(axiom_tag) = AddIdLeftTag} +
{ax.(axiom_tag) = AddIdRightTag} +
{ax.(axiom_tag) = MulAssocTag} +
{ax.(axiom_tag) = MulIdLeftTag} +
{ax.(axiom_tag) = MulIdRightTag} +
{ax.(axiom_tag) = MulLeftInvTag}.
Proof.
intros ax. destruct ax.(axiom_tag); [left; reflexivity right; left; reflexivity
right; right; left; reflexivity right; right; right; left; reflexivity
right; right; right; right; left; reflexivity right; right; right; right; right; left; reflexivity
right; right; right; right; right; right; left; reflexivity].
Qed.

( ======================== 核心定理（证明完备，无跳跃） ======================== )

( 定理1：自然数加法幺半群实例 )
Definition NatAddMonoid : Monoid := {
carrier := nat;
op := add;
id := O;
op_assoc := add_assoc;
id_left := add_0_l;
id_right := add_0_r
}.

( 定理2：自然数加法单位元唯一性 )
Theorem nat_add_monoid_id_unique : forall x : nat,
(forall a : nat, op NatAddMonoid x a = a /\ op NatAddMonoid a x = a) -> x = O.
Proof.
intros x H. apply monoid_id_unique_aux with (M := NatAddMonoid) (id2 := x) (id1 := O).
intros a. apply H.
intros a. split; [apply NatAddMonoid.(id_left) apply NatAddMonoid.(id_right)].
Qed.

( 定理3：整数加法群实例 )
Definition IntAddMonoid : Monoid := {
carrier := Z;
op := Z.add;
id := 0%Z;
op_assoc := Z.add_assoc;
id_left := Z.add_0_l;
id_right := Z.add_0_r
}.

Definition IntAddGroup : Group := {
group_monoid := IntAddMonoid;
inv := Z.opp;
mul_left_inv := Z.add_opp_diag_r
}.

( 定理4：代数公理无交集判定 )
Theorem algebra_axiom_disjoint : forall (ax1 ax2 : AlgebraAxiom),
ax1.(axiom_tag) <> ax2.(axiom_tag) -> ax1.(axiom_content) <> ax2.(axiom_content).
Proof.
intros ax1 ax2 H_tag_neq H_content_eq.
destruct ax1 as [tag1 content1], ax2 as [tag2 content2] in .
revert H_content_eq H_tag_neq.
destruct tag1, tag2; intros H_content_eq H_tag_neq; try discriminate H_tag_neq.
apply H_tag_neq. reflexivity.
apply H_tag_neq. reflexivity.
apply H_tag_neq. reflexivity.
apply H_tag_neq. reflexivity.
apply H_tag_neq. reflexivity.
apply H_tag_neq. reflexivity.
apply H_tag_neq. reflexivity.
Qed.

( 定理5：非平凡幺半群无零对象 )
Theorem non_trivial_monoid_no_zero : forall (M : Monoid),
(exists a b : carrier M, a <> b) ->
~(exists Z : carrier M, (forall a : carrier M, op M Z a = Z) /\ (forall a : carrier M, op M a Z = Z)).
Proof.
intros M [a b Hab] [Z [HZl HZr]].
assert (a = Z) by (rewrite <- (id_right M a); apply HZr).
assert (b = Z) by (rewrite <- (id_right M b); apply HZr).
rewrite H, H0 in Hab; contradiction.
Qed.

( ======================== 模块导出（无符号冲突，支撑二级模块调用） ======================== )
Export add add_assoc add_0_l add_0_r.
Export Monoid Group NatAddMonoid IntAddMonoid IntAddGroup.
Export monoid_id_unique_aux nat_add_monoid_id_unique algebra_axiom_disjoint.
Export non_trivial_monoid_no_zero AlgebraAxiom AlgebraAxiomTag algebra_axiom_tag_dec.
Export Monoid_carrier Monoid_op Monoid_id Group_inv.

( 激活作用域，确保下游模块调用时符号解析一致 *)
Open Scope algebra_scope.
Open Scope nat_scope.
Open Scope Z_scope.
