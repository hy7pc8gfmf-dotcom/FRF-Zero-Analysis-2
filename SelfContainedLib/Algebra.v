(* © 2025 FRF-Zero-Analysis Project. Licensed under GPLv3 or commercial license. *)
(* SelfContainedLib/Algebra.v - 自然数加法幺半群与代数公理基础 *)

Require Import Coq.Init.Datatypes.
Require Import Coq.Arith.PeanoNat.

(* ======================== 基础定义 ======================== *)

(* 自然数加法（与标准库一致，但显式定义以确保自包含性 *)  
Fixpoint add (n m : nat) : nat :=
  match n with
  | O => m
  | S p => S (add p m)
  end.

(* ======================== 幺半群结构 ======================== *)

Record Monoid : Type := {
  carrier : Type;
  op : carrier -> carrier -> carrier;
  id : carrier;
  op_assoc : forall a b c : carrier, op (op a b) c = op a (op b c);
  id_left : forall a : carrier, op id a = a;
  id_right : forall a : carrier, op a id = a
}.

(* ======================== 群结构（扩展幺半群） ======================== *)

Record Group : Type := {
  group_monoid : Monoid;
  inv : carrier group_monoid -> carrier group_monoid;
  mul_left_inv : forall a : carrier group_monoid,
    op group_monoid (inv a) a = id group_monoid
}.

(* ======================== 辅助引理：自然数加法性质 ======================== *)

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

(* ======================== 自然数加法幺半群实例 ======================== *)

Definition NatAddMonoid : Monoid := {|
  carrier := nat;
  op := add;
  id := O;
  op_assoc := add_assoc;
  id_left := add_0_l;
  id_right := add_0_r
|}.

(* ======================== 幺半群单位元唯一性辅助引理 ======================== *)

Lemma monoid_id_unique_aux :
  forall (M : Monoid) (id2 id1 : carrier M),
    (forall a : carrier M, op M id2 a = a /\ op M a id2 = a) ->
    (forall a : carrier M, op M id1 a = a /\ op M a id1 = a) ->
    id2 = id1.
Proof.
  intros M id2 id1 H2 H1.
  specialize (H2 id1) as [H2_left _].
  specialize (H1 id2) as [_ H1_right].
  transitivity (op M id2 id1).
  - symmetry. exact H1_right.
  - exact H2_left.
Qed.

Theorem nat_add_monoid_id_unique : forall x : nat,
  (forall a : nat, op NatAddMonoid x a = a /\ op NatAddMonoid a x = a) -> x = O.
Proof.
  intros x H.
  apply monoid_id_unique_aux with (M := NatAddMonoid) (id2 := x) (id1 := O).
  - exact H.
  - intros a. split; [apply NatAddMonoid.(id_left)| apply NatAddMonoid.(id_right)].
Qed.

(* ======================== 代数公理标签系统 ======================== *)

Inductive AlgebraAxiomTag : Type :=
| AddAssocTag
| AddIdLeftTag
| AddIdRightTag
| MulAssocTag
| MulIdLeftTag
| MulIdRightTag
| MulLeftInvTag.

Record AlgebraAxiom : Type := {
  axiom_tag : AlgebraAxiomTag
}.

(* ======================== 公理标签穷尽性定理 ======================== *)

Theorem algebra_axiom_tag_cases : forall (ax : AlgebraAxiom),
  ax.(axiom_tag) = AddAssocTag \/
  ax.(axiom_tag) = AddIdLeftTag \/
  ax.(axiom_tag) = AddIdRightTag \/
  ax.(axiom_tag) = MulAssocTag \/
  ax.(axiom_tag) = MulIdLeftTag \/
  ax.(axiom_tag) = MulIdRightTag \/
  ax.(axiom_tag) = MulLeftInvTag.
Proof.
  intros ax.
  destruct ax.(axiom_tag).
  - left; reflexivity.
  - right; left; reflexivity.
  - right; right; left; reflexivity.
  - right; right; right; left; reflexivity.
  - right; right; right; right; left; reflexivity.
  - right; right; right; right; right; left; reflexivity.
  - right; right; right; right; right; right; reflexivity.
Qed.

(* ======================== 非平凡幺半群无零元定理 ======================== *)

Theorem non_trivial_monoid_no_zero : forall (M : Monoid),
  (exists a b : carrier M, a <> b) ->
  ~(exists Z : carrier M,
      (forall a : carrier M, op M Z a = Z) /\
      (forall a : carrier M, op M a Z = Z)).
Proof.
  intros M [a b Hab] [Z [HZl HZr]].
  assert (Ha : a = Z).
  { rewrite <- (id_left M a). rewrite HZr. reflexivity. }
  assert (Hb : b = Z).
  { rewrite <- (id_left M b). rewrite HZr. reflexivity. }
  rewrite Ha, Hb in Hab. contradiction.
Qed.

(* ======================== 符号记法与作用域 ======================== *)

Declare Scope algebra_scope.
Notation "a ·[ M ] b" := (M.(op) a b) (at level 50) : algebra_scope.
Notation "1_[ M ]" := (M.(id)) (at level 30) : algebra_scope.
Notation "inv[ G ] a" := (G.(inv) a) (at level 40) : algebra_scope.

Open Scope algebra_scope.
Open Scope nat_scope.

(* ======================== 模块导出 ======================== *)

Export add add_assoc add_0_l add_0_r.
Export Monoid Group NatAddMonoid.
Export monoid_id_unique_aux nat_add_monoid_id_unique.
Export non_trivial_monoid_no_zero.
Export AlgebraAxiomTag AlgebraAxiom algebra_axiom_tag_cases.