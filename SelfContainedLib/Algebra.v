(* SelfContainedLib/Algebra.v *)
(* 修复版本：确保与FRF_MetaTheory.v兼容 *)
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Reals.Reals.
From Coq Require Import ZArith.Int.

(* ======================== 核心代数定义 ======================== *)

(* 1. 自然数加法 *)
Fixpoint add (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (add n' m)
  end.

(* 2. 幺半群定义 - 与FRF_MetaTheory.v兼容的版本 *)
Record Monoid : Type := {
  carrier : Type;
  op : carrier -> carrier -> carrier;
  id : carrier;
  op_assoc : forall a b c, op (op a b) c = op a (op b c);
  id_left : forall a, op id a = a;
  id_right : forall a, op a id = a;
}.

(* 3. 群定义 *)
Record Group : Type := {
  group_monoid : Monoid;
  inv : carrier group_monoid -> carrier group_monoid;
  mul_left_inv : forall a : carrier group_monoid, 
    op group_monoid (inv a) a = id group_monoid;
}.

(* ======================== 基础引理和定理 ======================== *)

(* 自然数加法性质 *)
Theorem add_assoc : forall a b c : nat, add (add a b) c = add a (add b c).
Proof.
  induction a; intros b c; simpl.
  - reflexivity.
  - rewrite IHa; reflexivity.
Qed.

Theorem add_0_l : forall a : nat, add O a = a.
Proof. reflexivity. Qed.

Theorem add_0_r : forall a : nat, add a O = a.
Proof.
  induction a; intros; simpl.
  - reflexivity.
  - rewrite IHa; reflexivity.
Qed.

(* 幺半群单位元唯一性 *)
Lemma monoid_id_unique_aux : forall (M : Monoid) (id1 id2 : carrier M),
  (forall a : carrier M, op M id1 a = a) ->
  (forall a : carrier M, op M id2 a = a) ->
  id1 = id2.
Proof.
  intros M id1 id2 H1 H2.
  specialize (H1 id2).  (* op M id1 id2 = id2 *)
  specialize (H2 id1).  (* op M id2 id1 = id1 *)
  
  transitivity (op M id2 id1).
  - symmetry. exact H2.
  - transitivity (op M id1 id2).
    + rewrite <- (H1 id1) at 1.
      rewrite <- (H2 id2) at 1.
      rewrite (op_assoc M id2 id1 id2).
      rewrite H2. rewrite H1.
      reflexivity.
    + exact H1.
Qed.

(* ======================== 核心实例 ======================== *)

(* 自然数加法幺半群 *)
Definition NatAddMonoid : Monoid := {|
  carrier := nat;
  op := add;
  id := O;
  op_assoc := add_assoc;
  id_left := add_0_l;
  id_right := add_0_r;
|}.

(* 整数加法幺半群 *)
Definition IntAddMonoid : Monoid := {|
  carrier := Z;
  op := Z.add;
  id := 0%Z;
  op_assoc := Z.add_assoc;
  id_left := Z.add_0_l;
  id_right := Z.add_0_r;
|}.

(* 整数加法群 *)
Definition IntAddGroup : Group := {|
  group_monoid := IntAddMonoid;
  inv := Z.opp;
  mul_left_inv := Z.add_opp_diag_l;
|}.

(* ======================== 代数公理系统 ======================== *)

Inductive AlgebraAxiomTag : Type :=
  | AddAssocTag : AlgebraAxiomTag
  | AddIdLeftTag : AlgebraAxiomTag
  | AddIdRightTag : AlgebraAxiomTag
  | MulAssocTag : AlgebraAxiomTag
  | MulIdLeftTag : AlgebraAxiomTag
  | MulIdRightTag : AlgebraAxiomTag
  | MulLeftInvTag : AlgebraAxiomTag.

Definition Axiom : Type := Prop.

Record AlgebraAxiom : Type := {
  axiom_tag : AlgebraAxiomTag;
  axiom_content : Axiom;
}.

(* ======================== 实用引理 ======================== *)

Lemma algebra_axiom_tag_dec : forall (ax : AlgebraAxiom),
  {ax.(axiom_tag) = AddAssocTag} +
  {ax.(axiom_tag) = AddIdLeftTag} +
  {ax.(axiom_tag) = AddIdRightTag} +
  {ax.(axiom_tag) = MulAssocTag} +
  {ax.(axiom_tag) = MulIdLeftTag} +
  {ax.(axiom_tag) = MulIdRightTag} +
  {ax.(axiom_tag) = MulLeftInvTag}.
Proof.
  intros ax. destruct ax.(axiom_tag); 
  [left; reflexivity | right; left; reflexivity | 
   right; right; left; reflexivity | right; right; right; left; reflexivity | 
   right; right; right; right; left; reflexivity | 
   right; right; right; right; right; left; reflexivity | 
   right; right; right; right; right; right; left; reflexivity].
Qed.

Theorem algebra_axiom_disjoint : forall (ax1 ax2 : AlgebraAxiom),
  ax1.(axiom_tag) ≠ ax2.(axiom_tag) -> ax1.(axiom_content) ≠ ax2.(axiom_content).
Proof.
  intros ax1 ax2 H_tag_neq H_content_eq.
  rewrite H_content_eq in H_tag_neq.
  destruct ax1.(axiom_tag) as [| | | | | |], ax2.(axiom_tag) as [| | | | | |];
  try reflexivity; inversion H_tag_neq; contradiction.
Qed.

Theorem non_trivial_monoid_no_zero : forall (M : Monoid),
  (exists a b : carrier M, a ≠ b) ->
  ¬(exists Z : carrier M, (forall a : carrier M, op M Z a = Z) ∧ (forall a : carrier M, op M a Z = Z)).
Proof.
  intros M [a b Hab] [Z [HZ1 HZ2]].
  assert (a = Z).
  { rewrite <- (id_left M a) at 2. rewrite HZ2. reflexivity. }
  assert (b = Z).
  { rewrite <- (id_left M b) at 2. rewrite HZ2. reflexivity. }
  rewrite H, H0 in Hab; contradiction.
Qed.

(* ======================== 符号和导出 ======================== *)

Notation "op M a b" := (op M a b) (at level 50) : algebra_scope.
Notation "id M" := (id M) (at level 40) : algebra_scope.
Notation "inv G a" := (inv G a) (at level 40) : algebra_scope.

Open Scope algebra_scope.
Open Scope nat_scope.
Open Scope Z_scope.

(* 导出所有核心定义 *)
Export add add_assoc add_0_l add_0_r.
Export Monoid Group NatAddMonoid IntAddMonoid IntAddGroup.
Export monoid_id_unique_aux algebra_axiom_disjoint non_trivial_monoid_no_zero.
Export AlgebraAxiom AlgebraAxiomTag algebra_axiom_tag_dec.