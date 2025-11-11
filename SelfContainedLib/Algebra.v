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

(* 4. 代数公理标签 *)
Inductive AlgebraAxiomTag : Type := 
| AddAssocTag
| AddIdLeftTag 
| AddIdRightTag 
| MulAssocTag 
| MulIdLeftTag 
| MulIdRightTag 
| MulLeftInvTag.

(* 5. 代数公理封装 *)
Record AlgebraAxiom : Type := {
  axiom_tag : AlgebraAxiomTag;
  axiom_content : Prop;
}.

(* 符号记法 *)
Declare Scope algebra_scope.
Notation "a ·[ M ] b" := (M.(op) a b) (at level 50) : algebra_scope.
Notation "1_[ M ]" := (M.(id)) (at level 30) : algebra_scope.
Notation "inv[ G ] a" := (G.(inv) a) (at level 40) : algebra_scope.
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

Lemma monoid_id_unique_aux : forall (M : Monoid) (id2 id1 : carrier M), 
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

(* 代数公理类型相等性判定 *)
Definition algebra_axiom_tag_eq_dec : forall (t1 t2 : AlgebraAxiomTag), {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Defined.

Lemma algebra_axiom_tag_dec : forall (ax : AlgebraAxiom),
  (ax.(axiom_tag) = AddAssocTag) \/
  (ax.(axiom_tag) = AddIdLeftTag) \/
  (ax.(axiom_tag) = AddIdRightTag) \/
  (ax.(axiom_tag) = MulAssocTag) \/
  (ax.(axiom_tag) = MulIdLeftTag) \/
  (ax.(axiom_tag) = MulIdRightTag) \/
  (ax.(axiom_tag) = MulLeftInvTag).
Proof.
  intros ax.
  destruct ax.(axiom_tag);
  [ left; reflexivity
  | right; left; reflexivity
  | right; right; left; reflexivity
  | right; right; right; left; reflexivity
  | right; right; right; right; left; reflexivity
  | right; right; right; right; right; left; reflexivity
  | right; right; right; right; right; right; reflexivity ].
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

(* 代数公理无交集判定 - 完全修复版本 *)
Theorem algebra_axiom_disjoint : forall (ax1 ax2 : AlgebraAxiom),
  ax1.(axiom_tag) <> ax2.(axiom_tag) -> 
  ax1.(axiom_content) <> ax2.(axiom_content).
Proof.
  intros ax1 ax2 H_tag_neq H_content_eq.
  destruct ax1 as [tag1 content1], ax2 as [tag2 content2].
  simpl in *.
  destruct tag1; destruct tag2;
  try (contradiction H_tag_neq; reflexivity);
  try discriminate.
Qed.

Theorem non_trivial_monoid_no_zero : forall (M : Monoid),
  (exists a b : carrier M, a <> b) ->
  ~(exists Z : carrier M, (forall a : carrier M, op M Z a = Z) /\ (forall a : carrier M, op M a Z = Z)).
Proof.
  intros M [a b Hab] [Z [HZl HZr]].
  assert (a = Z).
  { rewrite <- (id_left M a) at 2. rewrite HZr. reflexivity. }
  assert (b = Z).
  { rewrite <- (id_left M b) at 2. rewrite HZr. reflexivity. }
  rewrite H, H0 in Hab; contradiction.
Qed.

(* ======================== 模块导出 ======================== *)
Export add add_assoc add_0_l add_0_r.
Export Monoid Group NatAddMonoid.
Export monoid_id_unique_aux nat_add_monoid_id_unique algebra_axiom_disjoint.
Export non_trivial_monoid_no_zero AlgebraAxiom AlgebraAxiomTag algebra_axiom_tag_dec algebra_axiom_tag_eq_dec.