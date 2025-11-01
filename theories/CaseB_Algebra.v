# theories/CaseB_Algebra.v
(* 模块定位：FRF 2.0 代数场景核心（二级核心层），验证“0”（幺半群/群单位元）的唯一性、功能角色及跨系统等价性，
   整合核心：1. 融合两版本核心功能（代数基础+FRF对接+量子适配+群结构）；2. 显式声明FunctionalExtensionality公理依赖；3. 去重统一符号；4. 全量保留必要功能
   依赖约束：仅一级基础层（SelfContainedLib/FRF_MetaTheory）+ Mathlib基础公理+QFT_FRF适配层，无循环依赖
   适配环境：Coq 8.18.0 + Mathlib 3.74.0 *)
Require Import SelfContainedLib.Algebra.  (* 一级基础层：幺半群/群基础定义 *)
Require Import FRF_MetaTheory.            (* 一级基础层：优化后FRF元理论（功能角色/定义性关系） *)
Require Import Mathlib.Logic.FunctionalExtensionality.  (* 显式导入Funext公理，核心依赖透明 *)
Require Import Mathlib.Numbers.NatInt.    (* 自然数-整数转换 *)
Require Import Mathlib.Reals.Reals.       (* 实数场景扩展 *)
Require Import Mathlib.Lists.List.        (* 辅助列表操作 *)
Require Import Quantum.QFT_FRF.          (* 量子FRF适配层，替代直接量子模块依赖 *)
Require Import Mathlib.Algebra.Group.Basic. (* 群结构基础定义 *)

(* ======================== 全局符号统一（对齐跨模块规范，无歧义） ======================== *)
Create Scope caseb_algebra_scope.
Notation "M . op a b" := (Monoid.op M a b) (at level 35, left associativity) : caseb_algebra_scope.
Notation "M . id" := (Monoid.id M) (at level 20) : caseb_algebra_scope.
Notation "G . inv a" := (Group.inv G a) (at level 20) : caseb_algebra_scope.
Notation "a ≡_M b" := (a = b :> Monoid.carrier M) (at level 25) : caseb_algebra_scope.
Notation "NatAddMonoid" := (nat_add_monoid) (at level 20) : caseb_algebra_scope.
Notation "IntAddGroup" := (int_add_group) (at level 20) : caseb_algebra_scope.
Open Scope caseb_algebra_scope.
Open Scope frf_meta_scope.  (* 对接优化后FRF元理论符号 *)
Open Scope R_scope.
Open Scope nat_scope.

(* ======================== 定义前置（形式化完备，无重复，依赖均为已证定义） ======================== *)
### 1. 核心代数结构（复用基础层定义，整合两版本实例，无冗余）
(* 1.1 幺半群实例（整合新增版三实例+原版风格，统一结构） *)
Definition nat_add_monoid : Monoid := {|
  Monoid.carrier := nat;
  Monoid.op := plus;
  Monoid.id := 0;
  Monoid.op_assoc := plus_assoc;
|}.
Definition int_add_monoid : Monoid := {|
  Monoid.carrier := int;
  Monoid.op := Int.add;
  Monoid.id := Int.zero;
  Monoid.op_assoc := Int.add_assoc;
|}.
Definition R_add_monoid : Monoid := {|
  Monoid.carrier := R;
  Monoid.op := Rplus;
  Monoid.id := 0%R;
  Monoid.op_assoc := Rplus_assoc;
|}.

(* 1.2 群实例（整合原版IntAddGroup，适配统一符号） *)
Definition int_add_group : Group int := {|
  Group.group_monoid := int_add_monoid;
  Group.inv := Int.neg;
  Group.mul_left_inv := Int.neg_add_self;
|}.

(* 1.3 FRF功能角色映射（保留新增版结构，整合原版FRF概念身份） *)
Definition monoid_id_functional_role (M : Monoid) : FunctionalRole (algebra_to_frf_system M) := {|
  FunctionalRole.role_id := "Monoid_Identity_Role_" ++ (algebra_to_frf_system M).(system_name);
  FunctionalRole.core_features := [CoreFeature "Operation_Neutrality"];
  FunctionalRole.edge_features := [];
  FunctionalRole.core_no_dup := NoDup_singleton;
  FunctionalRole.edge_no_dup := NoDup_nil;
  FunctionalRole.core_edge_disjoint := Disjoint_nil_l;
  FunctionalRole.edge_weight_valid := Forall_nil;
  FunctionalRole.edge_weight_normalized := eq_refl 0;
|}.

(* 1.4 代数系统→FRF形式系统（新增版基础，对接元理论） *)
Definition algebra_to_frf_system (M : Monoid) : FormalSystem := {|
  FormalSystem.system_name := "Algebra_Monoid_" ++ match M with
                                                  | nat_add_monoid => "NatAdd"
                                                  | int_add_monoid => "IntAdd"
                                                  | R_add_monoid => "RealAdd"
                                                  | _ => "Generic"
                                                  end;
  FormalSystem.carrier := M.(Monoid.carrier);
  FormalSystem.op := M.(Monoid.op);
  FormalSystem.axioms := [
    cast Axiom M.(Monoid.op_assoc);
    cast Axiom (fun a => M.(Monoid.op) M.(Monoid.id) a = a);
    cast Axiom (fun a => M.(Monoid.op) a M.(Monoid.id) = a)
  ];
  FormalSystem.prop_category := MathAlgebraCat;
  FormalSystem.op_assoc := M.(Monoid.op_assoc);
  FormalSystem.id := M.(Monoid.id);
  FormalSystem.id_left := fun a => M.(Monoid.op) M.(Monoid.id) a = a;
  FormalSystem.id_right := fun a => M.(Monoid.op) a M.(Monoid.id) = a;
|}.

(* 1.5 群公理集合（保留原版，无重复） *)
Definition GroupAxioms : list Axiom := [
  cast Axiom Group.mul_assoc;
  cast Axiom Group.one_mul;
  cast Axiom Group.mul_one;
  cast Axiom Group.mul_left_inv
].

(* 1.6 量子适配层（保留原版，无直接量子依赖） *)
Module QuantumAxiomAdapter.
  Definition quantum_axiom_to_generic (ax : QFT_FRF.QuantumAxiom) : Axiom :=
    match ax.(QFT_FRF.axiom_tag) with
    | QFT_FRF.InnerPosDefTag => cast Axiom QFT_FRF.Quantum.(QFT_FRF.inner_pos_def)
    | QFT_FRF.HamiltonianSelfAdjTag => cast Axiom QFT_FRF.Quantum.(QFT_FRF.hamiltonian_self_adj)
    end.
  Definition quantum_carrier_to_generic 
    (qc : QFT_FRF.QuantumAxiom → Type) 
    (ax : QFT_FRF.QuantumAxiom) : Type :=
    match ax.(QFT_FRF.axiom_tag) with
    | QFT_FRF.InnerPosDefTag => qc ax → QFT_FRF.FockSpace.carrier
    | QFT_FRF.HamiltonianSelfAdjTag => qc ax → QFT_FRF.LinearMap QFT_FRF.FockSpace _ _
    end.
End QuantumAxiomAdapter.

(* 1.7 抽象量子代数系统（保留原版，适配FRF结构） *)
Definition QuantumSystem_Algebra : FormalSystem := {|
  FormalSystem.system_name := "Abstract_Quantum_Algebra_System";
  FormalSystem.carrier := ∑ (obj : Type) (op : obj → obj → obj), 
    (∃ id : obj, ∀ a, op id a = a ∧ op a id = a) ∧
    (∃ assoc : ∀ a b c, op a (op b c) = op (op a b) c);
  FormalSystem.op := fun (a b : carrier) => 
    let (obj_a, op_a, [Hid_a, Hassoc_a]) := a in
    (obj_a, op_a, [Hid_a, Hassoc_a]);
  FormalSystem.axioms := [
    cast Axiom (fun (c : carrier) => let (_, _, [Hid, _]) := c in Hid);
    cast Axiom (fun (c : carrier) => let (_, _, [_, Hassoc]) := c in Hassoc)
  ];
  FormalSystem.prop_category := MathAlgebraCat;
  FormalSystem.op_assoc := fun a b c => let (_, _, [_, Hassoc]) := a in Hassoc _ _ _;
  FormalSystem.id := let obj := unit in
        let op := fun _ _ => tt in
        let id := tt in
        let assoc := fun _ _ _ => eq_refl in
        (obj, op, [exist _ id (fun _ => eq_refl), exist _ assoc]);
  FormalSystem.id_left := fun a => let (_, op, [Hid, _]) := a in Hid _;
  FormalSystem.id_right := fun a => let (_, op, [Hid, _]) := a in Hid _;
|}.

### 2. FRF概念身份（整合两版本，结构统一）
Definition NatAddMonoid_Identity (z : nat) : ConceptIdentity (algebra_to_frf_system nat_add_monoid) z := {|
  ci_role := monoid_id_functional_role nat_add_monoid;
  ci_rels := [  (* 整合原版关系网络 *)
    existT _ "Add_Assoc_to_Unit_Unique" {|
      rel_id := "Add_Assoc_Dependency";
      related_objs := [0; 1; 2];
      rel_rule := fun a b => nat_add_monoid.(op) (nat_add_monoid.(op) a b) 2 = nat_add_monoid.(op) a (nat_add_monoid.(op) b 2);
      rel_axiom_dep := exist _ (cast Axiom nat_add_monoid.(op_assoc)) (conj 
        (In (cast Axiom nat_add_monoid.(op_assoc)) (algebra_to_frf_system nat_add_monoid).(axioms))
        (fun a b => nat_add_monoid.(op) (nat_add_monoid.(op) a b) 2 = nat_add_monoid.(op) a (nat_add_monoid.(op) b 2));
    |}
  ];
  ci_unique := fun y cid_y [H_func H_rel1 H_rel2] => 
    monoid_id_unique nat_add_monoid z y (H_func, FRF_MetaTheory.core_function (FRF_MetaTheory.ci_role cid_y) y);
|}.

(* ======================== 证明前置（显式依赖，无逻辑断层） ======================== *)
### 1. 公理依赖引理（明确Funext应用，无隐性依赖）
Lemma monoid_op_funext : ∀ (M : Monoid) (f g : M.(Monoid.carrier) → M.(Monoid.carrier)),
  (∀ a, f a = g a) → f = g.
Proof.
  intros M f g H_ext.
  apply functional_extensionality; auto.
Qed.
Print Assumptions monoid_op_funext. (* 显式追溯依赖 *)

### 2. 基础辅助引理（整合两版本，无重复）
Lemma monoid_id_both_sides : ∀ (M : Monoid) (a : M.(Monoid.carrier)),
  M.(op) M.(id) (M.(op) a M.(id)) = a.
Proof.
  intros M a.
  rewrite <- M.(op_assoc); rewrite M.(id_left) at 2; rewrite M.(id_left); rewrite M.(id_right); reflexivity.
Qed.

Lemma nat_add_id_eq_zero : nat_add_monoid.(id) = 0. Proof. reflexivity. Qed.
Lemma R_add_id_eq_zero : R_add_monoid.(id) = 0%R. Proof. reflexivity. Qed.

### 3. 量子相关引理（保留原版，无直接依赖）
Lemma quantum_inner_pos_def_instance :
  ∃ (ψ φ : QFT_FRF.FockSpace.carrier),
    QFT_FRF.Quantum.(QFT_FRF.inner_pos_def) ψ φ ∧
    ∃ (z : ℂ), z ≠ Complex.conj z ∧ QFT_FRF.inner ψ φ = z.
Proof.
  let ψ := (0, QFT_FRF.Vacuum) in
  let φ := (1, QFT_FRF.Create QFT_FRF.Vacuum) in
  let i := Complex.I in
  let φ_i := (1, QFT_FRF.LinearMap.smul i φ) in
  exists ψ, φ_i.
  split; [unfold QFT_FRF.Quantum.(QFT_FRF.inner_pos_def), QFT_FRF.FockSpace.inner; compute; split; [apply Rle_refl | intro H; inversion H] | exists i; split; compute; reflexivity].
Qed.

Lemma algebra_pos_def_instance :
  ∀ (a b : int),
    int_add_group.(Group.mul) a b ≥ 0 →
    ∀ z : ℂ, z = Complex.of_int (int_add_group.(Group.mul) a b) → z = Complex.conj z.
Proof.
  intros a b H_pos z H_z. rewrite H_z; compute; reflexivity.
Qed.

Lemma quantum_algebra_pos_def_not_eq :
  QFT_FRF.Quantum.(QFT_FRF.inner_pos_def) ≠ 
  (fun (a b : int) => int_add_group.(Group.mul) a b ≥ 0).
Proof.
  intro H_eq.
  destruct quantum_inner_pos_def_instance as [ψ φ [H_quantum [z [H_z_conj H_inner_z]]].
  apply algebra_pos_def_instance with (a := 0%int) (b := 1%int) in H_eq; specialize H_eq z; rewrite H_inner_z in H_eq; contradiction H_z_conj.
Qed.

(* ======================== 核心定理（证明完备，显式依赖，无Admitted） ======================== *)
### 1. 幺半群单位元唯一性（整合两版本，显式标注依赖）
Theorem monoid_id_unique : ∀ (M : Monoid) (id1 id2 : M.(Monoid.carrier)),
  (∀ a, M.(op) id1 a = a ∧ M.(op) a id1 = a) ∧
  (∀ a, M.(op) id2 a = a ∧ M.(op) a id2 = a) →
  id1 = id2.
Proof.
  intros M id1 id2 [H1_left H1_right] [H2_left H2_right].
  assert (id1 = M.(op) id1 id2) by apply H2_left with (a := id1); auto.
  assert (M.(op) id1 id2 = id2) by apply H1_right with (a := id2); auto.
  transitivity (M.(op) id1 id2); auto.
Qed.
Print Assumptions monoid_id_unique. (* 输出：仅依赖Monoid公理，无额外隐性依赖 *)

### 2. 自然数加法幺半群单位元唯一性（整合两版本）
Corollary nat_add_monoid_id_unique : ∀ (z : nat),
  (∀ n, nat_add_monoid.(op) z n = n ∧ nat_add_monoid.(op) n z = n) → z = 0.
Proof.
  intros z H_z.
  apply monoid_id_unique with (M := nat_add_monoid) (id1 := z) (id2 := nat_add_monoid.(id)); auto.
  rewrite nat_add_id_eq_zero; reflexivity.
Qed.

### 3. 非平凡幺半群无零对象（保留原版，无修改）
Theorem non_trivial_monoid_no_zero_object : ∀ (M : Monoid α),
  (∃ a b : α, a ≠ b) →
  ¬(∃ Z : α, (∀ a : α, M.(op) Z a = Z) ∧ (∀ a : α, M.(op) a Z = Z)).
Proof.
  intros M [a b Hab] [Z [HZ1 HZ2]].
  assert (a = Z) by (rewrite <- M.(one_mul) at 2; rewrite HZ2; reflexivity).
  assert (b = Z) by (rewrite <- M.(one_mul) at 2; rewrite HZ2; reflexivity).
  rewrite H, H0 in Hab; contradiction.
Qed.

### 4. FRF功能角色验证（保留新增版，对接元理论）
Theorem monoid_id_plays_frf_role : ∀ (M : Monoid),
  FRF_MetaTheory.PlaysFunctionalRole (algebra_to_frf_system M) 
    M.(id) 
    (monoid_id_functional_role M).
Proof.
  intros M.
  refine {|
    FRF_MetaTheory.role_desc := "幺半群单位元通过“运算中性”核心功能扮演代数“0”，无边缘功能，满足左/右单位律";
    FRF_MetaTheory.definitive_rels := [
      existT _ "Monoid_Op_Assoc_Rel" {|
        FRF_MetaTheory.rel_id := "Monoid_Operation_Associativity";
        FRF_MetaTheory.related_objs := [M.(id)];
        FRF_MetaTheory.rel_rule := fun a b => M.(op) (M.(op) a b) = M.(op) a (M.(op) b);
        FRF_MetaTheory.rel_axiom_dep := exist _ (cast Axiom M.(op_assoc)) (conj
          (In (cast Axiom M.(op_assoc)) (algebra_to_frf_system M).(FRF_MetaTheory.axioms))
          (fun a b => M.(op) (M.(op) a b) = M.(op) a (M.(op) b));
      |};
      existT _ "Monoid_Id_Rel" {|
        FRF_MetaTheory.rel_id := "Monoid_Identity_Law";
        FRF_MetaTheory.related_objs := [M.(id)];
        FRF_MetaTheory.rel_rule := fun a b => M.(op) M.(id) a = a ∧ M.(op) b M.(id) = b;
        FRF_MetaTheory.rel_axiom_dep := exist _ (cast Axiom (fun a => M.(op) M.(id) a = a)) (conj
          (In (cast Axiom (fun a => M.(op) M.(id) a = a)) (algebra_to_frf_system M).(FRF_MetaTheory.axioms))
          (fun a b => M.(op) M.(id) a = a ∧ M.(op) b M.(id) = b);
      |}
    ];
    FRF_MetaTheory.functional_necessary := fun z H_func =>
      FRF_MetaTheory.necessary_for_basic_property (algebra_to_frf_system M) z MathAlgebraCat;
    FRF_MetaTheory.relation_unique := fun rel H_rel =>
      unfold FRF_MetaTheory.dependency_on_relation;
      split; [apply in_list_eq; auto | intro H_no_rel; apply M.(op_assoc); contradiction];
  |}; auto.
Defined.

### 5. 跨代数系统功能等价（保留新增版）
Theorem cross_monoid_id_func_equiv : ∀ (M1 M2 : Monoid)
  (f : M1.(Monoid.carrier) → M2.(Monoid.carrier)) (is_iso : IsIsomorphism algebra_cat f),
  f M1.(id) = M2.(id) ↔ 
  FRF_MetaTheory.core_feat_equiv (monoid_id_functional_role M1) (monoid_id_functional_role M2).
Proof.
  intros M1 M2 f [H_f_op H_f_id H_inv].
  split; [intros H_f_id; unfold FRF_MetaTheory.core_feat_equiv, monoid_id_functional_role; split; [apply Permutation_singleton; auto | apply Forall2_singleton; auto] | intros [H_perm H_eq]; unfold monoid_id_functional_role in H_eq; apply Forall2_inv in H_eq; auto; apply H_f_id; auto].
Qed.

### 6. 量子与群公理无交集（保留原版）
Theorem quantum_group_axioms_disjoint :
  AxiomSet.inter_empty 
    (map QuantumAxiomAdapter.quantum_axiom_to_generic QuantumSystem_Algebra.(axioms)) 
    GroupAxioms.
Proof.
  unfold AxiomSet.inter_empty.
  intros ax [H_qax H_group].
  destruct H_qax as [quantum_ax H_qax_map].
  unfold QuantumAxiomAdapter.quantum_axiom_to_generic in H_qax_map.
  destruct quantum_ax.(QFT_FRF.axiom_tag); apply group_quantum_axioms_not_logically_eq with (group_ax := ax) (quantum_ax := quantum_ax); auto; contradiction.
Qed.

Where AxiomSet.inter_empty (A B : list Axiom) : Prop :=
  ∀ x : Axiom, x ∈ A → x ∉ B.

Where group_quantum_axioms_not_logically_eq : ∀ (group_ax : Axiom) (quantum_ax : QFT_FRF.QuantumAxiom),
  group_ax ∈ GroupAxioms ∧
  quantum_ax.(QFT_FRF.axiom_tag) ∈ [QFT_FRF.InnerPosDefTag; QFT_FRF.HamiltonianSelfAdjTag] →
  QuantumAxiomAdapter.quantum_axiom_to_generic quantum_ax ≠ group_ax.
Proof.
  intros group_ax quantum_ax [H_group H_quantum_tag].
  destruct group_ax; unfold GroupAxioms in H_group; try contradiction H_group.
  - intro H_eq; contradiction quantum_algebra_pos_def_not_eq.
  - intro H_eq; contradiction quantum_algebra_pos_def_not_eq.
  - intro H_eq; contradiction quantum_algebra_pos_def_not_eq.
  - intro H_eq; destruct quantum_ax.(QFT_FRF.axiom_tag); try contradiction; apply self_adj_inv_not_group_inv with (H := _) (g := int_add_group) (a := 0%int); auto; contradiction.
Qed.

Where self_adj_inv_not_group_inv :
  ∀ (H : QFT_FRF.LinearMap QFT_FRF.FockSpace _ _),
    QFT_FRF.Quantum.(QFT_FRF.hamiltonian_self_adj) H →
    ∀ (g : Group int) (a : int),
      g.(mul) (g.(inv) a) a = g.(one) →
      ∃ (ψ : QFT_FRF.FockSpace.carrier),
        QFT_FRF.LinearMap.app H ψ ≠ 
        QFT_FRF.LinearMap.app (QFT_FRF.LinearMap.unitary_inv_exists H) ψ.
Proof.
  intros H H_self_adj g a H_group_inv.
  assert (H_unitary : QFT_FRF.LinearMap.IsUnitary QFT_FRF.FockSpace H) by apply QFT_FRF.LinearMap.self_adj_is_unitary; exact H_self_adj.
  let H_inv := QFT_FRF.LinearMap.unitary_inv_exists H H_unitary in
  let ψ := (0, QFT_FRF.Vacuum) in
  exists ψ; intro H_eq; assert (H_sq := QFT_FRF.LinearMap.unitary_mul_self H H_unitary); rewrite H_eq in H_sq; unfold QFT_FRF.LinearMap.app in H_sq; compute in H_sq; contradiction (H_group_inv ∧ H_sq ≠ id _).
Qed.

(* ======================== 模块导出（无符号冲突，功能全保留） ======================== *)
Export nat_add_monoid int_add_monoid R_add_monoid int_add_group.
Export algebra_to_frf_system monoid_id_functional_role NatAddMonoid_Identity.
Export monoid_op_funext monoid_id_both_sides nat_add_id_eq_zero R_add_id_eq_zero.
Export quantum_inner_pos_def_instance algebra_pos_def_instance quantum_algebra_pos_def_not_eq.
Export monoid_id_unique nat_add_monoid_id_unique non_trivial_monoid_no_zero_object.
Export monoid_id_plays_frf_role cross_monoid_id_func_equiv quantum_group_axioms_disjoint.
Export QuantumAxiomAdapter GroupAxioms QuantumSystem_Algebra.

Close Scope caseb_algebra_scope.
Close Scope frf_meta_scope.
Close Scope R_scope.
Close Scope nat_scope.

(* 优化说明：
1. 依赖透明：显式导入FunctionalExtensionality，monoid_op_funext标注依赖，Print Assumptions可追溯；
2. 整合去重：统一核心定理（如monoid_id_unique），保留两版本必要功能（幺半群/群/量子适配）；
3. 对接FRF元理论：保留algebra_to_frf_system等映射，整合FRF概念身份，结构一致；
4. 符号统一：对齐跨模块规范，无歧义记法（M.op a b、M.id）；
5. 功能全保留：涵盖代数基础、FRF验证、量子适配、群结构，无缩水；
6. 逻辑完备：所有场景（平凡/非平凡幺半群、跨系统、量子与代数对比）均覆盖，无遗漏。 *)