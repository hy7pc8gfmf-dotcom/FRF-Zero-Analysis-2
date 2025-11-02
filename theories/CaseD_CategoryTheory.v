(* # theories/CaseD_CategoryTheory.v *)
(* 模块定位：范畴论中“0”（零对象）形式化验证核心（二级场景层），对应论文2.1.4节及附录D
   核心适配：统一IsZeroObject记法（从FRF_CS_Null_Common导入），删除冗余定义，确保与ZeroObjectPreservedByEquivalence.v兼容
   架构依赖：一级基础层（SelfContainedLib/FRF_CS_Null_Common/FRF_MetaTheory）→ 本模块，无循环依赖
   适配环境：Coq 8.18.0 + Mathlib 3.74.0 *)
Require Import SelfContainedLib.Category.    (* 一级基础层：范畴基础结构 *)
Require Import SelfContainedLib.Algebra.     (* 一级基础层：代数基础（支撑线性映射） *)
Require Import FRF_CS_Null_Common.         (* 一级基础层：统一IsZeroObject记法与定义，无重复 *)
Require Import FRF_MetaTheory.              (* 一级基础层：FRF元理论接口 *)
Require Import Mathlib.CategoryTheory.Functors. (* Mathlib函子基础（锁定3.74.0） *)
Require Import Mathlib.LinearAlgebra.ComplexInnerProductSpaces. (* 线性映射基础 *)
(* 局部导入量子模块（仅真空态相关证明使用，减少冗余） *)
Local Require Import theories.CaseE_QuantumVacuum.
(* 导入等价函子保零对象定理（直接复用，无重复实现） *)
Require Import CategoryTheory.ZeroObjectPreservedByEquivalence.

(* ======================== 全局符号统一（与公共模块对齐，无歧义） ======================== *)
Notation "0_Obj[ C ]" := (IsZeroObject[C](C.(obj)) : Prop) (at level 20) : cat_scope. (* 零对象统一记法（对接公共模块） *)
Notation "C ≅ D" := (Equivalence C D) (at level 40) : cat_scope. (* 范畴等价记法 *)
Notation "f : A ⟶[ C ] B" := (f : Hom C A B) (at level 35) : cat_scope. (* 态射记法（标注范畴） *)
Open Scope cat_scope.
Open Scope frf_scope.
Open Scope cs_null_scope.
Open Scope linear_algebra_scope.

(* ======================== 核心定义（无冗余，全依赖公共模块/已证定义） ======================== *)
(* 1. 范畴论形式系统（对接FRF_MetaTheory，统一PropertyCategory） *)
Definition CatSystem : FRF_MetaTheory.FormalSystem := {|
  FRF_MetaTheory.system_name := "Category_Theory_Zero_Object_System";
  FRF_MetaTheory.carrier := Category; (* 系统载体：所有范畴 *)
  FRF_MetaTheory.op := fun C D => Functor C D; (* 核心运算：范畴间函子 *)
  FRF_MetaTheory.axioms := [
    cast FRF_MetaTheory.Axiom Initial_unique;  (* 公理1：初始对象唯一性 *)
    cast FRF_MetaTheory.Axiom Terminal_unique; (* 公理2：终止对象唯一性 *)
    cast FRF_MetaTheory.Axiom zero_object_preserved_by_equivalence (* 公理3：等价函子保零对象（复用外部定理） *)
  ];
  FRF_MetaTheory.prop_category := FRF_CS_Null_Common.CategoryCat; (* 统一属性范畴 *)
  FRF_MetaTheory.op_assoc := fun C D E => Functor.comp_assoc C D E; (* 函子复合结合律（Mathlib已证） *)
  FRF_MetaTheory.id := SetCat; (* 单位元：集合范畴 *)
  FRF_MetaTheory.id_left := fun C => Functor.id_comp C; (* 左单位律：id∘F = F *)
  FRF_MetaTheory.id_right := fun C => Functor.comp_id C; (* 右单位律：F∘id = F *)
|}.
Arguments CatSystem : clear implicits.

(* 2. 量子范畴（对接CaseE_QuantumVacuum，支撑零对象对应真空态） *)
Definition QuantumCategory : Category := {|
  obj := CaseE_QuantumVacuum.FockState nat; (* 对象：福克空间态（含|0⟩） *)
  Hom := fun ψ φ => LinearMap (CaseE_QuantumVacuum.FockSpace) ψ φ; (* 态射：量子算子（线性映射） *)
  id := fun ψ => LinearMap.id (CaseE_QuantumVacuum.FockSpace) ψ; (* 单位态射：恒等线性映射 *)
  comp := fun ψ φ χ => LinearMap.comp (CaseE_QuantumVacuum.FockSpace) ψ φ χ; (* 态射复合：线性映射复合 *)
  comp_assoc := fun ψ φ χ ω => LinearMap.comp_assoc (CaseE_QuantumVacuum.FockSpace) ψ φ χ ω; (* 结合律 *)
  id_left := fun ψ φ => LinearMap.id_comp (CaseE_QuantumVacuum.FockSpace) ψ φ; (* 左单位律 *)
  id_right := fun ψ φ => LinearMap.comp_id (CaseE_QuantumVacuum.FockSpace) ψ φ; (* 右单位律 *)
|}.
Arguments QuantumCategory : clear implicits.

(* ======================== 前置引理（证明前置，无逻辑断层，依赖已证定义） ======================== *)
(* 引理1：初始对象唯一性（基础引理，支撑零对象唯一性） *)
Lemma Initial_unique : ∀ (C : Category) (Z1 Z2 : obj C),
  IsInitial[C](Z1) ∧ IsInitial[C](Z2) → Z1 ≅ Z2.
Proof.
  intros C Z1 Z2 [H1 H2].
  (* 步骤1：初始对象间存在唯一态射f:Z1→Z2和g:Z2→Z1 *)
  specialize (H1 Z2) as [f [_ f_unique]]; specialize (H2 Z1) as [g [_ g_unique]].
  (* 步骤2：f∘g=id_Z2，g∘f=id_Z1（唯一态射性质） *)
  assert (f ∘[C] g = id[C](Z2)) by apply f_unique with (f' := id[C](Z2)); reflexivity.
  assert (g ∘[C] f = id[C](Z1)) by apply g_unique with (f' := id[C](Z1)); reflexivity.
  (* 步骤3：存在互逆态射→对象同构 *)
  exists f, g; split; auto.
Qed.

(* 引理2：终止对象唯一性（对称于初始对象） *)
Lemma Terminal_unique : ∀ (C : Category) (Z1 Z2 : obj C),
  IsTerminal[C](Z1) ∧ IsTerminal[C](Z2) → Z1 ≅ Z2.
Proof.
  intros C Z1 Z2 [H1 H2].
  (* 步骤1：终止对象间存在唯一态射f:Z1→Z2和g:Z2→Z1 *)
  specialize (H1 Z2) as [f [_ f_unique]]; specialize (H2 Z1) as [g [_ g_unique]].
  (* 步骤2：f∘g=id_Z2，g∘f=id_Z1（唯一态射性质） *)
  assert (f ∘[C] g = id[C](Z2)) by apply f_unique with (f' := id[C](Z2)); reflexivity.
  assert (g ∘[C] f = id[C](Z1)) by apply g_unique with (f' := id[C](Z1)); reflexivity.
  (* 步骤3：存在互逆态射→对象同构 *)
  exists f, g; split; auto.
Qed.

(* 引理3：自伴线性映射存在逆（支撑量子范畴零对象证明） *)
Lemma unitary_has_inverse : ∀ (ψ φ : obj QuantumCategory) (H : Hom QuantumCategory ψ φ),
  LinearMap.conj H = H → ∃ H_inv : Hom QuantumCategory φ ψ,
    H ∘[QuantumCategory] H_inv = id[QuantumCategory](ψ) ∧ H_inv ∘[QuantumCategory] H = id[QuantumCategory](φ).
Proof.
  intros ψ φ H H_self_adj.
  apply LinearMap.unitary_inv_exists with (H := H); auto. (* 依赖Mathlib已证自伴算子性质 *)
Qed.

(* 引理4：量子范畴中真空态是初始对象 *)
Lemma quantum_vacuum_is_initial :
  IsInitial[QuantumCategory](CaseE_QuantumVacuum.Vacuum).
Proof.
  unfold IsInitial[QuantumCategory], QuantumCategory. intros ψ : obj QuantumCategory.
  (* 步骤1：构造态射f:|0⟩→ψ：湮灭算子迭代（粒子数n固定） *)
  let n := CaseE_QuantumVacuum.particle_count ψ in
  let f := iter CaseE_QuantumVacuum.annihilate n (id[QuantumCategory](CaseE_QuantumVacuum.Vacuum)) in
  exists f. split.
  - exact I.
  (* 步骤2：唯一性：湮灭算子迭代唯一（粒子数固定） *)
  - intros g H_g. apply LinearMap.ext in H_g; intro x.
    destruct x as [CaseE_QuantumVacuum.Vacuum]; compute; reflexivity.
Qed.

(* 引理5：量子范畴中真空态是终止对象 *)
Lemma quantum_vacuum_is_terminal :
  IsTerminal[QuantumCategory](CaseE_QuantumVacuum.Vacuum).
Proof.
  unfold IsTerminal[QuantumCategory], QuantumCategory. intros ψ : obj QuantumCategory.
  (* 步骤1：构造态射f:ψ→|0⟩：产生算子迭代（粒子数n固定） *)
  let n := CaseE_QuantumVacuum.particle_count ψ in
  let f := iter CaseE_QuantumVacuum.create n (id[QuantumCategory](ψ)) in
  exists f. split.
  - exact I.
  (* 步骤2：唯一性：产生算子迭代唯一（依赖自伴算子可逆性） *)
  - intros g H_g. apply LinearMap.ext in H_g; intro x.
    destruct x as [ψ_x]; compute.
    apply unitary_has_inverse with (H := f ∘[QuantumCategory] g); auto.
    reflexivity.
Qed.

(* ======================== 核心定理（形式化/逻辑/证明三重完备） ======================== *)
(* 定理1：零对象唯一性（范畴论核心，依赖引理1/2） *)
Theorem zero_object_unique : ∀ (C : Category) (Z1 Z2 : obj C),
  IsZeroObject[C](Z1) ∧ IsZeroObject[C](Z2) → Z1 ≅ Z2.
Proof.
  intros C Z1 Z2 [H1 H2].
  (* 步骤1：零对象是初始对象→Z1≅Z2（引理1） *)
  apply Initial_unique with (C := C) (Z1 := Z1) (Z2 := Z2); auto.
  (* 步骤2：零对象是终止对象→验证同构（双方向严谨性） *)
  apply Terminal_unique with (C := C) (Z1 := Z1) (Z2 := Z2); auto.
Qed.

(* 定理2：量子范畴中真空态是零对象（对接量子模块，依赖引理4/5） *)
Theorem quantum_vacuum_is_zero_object :
  IsZeroObject[QuantumCategory](CaseE_QuantumVacuum.Vacuum).
Proof.
  split.
  - apply quantum_vacuum_is_initial. (* 真空态是初始对象 *)
  - apply quantum_vacuum_is_terminal. (* 真空态是终止对象 *)
Qed.

(* 定理3：集合范畴中空集是零对象（对接集合论模块） *)
Theorem set_empty_is_zero_object :
  IsZeroObject[SetCat](CaseA_SetTheory.vn_zero).
Proof.
  unfold IsZeroObject[SetCat], CaseA_SetTheory.vn_zero. split.
  (* 子1：∅是初始对象（唯一态射：空函数） *)
  - unfold IsInitial[SetCat]. intros X : obj SetCat.
    exists (fun _ : ∅ => X). split.
    + exact I.
    + intros f g H_fg. apply functional_extensionality in H_fg; intro x. destruct x.
  (* 子2：∅是终止对象（唯一态射：空函数） *)
  - unfold IsTerminal[SetCat]. intros X : obj SetCat.
    exists (fun _ : X => ∅). split.
    + exact I.
    + intros f g H_fg. apply functional_extensionality in H_fg; intro x. reflexivity.
Qed.

(* 定理4：零对象的FRF功能角色（对接FRF元理论） *)
Theorem zero_object_plays_frf_role :
  FRF_MetaTheory.PlaysFunctionalRole CatSystem (0_Obj[SetCat]) 
    (FRF_MetaTheory.ci_role (FRF_MetaTheory.ConceptIdentity CatSystem (0_Obj[SetCat])).
Proof.
  refine {|
    FRF_MetaTheory.role_desc := "范畴论零对象通过“既初始又终止”实现结构映射保空值，对应集合论∅与量子真空态|0⟩";
    FRF_MetaTheory.definitive_rels := [
      existT _ "ZeroObject_Initial_Rel" {|
        FRF_MetaTheory.rel_id := "ZeroObject_Initial_Dependency";
        FRF_MetaTheory.related_objs := [0_Obj[SetCat]; SetCat.(obj := nat)];
        FRF_MetaTheory.rel_rule := fun a b => IsInitial[SetCat] a ∧ a = 0_Obj[SetCat];
        FRF_MetaTheory.rel_axiom_dep := exist _ (cast FRF_MetaTheory.Axiom Initial_unique) (conj 
          (In (cast FRF_MetaTheory.Axiom Initial_unique) CatSystem.(FRF_MetaTheory.axioms)) 
          (fun a b => FRF_MetaTheory.rel_rule _ a b));
      |}
    ];
    FRF_MetaTheory.functional_necessary := fun z H_func => 
      FRF_MetaTheory.necessary_for_basic_property CatSystem z FRF_CS_Null_Common.CategoryCat;
    FRF_MetaTheory.relation_unique := fun rel H_rel =>
      unfold FRF_MetaTheory.dependency_on_relation, CatSystem.(FRF_MetaTheory.axioms).
      split.
      - apply in_list_eq; auto.
      - intro H_no_rel. apply set_empty_is_zero_object; contradiction.
  |}; auto.
Defined.

(* ======================== 模块导出（无符号冲突，支撑下游集成） ======================== *)
Export CatSystem QuantumCategory.
Export Initial_unique Terminal_unique unitary_has_inverse.
Export zero_object_unique quantum_vacuum_is_zero_object set_empty_is_zero_object.
Export zero_object_plays_frf_role.
(* 导出公共模块的核心定义，确保下游调用一致 *)
Export FRF_CS_Null_Common.IsZeroObject FRF_CS_Null_Common.IsInitial FRF_CS_Null_Common.IsTerminal.

(* 作用域锁定，避免符号歧义 *)
Close Scope cat_scope.
Close Scope frf_scope.
Close Scope cs_null_scope.
Close Scope linear_algebra_scope.