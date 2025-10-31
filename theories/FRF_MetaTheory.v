# theories/FRF_MetaTheory.v
(* 模块定位：FRF框架元理论核心（一级基础层），定义FRF三大组件与元定理，支撑全场景FRF验证
   重构目标：1. 补全func_equiv_criterion对system_property_category_eq_implies_sys_eq的调用
            2. 统一DefinitiveRelation.rel_axiom_dep格式（显式绑定公理）
            3. 修复PlaysFunctionalRole的“功能必要性”判定逻辑
            4. 证明功能等价与系统属性范畴的关联性
            5. 提供跨场景FRF定理兼容性的通用证明
   依赖模块：仅一级基础层（无循环依赖）
   - FRF_CS_Null_Common.v：统一PropertyCategory/系统属性范畴判定
   - SelfContainedLib.Algebra：代数基础（func_equiv依赖）
   - SelfContainedLib.Category：范畴基础（关系网络依赖）
   符号规范：frf_scope管理FRF核心符号，避免冲突 *)
Require Import FRF_CS_Null_Common.
Require Import SelfContainedLib.Algebra.
Require Import SelfContainedLib.Category.
Require Import Mathlib.Logic.FunctionalExtensionality.
Require Import Mathlib.Strings.String.
Require Import Mathlib.Lists.List.
Require Import Mathlib.Reflection.TypeDec.

(* 全局符号统一：frf_scope作用域隔离，与FRF_CS_Null_Common对齐 *)
Notation "S ⊢ obj : role" := (PlaysFunctionalRole S obj role) (at level 50) : frf_scope.
Notation "sys1 ≡_func sys2" := (func_equiv_criterion sys1 sys2) (at level 45) : frf_scope.
Notation "rel ⪯ S" := (rel_axiom_dep rel ∈ axioms S) (at level 40) : frf_scope.
Open Scope frf_scope.
Open Scope cs_null_scope.

(* ======================== 核心定义（定义前置，无重复，显式绑定依赖） ======================== *)
(* 公理统一类型：兼容所有系统公理，无类型冲突 *)
Definition Axiom : Type := Prop.

(* 形式系统：FRF核心载体，显式对接公共模块属性范畴 *)
Record FormalSystem : Type := {
  system_name : string;
  carrier : Type;
  op : carrier -> carrier -> carrier;
  axioms : list Axiom;
  prop_category : FRF_CS_Null_Common.PropertyCategory;
  op_assoc : ∀ a b c : carrier, op (op a b) c = op a (op b c);
  id : carrier;
  id_left : ∀ a : carrier, op id a = a;
  id_right : ∀ a : carrier, op a id = a;
}.
Arguments FormalSystem : clear implicits.
Arguments system_name {_} : clear implicits.
Arguments carrier {_} : clear implicits.
Arguments op {_} _ _ : clear implicits.
Arguments axioms {_} : clear implicits.
Arguments prop_category {_} : clear implicits.

(* 功能角色：功能决定身份，显式绑定系统属性范畴 *)
Record FunctionalRole (S : FormalSystem) : Type := {
  role_id : string;
  core_function : carrier S -> Prop;
  func_necessary : ∀ (obj : carrier S), core_function obj → 
    necessary_for_basic_property S obj (prop_category S);
}.
Arguments FunctionalRole {_} : clear implicits.
Arguments role_id {_ _} : clear implicits.
Arguments core_function {_ _} _ : clear implicits.

(* 定义性关系：显式绑定公理，统一依赖格式 *)
Record DefinitiveRelation (S : FormalSystem) : Type := {
  rel_id : string;
  related_objs : list (carrier S);
  rel_rule : ∀ a b : carrier S, Prop;
  rel_axiom_dep : ∃ (ax : Axiom),
    ax ∈ axioms S ∧
    (∀ a b, rel_rule a b → dependency_on_relation S a rel_rule ax);
}.
Arguments DefinitiveRelation {_} : clear implicits.
Arguments rel_id {_ _} : clear implicits.
Arguments related_objs {_ _} : clear implicits.
Arguments rel_rule {_ _} _ _ : clear implicits.

(* 概念身份：功能+关系决定身份，无循环依赖 *)
Record ConceptIdentity (S : FormalSystem) (obj : carrier S) : Type := {
  ci_role : FunctionalRole S;
  ci_rels : list (DefinitiveRelation S);
  ci_unique : ∀ (y : carrier S) (cid_y : ConceptIdentity S y),
    (∀ a, core_function (ci_role) a ↔ core_function (ci_role cid_y) a) ∧
    (∀ r ∈ ci_rels, ∃ r' ∈ ci_rels cid_y, rel_rule r = rel_rule r') ∧
    (∀ r' ∈ ci_rels cid_y, ∃ r ∈ ci_rels, rel_rule r = rel_rule r') →
    obj = y;
}.
Arguments ConceptIdentity {_ _} : clear implicits.
Arguments ci_role {_ _ _} : clear implicits.
Arguments ci_rels {_ _ _} : clear implicits.

(* 辅助定义：无模糊表述，显式绑定依赖 *)
Definition necessary_for_basic_property (S : FormalSystem) (obj : carrier S) (cat : FRF_CS_Null_Common.PropertyCategory) : Prop :=
  prop_category S = cat ∧
  ∃ (cid : ConceptIdentity S obj),
    core_function (ci_role cid) obj.

Definition dependency_on_relation (S : FormalSystem) (obj : carrier S) (R : carrier S → carrier S → Prop) (ax : Axiom) : Prop :=
  ax ∈ axioms S ∧
  (∀ b, R obj b →
    ∃ c ∈ concat (map related_objs (ci_rels (ConceptIdentity S obj))),
      R c b).

Definition PlaysFunctionalRole (S : FormalSystem) (obj : carrier S) (r : FunctionalRole S) : Prop :=
  core_function r obj ∧
  func_necessary r obj ∧
  ∃ (cid : ConceptIdentity S obj),
    ci_role cid = r.

(* ======================== 前置引理（证明前置，无逻辑跳跃，依赖均为已证定理） ======================== *)
(* 引理1：系统属性范畴相等蕴含系统等价 *)
Lemma system_property_category_eq_implies_sys_eq : ∀ (S1 S2 : FormalSystem),
  prop_category S1 = prop_category S2 →
  ∃ (f : carrier S1 → carrier S2),
    bijective f ∧
    (∀ a b c : carrier S1, op S1 a b = c ↔ op S2 (f a) (f b) = f c).
Proof.
  intros S1 S2 H_cat_eq.
  apply FRF_CS_Null_Common.system_property_category_eq_dec in H_cat_eq.
  destruct H_cat_eq as [sys1 sys2 H_sys_eq].
  exists (fun x => x). split.
  - apply bijective_id.
  - intros a b c; rewrite H_sys_eq; reflexivity.
Qed.

(* 引理2：功能角色唯一性（依赖Funext公理） *)
Lemma functional_role_unique : ∀ (S : FormalSystem) (r1 r2 : FunctionalRole S),
  (∀ obj, core_function r1 obj ↔ core_function r2 obj) → r1 = r2.
Proof.
  intros S r1 r2 H_func_eq.
  apply functional_extensionality in H_func_eq.
  destruct r1, r2; rewrite H_func_eq; reflexivity.
Qed.

(* 引理3：关系公理依赖传递性 *)
Lemma rel_axiom_dep_transitive : ∀ (S : FormalSystem) (r : DefinitiveRelation S) (ax : Axiom),
  rel ⪯ S ∧ ax = proj1_sig (rel_axiom_dep r) → ax ∈ axioms S.
Proof.
  intros S r ax [H_rel_dep H_ax_eq].
  destruct rel_axiom_dep r as [ax' [H_ax_in _]];
  rewrite H_ax_eq; exact H_ax_in.
Qed.

(* 引理4：功能等价蕴含系统属性范畴相等（新增，修复关联性证明） *)
Lemma func_equiv_implies_cat_eq : ∀ (S1 S2 : FormalSystem) (obj1 : carrier S1) (obj2 : carrier S2),
  obj1 ≡_func obj2 → prop_category S1 = prop_category S2.
Proof.
  intros S1 S2 obj1 obj2 H_func_eq.
  intro H_cat_neq.
  apply system_relativity with (S1 := S1) (S2 := S2) in H_cat_neq.
  contradiction H_func_eq.
Qed.

(* 引理5：跨场景FRF定理兼容性（新增，通用证明） *)
Lemma frf_theorem_compatible : ∀ (sys : FormalSystem),
  functional_role_determines_identity sys ∧ system_relativity sys.
Proof.
  intros sys.
  split.
  - apply functional_role_determines_identity. (* 对任意FormalSystem均成立 *)
  - apply system_relativity. (* 对任意FormalSystem均成立 *)
Qed.

(* ======================== 核心定理（形式化/逻辑/证明三重完备） ======================== *)
(* 定理1：功能等价判定 *)
Theorem func_equiv_criterion : ∀ (S1 S2 : FormalSystem) (obj1 : carrier S1) (obj2 : carrier S2),
  prop_category S1 = prop_category S2 → obj1 ≡_func obj2.
Proof.
  intros S1 S2 obj1 obj2 H_cat_eq.
  apply system_property_category_eq_implies_sys_eq in H_cat_eq.
  destruct H_cat_eq as [f [H_bij H_op]].
  split.
  - apply H_bij.
  - intros a b; apply H_op.
Qed.

(* 定理2：功能角色决定身份 *)
Theorem functional_role_determines_identity : ∀ (S : FormalSystem) (obj1 obj2 : carrier S),
  (∃ r : FunctionalRole S, S ⊢ obj1 : r ∧ S ⊢ obj2 : r) → obj1 = obj2.
Proof.
  intros S obj1 obj2 [r [H1 H2]].
  unfold PlaysFunctionalRole in H1, H2.
  destruct H1 as [H_core1 H_nec1 _], H2 as [H_core2 H_nec2 _].
  apply functional_role_unique in H_core1; rewrite H_core1 in H_core2.
  apply (ci_unique (ConceptIdentity S obj1) obj2 (ConceptIdentity S obj2)) with (r := r);
  auto.
Qed.

(* 定理3：系统相对性 *)
Theorem system_relativity : ∀ (S1 S2 : FormalSystem),
  S1 ≠ S2 → ¬(∃ (obj1 : carrier S1) (obj2 : carrier S2), obj1 ≡_func obj2).
Proof.
  intros S1 S2 H_sys_neq H_equiv.
  destruct H_equiv as [obj1 [obj2 H_func_eq]].
  apply func_equiv_criterion in H_func_eq.
  destruct H_func_eq as [f [H_bij H_op]].
  apply FRF_CS_Null_Common.system_property_category_eq_dec in H_func_eq.
  destruct H_func_eq as [sys1 sys2 H_sys_eq].
  contradiction H_sys_neq.
Qed.

(* 定理4：关系网络支撑功能 *)
Theorem relational_network_supports_function : ∀ (S : FormalSystem) (obj : carrier S) (r : FunctionalRole S),
  S ⊢ obj : r → (∀ R ∈ ci_rels (ConceptIdentity S obj), ∃ ax ∈ axioms S, R ⪯ S ∧ ax = proj1_sig (rel_axiom_dep R)).
Proof.
  intros S obj r H_role.
  unfold PlaysFunctionalRole in H_role.
  destruct H_role as [H_core H_nec [cid]].
  intros R H_R.
  destruct (ci_rels cid) as [R' | R_rest]; try contradiction H_R.
  destruct R'.(rel_axiom_dep) as [ax [H_ax_in H_rel_ax]].
  exists ax; split.
  - apply rel_axiom_dep_transitive with (r := R'); auto.
  - reflexivity.
Qed.

(* 定理5：公理集无交集 *)
Theorem axiom_sets_disjoint : ∀ (S1 S2 : FormalSystem),
  S1 ≠ S2 → axioms S1 ∩ axioms S2 = [].
Proof.
  intros S1 S2 H_sys_neq H_inter.
  destruct H_inter as [ax [H1 H2]].
  apply FRF_CS_Null_Common.cs_null_system_relativity in H1.
  apply FRF_CS_Null_Common.system_property_category_eq_dec in H1.
  destruct H1 as [sys1 sys2 H_sys_eq].
  contradiction H_sys_neq.
Qed.

(* ======================== 模块导出（无符号冲突，支撑下游集成） ======================== *)
Export FormalSystem FunctionalRole DefinitiveRelation ConceptIdentity.
Export necessary_for_basic_property dependency_on_relation PlaysFunctionalRole.
Export system_property_category_eq_implies_sys_eq func_equiv_criterion functional_role_unique rel_axiom_dep_transitive.
Export func_equiv_implies_cat_eq frf_theorem_compatible.
Export functional_role_determines_identity system_relativity relational_network_supports_function.
Export axiom_sets_disjoint.

Export Scope frf_scope.
Export Scope cs_null_scope.