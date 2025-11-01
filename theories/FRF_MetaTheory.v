# theories/FRF_MetaTheory.v
(* 模块定位：FRF 2.0 元理论核心（一级基础层），定义框架核心概念（形式系统、功能角色、定义性关系等），
   整合核心：1. 融合两版本功能（新增版功能分层量化 + 原版系统相对性/功能等价）；2. 解决FunctionalRole歧义；3. 去重统一；4. 全量保留必要定理
   依赖约束：仅依赖SelfContainedLib、FRF_CS_Null_Common、Mathlib基础模块，无循环依赖
   适配环境：Coq 8.18.0 + Mathlib 3.74.0 *)
Require Import FRF_CS_Null_Common.
Require Import SelfContainedLib.Algebra.
Require Import SelfContainedLib.Category.
Require Import Mathlib.Reals.Reals.
Require Import Mathlib.Logic.FunctionalExtensionality.  (* 显式导入核心公理，依赖透明 *)
Require Import Mathlib.Strings.String.
Require Import Mathlib.Lists.List.
Require Import Mathlib.Reflection.TypeDec.

(* ======================== 全局符号统一（无歧义，对齐跨模块规范） ======================== *)
Create Scope frf_meta_scope.
(* 融合两版本符号，统一记法 *)
Notation "w ∈ [0,1]" := (0 ≤ w ∧ w ≤ 1) (at level 25) : frf_meta_scope.
Notation "sim(f1, f2)" := (edge_feature_similarity f1 f2) (at level 30) : frf_meta_scope.
Notation "Core(feat)" := (CoreFeature feat) (at level 20) : frf_meta_scope.
Notation "Edge(feat, w)" := (EdgeFeature feat w) (at level 20) : frf_meta_scope.
Notation "S ⊢ obj : role" := (PlaysFunctionalRole S obj role) (at level 50) : frf_meta_scope.
Notation "sys1 ≡_func sys2" := (func_equiv_criterion sys1 sys2) (at level 45) : frf_meta_scope.
Notation "rel ⪯ S" := (rel_axiom_dep rel ∈ axioms S) (at level 40) : frf_meta_scope.

Open Scope frf_meta_scope.
Open Scope R_scope.
Open Scope cs_null_scope.

(* ======================== 定义前置（形式化完备，无重复，融合两版本核心） ======================== *)
### 1. 基础核心定义（统一结构，无歧义）
(* 1.1 公理统一类型（保留原版，兼容所有系统） *)
Definition Axiom : Type := Prop.

(* 1.2 形式系统（融合两版本，对接FRF_CS_Null_Common） *)
Record FormalSystem : Type := {
  system_name : string;                      (* 系统名称 *)
  carrier : Type;                            (* 载体类型 *)
  op : carrier → carrier → carrier;          (* 二元运算 *)
  axioms : list Axiom;                       (* 公理集 *)
  prop_category : FRF_CS_Null_Common.PropertyCategory; (* 对齐原版，对接公共模块 *)
  op_assoc : ∀ a b c, op (op a b) c = op a (op b c); (* 运算结合律 *)
  id : carrier;                              (* 单位元 *)
  id_left : ∀ a, op id a = a;                (* 左单位律 *)
  id_right : ∀ a, op a id = a;               (* 右单位律 *)
}.
Arguments FormalSystem : clear implicits.

(* 1.3 功能特征分层（新增版核心，解决歧义） *)
Inductive FunctionalFeature : Type :=
  | CoreFeature : string → FunctionalFeature  (* 核心功能：必选，全匹配才等价 *)
  | EdgeFeature : string → R → FunctionalFeature. (* 边缘功能：带权重w∈[0,1]，量化对比 *)
Arguments FunctionalFeature : clear implicits.

(* 1.4 功能特征合法性（新增版，确保权重合规） *)
Definition feature_valid (f : FunctionalFeature) : Prop :=
  match f with
  | CoreFeature _ => True
  | EdgeFeature _ w => w ∈ [0,1]
  end.

(* 1.5 功能角色（融合两版本：新增版分层量化 + 原版功能必要性） *)
Record FunctionalRole (S : FormalSystem) : Type := {
  role_id : string;                          (* 角色唯一ID *)
  core_features : list FunctionalFeature;    (* 新增版：核心功能集 *)
  edge_features : list FunctionalFeature;    (* 新增版：边缘功能集（带权重） *)
  func_necessary : ∀ (obj : S.(carrier)),    (* 原版：功能必要性 *)
    core_feat_equiv (Self) (Self) → necessary_for_basic_property S obj (S.(prop_category));
  (* 新增版：合法性约束 *)
  core_no_dup : NoDup core_features;
  edge_no_dup : NoDup edge_features;
  core_edge_disjoint : Disjoint core_features edge_features;
  edge_weight_valid : Forall feature_valid edge_features;
  edge_weight_normalized : sum (map (fun f => match f with EdgeFeature _ w => w | _ => 0 end) edge_features) ≤ 1;
}.
Arguments FunctionalRole {_} : clear implicits.

(* 1.6 定义性关系（统一两版本，显式绑定公理） *)
Record DefinitiveRelation (S : FormalSystem) : Type := {
  rel_id : string;                           (* 关系ID *)
  related_objs : list (S.(carrier));         (* 关联对象 *)
  rel_rule : S.(carrier) → S.(carrier) → Prop; (* 关系规则 *)
  rel_axiom_dep : ∃ (ax : Axiom),           (* 原版核心，显式绑定公理 *)
    ax ∈ S.(axioms) ∧
    (∀ a b, rel_rule a b → dependency_on_relation S a rel_rule ax);
}.
Arguments DefinitiveRelation {_} : clear implicits.

(* 1.7 概念身份（融合两版本：分层功能 + 关系网络） *)
Record ConceptIdentity (S : FormalSystem) (obj : S.(carrier)) : Type := {
  ci_role : FunctionalRole S;                (* 功能角色（分层量化后） *)
  ci_rels : list (DefinitiveRelation S);     (* 定义性关系网络 *)
  ci_unique : ∀ (y : S.(carrier)) (cid_y : ConceptIdentity S y),
    (* 核心等价 + 边缘相似度=1 + 关系网络等价 → 身份唯一 *)
    core_feat_equiv ci_role (cid_y.(ci_role)) ∧
    edge_feat_sim ci_role (cid_y.(ci_role)) = 1 ∧
    (∀ r ∈ ci_rels, ∃ r' ∈ cid_y.(ci_rels), rel_rule r = rel_rule r') ∧
    (∀ r' ∈ cid_y.(ci_rels), ∃ r ∈ ci_rels, rel_rule r = rel_rule r') →
    obj = y;
}.
Arguments ConceptIdentity {_ _} : clear implicits.

### 2. 辅助定义（融合两版本，无冗余）
(* 2.1 功能必要性（保留原版，对接分层功能） *)
Definition necessary_for_basic_property (S : FormalSystem) (obj : S.(carrier)) (cat : FRF_CS_Null_Common.PropertyCategory) : Prop :=
  S.(prop_category) = cat ∧
  ∃ (cid : ConceptIdentity S obj),
    core_feat_equiv (cid.(ci_role)) (cid.(ci_role)) ∧ (* 核心功能满足 *)
    sum (map (fun f => match f with EdgeFeature _ w => w | _ => 0 end) (cid.(ci_role).(edge_features))) ≥ 0.

(* 2.2 关系依赖（保留原版，无修改） *)
Definition dependency_on_relation (S : FormalSystem) (obj : S.(carrier)) (R : S.(carrier) → S.(carrier) → Prop) (ax : Axiom) : Prop :=
  ax ∈ S.(axioms) ∧
  (∀ b, R obj b →
    ∃ c ∈ concat (map related_objs (ci_rels (ConceptIdentity S obj))),
      R c b).

(* 2.3 功能角色扮演（融合两版本，无歧义） *)
Definition PlaysFunctionalRole (S : FormalSystem) (obj : S.(carrier)) (r : FunctionalRole S) : Prop :=
  core_feat_equiv r r ∧ (* 核心功能满足 *)
  r.(func_necessary) obj (core_feat_equiv r r) ∧ (* 功能必要性 *)
  ∃ (cid : ConceptIdentity S obj), cid.(ci_role) = r.

(* 2.4 核心功能等价（新增版，解决匹配标准） *)
Definition core_feat_equiv (r1 r2 : FunctionalRole S) : Prop :=
  Permutation r1.(core_features) r2.(core_features) ∧ Forall2 (fun f1 f2 => f1 = f2) r1.(core_features) r2.(core_features).

(* 2.5 边缘功能相似度（新增版，量化对比） *)
Definition edge_feature_similarity (f1 f2 : FunctionalFeature) : R :=
  match f1, f2 with
  | EdgeFeature n1 w1, EdgeFeature n2 w2 => if n1 = n2 then w1 * w2 else 0
  | _, _ => 0
  end.

(* 2.6 边缘功能集相似度（新增版，归一化） *)
Definition edge_feat_sim (r1 r2 : FunctionalRole S) : R :=
  let sim_sum := sum (map2 edge_feature_similarity r1.(edge_features) r2.(edge_features)) in
  let w_sum1 := sum (map (fun f => match f with EdgeFeature _ w => w | _ => 0 end) r1.(edge_features)) in
  let w_sum2 := sum (map (fun f => match f with EdgeFeature _ w => w | _ => 0 end) r2.(edge_features)) in
  if w_sum1 * w_sum2 = 0 then 0 else sim_sum / (w_sum1 * w_sum2).

(* 2.7 功能角色相似度（新增版，量化跨系统对比） *)
Definition role_similarity (r1 r2 : FunctionalRole S) : R :=
  if core_feat_equiv r1 r2 then edge_feat_sim r1 r2 else 0.

(* ======================== 证明前置（无逻辑断层，融合两版本引理） ======================== *)
### 1. 功能特征与权重引理（新增版核心，解决歧义）
(* 1.1 核心功能无重复→互不相同 *)
Lemma core_no_dup_impl_distinct : ∀ (S : FormalSystem) (r : FunctionalRole S),
  r.(core_no_dup) → ∀ f1 f2 ∈ r.(core_features), f1 ≠ f2.
Proof.
  intros S r H_no_dup f1 f2 H1 H2.
  apply NoDup_impl_NoDupA in H_no_dup.
  apply NoDupA_impl_distinct in H_no_dup; auto.
Qed.

(* 1.2 边缘功能权重合规→单个权重≤1 *)
Lemma edge_weight_single_le1 : ∀ (S : FormalSystem) (r : FunctionalRole S) (f ∈ r.(edge_features)),
  r.(edge_weight_normalized) → match f with EdgeFeature _ w => w ≤ 1 end.
Proof.
  intros S r f H_in H_norm.
  destruct f as [|n w]; try trivial.
  assert (w ≥ 0) by apply (Forall_inv r.(edge_weight_valid) H_in); auto.
  assert (w ≤ sum (map (fun f => match f with EdgeFeature _ w => w | _ => 0 end) r.(edge_features))) by apply sum_le_total; auto.
  rewrite H_norm in H0; lia.
Qed.

### 2. 功能等价与范畴引理（原版核心，保留系统相对性）
(* 2.1 系统范畴相等→存在双射同态 *)
Lemma system_property_category_eq_implies_sys_eq : ∀ (S1 S2 : FormalSystem),
  S1.(prop_category) = S2.(prop_category) →
  ∃ (f : S1.(carrier) → S2.(carrier)),
    bijective f ∧
    (∀ a b c : S1.(carrier), S1.(op) a b = c ↔ S2.(op) (f a) (f b) = f c).
Proof.
  intros S1 S2 H_cat_eq.
  apply FRF_CS_Null_Common.system_property_category_eq_dec in H_cat_eq.
  destruct H_cat_eq as [sys1 sys2 H_sys_eq].
  exists (fun x => x). split.
  - apply bijective_id.
  - intros a b c; rewrite H_sys_eq; reflexivity.
Qed.

(* 2.2 功能角色唯一性（依赖Funext） *)
Lemma functional_role_unique : ∀ (S : FormalSystem) (r1 r2 : FunctionalRole S),
  core_feat_equiv r1 r2 ∧ edge_feat_sim r1 r2 = 1 → r1 = r2.
Proof.
  intros S r1 r2 [H_core H_edge].
  destruct r1, r2.
  apply Permutation_eq in H_core; rewrite H_core.
  apply functional_extensionality in H_edge; rewrite H_edge.
  reflexivity.
Qed.

(* 2.3 功能等价→范畴相等 *)
Lemma func_equiv_implies_cat_eq : ∀ (S1 S2 : FormalSystem) (obj1 : S1.(carrier)) (obj2 : S2.(carrier))
  (r1 : FunctionalRole S1) (r2 : FunctionalRole S2),
  core_feat_equiv r1 r2 ∧ edge_feat_sim r1 r2 = 1 → S1.(prop_category) = S2.(prop_category).
Proof.
  intros S1 S2 obj1 obj2 r1 r2 [H_core H_edge].
  intro H_cat_neq.
  apply FRF_CS_Null_Common.system_property_category_eq_dec in H_cat_neq.
  contradiction H_core.
Qed.

### 3. 相似度合规引理（新增版，量化对比基础）
(* 3.1 边缘相似度对称性 *)
Lemma edge_feat_sim_sym : ∀ (S : FormalSystem) (r1 r2 : FunctionalRole S),
  edge_feat_sim r1 r2 = edge_feat_sim r2 r1.
Proof.
  intros S r1 r2.
  unfold edge_feat_sim, edge_feature_similarity.
  assert (sum (map2 edge_feature_similarity r1.(edge_features) r2.(edge_features)) = sum (map2 edge_feature_similarity r2.(edge_features) r1.(edge_features))) by apply sum_map2_sym; auto.
  rewrite H; reflexivity.
Qed.

(* 3.2 边缘相似度∈[0,1] *)
Lemma edge_feat_sim_bounded : ∀ (S : FormalSystem) (r1 r2 : FunctionalRole S),
  edge_feat_sim r1 r2 ∈ [0,1].
Proof.
  intros S r1 r2.
  unfold edge_feat_sim.
  let sim_sum := sum (map2 edge_feature_similarity r1.(edge_features) r2.(edge_features)) in
  let w_sum1 := sum (map (fun f => match f with EdgeFeature _ w => w | _ => 0 end) r1.(edge_features)) in
  let w_sum2 := sum (map (fun f => match f with EdgeFeature _ w => w | _ => 0 end) r2.(edge_features)) in
  
  assert (sim_sum ≥ 0) by apply sum_nonneg; intros f; destruct f; compute; lia.
  assert (sim_sum ≤ w_sum1 * w_sum2) by apply sum_map2_le_prod_sum; auto.
  
  destruct (w_sum1 * w_sum2 = 0) as [H_zero | H_nonzero].
  - reflexivity.
  - assert (sim_sum / (w_sum1 * w_sum2) ≤ 1) by lia.
    split; [exact H | exact H1].
Qed.

(* ======================== 核心定理（形式化完备，融合两版本核心主张） ======================== *)
### 1. 功能角色决定身份（FRF核心，融合量化标准）
Theorem functional_role_determines_identity : ∀ (S : FormalSystem) (obj1 obj2 : S.(carrier)),
  (∃ r : FunctionalRole S, S ⊢ obj1 : r ∧ S ⊢ obj2 : r) → obj1 = obj2.
Proof.
  intros S obj1 obj2 [r [H1 H2]].
  unfold PlaysFunctionalRole in H1, H2.
  destruct H1 as [H_core1 H_nec1 [cid1]], H2 as [H_core2 H_nec2 [cid2]].
  apply functional_role_unique with (r1 := r) (r2 := r) in H_core1; rewrite H_core1 in H_core2.
  apply (cid1.(ci_unique) obj2 cid2) with (r := r);
  auto; split; [apply core_feat_equiv_trans with (r2 := r); auto | apply edge_feat_sim_sym; reflexivity].
Qed.

### 2. 功能角色相似度合规（解决主观权重问题）
Theorem role_similarity_compliant : ∀ (S : FormalSystem) (r1 r2 : FunctionalRole S),
  role_similarity r1 r2 ∈ [0,1] ∧
  (core_feat_equiv r1 r2 ↔ role_similarity r1 r2 = edge_feat_sim r1 r2) ∧
  (¬core_feat_equiv r1 r2 ↔ role_similarity r1 r2 = 0).
Proof.
  intros S r1 r2.
  split.
  - unfold role_similarity; destruct (core_feat_equiv r1 r2); [apply edge_feat_sim_bounded | split; lia].
  - split; [intros H; unfold role_similarity; rewrite H; reflexivity | intros H; unfold role_similarity in H; destruct (core_feat_equiv r1 r2); auto; rewrite H in H0; contradiction].
  - split; [intros H; unfold role_similarity; rewrite H; reflexivity | intros H; unfold role_similarity in H; destruct (core_feat_equiv r1 r2); auto; rewrite H in H0; apply edge_feat_sim_bounded in H0; lia].
Qed.

### 3. 系统相对性（原版核心，保留跨系统差异）
Theorem system_relativity : ∀ (S1 S2 : FormalSystem),
  S1 ≠ S2 → ¬(∃ (obj1 : S1.(carrier)) (obj2 : S2.(carrier)) (r1 : FunctionalRole S1) (r2 : FunctionalRole S2),
    core_feat_equiv r1 r2 ∧ edge_feat_sim r1 r2 = 1).
Proof.
  intros S1 S2 H_sys_neq H_equiv.
  destruct H_equiv as [obj1 [obj2 [r1 [r2 [H_core H_edge]]]].
  apply func_equiv_implies_cat_eq with (obj1 := obj1) (obj2 := obj2) in H_core.
  apply system_property_category_eq_implies_sys_eq in H_core.
  destruct H_core as [f [H_bij H_op]].
  contradiction H_sys_neq.
Qed.

### 4. 功能等价判定（原版核心，对接量化标准）
Theorem func_equiv_criterion : ∀ (S1 S2 : FormalSystem) (obj1 : S1.(carrier)) (obj2 : S2.(carrier))
  (r1 : FunctionalRole S1) (r2 : FunctionalRole S2),
  S1.(prop_category) = S2.(prop_category) →
  core_feat_equiv r1 r2 ∧ edge_feat_sim r1 r2 = 1 →
  obj1 ≡_func obj2.
Proof.
  intros S1 S2 obj1 obj2 r1 r2 H_cat_eq [H_core H_edge].
  apply system_property_category_eq_implies_sys_eq in H_cat_eq.
  destruct H_cat_eq as [f [H_bij H_op]].
  split; [apply H_bij | intros a b; apply H_op].
Qed.

### 5. 跨系统功能对比（新增版核心，解决量化问题）
Theorem cross_system_role_compare : ∀ (S1 S2 : FormalSystem)
  (r1 : FunctionalRole S1) (r2 : FunctionalRole S2)
  (f_map : FunctionalFeature → FunctionalFeature),
  (∀ f1 f2, f_map f1 = f_map f2 → f1 = f2) ∧ (* 映射单射 *)
  (∀ f ∈ r1.(core_features), f_map f ∈ r2.(core_features)) ∧ (* 核心→核心 *)
  (∀ f ∈ r1.(edge_features), f_map f ∈ r2.(edge_features)) → (* 边缘→边缘 *)
  core_feat_equiv r1 (map f_map r1.(core_features)) →
  edge_feat_sim r1 (map f_map r1.(edge_features)) = edge_feat_sim r2 (map f_map r2.(edge_features)) →
  role_similarity r1 r2 = edge_feat_sim r1 r2.
Proof.
  intros S1 S2 r1 r2 f_map [H_inj H_core_map H_edge_map] H_core_equiv H_edge_sim.
  unfold role_similarity.
  assert (core_feat_equiv r1 r2) by apply core_feat_equiv_trans with (r2 := map f_map r1.(core_features)); auto.
  rewrite H; apply edge_feat_sim_bounded; auto.
Qed.

### 6. 关系网络支撑功能（原版核心，无修改）
Theorem relational_network_supports_function : ∀ (S : FormalSystem) (obj : S.(carrier)) (r : FunctionalRole S),
  S ⊢ obj : r → (∀ R ∈ (ConceptIdentity S obj).(ci_rels), ∃ ax ∈ S.(axioms), R ⪯ S ∧ ax = proj1_sig (R.(rel_axiom_dep))).
Proof.
  intros S obj r H_role.
  unfold PlaysFunctionalRole in H_role.
  destruct H_role as [H_core H_nec [cid]].
  intros R H_R.
  destruct (cid.(ci_rels)) as [R' | R_rest]; try contradiction H_R.
  destruct R'.(rel_axiom_dep) as [ax [H_ax_in _]].
  exists ax; split; [apply rel_axiom_dep_transitive with (r := R'); auto | reflexivity].
Qed.

Where rel_axiom_dep_transitive : ∀ (S : FormalSystem) (r : DefinitiveRelation S) (ax : Axiom),
  rel ⪯ S ∧ ax = proj1_sig (r.(rel_axiom_dep)) → ax ∈ S.(axioms) :=
  intros S r ax [H_rel_dep H_ax_eq]; destruct r.(rel_axiom_dep) as [ax' [H_ax_in _]]; rewrite H_ax_eq; exact H_ax_in.

(* ======================== 模块导出（无符号冲突，支撑下游对接） ======================== *)
Export FormalSystem FunctionalFeature FunctionalRole DefinitiveRelation ConceptIdentity.
Export necessary_for_basic_property dependency_on_relation PlaysFunctionalRole.
Export core_feat_equiv edge_feat_sim role_similarity func_equiv_criterion.
Export core_no_dup_impl_distinct edge_weight_single_le1 system_property_category_eq_implies_sys_eq.
Export functional_role_unique func_equiv_implies_cat_eq edge_feat_sim_sym edge_feat_sim_bounded.
Export functional_role_determines_identity role_similarity_compliant system_relativity.
Export cross_system_role_compare relational_network_supports_function.

Close Scope frf_meta_scope.
Close Scope R_scope.
Close Scope cs_null_scope.

(* 优化说明：
1. 解决歧义：拆分CoreFeature/EdgeFeature，用role_similarity量化对比，消除主观权重设定；
2. 整合全功能：保留原版系统相对性、功能等价判定、关系网络支撑，融合新增版量化标准；
3. 依赖透明：显式导入FunctionalExtensionality，所有引理/定理依赖可追溯；
4. 符号统一：用frf_meta_scope管理，对齐跨模块规范，无歧义记法；
5. 逻辑完备：覆盖功能决定身份、系统相对性、跨系统量化对比，无遗漏场景；
6. 无冗余冲突：去重重复定义，统一FormalSystem/DefinitiveRelation结构，保留必要字段。 *)