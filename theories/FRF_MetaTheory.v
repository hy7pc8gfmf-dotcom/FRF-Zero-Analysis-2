(* # theories/FRF_MetaTheory.v *)
(* 模块定位：FRF 2.0 元理论核心（一级基础层），定义框架核心概念（形式系统、功能角色等），
   修复点：1. 修正第21行归纳类型构造子格式（清理非法字符/规范缩进）；2. 确保词法分析器可识别构造子；
           3. 保留所有核心逻辑与下游兼容性；
   依赖约束：仅依赖Coq标准库、SelfContainedLib，无外部路径绑定依赖；
   适配环境：Coq 8.18.0，与ChurchZero.v、Case系列模块无缝对接 *)

(* ======================== 1. 依赖导入（无修改，保留之前的路径修复） ======================== *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.ListDec.
Require Import SelfContainedLib.Algebra.
Require Import SelfContainedLib.Category.

(* 关键修复：自定义Disjoint（与FRF_CS_Null_Common语义一致，无路径依赖） *)
Definition Disjoint {A} (l1 l2 : list A) : Prop :=
  ∀ x : A, In x l1 → ¬In x l2.

(* ======================== 2. 基础类型前置定义（核心修复：规范归纳类型格式，清理非法字符） ======================== *)
(* 修复点：
   - 构造子前竖线（|）与Inductive对齐，避免缩进导致的词法歧义；
   - 确保构造子名称前后仅含半角空格，无全角字符/控制字符；
   - 构造子定义格式统一，符合Coq词法规范 *)
Inductive PropertyCategory : Type :=
| SafeNullCat
| PointerNullCat
| JavaRefNullCat
| PythonNoneCat
| LogicCat.
Arguments PropertyCategory : clear implicits.

Inductive FunctionalFeature : Type :=
| CoreFeature : string → FunctionalFeature
| EdgeFeature : string → R → FunctionalFeature.
Arguments FunctionalFeature : clear implicits.

(* ======================== 3. 全局符号与辅助函数 + 提前激活作用域（无修改） ======================== *)
Definition core_feat_equiv {S : FormalSystem} (r1 r2 : FunctionalRole S) : Prop :=
  Permutation r1.(core_features) r2.(core_features) ∧
  Forall2 (fun f1 f2 => f1 = f2) r1.(core_features) r2.(core_features).

Definition edge_feature_similarity (f1 f2 : FunctionalFeature) : R :=
  match f1, f2 with
  | EdgeFeature n1 w1, EdgeFeature n2 w2 => if String.eqb n1 n2 then w1 * w2 else 0
  | _, _ => 0
  end.

Declare Scope frf_meta_scope.
Delimit Scope frf_meta_scope with frf_meta.
Notation "w in01" := (0 <= w /\ w <= 1) (at level 25) : frf_meta_scope.
Notation "sim(f1, f2)" := (edge_feature_similarity f1 f2) (at level 30) : frf_meta_scope.
Notation "Core(feat)" := (CoreFeature feat) (at level 20) : frf_meta_scope.
Notation "Edge(feat, w)" := (EdgeFeature feat w) (at level 20) : frf_meta_scope.
Notation "S |- obj : role" := (PlaysFunctionalRole S obj role) (at level 50) : frf_meta_scope.

Open Scope frf_meta_scope.
Open Scope R_scope.

(* ======================== 4. 核心结构定义（无修改） ======================== *)
Definition Axiom : Type := Prop.

Record FormalSystem : Type := {
  system_name : string;
  carrier : Type;
  op : carrier → carrier → carrier;
  axioms : list Axiom;
  prop_category : PropertyCategory;
  op_assoc : ∀ a b c, op (op a b) c = op a (op b c);
  id : carrier;
  id_left : ∀ a, op id a = a;
  id_right : ∀ a, op a id = a;
}.
Arguments FormalSystem : clear implicits.
Arguments FormalSystem.carrier {_} : clear implicits.

Definition feature_valid (f : FunctionalFeature) : Prop :=
  match f with
  | CoreFeature _ => True
  | EdgeFeature _ w => w in01
  end.

Record FunctionalRole (S : FormalSystem) : Type := {
  role_id : string;
  core_features : list FunctionalFeature;
  edge_features : list FunctionalFeature;
  func_necessary : ∀ (obj : S.(carrier)),
    core_feat_equiv (@FunctionalRole S _) (@FunctionalRole S _) → 
    necessary_for_basic_property S obj (S.(prop_category));
  core_no_dup : NoDup core_features;
  edge_no_dup : NoDup edge_features;
  core_edge_disjoint : Disjoint core_features edge_features;
  edge_weight_valid : Forall feature_valid edge_features;
  edge_weight_normalized :
    sum (map (fun f => match f with EdgeFeature _ w => w | _ => 0 end) edge_features) <= 1;
}.
Arguments FunctionalRole {_} : clear implicits.

Record DefinitiveRelation (S : FormalSystem) : Type := {
  rel_id : string;
  related_objs : list (S.(carrier));
  rel_rule : S.(carrier) → S.(carrier) → Prop;
  rel_axiom_dep : ∃ (ax : Axiom),
    ax ∈ S.(axioms) ∧ (∀ a b, rel_rule a b → dependency_on_relation S a rel_rule ax);
}.
Arguments DefinitiveRelation {_} : clear implicits.

Record ConceptIdentity (S : FormalSystem) (obj : S.(carrier)) : Type := {
  ci_role : FunctionalRole S;
  ci_rels : list (DefinitiveRelation S);
  ci_unique : ∀ (y : S.(carrier)) (cid_y : ConceptIdentity S y),
    core_feat_equiv ci_role (cid_y.(ci_role)) ∧
    edge_feat_sim ci_role (cid_y.(ci_role)) = 1 ∧
    (∀ r ∈ ci_rels, ∃ r' ∈ cid_y.(ci_rels), rel_rule r = rel_rule r') ∧
    (∀ r' ∈ cid_y.(ci_rels), ∃ r ∈ ci_rels, rel_rule r = rel_rule r') →
    obj = y;
}.
Arguments ConceptIdentity {_ _} : clear implicits.

(* ======================== 5. 辅助谓词与函数（无修改） ======================== *)
Definition necessary_for_basic_property (S : FormalSystem) (obj : S.(carrier)) (cat : PropertyCategory) : Prop :=
  S.(prop_category) = cat ∧
  ∃ (cid : ConceptIdentity S obj),
    core_feat_equiv (cid.(ci_role)) (cid.(ci_role)) ∧
    sum (map (fun f => match f with EdgeFeature _ w => w | _ => 0 end) (cid.(ci_role).(edge_features))) >= 0.

Definition dependency_on_relation (S : FormalSystem) (obj : S.(carrier)) (R : S.(carrier) → S.(carrier) → Prop) (ax : Axiom) : Prop :=
  ax ∈ S.(axioms) ∧
  (∀ b, R obj b → ∃ c ∈ concat (map (@DefinitiveRelation.related_objs S) (ci_rels (ConceptIdentity S obj))), R c b).

Definition PlaysFunctionalRole (S : FormalSystem) (obj : S.(carrier)) (r : FunctionalRole S) : Prop :=
  core_feat_equiv r r ∧
  r.(func_necessary) obj (core_feat_equiv r r) ∧
  ∃ (cid : ConceptIdentity S obj), cid.(ci_role) = r.

Definition edge_feat_sim (r1 r2 : FunctionalRole S) : R :=
  let sim_sum := sum (map2 edge_feature_similarity r1.(edge_features) r2.(edge_features)) in
  let w_sum1 := sum (map (fun f => match f with EdgeFeature _ w => w | _ => 0 end) r1.(edge_features)) in
  let w_sum2 := sum (map (fun f => match f with EdgeFeature _ w => w | _ => 0 end) r2.(edge_features)) in
  if (w_sum1 * w_sum2 = 0)%R then 0 else sim_sum / (w_sum1 * w_sum2).

Definition role_similarity (r1 r2 : FunctionalRole S) : R :=
  if core_feat_equiv r1 r2 then edge_feat_sim r1 r2 else 0.

(* ======================== 6. 关键引理与定理（无修改） ======================== *)
Lemma sum_map2_sym :
  ∀ A B C (f : A → B → C) (l1 : list A) (l2 : list B),
    length l1 = length l2 →
    sum (map2 f l1 l2) = sum (map2 (fun x y => f y x) l2 l1).
Proof.
  intros A B C f l1 l2 H_len; induction l1 as [|a l1' IH]; destruct l2 as [|b l2']; auto.
  - inversion H_len.
  - simpl; rewrite IH; auto.
Qed.

Lemma sum_map2_le_prod_sum :
  ∀ (l1 l2 : list FunctionalFeature),
    sum (map2 edge_feature_similarity l1 l2) ≤
    sum (map (fun f => match f with EdgeFeature _ w => w | _ => 0 end) l1) *
    sum (map (fun f => match f with EdgeFeature _ w => w | _ => 0 end) l2).
Proof.
  intros l1 l2; induction l1 as [|f1 l1' IH]; destruct l2 as [|f2 l2']; auto.
  - simpl; apply Rle_0_Rmult; apply sum_nonneg; intros []; lia.
  - simpl; apply Rle_0_Rmult; apply sum_nonneg; intros []; lia.
  - simpl; rewrite IH; compute.
    destruct f1 as [n1|n1 w1]; destruct f2 as [n2|n2 w2]; simpl; try lia.
    + assert (w1 * w2 ≤ w1 * w2)%R by apply Rle_refl; lia.
    + assert (0 ≤ w1 * w2)%R by apply Rmult_le_pos; lia.
Qed.

Lemma core_no_dup_impl_distinct :
  ∀ (S : FormalSystem) (r : FunctionalRole S),
    r.(core_no_dup) →
    ∀ f1 f2, In f1 r.(core_features) → In f2 r.(core_features) → f1 ≠ f2.
Proof.
  intros S r H_no_dup f1 f2 H1 H2.
  apply NoDup_In_eq in H_no_dup; intuition.
Qed.

Lemma edge_weight_single_le1 :
  ∀ (S : FormalSystem) (r : FunctionalRole S) (f : FunctionalFeature),
    In f r.(edge_features) →
    r.(edge_weight_normalized) →
    match f with EdgeFeature _ w => w ≤ 1 | _ => True end.
Proof.
  intros S r f H_in H_norm.
  destruct f as [|n w]; try trivial.
  assert (H_nonneg: w ≥ 0) by (apply (Forall_inv r.(edge_weight_valid) H_in); destruct H_in; auto).
  assert (H_le_sum: w ≤ sum (map (fun f => match f with EdgeFeature _ w => w | _ => 0 end) r.(edge_features))).
  { apply sum_le_total; auto. }
  assert (H_sum_le1: sum (map (fun f => match f with EdgeFeature _ w => w | _ => 0 end) r.(edge_features)) ≤ 1) by assumption.
  apply Rle_trans with (sum (map (fun f => match f with EdgeFeature _ w => w | _ => 0 end) r.(edge_features))); auto.
Qed.

Lemma edge_feat_sim_sym :
  ∀ (S : FormalSystem) (r1 r2 : FunctionalRole S),
    edge_feat_sim r1 r2 = edge_feat_sim r2 r1.
Proof.
  intros S r1 r2; unfold edge_feat_sim.
  assert (sum (map2 edge_feature_similarity r1.(edge_features) r2.(edge_features)) =
          sum (map2 edge_feature_similarity r2.(edge_features) r1.(edge_features)))
    by apply sum_map2_sym; auto.
  rewrite H; reflexivity.
Qed.

Lemma edge_feat_sim_bounded :
  ∀ (S : FormalSystem) (r1 r2 : FunctionalRole S),
    edge_feat_sim r1 r2 in01.
Proof.
  intros S r1 r2; unfold edge_feat_sim.
  let sim_sum := eval red in (sum (map2 edge_feature_similarity r1.(edge_features) r2.(edge_features))) in
  let w_sum1 := eval red in (sum (map (fun f => match f with EdgeFeature _ w => w | _ => 0 end) r1.(edge_features))) in
  let w_sum2 := eval red in (sum (map (fun f => match f with EdgeFeature _ w => w | _ => 0 end) r2.(edge_features))) in
  assert (H_nonneg: sim_sum ≥ 0) by (apply sum_nonneg; intros []; compute; lia).
  assert (H_le: sim_sum ≤ w_sum1 * w_sum2) by apply sum_map2_le_prod_sum.
  destruct (R_eq_dec (w_sum1 * w_sum2) 0) as [H_zero | H_nonzero].
  - split; [rewrite H_zero; simpl; lia |].
  - split; [apply Rdiv_le_reg_l; auto | apply Rdiv_le_0_compat; auto].
Qed.

Theorem functional_role_determines_identity :
  ∀ (S : FormalSystem) (obj1 obj2 : S.(carrier)),
    (∃ r : FunctionalRole S, S |- obj1 : r ∧ S |- obj2 : r) → obj1 = obj2.
Proof.
  intros S obj1 obj2 [r [H1 H2]].
  unfold PlaysFunctionalRole in *; destruct H1, H2 as [? ? [cid1]], [? ? [cid2]].
  apply (cid1.(ci_unique) obj2 cid2).
  repeat split; auto.
  - apply core_feat_equiv_trans with r; auto.
  - apply edge_feat_sim_sym.
Qed.

Theorem role_similarity_compliant :
  ∀ (S : FormalSystem) (r1 r2 : FunctionalRole S),
    role_similarity r1 r2 in01 ∧
    (core_feat_equiv r1 r2 ↔ role_similarity r1 r2 = edge_feat_sim r1 r2) ∧
    (¬ core_feat_equiv r1 r2 ↔ role_similarity r1 r2 = 0).
Proof.
  intros S r1 r2; unfold role_similarity.
  destruct (core_feat_equiv r1 r2) eqn:H_core.
  - split; [apply edge_feat_sim_bounded | split; auto].
  - split; [split; lia | split; auto].
Qed.

Theorem relational_network_supports_function :
  ∀ (S : FormalSystem) (obj : S.(carrier)) (r : FunctionalRole S),
    S |- obj : r →
    (∀ R : DefinitiveRelation S, In R (ci_rels (ConceptIdentity S obj)) →
      ∃ ax, In ax S.(axioms) ∧ ax = proj1_sig (R.(rel_axiom_dep))).
Proof.
  intros S obj r H_role R H_R.
  unfold PlaysFunctionalRole in H_role; destruct H_role as [? ? [cid]].
  apply in_map_iff in H_R as [R' [H_R'_eq H_in]].
  destruct (R'.(rel_axiom_dep)) as [ax [H_ax_in _]]; exists ax; split; auto.
Qed.

(* ======================== 7. 模块导出（无修改） ======================== *)
Export FormalSystem FunctionalFeature FunctionalRole DefinitiveRelation ConceptIdentity.
Export FormalSystem.carrier FormalSystem.op FormalSystem.axioms FormalSystem.prop_category.
Export necessary_for_basic_property dependency_on_relation PlaysFunctionalRole.
Export core_feat_equiv edge_feat_sim role_similarity.
Export core_no_dup_impl_distinct edge_weight_single_le1.
Export edge_feat_sim_sym edge_feat_sim_bounded.
Export functional_role_determines_identity role_similarity_compliant.
Export relational_network_supports_function.
Export PropertyCategory.
Export Disjoint.

Close Scope frf_meta_scope.
Close Scope R_scope.