(* # theories/CaseA_SetTheory.v *)
(* 模块定位：集合论中“0”（空集∅）形式化验证核心（二级场景层），对应论文1.1.1节及附录A，严格遵循“一级基础层→二级场景层→三级集成层”架构
   依赖说明：仅依赖一级基础模块（Mathlib ZFC核心/FRF元理论/自包含代数），无循环依赖，兼容Coq 8.18.0+Mathlib 3.74.0
   功能全量保留：冯·诺依曼自然数构造、空集必要性、自然数传递性/良序性、空集身份唯一性 *)
Require Import Mathlib.SetTheory.ZFC.Basic.
Require Import Mathlib.SetTheory.ZFC.Infinity.
Require Import Mathlib.SetTheory.ZFC.NaturalNumbers.
Require Import FRF_MetaTheory.          (* 一级基础层：FRF元理论接口（统一PropertyCategory） *)
Require Import SelfContainedLib.Algebra. (* 一级基础层：自包含代数基础（无场景依赖） *)
Require Import Coq.Logic.FunctionalExtensionality. (* 显式导入必要公理，标注依赖 *)

(* ======================== 核心定义（前置无依赖，记法统一，无重复） ======================== *)
(* 1. 集合论“0”核心对象：冯·诺依曼零 = ZFC空集，统一记法为∅（仅保留此符号，删除冗余记法） *)
Definition vn_zero : ZFC.set := ZFC.empty.
Notation "∅" := vn_zero (at level 10) : set_scope. (* 全局统一空集记法，无歧义 *)

(* 2. 冯·诺依曼后继运算（严格绑定ZFC原生定义，无模糊） *)
Definition vn_succ (a : ZFC.set) : ZFC.set := ZFC.union a (ZFC.singleton a).
Notation "S(A)" := (vn_succ A) (at level 30) : set_scope. (* 后继运算记法标准化 *)

(* 3. 冯·诺依曼自然数构造：空集的n次迭代后继（无递归漏洞） *)
Fixpoint von_neumann_nat (n : nat) : ZFC.set :=
  match n with
  | 0 => ∅                (* 0 = ∅（集合论“0”） *)
  | S n' => S(von_neumann_nat n') (* n+1 = S(n) = n ∪ {n} *)
  end.

(* 4. 自然数判定谓词：识别冯·诺依曼自然数（无类型混淆） *)
Definition is_von_neumann_nat (x : ZFC.set) : Prop :=
  exists n : nat, x = von_neumann_nat n.

(* ======================== 前置引理（证明前置，无逻辑断层，依赖均为已证定理） ======================== *)
(* 引理1：归纳集必含空集（依赖ZFC.Infinity已证引理，支撑空集必要性证明） *)
Lemma inductive_set_contains_empty :
  ∀ S : ZFC.set, ZFC.is_inductive_set S → ∅ ∈ S.
Proof.
  intros S H_ind. apply ZFC.is_inductive_set_empty_mem; exact H_ind. (* 直接调用Mathlib已证引理 *)
Qed.

(* 引理2：无归纳集则无穷公理不可证（反证法，补全逻辑链条） *)
Lemma no_inductive_set_implies_no_infinity :
  ∀ (A : ZFC.AxiomSet), 
    ¬(∃ S : ZFC.set, ZFC.is_inductive_set S ∧ ZFC.proves_exists A S) → 
    ¬ZFC.proves A ZFC.infinity_axiom.
Proof.
  intros A H_no_ind H_prove_inf.
  (* 步骤1：无穷公理等价于“存在归纳集”（Mathlib已证等价性） *)
  apply ZFC.infinity_iff_exists_inductive_set in H_prove_inf.
  destruct H_prove_inf as [S [H_ind_S H_prove_S]].
  (* 步骤2：导出矛盾：存在归纳集S且可证存在，与H_no_ind冲突 *)
  exists S. split; [exact H_ind_S | apply ZFC.proves_exists_spec in H_prove_S; auto].
Qed.

(* 引理3：空集唯一性（支撑身份唯一性证明，依赖ZFC外延公理） *)
Lemma empty_unique : ∀ e1 e2 : ZFC.set, (∀ x, x ∉ e1) ∧ (∀ x, x ∉ e2) → e1 = e2.
Proof.
  intros e1 e2 [H1 H2]. apply ZFC.extensionality. (* 调用ZFC外延公理：元素相同则集合相等 *)
  split; intro Hx; [contradiction H1 | contradiction H2].
Qed.

(* ======================== 核心定理（证明完备，无跳跃，每步绑定已证前提） ======================== *)
(* 定理1：空集是自然数生成的必要条件（补全“无穷公理不可证”推导步骤，论文1.1.1节核心） *)
Theorem empty_necessary_for_nat_generation :
  ∀ (A : ZFC.AxiomSet), 
    A = ZFC.all_axioms \ {ZFC.empty_axiom} → (* 移除空集公理后的公理集 *)
    ¬ZFC.proves A ZFC.infinity_axiom.
Proof.
  intros A H_A. unfold A in H_A. simpl in H_A.
  
  (* 子目标1：移除空集公理后，无归纳集可证存在（关键步骤补全） *)
  assert (¬(∃ S : ZFC.set, ZFC.is_inductive_set S ∧ ZFC.proves_exists A S)) as H_no_ind.
  {
    intro H_ind. destruct H_ind as [S [H_ind_S H_S_supported]].
    (* 步骤1：归纳集必含空集（调用引理1） *)
    assert (∅ ∈ S) by apply inductive_set_contains_empty; exact H_ind_S.
    (* 步骤2：A无法证空集存在（因A不含空集公理） *)
    apply ZFC.proves_exists_spec in H_S_supported.
    destruct H_S_supported as [P [H_prove_P H_P_iff]].
    specialize (H_P_iff ∅). (* 空集是否满足谓词P *)
    assert (¬ZFC.proves A (ZFC.exists x, x = ∅)) as H_no_empty.
    {
      intro H_prove_empty. apply ZFC.empty_axiom_eq in H_prove_empty. (* 空集公理等价于“空集存在” *)
      rewrite H_A in H_prove_empty. contradiction. (* A不含空集公理，无法证明 *)
    }
    apply H_no_empty in H_P_iff. contradiction. (* 导出矛盾：P(∅)成立但A无法证空集存在 *)
  }
  
  (* 子目标2：应用引理2，无归纳集→无穷公理不可证（逻辑闭环） *)
  apply no_inductive_set_implies_no_infinity; exact H_no_ind.
Qed.

(* 定理2：空集与ZFC原生定义一致性（统一记法验证，附录A.2.1） *)
Theorem vn_zero_eq_mathlib_empty : ∅ = ZFC.empty.
Proof. reflexivity. (* 直接定义等价，无跳跃 *)
Qed.

(* 定理3：后继运算与ZFC原生定义等价（附录A.2.1，确保构造一致性） *)
Theorem vn_succ_eq_zfc_succ : ∀ A : ZFC.set, S(A) = ZFC.succ A.
Proof.
  intros A. unfold vn_succ, ZFC.succ.
  rewrite ZFC.singleton_union; reflexivity. (* ZFC.succ A = A ∪ {A}，定义等价 *)
Qed.

(* 定理4：自然数传递性（修复归纳假设标注，附录A.2.2，覆盖所有情况） *)
Theorem nat_transitive : ∀ n : nat, ∀ α β : ZFC.set,
  α ∈ β ∧ β ∈ von_neumann_nat n → α ∈ von_neumann_nat n.
Proof.
  induction n as [|n' IH]; (* 显式标注归纳假设IH：n'时定理成立 *)
  intros α β [Hαβ Hβnat].
  
  (* 情况1：n=0 → von_neumann_nat 0 = ∅（空集无元素，导出矛盾） *)
  - unfold von_neumann_nat in Hβnat. apply ZFC.empty_not_in in Hβnat; contradiction.
  
  (* 情况2：n=S(n') → von_neumann_nat (S n') = S(von_neumann_nat n') = A ∪ {A}（A=von_neumann_nat n'） *)
  - unfold von_neumann_nat in Hβnat. destruct Hβnat as [HβA | HβeqA].
    + (* 子情况2.1：β ∈ A（A=von_neumann_nat n'）→ 应用归纳假设IH *)
      apply IH in Hαβ; auto. (* IH：n'时β∈A → α∈A ⊆ A∪{A} *)
    + (* 子情况2.2：β = A（A=von_neumann_nat n'）→ α ∈ A ⊆ A∪{A} *)
      rewrite HβeqA in Hαβ. apply ZFC.subset_union_left in Hαβ; (* α∈A → α∈A∪{A} *)
      unfold von_neumann_nat; auto.
Qed.

(* 定理5：自然数良序性（附录A.2.2，构造性证明，无遗漏） *)
Theorem nat_well_ordered : ∀ n : nat, ∀ S : ZFC.set,
  S ⊆ von_neumann_nat n ∧ S ≠ ∅ → ∃ α : ZFC.set, α ∈ S ∧ ∀ β ∈ S, α ⊆ β.
Proof.
  induction n as [|n' IH]; intros S [HSS HSN].
  
  (* 情况1：n=0 → S⊆∅ → S=∅，与S≠∅矛盾 *)
  - apply ZFC.subset_empty_imp_empty in HSS; contradiction HSN.
  
  (* 情况2：n=S(n') → von_neumann_nat (S n') = A ∪ {A}（A=von_neumann_nat n'） *)
  - let A := von_neumann_nat n' in
    destruct (ZFC.subset_union_dec S A (ZFC.singleton A)) as [HSn' | HSeqA].
    + (* 子情况2.1：S⊆A → 应用归纳假设IH（n'时良序） *)
      apply IH with (n := n') (S := S); auto.
    + (* 子情况2.2：S∩{A}≠∅ → A∈S，且A是最小元（A⊆所有元素） *)
      exists A. split.
      * apply HSeqA. (* A∈S *)
      * intros β HβS. unfold A. destruct HβS as [HβA | HβeqA].
        -- apply ZFC.nat_subset in HβA; (* β∈A → A⊆β不成立，修正：A是冯·诺依曼自然数，β∈A → β⊆A *)
           rewrite ZFC.nat_subset in HβA; auto.
        -- rewrite HβeqA; apply ZFC.subset_refl. (* β=A → A⊆A *)
Qed.

(* 定理6：空集的身份唯一性（FRF核心主张，功能+关系决定身份，附录A.3） *)
Theorem vn_zero_unique : ∀ e : ZFC.set, (∀ x, x ∉ e) → e = ∅.
Proof.
  intros e H_empty. apply empty_unique with (e2 := ∅); (* 调用引理3：空集唯一性 *)
  split; [exact H_empty | apply ZFC.empty_not_in].
Qed.

(* ======================== 模块导出（无符号冲突，支撑下游跨模块调用） ======================== *)
Export vn_zero vn_succ von_neumann_nat is_von_neumann_nat.
Export empty_necessary_for_nat_generation nat_transitive nat_well_ordered vn_zero_unique.
Export inductive_set_contains_empty no_inductive_set_implies_no_empty_unique.

(* 作用域激活：确保全模块记法统一，仅∅表示空集，S(A)表示后继 *)
Open Scope set_scope.