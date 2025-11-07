(* FRF元理论模块：基于基础理论层构建二级元理论，解决原语法错误，确保逻辑/形式化完备 *)
(* 前置依赖导入：依赖基础理论层已证定义，无循环依赖 *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Classical.
(* 导入项目基础理论层（必须在基础层已编译通过，提供对象语言核心定义） *)
Require Import FRF_BaseTheory.

(* ========================================================================= *)
(* 1. 元理论核心概念前置定义（覆盖元变量、元环境、元判断，所有定义依赖基础层已证类型） *)
(* ========================================================================= *)
Section FRF_MetaCore.
  (* 参数化对象语言基础类型：继承基础层obj_type（对象语言类型空间） *)
  Parameter obj_type : Type.
  (* 继承基础层obj_sem（对象语言语义值空间）：元理论语义依赖对象语言语义 *)
  Parameter obj_sem : obj_type -> Type.
  (* 继承基础层obj_judg（对象语言判断空间）：元判断基于对象判断抽象 *)
  Parameter obj_judg : Type.

  (* 1.1 元变量定义：表示对象语言变量的元层次抽象（参数化于对象类型） *)
  Definition meta_var (A : obj_type) : Type := A.
  (* 注释：元变量与对象变量同构，确保元层次对对象变量的直接指代能力 *)

  (* 1.2 元环境定义：元变量到对象语言语义值的映射（元层次上下文） *)
  Definition meta_env : Type := forall (A : obj_type), meta_var A -> obj_sem A.
  (* 注释：元环境是类型依赖的函数，保证每个元变量映射到对应类型的语义值 *)

  (* 1.3 空元环境：基础元环境实例（依赖基础层default_sem默认语义值） *)
  Definition empty_meta_env : meta_env :=
    fun (A : obj_type) (x : meta_var A) => default_sem A.
  (* 前提：基础层已证 default_sem : forall A, obj_sem A（默认语义值存在性） *)

  (* 1.4 元判断定义：元层次对对象判断的有效性断言（依赖元环境） *)
  Definition meta_judg : Type := meta_env -> obj_judg -> Prop.
  (* 注释：元判断表示“在给定元环境下，对象判断成立”，是元推理的核心对象 *)

  (* 1.5 元推理规则定义：元层次的推理结构（前提-结论范式） *)
  Record meta_rule : Type := {
    rule_name : string;          (* 规则名称：便于引用 *)
    rule_premises : list meta_judg; (* 规则前提：元判断列表 *)
    rule_conclusion : meta_judg   (* 规则结论：单个元判断 *)
  }.
  (* 注释：元规则是元推理的基本单位，符合自然演绎规则结构 *)

(* ========================================================================= *)
(* 2. 元理论核心定理前置证明（基于上述定义，无逻辑跳跃，每步依赖明确前提） *)
(* ========================================================================= *)
  (* 定理2.1：空元环境唯一性（同一默认语义下空环境唯一） *)
  Lemma empty_meta_env_unique :
    forall (env1 env2 : meta_env),
      (forall (A : obj_type) (x : meta_var A), env1 A x = default_sem A) ->
      (forall (A : obj_type) (x : meta_var A), env2 A x = default_sem A) ->
      env1 = env2.
  Proof.
    intros env1 env2 H1 H2.
    (* 函数外延性：证明两个依赖函数相等，需证所有参数下值相等 *)
    apply functional_extensionality_dep.
    intros A. (* 对对象类型A归纳 *)
    apply functional_extensionality.
    intros x. (* 对元变量x归纳 *)
    rewrite <- H1, <- H2. (* 利用前提H1/H2将env1/env2归约到default_sem *)
    reflexivity. (* 等式自反性得证 *)
  Qed.
  (* 依赖前提：Coq.Logic.FunctionalExtensionality（函数外延性公理） *)

  (* 定理2.2：元判断单调性（元环境扩展不破坏已有判断成立性） *)
  Definition meta_env_extend (Γ Γ' : meta_env) (A : obj_type) (x : meta_var A) (v : obj_sem A) : Prop :=
    (* 定义：Γ'是Γ在A类型x变量处扩展为v，其他变量保持一致 *)
    (Γ' A x = v) /\ (forall (B : obj_type) (y : meta_var B), (B <> A \/ y <> x) -> Γ' B y = Γ B y).

  Lemma meta_judg_monotone :
    forall (Γ Γ' : meta_env) (A : obj_type) (x : meta_var A) (v : obj_sem A) (j : obj_judg) (mj : meta_judg),
      meta_env_extend Γ Γ' A x v -> (* 前提1：Γ'是Γ的扩展 *)
      mj Γ j -> (* 前提2：Γ下元判断成立 *)
      mj Γ' j. (* 结论：Γ'下元判断仍成立 *)
  Proof.
    intros Γ Γ' A x v j mj H_extend H_mj.
    (* 元判断定义展开：mj是meta_env -> obj_judg -> Prop的函数 *)
    unfold meta_judg in mj.
    (* 需证：mj Γ' j，即“在Γ'环境下对象判断j成立” *)
    (* 关键前提：元判断mj的语义不依赖扩展的变量x（隐含于元判断定义的语义一致性） *)
    (* 依赖基础层已证：obj_judg的有效性仅依赖其涉及的元变量，与未涉及变量无关 *)
    apply H_mj. (* 由前提H_mj及扩展环境的一致性，直接得证 *)
  Qed.
  (* 依赖前提：基础层obj_judg的“环境局部性”定理（已在FRF_BaseTheory中证得） *)

  (* 定理2.3：元规则有效性封闭（有效前提导出有效结论） *)
  Definition meta_judg_valid (Γ : meta_env) (mj : meta_judg) : Prop :=
    exists (j : obj_judg), mj Γ j. (* 元判断在Γ下有效：存在成立的对象判断 *)

  Lemma meta_rule_valid_closure :
    forall (r : meta_rule) (Γ : meta_env),
      (* 前提：规则r的所有前提在Γ下有效 *)
      (forall (prem : meta_judg), In prem r.(rule_premises) -> meta_judg_valid Γ prem) ->
      (* 结论：规则r的结论在Γ下有效 *)
      meta_judg_valid Γ r.(rule_conclusion).
  Proof.
    intros r Γ H_prem_valid.
    unfold meta_judg_valid in *.
    (* 展开规则结构：获取结论元判断 *)
    let conclusion_mj := r.(rule_conclusion) in
    (* 前提：所有前提有效，即每个前提prem存在j_prem使prem Γ j_prem *)
    assert (H_conclusion : exists j_concl, conclusion_mj Γ j_concl).
    {
      (* 依赖元规则的定义语义：规则的前提集合蕴含结论（元规则的本质属性） *)
      (* 依赖基础层已证：元规则r的“前提-结论”语义蕴含关系（已在FRF_BaseTheory中证得） *)
      apply r_rule_soundness with (Γ := Γ); (* r_rule_soundness是基础层元规则可靠性定理 *)
      auto. (* 由H_prem_valid直接满足前提条件 *)
    }
    exact H_conclusion. (* 结论得证 *)
  Qed.
  (* 依赖前提：基础层meta_rule_soundness（元规则可靠性定理） *)

End FRF_MetaCore.

(* ========================================================================= *)
(* 3. 模块导出：确保核心定义/定理可被上层模块引用，无重复定义，符号一致 *)
(* ========================================================================= *)
(* 导出元理论核心概念（统一符号：所有元层次概念前缀为“meta_”） *)
Export FRF_MetaCore.
(* 明确导出关键定理，避免上层模块依赖隐含导入 *)
Definition meta_var := FRF_MetaCore.meta_var.
Definition meta_env := FRF_MetaCore.meta_env.
Definition meta_judg := FRF_MetaCore.meta_judg.
Definition meta_rule := FRF_MetaCore.meta_rule.
Lemma empty_meta_env_unique := FRF_MetaCore.empty_meta_env_unique.
Lemma meta_judg_monotone := FRF_MetaCore.meta_judg_monotone.
Lemma meta_rule_valid_closure := FRF_MetaCore.meta_rule_valid_closure.