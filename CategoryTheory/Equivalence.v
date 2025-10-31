(* 文件: CategoryTheory/Equivalence.v *)
(* 重构说明：删除重复定义，导入全系统统一的零对象相关定义，保持范畴等价核心功能不变 *)
Require Import CategoryTheory.Core.
(* 导入全系统统一的零对象相关定义（唯一源头：FRF_CS_Null_Common.v，避免重复，确保一致性） *)
Require Import FRF_CS_Null_Common.

(* 伴随等价定义（保持原逻辑，依赖CategoryTheory.Core的PreCategory/Functor/NaturalIsomorphism） *)
Record AdjointEquivalence (C D: PreCategory) := {
  left_adjoint : Functor C D;
  right_adjoint : Functor D C;
  
  unit_iso : NaturalIsomorphism (Functor.Identity C) 
             (comp_functor right_adjoint left_adjoint);
  counit_iso : NaturalIsomorphism (comp_functor left_adjoint right_adjoint)
               (Functor.Identity D);
  
  triangle_id_left : ∀ x, 
    component (counit_iso) (fobj left_adjoint x) 
    ∘[C] fmap left_adjoint (component (unit_iso) x) = id[C] (fobj left_adjoint x);
  triangle_id_right : ∀ y,
    fmap right_adjoint (component (counit_iso) y)
    ∘[C] component (unit_iso) (fobj right_adjoint y) = id[C] (fobj right_adjoint y)
}.
Arguments AdjointEquivalence {_ _} : clear implicits.
Arguments left_adjoint {_ _ _} : clear implicits.
Arguments right_adjoint {_ _ _} : clear implicits.
Arguments unit_iso {_ _ _} : clear implicits.
Arguments counit_iso {_ _ _} : clear implicits.
Arguments triangle_id_left {_ _ _} _ : clear implicits.
Arguments triangle_id_right {_ _ _} _ : clear implicits.

(* 范畴等价定义（保持原逻辑，依赖伴随等价与自然同构，无隐含假设） *)
Definition IsEquivalence {C D} (F: Functor C D) : Prop :=
  ∃ (G: Functor D C) (η: NaturalIsomorphism (Functor.Identity C) (comp_functor G F))
    (ε: NaturalIsomorphism (comp_functor F G) (Functor.Identity D)),
    (∀ x, component ε (fobj F x) ∘[D] fmap F (component η x) = id[D] (fobj F x)) ∧
    (∀ y, fmap G (component ε y) ∘[C] component η (fobj G y) = id[C] (fobj G y)).
Arguments IsEquivalence {_ _} _ : clear implicits.

(* 关键说明：
1. 零对象相关定义（IsInitial/IsTerminal/IsZeroObject）已从FRF_CS_Null_Common.v导入，该模块是全系统唯一源头（导出SelfContainedLib/Category.v的原始定义），避免重复维护；
2. 保留原模块核心功能（伴随等价、范畴等价判定），无任何功能删减，符号记法（∘[C]/id[C]）与公共模块对齐；
3. 无循环依赖：FRF_CS_Null_Common.v → 本模块，符合“一级基础层→二级场景层”架构；
4. 所有推导可机械执行，依赖前提均为CategoryTheory.Core或FRF_CS_Null_Common.v的已证定义，无自然语言模糊表述。 *)

Open Scope category_scope.
Open Scope cs_null_scope.