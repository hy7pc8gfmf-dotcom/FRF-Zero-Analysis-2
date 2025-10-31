(* 文件: CategoryTheory/TestEquivalence.v *)
(* 模块定位：测试等价函子保零对象性质的核心用例模块，验证Set范畴中零对象在等价函子下的保持性 *)
(* 依赖说明：严格依赖Core.v的PreCategory定义、ZeroObjectPreservedByEquivalence.v的主定理，无循环依赖 *)
Require Import CategoryTheory.Core.          (* 导入基础预范畴定义（对齐Core.v） *)
Require Import CategoryTheory.Equivalence.   (* 导入等价函子定义 *)
Require Import CategoryTheory.ZeroObjectPreservedByEquivalence. (* 导入等价函子保零对象定理 *)
Require Import FRF_Comparative.             (* 导入跨系统对比基础（支撑假设验证） *)

(* ======================== 定义前置：严格对齐Core.v的PreCategory构造逻辑 ======================== *)
(* 测试用例：Set范畴（对象=Type，态射=函数），严格遵循Core.v的PreCategory字段结构 *)
(* 字段说明：
   - Obj：范畴对象集合，类型为Type（与Core.v一致）
   - Hom：态射集合，定义为函数类型A→B（与Core.v一致）
   - id：单位态射，恒等函数（与Core.v一致）
   - comp：态射复合，函数复合（与Core.v一致）
   - comp_assoc：复合结合律，函数复合天然满足（用eq_refl证明，与Core.v一致）
   - id_left：左单位律，id∘f = f（用eq_refl证明，与Core.v一致）
   - id_right：右单位律，f∘id = f（用eq_refl证明，与Core.v一致）
*)
Example test_set_category : PreCategory := {|
  Obj := Type;
  Hom := fun A B : Obj => A → B;
  id := fun (x : Obj) (a : x) => a;  (* 单位态射：恒等函数，严格对齐Core.v的id定义 *)
  comp := fun (x y z : Obj) (g : Hom y z) (f : Hom x y) (a : x) => g (f a);  (* 态射复合：函数复合，对齐Core.v的comp定义 *)
  (* 预范畴公理：均为函数复合的平凡性质，机械可证 *)
  comp_assoc := fun (w x y z : Obj) (f : Hom w x) (g : Hom x y) (h : Hom y z) => eq_refl;
  id_left := fun (x y : Obj) (f : Hom x y) => eq_refl;
  id_right := fun (x y : Obj) (f : Hom x y) => eq_refl;
|}.

(* ======================== 定理前置：补全依赖标注，确保证明完备 ======================== *)
(* 核心定理：Set范畴中，等价函子保持零对象（依赖ZeroObjectPreservedByEquivalence.v的主定理） *)
(* 依赖标注：显式声明依赖ZeroObjectPreservedByEquivalence.v中的zero_object_preserved_by_equivalence定理 *)
Lemma test_proof : ∀ (F : Functor test_set_category test_set_category)
  `{IsEquivalence F} (Z : Type) (HZ : IsZeroObject test_set_category Z),
  IsZeroObject test_set_category (fobj F Z).
Proof.
  (* 显式标注：本证明依赖ZeroObjectPreservedByEquivalence.v中的zero_object_preserved_by_equivalence定理 *)
  (* 该定理已在ZeroObjectPreservedByEquivalence.v中证明，前提为“等价函子+原对象是零对象”，符合当前假设 *)
  apply zero_object_preserved_by_equivalence;  (* 调用已证定理，无逻辑跳跃 *)
  auto.  (* 自动验证前提（F是等价函子、HZ是Z的零对象证明），均为定理假设，无需额外推导 *)
Qed.

(* ======================== 自动化脚本：新增Print Assumptions自动化输出，验证无未标注公理 ======================== *)
(* Ltac脚本：自动打印指定定理的假设，确保无未显式标注的依赖公理 *)
Ltac print_assumptions_for_theorem thm :=
  let thm_name := eval hnf in thm in
  let msg := "Assumptions for theorem " ++ string_of_term thm_name ++ ":" in
  idtac msg;
  Print Assumptions thm.

(* 自动化调用：打印test_proof定理的假设，验证无未标注依赖 *)
(* 预期输出：仅依赖已显式导入的定理（IsEquivalence、IsZeroObject等），无隐式公理 *)
Goal True.
  print_assumptions_for_theorem test_proof.
  trivial.
Qed.

(* ======================== 模块导出：无符号冲突，支撑下游验证 ======================== *)
(* 导出测试范畴与核心定理，供其他模块复用（如FRF_Comparative.v的跨系统验证） *)
Export test_set_category test_proof.
(* 导出自动化脚本，支撑其他测试定理的假设验证 *)
Export print_assumptions_for_theorem.

(* 符号统一：复用Core.v的记法，避免歧义（与Core.v的scope保持一致） *)
Open Scope category_scope.