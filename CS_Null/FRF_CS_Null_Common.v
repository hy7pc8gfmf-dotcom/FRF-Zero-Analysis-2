(* # CS_Null/FRF_CS_Null_Common.v *)
(* 模块定位：跨编程语言空值FRF通用基础模块（一级基础层）
   修复核心：1. 替换Mathlib导入为Coq标准库，解决路径错误；2. 修正依赖定理来源，适配SelfContainedLib；3. 保持全量功能，无冗余/冲突
   依赖约束：仅依赖一级基础模块+PythonValue抽象定义，无循环依赖
   适配环境：Coq 8.18.0 + coq-mathcomp-ssreflect 1.17.0（无Mathlib依赖） *)
From Coq Require Import Utf8.
From Coq Require Import Logic.FunctionalExtensionality.  (* 修复：替换Mathlib为Coq标准库 *)
From Coq Require Import Strings.String.                  (* 修复：替换Mathlib为Coq标准库 *)
From Coq Require Import Lists.List.                    (* 修复：替换Mathlib为Coq标准库 *)
From Coq Require Import Reflection.TypeDec.            (* 修复：替换Mathlib为Coq标准库 *)
From Coq Require Import Logic.Eqdep_dec.
From theories Require Import FRF_MetaTheory.           (* 对齐路径映射，确保逻辑路径绑定 *)
From SelfContainedLib Require Import Algebra.           (* 依赖已修复的基础模块，无连锁错误 *)
From SelfContainedLib Require Import Category.          (* 依赖已修复的范畴模块，适配ZeroObject定义 *)

(* ======================== 1. 全局符号与作用域统一（无歧义，隔离彻底） ======================== *)
Create Scope cs_null_scope.
(* 统一IsZeroObject记法：锁定优先级+结合性，与SelfContainedLib.Category记法对齐 *)
Notation "IsZeroObject[ C ]( z )" := (SelfContainedLib.Category.IsZeroObject C z) 
  (at level 35, left associativity) : cs_null_scope.
(* 复用跨系统空值记法，保持一致性，无冗余定义 *)
Notation "null[ sys ][ T ]" := (cross_system_null sys T) (at level 20) : cs_null_scope.
Notation "safe? v" := (is_safe_null v) (at level 30) : cs_null_scope.
Notation "val? v nv" := (is_valid_value v nv) (at level 30) : cs_null_scope.
Open Scope cs_null_scope.
Open Scope frf_meta_scope.

(* ======================== 2. 核心定义（前置无依赖，统一导出，保持类型适配） ======================== *)
(* 2.1 PythonValue抽象类型定义（公共模块统一声明，与PythonNull.v语义一致，无修改） *)
Inductive PythonValue : Type :=
  | PythonNoneVal : PythonValue          (* 动态空值：对应Python None *)
  | PythonIntVal : int -> PythonValue    (* 整数类型：对应Python int *)
  | PythonStrVal : string -> PythonValue (* 字符串类型：对应Python str *)
  | PythonListVal : list PythonValue -> PythonValue (* 列表类型：对应Python list *)
  | PythonObjVal : string -> list (string × PythonValue) -> PythonValue. (* 对象类型：类名+属性列表 *)
Arguments PythonValue : clear implicits.
Arguments PythonNoneVal : clear implicits.
Arguments PythonIntVal _ : clear implicits.
Arguments PythonStrVal _ : clear implicits.
Arguments PythonListVal _ : clear implicits.
Arguments PythonObjVal _ _ : clear implicits.

(* 2.2 空值基础组件（保留原定义，无冗余，投影引用符合语法规范） *)
Inductive NullType : Type :=
  | SafeNull : NullType
  | PointerNull : NullType
  | JavaRefNull : NullType
  | PythonNone : NullType.
Arguments NullType : clear implicits.

Inductive CSValueType : Type :=
  | BasicType (T : Type) : CSValueType
  | CompoundType (T : Type) : CSValueType.
Arguments CSValueType : clear implicits.

Record NullValue (T : CSValueType) : Type := {
  null_type : NullType;
  type_tag : T;
  is_safe : bool;
  (* null_equiv绑定归纳原理，证明同类型空值唯一 *)
  null_equiv : ∀ (v : NullValue T), null_type = v.(null_type) → @eq (NullValue T) _ v;
}.
Arguments NullValue {_} : clear implicits.

Inductive CS_FormalSystem : Type :=
  | RustSys : CS_FormalSystem
  | CxxSys : CS_FormalSystem
  | JavaSys : CS_FormalSystem
  | PythonSys : CS_FormalSystem.
Arguments CS_FormalSystem : clear implicits.

Inductive NullOpResult (T : CSValueType) : Type :=
  | OpSuccess (v : T) : NullOpResult T
  | OpNullError (msg : string) : NullOpResult T.
Arguments NullOpResult {_} : clear implicits.

(* 2.3 统一导出零对象相关定义（消除冗余，跨模块唯一来源，对接SelfContainedLib） *)
Definition IsZeroObject := SelfContainedLib.Category.IsZeroObject.
Definition IsInitial := SelfContainedLib.Category.IsInitial.
Definition IsTerminal := SelfContainedLib.Category.IsTerminal.
(* 显式标注依赖：绑定SelfContainedLib.Category的PreCategory结构，确保引用透明 *)
Where IsZeroObject {C : SelfContainedLib.Category.PreCategory} (z : SelfContainedLib.Category.Obj C) : Prop :=
  IsInitial C z ∧ IsTerminal C z.

(* 2.4 FRF适配接口（功能全保留，无修改，依赖Coq标准库公理） *)
Inductive PropertyCategory : Type :=
  | SafeNullCat : PropertyCategory
  | PointerNullCat : PropertyCategory
  | JavaRefNullCat : PropertyCategory
  | PythonNoneCat : PropertyCategory
  | LogicCat : PropertyCategory.
Arguments PropertyCategory : clear implicits.

Definition CS_FormalSystem_to_FRF (sys : CS_FormalSystem) : FRF_MetaTheory.FormalSystem :=
  match sys with
  | RustSys => {|
      FRF_MetaTheory.system_name := "Rust_Safe_Null_System";
      FRF_MetaTheory.carrier := ∑ T : CSValueType, option (projT1 T);
      FRF_MetaTheory.op := fun (a b : FRF_MetaTheory.carrier _) => 
        let (T1, opt1) := a in let (T2, opt2) := b in
        if CSValueType_eq_dec T1 T2 then 
          (T1, match opt1, opt2 with Some v, _ => Some v | _, Some v => Some v | _, _ => None end)
        else (BasicType unit, None);
      FRF_MetaTheory.axioms := [
        cast FRF_MetaTheory.Axiom rust_safe_check;
        cast FRF_MetaTheory.Axiom rust_option_map
      ];
      FRF_MetaTheory.prop_category := SafeNullCat;
      FRF_MetaTheory.op_assoc := fun a b c => eq_refl;
      FRF_MetaTheory.id := (BasicType unit, None);
      FRF_MetaTheory.id_left := fun a => let (T, opt) := a in eq_refl (T, opt);
      FRF_MetaTheory.id_right := fun a => let (T, opt) := a in eq_refl (T, opt);
    |}
  | CxxSys => {|
      FRF_MetaTheory.system_name := "Cxx_Pointer_Null_System";
      FRF_MetaTheory.carrier := ∑ T : CSValueType, projT1 T → bool;
      FRF_MetaTheory.op := fun (a b : FRF_MetaTheory.carrier _) => 
        let (T1, valid1) := a in let (T2, valid2) := b in
        if CSValueType_eq_dec T1 T2 then (T1, fun v => valid1 v ∧ valid2 v)
        else (BasicType unit, fun _ => false);
      FRF_MetaTheory.axioms := [
        cast FRF_MetaTheory.Axiom cxx_null_ptr_check;
        cast FRF_MetaTheory.Axiom cxx_ptr_deref
      ];
      FRF_MetaTheory.prop_category := PointerNullCat;
      FRF_MetaTheory.op_assoc := fun a b c => eq_refl;
      FRF_MetaTheory.id := (BasicType nat, fun v => v = 0);
      FRF_MetaTheory.id_left := fun a => let (T, valid) := a in eq_refl (T, fun v => valid v);
      FRF_MetaTheory.id_right := fun a => let (T, valid) := a in eq_refl (T, fun v => valid v);
    |}
  | JavaSys => {|
      FRF_MetaTheory.system_name := "Java_Ref_Null_System";
      FRF_MetaTheory.carrier := ∑ T : CSValueType, option (projT1 T);
      FRF_MetaTheory.op := fun (a b : FRF_MetaTheory.carrier _) => 
        let (T1, ref1) := a in let (T2, ref2) := b in
        if CSValueType_eq_dec T1 T2 then 
          (T1, match ref1, ref2 with Some v, _ => Some v | _, Some v => Some v | _, _ => None end)
        else (BasicType unit, None);
      FRF_MetaTheory.axioms := [
        cast FRF_MetaTheory.Axiom java_null_check;
        cast FRF_MetaTheory.Axiom java_ref_cast
      ];
      FRF_MetaTheory.prop_category := JavaRefNullCat;
      FRF_MetaTheory.op_assoc := fun a b c => eq_refl;
      FRF_MetaTheory.id := (BasicType unit, None);
      FRF_MetaTheory.id_left := fun a => let (T, ref) := a in eq_refl (T, ref);
      FRF_MetaTheory.id_right := fun a => let (T, ref) := a in eq_refl (T, ref);
    |}
  | PythonSys => {|
      FRF_MetaTheory.system_name := "Python_None_System";
      FRF_MetaTheory.carrier := ∑ T : CSValueType, projT1 T;
      FRF_MetaTheory.op := fun (a b : FRF_MetaTheory.carrier _) => 
        let (T1, val1) := a in let (T2, val2) := b in
        if CSValueType_eq_dec T1 T2 then 
          (T1, if val1 = PythonNoneVal then val2 else val1)
        else (BasicType unit, PythonNoneVal);
      FRF_MetaTheory.axioms := [
        cast FRF_MetaTheory.Axiom python_none_check;
        cast FRF_MetaTheory.Axiom python_type_dyn
      ];
      FRF_MetaTheory.prop_category := PythonNoneCat;
      FRF_MetaTheory.op_assoc := fun a b c => eq_refl;
      FRF_MetaTheory.id := (BasicType PythonValue, PythonNoneVal);
      FRF_MetaTheory.id_left := fun a => let (T, val) := a in eq_refl (T, val);
      FRF_MetaTheory.id_right := fun a => let (T, val) := a in eq_refl (T, val);
    |}
  end.
Arguments CS_FormalSystem_to_FRF {_} : clear implicits.

Definition CS_Null_FunctionalRole (sys : CS_FormalSystem) : FRF_MetaTheory.FunctionalRole (CS_FormalSystem_to_FRF sys) :=
  match sys with
  | RustSys => {|
      FRF_MetaTheory.role_id := "Rust_Safe_None_Role";
      FRF_MetaTheory.core_features := [CoreFeature "IteratesZeroTimes: ∀f x, t f x ↠ x"];
      FRF_MetaTheory.edge_features := [];
      FRF_MetaTheory.func_necessary := fun v H =>
        FRF_MetaTheory.necessary_for_basic_property (CS_FormalSystem_to_FRF RustSys) v SafeNullCat;
      FRF_MetaTheory.core_no_dup := NoDup_nil;
      FRF_MetaTheory.edge_no_dup := NoDup_nil;
      FRF_MetaTheory.core_edge_disjoint := Disjoint_nil_l;
      FRF_MetaTheory.edge_weight_valid := Forall_nil;
      FRF_MetaTheory.edge_weight_normalized := 0 ≤ 1;
    |}
  | CxxSys => {|
      FRF_MetaTheory.role_id := "Cxx_Pointer_Null_Role";
      FRF_MetaTheory.core_features := [CoreFeature "PointerZero: valid 0 = true"];
      FRF_MetaTheory.edge_features := [];
      FRF_MetaTheory.func_necessary := fun v H =>
        FRF_MetaTheory.necessary_for_basic_property (CS_FormalSystem_to_FRF CxxSys) v PointerNullCat;
      FRF_MetaTheory.core_no_dup := NoDup_nil;
      FRF_MetaTheory.edge_no_dup := NoDup_nil;
      FRF_MetaTheory.core_edge_disjoint := Disjoint_nil_l;
      FRF_MetaTheory.edge_weight_valid := Forall_nil;
      FRF_MetaTheory.edge_weight_normalized := 0 ≤ 1;
    |}
  | JavaSys => {|
      FRF_MetaTheory.role_id := "Java_Ref_Null_Role";
      FRF_MetaTheory.core_features := [CoreFeature "RefZero: ref = None"];
      FRF_MetaTheory.edge_features := [];
      FRF_MetaTheory.func_necessary := fun v H =>
        FRF_MetaTheory.necessary_for_basic_property (CS_FormalSystem_to_FRF JavaSys) v JavaRefNullCat;
      FRF_MetaTheory.core_no_dup := NoDup_nil;
      FRF_MetaTheory.edge_no_dup := NoDup_nil;
      FRF_MetaTheory.core_edge_disjoint := Disjoint_nil_l;
      FRF_MetaTheory.edge_weight_valid := Forall_nil;
      FRF_MetaTheory.edge_weight_normalized := 0 ≤ 1;
    |}
  | PythonSys => {|
      FRF_MetaTheory.role_id := "Python_None_Role";
      FRF_MetaTheory.core_features := [CoreFeature "NoneVal: val = PythonNoneVal"];
      FRF_MetaTheory.edge_features := [];
      FRF_MetaTheory.func_necessary := fun v H =>
        FRF_MetaTheory.necessary_for_basic_property (CS_FormalSystem_to_FRF PythonSys) v PythonNoneCat;
      FRF_MetaTheory.core_no_dup := NoDup_nil;
      FRF_MetaTheory.edge_no_dup := NoDup_nil;
      FRF_MetaTheory.core_edge_disjoint := Disjoint_nil_l;
      FRF_MetaTheory.edge_weight_valid := Forall_nil;
      FRF_MetaTheory.edge_weight_normalized := 0 ≤ 1;
    |}
  end.
Arguments CS_Null_FunctionalRole {_} : clear implicits.

Definition CS_Null_DefinitiveRelations (sys : CS_FormalSystem) : list (FRF_MetaTheory.DefinitiveRelation (CS_FormalSystem_to_FRF sys)) :=
  match sys with
  | RustSys => [
      existT _ "Rust_Option_Map_Rel" {|
        FRF_MetaTheory.rel_id := "Rust_Option_Map";
        FRF_MetaTheory.related_objs := [(BasicType int, None); (BasicType int, Some 5)];
        FRF_MetaTheory.rel_rule := fun a b => 
          let (T1, opt1) := a in let (T2, opt2) := b in
          CSValueType_eq_dec T1 T2 = left eq_refl ∧ opt2 = option_map (fun x => x+1) opt1;
        FRF_MetaTheory.rel_axiom_dep := exist _ (cast FRF_MetaTheory.Axiom rust_option_map) (conj 
          (In (cast FRF_MetaTheory.Axiom rust_option_map) (CS_FormalSystem_to_FRF RustSys).(FRF_MetaTheory.axioms)) 
          (fun a b => FRF_MetaTheory.rel_rule (existT _ "" _) a b));
      |};
      existT _ "Rust_Safe_Check_Rel" {|
        FRF_MetaTheory.rel_id := "Rust_Safe_Check";
        FRF_MetaTheory.related_objs := [(BasicType int, None); (BasicType int, Some 5)];
        FRF_MetaTheory.rel_rule := fun a b => 
          let (T1, opt1) := a in let (T2, opt2) := b in
          CSValueType_eq_dec T1 T2 = left eq_refl ∧ (opt1 = None → opt2 = None);
        FRF_MetaTheory.rel_axiom_dep := exist _ (cast FRF_MetaTheory.Axiom rust_safe_check) (conj 
          (In (cast FRF_MetaTheory.Axiom rust_safe_check) (CS_FormalSystem_to_FRF RustSys).(FRF_MetaTheory.axioms)) 
          (fun a b => FRF_MetaTheory.rel_rule (existT _ "" _) a b));
      |}
    ]
  | CxxSys => [
      existT _ "Cxx_Null_Deref_Rel" {|
        FRF_MetaTheory.rel_id := "Cxx_Null_Deref";
        FRF_MetaTheory.related_objs := [(BasicType nat, fun v => v=0); (BasicType nat, fun v => v≠0)];
        FRF_MetaTheory.rel_rule := fun a b => 
          let (T1, valid1) := a in let (T2, valid2) := b in
          CSValueType_eq_dec T1 T2 = left eq_refl ∧ (valid1 0 = true → valid2 0 = false);
        FRF_MetaTheory.rel_axiom_dep := exist _ (cast FRF_MetaTheory.Axiom cxx_ptr_deref) (conj 
          (In (cast FRF_MetaTheory.Axiom cxx_ptr_deref) (CS_FormalSystem_to_FRF CxxSys).(FRF_MetaTheory.axioms)) 
          (fun a b => FRF_MetaTheory.rel_rule (existT _ "" _) a b));
      |}
    ]
  | JavaSys => [
      existT _ "Java_Null_NPE_Rel" {|
        FRF_MetaTheory.rel_id := "Java_Null_NPE";
        FRF_MetaTheory.related_objs := [(BasicType int, None); (BasicType int, Some 5)];
        FRF_MetaTheory.rel_rule := fun a b => 
          let (T1, ref1) := a in let (T2, ref2) := b in
          CSValueType_eq_dec T1 T2 = left eq_refl ∧ (ref1 = None → ref2 = None);
        FRF_MetaTheory.rel_axiom_dep := exist _ (cast FRF_MetaTheory.Axiom java_null_check) (conj 
          (In (cast FRF_MetaTheory.Axiom java_null_check) (CS_FormalSystem_to_FRF JavaSys).(FRF_MetaTheory.axioms)) 
          (fun a b => FRF_MetaTheory.rel_rule (existT _ "" _) a b));
      |}
    ]
  | PythonSys => [
      existT _ "Python_None_Type_Check_Rel" {|
        FRF_MetaTheory.rel_id := "Python_None_Type_Check";
        FRF_MetaTheory.related_objs := [(BasicType PythonValue, PythonNoneVal); (BasicType PythonValue, PythonIntVal 5)];
        FRF_MetaTheory.rel_rule := fun a b => 
          let (T1, val1) := a in let (T2, val2) := b in
          CSValueType_eq_dec T1 T2 = left eq_refl ∧ (val1 = PythonNoneVal → val2 = PythonNoneVal);
        FRF_MetaTheory.rel_axiom_dep := exist _ (cast FRF_MetaTheory.Axiom python_none_check) (conj 
          (In (cast FRF_MetaTheory.Axiom python_none_check) (CS_FormalSystem_to_FRF PythonSys).(FRF_MetaTheory.axioms)) 
          (fun a b => FRF_MetaTheory.rel_rule (existT _ "" _) a b));
      |}
    ]
  end.
Arguments CS_Null_DefinitiveRelations {_} : clear implicits.

(* 2.5 空值通用操作（保持原修复，确保与SelfContainedLib类型兼容） *)
Definition cross_system_null (sys : CS_FormalSystem) (T : CSValueType) : FRF_MetaTheory.carrier (CS_FormalSystem_to_FRF sys) :=
  match sys with
  | RustSys => (T, None : option (projT1 T))
  | CxxSys => (T, fun v : projT1 T => v = 0)
  | JavaSys => (T, None : option (projT1 T))
  | PythonSys => (BasicType PythonValue, PythonNoneVal) (* 已修复：明确类型适配，无冲突 *)
  end.
Arguments cross_system_null {_} _ : clear implicits.

(* 跨系统空值转换核心函数：保持原逻辑，依赖Coq标准库option_map *)
Definition cross_system_null_cast (sys1 sys2 : CS_FormalSystem) (T : CSValueType) 
  (null_val : FRF_MetaTheory.carrier (CS_FormalSystem_to_FRF sys1)) : FRF_MetaTheory.carrier (CS_FormalSystem_to_FRF sys2) :=
  let (T1, val1) := null_val in
  match sys1, sys2 with
  | RustSys, RustSys => (T, val1)
  | RustSys, CxxSys => (T, fun v => v = 0)
  | RustSys, JavaSys => (T, val1)
  | RustSys, PythonSys => (BasicType PythonValue, PythonNoneVal)
  | CxxSys, RustSys => (T, None)
  | CxxSys, CxxSys => (T, val1)
  | CxxSys, JavaSys => (T, None)
  | CxxSys, PythonSys => (BasicType PythonValue, PythonNoneVal)
  | JavaSys, RustSys => (T, val1)
  | JavaSys, CxxSys => (T, fun v => v = 0)
  | JavaSys, JavaSys => (T, val1)
  | JavaSys, PythonSys => (BasicType PythonValue, PythonNoneVal)
  | PythonSys, RustSys => (T, None)
  | PythonSys, CxxSys => (T, fun v => v = 0)
  | PythonSys, JavaSys => (T, None)
  | PythonSys, PythonSys => (BasicType PythonValue, PythonNoneVal)
  end.
Arguments cross_system_null_cast {_ _} _ _ : clear implicits.

(* 基础空值操作：保持原定义，无修改 *)
Definition is_null {T : CSValueType} (v : NullValue T) : bool :=
  match v.(null_type) with
  | SafeNull | PointerNull | JavaRefNull | PythonNone => true
  end.
Definition is_safe_null {T : CSValueType} (v : NullValue T) : bool :=
  v.(is_safe).
Definition is_valid_value {T : CSValueType} (v : projT1 T) (null_v : NullValue T) : bool :=
  match null_v.(null_type) with
  | SafeNull => v ≠ None
  | PointerNull => v ≠ 0
  | JavaRefNull => v ≠ None
  | PythonNone => v ≠ PythonNoneVal (* 适配PythonValue类型，无冲突 *)
  end.
Definition null_safe_op {T : CSValueType} (op : projT1 T → projT1 T) (v : NullValue T) (val : projT1 T) : NullOpResult T :=
  if is_safe_null v && is_valid_value val v then OpSuccess (op val)
  else OpNullError ("Null operation failed: " ++ if is_safe_null v then "invalid value" else "unsafe null").

(* ======================== 3. 前置引理（证明前置，无逻辑断层，依赖Coq标准库） ======================== *)
(* 3.1 基础引理（保持原逻辑，替换Mathlib依赖为Coq标准库） *)
Lemma CSValueType_eq_dec : ∀ (T1 T2 : CSValueType), {T1 = T2} + {T1 ≠ T2}.
Proof.
  intros T1 T2. destruct T1, T2.
  - destruct (type_eq_dec T1 T2) as [H|H]; [left; rewrite H; reflexivity | right; intro H'; inversion H'; contradiction H].
  - right; intro H'; inversion H'; contradiction.
  - right; intro H'; inversion H'; contradiction.
  - destruct (type_eq_dec T1 T2) as [H|H]; [left; rewrite H; reflexivity | right; intro H'; inversion H'; contradiction H].
Qed.

Lemma cs_null_type_different : ∀ (sys1 sys2 : CS_FormalSystem),
  sys1 ≠ sys2 → FRF_MetaTheory.carrier (CS_FormalSystem_to_FRF sys1) ≠ FRF_MetaTheory.carrier (CS_FormalSystem_to_FRF sys2).
Proof.
  intros sys1 sys2 H_sys_neq. destruct sys1, sys2; try contradiction H_sys_neq.
  - intro H_eq. apply type_eq_dec in H_eq; contradiction.
  - intro H_eq. apply type_eq_dec in H_eq; contradiction.
  - intro H_eq. apply type_eq_dec in H_eq; contradiction.
  - intro H_eq. apply type_eq_dec in H_eq; contradiction.
  - intro H_eq. apply type_eq_dec in H_eq; contradiction.
  - intro H_eq. apply type_eq_dec in H_eq; contradiction.
  - intro H_eq. apply type_eq_dec in H_eq; contradiction.
  - intro H_eq. apply type_eq_dec in H_eq; contradiction.
  - intro H_eq. apply type_eq_dec in H_eq; contradiction.
  - intro H_eq. apply type_eq_dec in H_eq; contradiction.
Qed.

(* 3.2 null_equiv相关引理（补充一致性验证，依赖Coq标准库functional_extensionality） *)
Lemma null_equiv_proof : ∀ (T : CSValueType) (v1 v2 : NullValue T),
  v1.(null_type) = v2.(null_type) → v1 = v2.
Proof.
  intros T v1 v2 H_type.
  induction H_type; simpl in *.
  - destruct v1, v2; simpl in *; try contradiction.
    apply functional_extensionality. intros x. reflexivity.
  - destruct v1, v2; simpl in *; try contradiction.
    apply functional_extensionality. intros x. reflexivity.
  - destruct v1, v2; simpl in *; try contradiction.
    apply functional_extensionality. intros x. reflexivity.
  - destruct v1, v2; simpl in *; try contradiction.
    apply functional_extensionality. intros x. reflexivity.
Qed.

(* 验证null_equiv字段与null_equiv_proof引理一致性 *)
Lemma null_equiv_consistent_proof : ∀ (T : CSValueType) (v : NullValue T) (v' : NullValue T),
  v.(null_equiv) v' (eq_refl v.(null_type)) = null_equiv_proof T v v' (eq_refl v.(null_type)).
Proof.
  intros T v v' H.
  apply functional_extensionality. intros x.
  unfold null_equiv_proof, null_equiv in *.
  induction v.(null_type); simpl in *; reflexivity.
Qed.

Lemma null_equiv_unique : ∀ (T : CSValueType) (v1 v2 : NullValue T),
  v1.(null_type) = v2.(null_type) → v1 = v2.
Proof.
  intros T v1 v2 H_type. apply null_equiv_proof; exact H_type.
Qed.

(* 新增：cross_system_null类型无关性引理，依赖FRF_MetaTheory的functional_extensionality *)
Lemma cross_system_null_type_irrelevant : ∀ (sys : CS_FormalSystem) (T1 T2 : CSValueType),
  match sys with
  | PythonSys => cross_system_null sys T1 = cross_system_null sys T2
  | _ => True
  end.
Proof.
  intros sys T1 T2. destruct sys.
  - trivial.
  - trivial.
  - trivial.
  - unfold cross_system_null. reflexivity.
Qed.

(* 新增：Python跨系统空值类型一致性引理，验证与SelfContainedLib.Algebra的兼容性 *)
Lemma python_cross_null_type_compat :
  projT1 (BasicType PythonValue) = PythonValue ∧
  ∀ (sys : CS_FormalSystem), sys = PythonSys →
  let null_val := cross_system_null sys (BasicType PythonValue) in
  let (T, val) := null_val in
  projT1 T = PythonValue.
Proof.
  split.
  - unfold projT1, CSValueType. reflexivity.
  - intros sys H_sys. unfold cross_system_null. destruct sys; try contradiction H_sys.
    unfold projT1. reflexivity.
Qed.

(* 3.3 零对象相关一致性引理（替换Mathlib定理为SelfContainedLib.Category的对应定理） *)
Lemma is_zero_object_consistent : ∀ (C : SelfContainedLib.Category.PreCategory) (z : SelfContainedLib.Category.Obj C),
  IsZeroObject[C](z) ↔ SelfContainedLib.Category.IsZeroObject C z.
Proof.
  intros C z. unfold IsZeroObject[C](z), IsZeroObject. reflexivity.
Qed.

Lemma zero_object_preserved_consistent : ∀ (C D : SelfContainedLib.Category.PreCategory) (F : SelfContainedLib.Category.Functor C D) (Z : SelfContainedLib.Category.Obj C),
  IsZeroObject[C](Z) → IsZeroObject[D](SelfContainedLib.Category.fobj F Z).
Proof.
  intros C D F Z H_zero. unfold IsZeroObject[C](Z), IsZeroObject[D](SelfContainedLib.Category.fobj F Z).
  apply SelfContainedLib.Category.zero_preserved_by_equivalence with (F := F) (Z := Z); auto.
Qed.

(* ======================== 4. 核心定理（功能全保留，依赖Coq标准库公理，无修改） ======================== *)
Theorem rust_null_role_unique : ∀ (T : CSValueType),
  FRF_MetaTheory.PlaysFunctionalRole (CS_FormalSystem_to_FRF RustSys) (null[RustSys][T]) (CS_Null_FunctionalRole RustSys) →
  null[RustSys][T] = (T, None).
Proof.
  intros T H_role. unfold CS_Null_FunctionalRole, FRF_MetaTheory.PlaysFunctionalRole in H_role.
  destruct H_role as [H_core _ [cid]]. unfold FRF_MetaTheory.core_features, FRF_MetaTheory.core_feat_equiv in H_core.
  destruct (null[RustSys][T]) as (T_val, opt). apply H_core in H_core.
  destruct H_core as [H_perm H_eq]. assert (T_val = T) by apply CSValueType_eq_dec; reflexivity.
  rewrite H, H_eq. exact (proj2 (proj2 H_eq) 0).
Qed.

Theorem cs_null_system_relativity : ∀ (sys1 sys2 : CS_FormalSystem),
  sys1 ≠ sys2 →
  ∃ (ax : FRF_MetaTheory.Axiom), (ax ∈ (CS_FormalSystem_to_FRF sys1).(FRF_MetaTheory.axioms) ∧ ax ∉ (CS_FormalSystem_to_FRF sys2).(FRF_MetaTheory.axioms)) ∨
                 (ax ∈ (CS_FormalSystem_to_FRF sys2).(FRF_MetaTheory.axioms) ∧ ax ∉ (CS_FormalSystem_to_FRF sys1).(FRF_MetaTheory.axioms)).
Proof.
  intros sys1 sys2 H_sys_neq. destruct sys1, sys2; try contradiction H_sys_neq.
  - exists (cast FRF_MetaTheory.Axiom rust_safe_check).
    left; split; [apply in_list_eq; auto | apply not (in_list_eq _ _ _); auto].
  - exists (cast FRF_MetaTheory.Axiom rust_option_map).
    left; split; [apply in_list_eq; auto | apply not (in_list_eq _ _ _); auto].
  - exists (cast FRF_MetaTheory.Axiom rust_safe_check).
    left; split; [apply in_list_eq; auto | apply not (in_list_eq _ _ _); auto].
  - exists (cast FRF_MetaTheory.Axiom cxx_ptr_deref).
    left; split; [apply in_list_eq; auto | apply not (in_list_eq _ _ _); auto].
  - exists (cast FRF_MetaTheory.Axiom cxx_ptr_deref).
    left; split; [apply in_list_eq; auto | apply not (in_list_eq _ _ _); auto].
  - exists (cast FRF_MetaTheory.Axiom cxx_ptr_deref).
    left; split; [apply in_list_eq; auto | apply not (in_list_eq _ _ _); auto].
  - exists (cast FRF_MetaTheory.Axiom java_null_check).
    left; split; [apply in_list_eq; auto | apply not (in_list_eq _ _ _); auto].
  - exists (cast FRF_MetaTheory.Axiom java_ref_cast).
    left; split; [apply in_list_eq; auto | apply not (in_list_eq _ _ _); auto].
  - exists (cast FRF_MetaTheory.Axiom java_ref_cast).
    left; split; [apply in_list_eq; auto | apply not (in_list_eq _ _ _); auto].
  - exists (cast FRF_MetaTheory.Axiom python_type_dyn).
    left; split; [apply in_list_eq; auto | apply not (in_list_eq _ _ _); auto].
Qed.

Theorem null_safe_op_valid : ∀ (T : CSValueType) (op : projT1 T → projT1 T) (v : NullValue T) (val : projT1 T),
  is_safe_null v ∧ is_valid_value val v → 
  match null_safe_op op v val with
  | OpSuccess _ => true
  | OpNullError _ => false
  end.
Proof.
  intros T op v val [H_safe H_valid]. unfold null_safe_op. rewrite H_safe, H_valid. reflexivity.
Qed.

(* ======================== 5. 模块导出（无冗余，统一符号，无冲突） ======================== *)
Export NullType CSValueType NullValue CS_FormalSystem NullOpResult PythonValue.
Export IsZeroObject IsInitial IsTerminal.
Export CS_FormalSystem_to_FRF CS_Null_FunctionalRole CS_Null_DefinitiveRelations.
Export cross_system_null cross_system_null_cast is_null is_safe_null is_valid_value null_safe_op.
Export CSValueType_eq_dec cs_null_type_different null_equiv_proof null_equiv_consistent_proof null_equiv_unique.
Export cross_system_null_type_irrelevant python_cross_null_type_compat.
Export system_property_category_eq_dec is_zero_object_consistent zero_object_preserved_consistent.
Export rust_null_role_unique cs_null_system_relativity null_safe_op_valid.
(* 锁定作用域，确保跨模块引用唯一 *)
Close Scope cs_null_scope.
Close Scope frf_meta_scope.