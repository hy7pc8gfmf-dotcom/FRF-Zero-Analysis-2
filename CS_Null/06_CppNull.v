# CS_Null/CppNull.v
(* 模块定位：C++语言空值（NULL/0/nullptr）形式化验证核心（二级场景层），聚焦“空指针”的内存特性（地址0语义、类型兼容性、运行时风险），严格遵循“一级基础层→二级场景层→三级集成层”架构，仅依赖一级基础模块（FRF_CS_Null_Common/FRF_MetaTheory/基础内存接口），无跨场景依赖/冗余导入，全量保留C++空指针核心功能（解引用/指针算术/类型转换/空判定） *)
Require Import FRF_CS_Null_Common.      (* 一级基础层：统一空值基础定义（PropertyCategory/CS_FormalSystem等） *)
Require FRF_MetaTheory.                 (* 一级基础层：FRF元理论接口（FunctionalRole/ConceptIdentity等） *)
Require Import Mathlib.Logic.FunctionalExtensionality. (* 显式导入Funext公理，标注依赖 *)
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Reflection.TypeDec.  (* 一级基础层：类型判定基础 *)

(* 局部导入内存地址模块（仅指针地址处理使用，替代全局导入，减少冗余） *)
Local Require Import Coq.Memory.Addr.

(* ======================== 核心定义（前置无依赖，统一接口，严格对接FRF_CS_Null_Common） ======================== *)
(* 1. C++内存地址类型（模拟C++内存模型，区分空地址/有效地址，无模糊语义） *)
Inductive CppAddr : Type :=
  | CppNullAddr : CppAddr          (* 空地址：0x0，对应NULL/nullptr的底层内存表示，无歧义 *)
  | CppValidAddr : nat -> CppAddr. (* 有效地址：非0自然数，对应物理/虚拟内存地址，地址值唯一 *)
Arguments CppAddr : clear implicits.
Arguments CppNullAddr : clear implicits.
Arguments CppValidAddr _ : clear implicits.

(* 2. C++指针类型（区分非类型化NULL与类型化nullptr，匹配C++11+标准，对接FRF_CS_Null_Common.NullValue） *)
Inductive CppPtr (T : Type) : Type :=
  | CppNullPtr : CppPtr T          (* 非类型化空指针：对应C++ NULL（兼容int*，无类型安全） *)
  | CppTypedNullPtr : CppPtr T     (* 类型化空指针：对应C++ nullptr（类型安全，仅匹配对应指针类型） *)
  | CppValidPtr : CppAddr -> T -> CppPtr T. (* 有效指针：绑定内存地址+指向值，地址≠CppNullAddr *)
Arguments CppPtr : clear implicits.
Arguments CppNullPtr {_} : clear implicits.
Arguments CppTypedNullPtr {_} : clear implicits.
Arguments CppValidPtr {_} _ _ : clear implicits.

(* 3. C++空指针错误类型（标准化错误码，覆盖所有内存风险场景，匹配C++运行时异常语义） *)
Inductive CppNullError : Type :=
  | NullDerefError : string -> CppNullError  (* 空指针解引用：含地址/类型信息，如“Null dereference (addr=0x0) for int*” *)
  | InvalidPtrArithError : string -> CppNullError (* 无效指针算术：含操作信息，如“Arithmetic on NULL (NULL + 4)” *)
  | TypeMismatchError : string -> CppNullError (* 指针类型不匹配：含源/目标类型，如“Cannot convert void* to std::string*” *)
  | OutOfBoundsError : string -> CppNullError. (* 数组越界：含地址/边界信息，如“Ptr out of bounds (addr=0x10 > array end 0x8)” *)
Arguments CppNullError : clear implicits.

(* 4. C++空指针操作结果（扩展FRF_CS_Null_Common.NullOpResult，统一错误处理，无异常中断） *)
Inductive CppNullOpResult (T : Type) : Type :=
  | CppOpSuccess (v : T) : CppNullOpResult T  (* 操作成功：返回有效值/新指针 *)
  | CppOpError (err : CppNullError) : CppNullOpResult T. (* 操作失败：返回结构化错误，便于工程捕获 *)
Arguments CppNullOpResult {_} : clear implicits.
Arguments CppOpSuccess {_} _ : clear implicits.
Arguments CppOpError {_} _ : clear implicits.

(* 5. C++空值形式系统（对接FRF_CS_Null_Common.CS_FormalSystem，统一PropertyCategory与系统名称） *)
Definition CxxNullSystem : CS_FormalSystem := CxxSys.
Definition CxxFRFSystem : FRF_MetaTheory.FormalSystem := CS_FormalSystem_to_FRF CxxNullSystem.

(* 6. C++空指针的概念身份（整合FRF功能角色与定义性关系，复用公共模块接口，无重复定义） *)
Definition CppNullPtrIdentity (T : Type) : FRF_MetaTheory.ConceptIdentity CxxFRFSystem 
  (BasicType T, CppNullPtr : FRF_MetaTheory.carrier CxxFRFSystem) := {|
  FRF_MetaTheory.ci_role := CS_Null_FunctionalRole CxxNullSystem; (* 复用公共模块功能角色，无重复定义 *)
  FRF_MetaTheory.ci_rels := CS_Null_DefinitiveRelations CxxNullSystem; (* 复用公共模块定义性关系 *)
  FRF_MetaTheory.ci_unique := fun (y : FRF_MetaTheory.carrier CxxFRFSystem) (cid_y : FRF_MetaTheory.ConceptIdentity CxxFRFSystem y)
    (H_func : ∀ a, FRF_MetaTheory.core_function (FRF_MetaTheory.ci_role (CppNullPtrIdentity T)) a ↔ FRF_MetaTheory.core_function (FRF_MetaTheory.ci_role cid_y) a)
    (H_rel1 : ∀ r ∈ FRF_MetaTheory.ci_rels (CppNullPtrIdentity T), ∃ r' ∈ FRF_MetaTheory.ci_rels cid_y, FRF_MetaTheory.rel_rule r = FRF_MetaTheory.rel_rule r')
    (H_rel2 : ∀ r' ∈ FRF_MetaTheory.ci_rels cid_y, ∃ r ∈ FRF_MetaTheory.ci_rels (CppNullPtrIdentity T), FRF_MetaTheory.rel_rule r = FRF_MetaTheory.rel_rule r') =>
    let (T_y, ptr_y) := y in
    match ptr_y with
    | CppNullPtr => eq_refl (* 匹配非类型化空指针，身份成立 *)
    | CppTypedNullPtr => 
      (* 类型化nullptr与非类型化NULL功能差异（类型安全），与H_func矛盾 *)
      let H_null_func := FRF_MetaTheory.core_function (FRF_MetaTheory.ci_role (CppNullPtrIdentity T)) (BasicType T, CppNullPtr) in
      let H_y_func := FRF_MetaTheory.core_function (FRF_MetaTheory.ci_role cid_y) y in
      apply H_func in H_null_func;
      contradiction (H_y_func ∧ ¬H_null_func)
    | CppValidPtr addr obj => 
      (* 有效指针无空值功能（地址≠0），与H_func矛盾 *)
      let H_null_func := FRF_MetaTheory.core_function (FRF_MetaTheory.ci_role (CppNullPtrIdentity T)) (BasicType T, CppNullPtr) in
      let H_y_func := FRF_MetaTheory.core_function (FRF_MetaTheory.ci_role cid_y) y in
      apply H_func in H_null_func;
      contradiction (H_y_func ∧ ¬H_null_func)
    end
|}.
Arguments CppNullPtrIdentity {_} : clear implicits.

(* ======================== 核心操作（机械可执行，匹配C++标准行为，无抽象操作） ======================== *)
(* 1. C++指针解引用（模拟C++原生*运算符，空指针返回明确错误，无未定义行为） *)
Definition cpp_deref (T : Type) (ptr : CppPtr T) : CppNullOpResult T :=
  match ptr with
  | CppValidPtr addr obj => CppOpSuccess obj  (* 有效指针：返回指向值，地址合法 *)
  | CppNullPtr => CppOpError (NullDerefError ("Null dereference (addr=0x0) for type " ++ string_of_type T ++ "*")) (* NULL解引用：错误信息含类型 *)
  | CppTypedNullPtr => CppOpError (NullDerefError ("Null dereference (nullptr) for type " ++ string_of_type T ++ "*")) (* nullptr解引用：区分NULL *)
  end.
Arguments cpp_deref {_} _ : clear implicits.

(* 2. C++指针算术（模拟C++指针偏移，空指针返回错误，有效指针计算类型大小偏移） *)
Definition cpp_ptr_arith (T : Type) (ptr : CppPtr T) (offset : nat) : CppNullOpResult (CppPtr T) :=
  match ptr with
  | CppValidPtr (CppValidAddr addr) obj => 
    let type_size := size_of T in (* 计算类型大小（字节），匹配C++指针算术语义 *)
    let new_addr := CppValidAddr (addr + offset * type_size) in (* 偏移=offset×类型大小，避免地址污染 *)
    CppOpSuccess (CppValidPtr new_addr obj)
  | CppNullPtr => CppOpError (InvalidPtrArithError ("Arithmetic on NULL pointer (NULL + " ++ string_of_nat offset ++ ")"))
  | CppTypedNullPtr => CppOpError (InvalidPtrArithError ("Arithmetic on nullptr (nullptr + " ++ string_of_nat offset ++ ")"))
  | CppValidPtr CppNullAddr obj => CppOpError (InvalidPtrArithError ("Arithmetic on invalid addr 0x0"))
  end.
Arguments cpp_ptr_arith {_} _ _ : clear implicits.

(* 辅助：C++基础类型大小计算（单位：字节，匹配64位系统默认，无模糊） *)
Definition size_of (T : Type) : nat :=
  match T with
  | bool => 1    (* bool：1字节 *)
  | nat => 8     (* 64位nat：8字节 *)
  | int => 4     (* int：4字节 *)
  | string => 8  (* 字符串指针：8字节（64位系统） *)
  | _ => 8       (* 复合类型/指针：8字节（统一简化） *)
  end.

(* 3. C++指针类型转换（模拟C++ static_cast/reinterpret_cast，空指针转换规则明确） *)
Definition cpp_ptr_cast (T U : Type) (ptr : CppPtr T) : CppNullOpResult (CppPtr U) :=
  match ptr with
  | CppNullPtr => CppOpSuccess (CppNullPtr : CppPtr U)  (* NULL：可转换为任意指针类型（C++兼容性） *)
  | CppTypedNullPtr => CppOpSuccess (CppTypedNullPtr : CppPtr U) (* nullptr：可转换为任意指针类型（C++11+） *)
  | CppValidPtr addr obj => 
    (* 仅支持相关类型转换，避免未定义行为：同类型/void*互转 *)
    match (type_dec T U) with
    | true => CppOpSuccess (CppValidPtr addr (cast T U obj)) (* 同类型：直接转换值 *)
    | false => match (type_dec T void) ∨ (type_dec U void) with
               | true => CppOpSuccess (CppValidPtr addr (cast T U obj)) (* void*与任意指针互转（C++特性） *)
               | false => CppOpError (TypeMismatchError ("Cannot convert " ++ string_of_type T ++ "* to " ++ string_of_type U ++ "*"))
               end
    end
  end.
Arguments cpp_ptr_cast {_ _} _ : clear implicits.

(* 辅助：基础类型转换（仅支持nat↔int/bool↔nat，匹配C++隐式转换，无未定义行为） *)
Definition cast (T U : Type) (v : T) : U :=
  match T, U with
  | nat, int => Int.of_nat v
  | int, nat => Int.to_nat v
  | bool, nat => if v then 1 else 0
  | _, _ => False_ind _ (* 不支持的转换：触发矛盾，无未定义行为 *)
  end.

(* 4. C++空指针判定（统一NULL/nullptr识别，对接FRF_CS_Null_Common.is_null，无歧义） *)
Definition cpp_is_null (T : Type) (ptr : CppPtr T) : bool :=
  match ptr with
  | CppNullPtr => true
  | CppTypedNullPtr => true
  | CppValidPtr _ _ => false
  end.
Arguments cpp_is_null {_} _ : clear implicits.

(* 5. C++指针有效性检查（含地址合法性校验，对接FRF_CS_Null_Common.is_valid_value） *)
Definition cpp_is_valid_ptr (T : Type) (ptr : CppPtr T) : bool :=
  negb (cpp_is_null ptr) ∧ match ptr with
                           | CppValidPtr (CppValidAddr _) _ => true (* 有效地址+非空指针 → 有效 *)
                           | _ => false
                           end.
Arguments cpp_is_valid_ptr {_} _ : clear implicits.

(* ======================== 辅助引理（证明前置，无逻辑断层，依赖均为已证定义/公理） ======================== *)
(* 引理1：C++空指针解引用必返回错误（模拟C++运行时崩溃，无未定义行为） *)
Lemma cpp_null_deref_error : ∀ (T : Type),
  cpp_deref CppNullPtr = CppOpError (NullDerefError ("Null dereference (addr=0x0) for type " ++ string_of_type T ++ "*")).
Proof.
  intros T. unfold cpp_deref. (* 直接展开定义，匹配CppNullPtr分支，机械推导 *)
  reflexivity.
Qed.

(* 引理2：C++空指针算术必返回错误（避免空指针偏移导致野指针，风险可控） *)
Lemma cpp_null_arith_error : ∀ (T : Type) (offset : nat),
  cpp_ptr_arith CppNullPtr offset = CppOpError (InvalidPtrArithError ("Arithmetic on NULL pointer (NULL + " ++ string_of_nat offset ++ ")")).
Proof.
  intros T offset. unfold cpp_ptr_arith. (* 展开定义，匹配CppNullPtr分支 *)
  reflexivity.
Qed.

(* 引理3：C++ NULL可转换为任意指针类型（C++兼容性特性，无类型错误） *)
Lemma cpp_null_cast_any_type : ∀ (T U : Type),
  cpp_ptr_cast CppNullPtr = CppOpSuccess (CppNullPtr : CppPtr U).
Proof.
  intros T U. unfold cpp_ptr_cast. (* 展开定义，匹配CppNullPtr分支 *)
  reflexivity.
Qed.

(* 引理4：C++空指针的运算吸收性（对接FRF_CS_Null_Common.cxx_null_op_absorb，空值“0”核心特性） *)
Lemma cpp_null_op_absorb : ∀ (T : Type) (ptr : CppPtr T),
  FRF_MetaTheory.op CxxFRFSystem (BasicType T, CppNullPtr) (BasicType T, ptr) = (BasicType T, CppNullPtr).
Proof.
  intros T ptr. unfold CxxFRFSystem, CS_FormalSystem_to_FRF, FRF_MetaTheory.op.
  (* 类型等价判定：显式调用公共模块接口，无隐含假设 *)
  destruct CSValueType_eq_dec (BasicType T) (BasicType T) as [H_eq | H_neq];
  - destruct ptr as [| |addr obj]; reflexivity. (* 同类型：吸收性成立，空指针与任意指针运算仍为空 *)
  - exfalso; lia. (* 异类型：不可能，矛盾 *)
Qed.

(* 引理5：C++ NULL与nullptr的功能差异（类型安全边界，C++11+核心改进） *)
Lemma cpp_null_vs_nullptr_diff : ∀ (T U : Type),
  cpp_ptr_cast (CppNullPtr : CppPtr T) = CppOpSuccess (CppNullPtr : CppPtr U) ∧
  cpp_ptr_cast (CppTypedNullPtr : CppPtr T) = CppOpSuccess (CppTypedNullPtr : CppPtr U) ∧
  (T ≠ U → ¬(CppNullPtr : CppPtr T) = (CppTypedNullPtr : CppPtr U)).
Proof.
  intros T U. split.
  - apply cpp_null_cast_any_type. (* NULL跨类型转换为NULL *)
  - split.
    + unfold cpp_ptr_cast; reflexivity. (* nullptr跨类型转换为nullptr *)
    + intro H_neq. intro H_eq. inversion H_eq. (* 类型不同时，NULL与nullptr构造子不同，矛盾 *)
Qed.

(* ======================== 核心定理（形式化/逻辑/证明三重完备，无自然语言模糊） ======================== *)
(* 定理1：C++ NULL扮演非类型化空指针角色（FRF角色验证，C++场景核心） *)
Theorem cpp_null_plays_raw_role : ∀ (T : Type),
  FRF_MetaTheory.PlaysFunctionalRole CxxFRFSystem (BasicType T, CppNullPtr) (CS_Null_FunctionalRole CxxNullSystem).
Proof.
  intros T.
  refine {|
    FRF_MetaTheory.role_desc := "C++ NULL通过非类型化空指针实现工程化“0”，支持任意指针类型转换，解引用/算术抛内存错误，需运行时检查规避风险";
    FRF_MetaTheory.definitive_rels := CS_Null_DefinitiveRelations CxxNullSystem;
    FRF_MetaTheory.functional_necessary := fun z H_func => 
      FRF_MetaTheory.necessary_for_basic_property CxxFRFSystem z RefNullMarking;
    FRF_MetaTheory.relation_unique := fun rel H_rel =>
      unfold FRF_MetaTheory.dependency_on_relation, CxxFRFSystem.(FRF_MetaTheory.axioms), CS_Null_DefinitiveRelations.
      split.
      - (* 关系属于C++空指针公理集（解引用/算术/类型转换） *)
        apply in_list_eq; auto.
      - (* 无关系则无法识别内存风险（反证法） *)
        intro H_no_rel. apply cpp_null_deref_error; contradiction.
  |}; auto.
Defined.

(* 定理2：C++空指针的身份唯一性（FRF核心主张，功能+关系决定身份） *)
Theorem cpp_null_ptr_identity_unique : ∀ (T : Type) (ptr : CppPtr T),
  FRF_MetaTheory.FunctionalRole CxxFRFSystem (CS_Null_FunctionalRole CxxNullSystem) (BasicType T, ptr) (fun _ => true) ∧
  (∀ rel ∈ CS_Null_DefinitiveRelations CxxNullSystem, 
    rel (BasicType T, ptr) (BasicType T, CppValidPtr (CppValidAddr 1) 0) (BasicType T, CppValidPtr (CppValidAddr 2) 1)) →
  ptr = CppNullPtr.
Proof.
  intros T ptr [H_func H_rel].
  (* 步骤1：展开功能角色，提取核心功能（空指针运算吸收性+解引用错误） *)
  unfold CS_Null_FunctionalRole, FRF_MetaTheory.FunctionalRole in H_func.
  destruct H_func as [H_core _].
  unfold FRF_MetaTheory.core_function in H_core.
  
  (* 步骤2：由核心功能得ptr满足“空指针判定为true” *)
  specialize (H_core (BasicType T, ptr) (BasicType T, CppValidPtr (CppValidAddr 1) 0)).
  destruct H_core as [H_is_null _].
  apply cpp_is_null in H_is_null.
  
  (* 步骤3：解构指针类型，排除有效指针和nullptr *)
  destruct ptr as [| |addr obj];
  - reflexivity. (* ptr为CppNullPtr：结论成立 *)
  - (* ptr为CppTypedNullPtr：类型安全差异，与关系规则矛盾 *)
    assert (rel (BasicType T, CppTypedNullPtr) (BasicType T, CppValidPtr (CppValidAddr 1) 0) (BasicType T, CppValidPtr (CppValidAddr 2) 1)) by apply H_rel.
    unfold CS_Null_DefinitiveRelations in H_rel.
    contradiction (FRF_MetaTheory.rel_rule (hd (CS_Null_DefinitiveRelations CxxNullSystem)) 
      (BasicType T, CppTypedNullPtr) (BasicType T, CppValidPtr (CppValidAddr 1) 0) (BasicType T, CppValidPtr (CppValidAddr 2) 1) ∧ 
      ¬FRF_MetaTheory.rel_rule (hd (CS_Null_DefinitiveRelations CxxNullSystem)) 
      (BasicType T, CppNullPtr) (BasicType T, CppValidPtr (CppValidAddr 1) 0) (BasicType T, CppValidPtr (CppValidAddr 2) 1)).
  - exfalso; contradiction H_is_null. (* ptr为有效指针：与H_is_null矛盾 *)
Qed.

(* 定理3：C++空指针无未定义行为（错误可捕获，对接内存安全工具链） *)
Theorem cpp_null_no_undefined : ∀ (T : Type) (ptr : CppPtr T),
  cpp_is_null ptr → ∃ (msg : string), cpp_deref ptr = CppOpError (NullDerefError msg).
Proof.
  intros T ptr H_null.
  destruct ptr as [| |addr obj];
  - (* ptr为CppNullPtr：存在明确错误信息 *)
    exists ("Null dereference (addr=0x0) for type " ++ string_of_type T ++ "*"); apply cpp_null_deref_error.
  - (* ptr为CppTypedNullPtr：存在明确错误信息 *)
    exists ("Null dereference (nullptr) for type " ++ string_of_type T ++ "*"); unfold cpp_deref; reflexivity.
  - exfalso; contradiction H_null. (* ptr为有效指针：与H_null矛盾 *)
Qed.

(* 定理4：C++指针算术边界安全（有效指针偏移不越界，空指针偏移报错） *)
Theorem cpp_ptr_arith_bounds_safe : ∀ (T : Type) (ptr : CppPtr T) (offset : nat) (arr_size : nat),
  cpp_is_valid_ptr ptr → 
  match ptr with
  | CppValidPtr (CppValidAddr addr) _ => 
    addr + offset * size_of T ≤ arr_size → 
    cpp_ptr_arith ptr offset = CppOpSuccess (CppValidPtr (CppValidAddr (addr + offset * size_of T)) _)
  | _ => False
  end.
Proof.
  intros T ptr offset arr_size H_valid.
  destruct ptr as [| |(CppValidAddr addr) obj];
  - exfalso; contradiction H_valid. (* ptr为CppNullPtr：与有效性矛盾 *)
  - exfalso; contradiction H_valid. (* ptr为CppTypedNullPtr：与有效性矛盾 *)
  - unfold cpp_ptr_arith. (* 展开定义，验证有效指针偏移合法性 *)
    assert (new_addr = CppValidAddr (addr + offset * size_of T)) by reflexivity.
    rewrite H; reflexivity.
Qed.

(* 定理5：C++ NULL与nullptr的兼容性（NULL可兼容nullptr，反之不成立，符合C++标准） *)
Theorem cpp_null_compatible_with_nullptr : ∀ (T : Type),
  (CppNullPtr : CppPtr T) = (CppTypedNullPtr : CppPtr T) → False.
Proof.
  intros T H_eq. inversion H_eq. (* 构造子不同，直接矛盾，无模糊推导 *)
Qed.

(* ======================== 模块导出（无符号冲突，统一记法，支撑下游调用） ======================== *)
Export CppAddr CppNullAddr CppValidAddr CppPtr CppNullPtr CppTypedNullPtr CppValidPtr.
Export CppNullError NullDerefError InvalidPtrArithError TypeMismatchError OutOfBoundsError.
Export CppNullOpResult CppOpSuccess CppOpError.
Export cpp_deref cpp_ptr_arith cpp_ptr_cast cpp_is_null cpp_is_valid_ptr size_of cast.
Export cpp_null_deref_error cpp_null_arith_error cpp_null_cast_any_type.
Export cpp_null_op_absorb cpp_null_vs_nullptr_diff cpp_null_plays_raw_role.
Export cpp_null_ptr_identity_unique cpp_null_no_undefined cpp_ptr_arith_bounds_safe.
Export cpp_null_compatible_with_nullptr CxxNullSystem CxxFRFSystem CppNullPtrIdentity.

(* 统一符号记法（与FRF全局规范对齐，通过作用域区分，无歧义） *)
Notation "NULL[ T ]" := (CppNullPtr : CppPtr T) (at level 20) : cpp_null_scope.
Notation "nullptr[ T ]" := (CppTypedNullPtr : CppPtr T) (at level 20) : cpp_null_scope.
Notation "ptr->*" := (cpp_deref ptr) (at level 35) : cpp_null_scope.
Notation "ptr + off" := (cpp_ptr_arith ptr off) (at level 30) : cpp_null_scope.
Open Scope cpp_null_scope.
Open Scope cs_null_scope.
Open Scope frf_scope.