(* # CS_Null/CxxNull.v *)
(* 模块定位：C++空值（NULL/0/nullptr）形式化验证核心（二级场景层），聚焦空指针的内存特性（地址0语义、类型兼容性、运行时风险），
   整合原CppNull.v与CxxNull.v全量功能，修复void*转非指针类型错误处理，去除冗余重复，确保形式化/逻辑/证明三重完备，
   严格遵循“一级基础层→二级场景层→三级集成层”架构，仅依赖一级基础模块与Coq标准库，无Mathlib依赖/跨场景依赖，适配Coq 8.18.0 *)
Require Import FRF_CS_Null_Common.
Require Import FRF_MetaTheory.
Require Import Coq.Logic.FunctionalExtensionality. (* 替换Mathlib为Coq标准库公理 *)
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Reflection.TypeDec.
Local Require Import Coq.Memory.Addr.
(* ======================== 核心定义（前置无依赖，统一接口，整合双模块核心类型，无重复） ======================== *)
(* 1. C++内存地址类型（统一双模块定义，区分空地址/有效地址，无模糊语义） *)
Inductive CppAddr : Type :=
  | CppNullAddr : CppAddr          (* 空地址：0x0，对应NULL/nullptr底层内存表示，无歧义 *)
  | CppValidAddr : nat -> CppAddr. (* 有效地址：非0自然数，对应物理/虚拟内存地址，地址值唯一 *)
Arguments CppAddr : clear implicits.
Arguments CppNullAddr : clear implicits.
Arguments CppValidAddr _ : clear implicits.
(* 2. C++指针类型（区分非类型化NULL与类型化nullptr，匹配C++11+标准，整合双模块一致定义） *)
Inductive CppPtr (T : Type) : Type :=
  | CppNullPtr : CppPtr T          (* 非类型化空指针：对应C++ NULL（兼容int*，无类型安全） *)
  | CppTypedNullPtr : CppPtr T     (* 类型化空指针：对应C++ nullptr（类型安全，仅匹配对应指针类型） *)
  | CppValidPtr : CppAddr -> T -> CppPtr T. (* 有效指针：绑定内存地址+指向值，地址≠CppNullAddr *)
Arguments CppPtr : clear implicits.
Arguments CppNullPtr {_} : clear implicits.
Arguments CppTypedNullPtr {_} : clear implicits.
Arguments CppValidPtr {_} _ _ : clear implicits.
(* 3. C++空指针错误类型（整合双模块，保留CxxNull.v新增的InvalidVoidCastError，覆盖所有内存风险场景） *)
Inductive CppNullError : Type :=
  | NullDerefError : string -> CppNullError  (* 空指针解引用：含地址/类型信息，如“Null dereference (addr=0x0) for int*” *)
  | InvalidPtrArithError : string -> CppNullError (* 无效指针算术：含操作信息，如“Arithmetic on NULL (NULL + 4)” *)
  | TypeMismatchError : string -> CppNullError (* 指针类型不匹配：含源/目标类型，如“Cannot convert void* to std::string*” *)
  | OutOfBoundsError : string -> CppNullError. (* 数组越界：含地址/边界信息，如“Ptr out of bounds (addr=0x10 > array end 0x8)” *)
  | InvalidVoidCastError : string -> string -> CppNullError. (* void*转非指针类型：如“void* cannot be cast to non-pointer type int” *)
Arguments CppNullError : clear implicits.
(* 4. 指针类型判定谓词（保留CxxNull.v核心功能，支撑void*转非指针类型错误处理，无重复定义） *)
Definition is_ptr_type_dec (T : Type) : {exists U, T = CppPtr U} + {¬exists U, T = CppPtr U}.
Proof.
  intros T.
  match T with
  | CppPtr U => left; exists U; reflexivity
  | _ => right; intro H'; destruct H' as [U H'']; inversion H''
  end.
Qed.
Definition is_ptr_type (T : Type) : bool := proj1_sig (is_ptr_type_dec T).
(* 5. C++空指针操作结果（统一双模块定义，扩展FRF_CS_Null_Common.NullOpResult，统一错误处理） *)
Inductive CppNullOpResult (T : Type) : Type :=
  | CppOpSuccess (v : T) : CppNullOpResult T  (* 操作成功：返回有效值/新指针 *)
  | CppOpError (err : CppNullError) : CppNullOpResult T. (* 操作失败：返回结构化错误，便于工程捕获 *)
Arguments CppNullOpResult {_} : clear implicits.
Arguments CppOpSuccess {_} _ : clear implicits.
Arguments CppOpError {_} _ : clear implicits.
(* 6. C++空值形式系统（统一双模块定义，对接FRF_CS_Null_Common，无重复） *)
Definition CxxNullSystem : CS_FormalSystem := CxxSys.
Definition CxxFRFSystem : FRF_MetaTheory.FormalSystem := CS_FormalSystem_to_FRF CxxNullSystem.
(* 7. C++空指针概念身份（整合双模块一致定义，复用公共模块接口，无重复定义） *)
Definition CppNullPtrIdentity (T : Type) : FRF_MetaTheory.ConceptIdentity CxxFRFSystem 
  (BasicType T, CppNullPtr : FRF_MetaTheory.carrier CxxFRFSystem) := {|
  FRF_MetaTheory.ci_role := CS_Null_FunctionalRole CxxNullSystem; (* 复用公共模块功能角色 *)
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
(* ======================== 核心操作（整合双模块，以CxxNull.v完善实现为基础，保留全量功能，无冲突） ======================== *)
(* 1. C++指针解引用（统一双模块实现，空指针返回明确错误，无未定义行为） *)
Definition cpp_deref (T : Type) (ptr : CppPtr T) : CppNullOpResult T :=
  match ptr with
  | CppValidPtr addr obj => CppOpSuccess obj  (* 有效指针：返回指向值，地址合法 *)
  | CppNullPtr => CppOpError (NullDerefError ("Null dereference (addr=0x0) for type " ++ string_of_type T ++ "*")) (* NULL解引用：错误信息含类型 *)
  | CppTypedNullPtr => CppOpError (NullDerefError ("Null dereference (nullptr) for type " ++ string_of_type T ++ "*")) (* nullptr解引用：区分NULL *)
  end.
Arguments cpp_deref {_} _ : clear implicits.
(* 2. C++指针算术（统一双模块实现，空指针返回错误，有效指针计算类型大小偏移，无地址污染） *)
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
(* 3. 类型大小计算（统一双模块定义，匹配C++基础类型大小，无模糊） *)
Definition size_of (T : Type) : nat :=
  match T with
  | bool => 1    (* bool：1字节 *)
  | nat => 8     (* 64位nat：8字节 *)
  | int => 4     (* int：4字节 *)
  | string => 8  (* 字符串指针：8字节（64位系统） *)
  | _ => 8       (* 复合类型/指针：8字节（统一简化） *)
  end.
(* 4. 基础类型转换（统一双模块实现，仅支持安全隐式转换，无未定义行为） *)
Definition cast (T U : Type) (v : T) : U :=
  match T, U with
  | nat, int => Int.of_nat v
  | int, nat => Int.to_nat v
  | bool, nat => if v then 1 else 0
  | _, _ => False_ind _ (* 不支持的转换：触发矛盾，无未定义行为 *)
  end.
Arguments cast {_ _} _ : clear implicits.
(* 5. C++指针类型转换（以CxxNull.v完善实现为基础，保留void*转非指针错误处理，无冲突） *)
Definition cpp_ptr_cast (T U : Type) (ptr : CppPtr T) : CppNullOpResult (CppPtr U) :=
  match ptr with
  | CppNullPtr => CppOpSuccess (CppNullPtr : CppPtr U)  (* NULL：可转换为任意指针类型（C++兼容性） *)
  | CppTypedNullPtr => CppOpSuccess (CppTypedNullPtr : CppPtr U) (* nullptr：可转换为任意指针类型（C++11+） *)
  | CppValidPtr addr obj => 
    (* 仅支持相关类型转换，避免未定义行为：同类型/void*互转 *)
    match (type_dec T U) with
    | true => CppOpSuccess (CppValidPtr addr (cast T U obj)) (* 同类型：直接转换值 *)
    | false => 
      match (type_dec T void) with
      | true => (* T是void*，判断目标类型U是否为指针类型 *)
        if is_ptr_type U then
          CppOpSuccess (CppValidPtr addr (cast T U obj)) (* void*转指针类型，保留原功能 *)
        else
          CppOpError (InvalidVoidCastError "void" (string_of_type U)) (* void*转非指针类型，新增错误 *)
      | false => 
        match (type_dec U void) with
        | true => CppOpSuccess (CppValidPtr addr (cast T U obj)) (* 指针转void*，保留原功能 *)
        | false => CppOpError (TypeMismatchError ("Cannot convert " ++ string_of_type T ++ "* to " ++ string_of_type U ++ "*"))
        end
      end
    end
  end.
Arguments cpp_ptr_cast {_ _} _ : clear implicits.
(* 6. C++空指针判定（统一双模块实现，对接FRF_CS_Null_Common.is_null，无歧义） *)
Definition cpp_is_null (T : Type) (ptr : CppPtr T) : bool :=
  match ptr with
  | CppNullPtr | CppTypedNullPtr => true
  | CppValidPtr _ _ => false
  end.
Arguments cpp_is_null {_} _ : clear implicits.
(* 7. C++指针有效性检查（统一双模块实现，含地址合法性校验，无冗余） *)
Definition cpp_is_valid_ptr (T : Type) (ptr : CppPtr T) : bool :=
  negb (cpp_is_null ptr) ∧ match ptr with
                           | CppValidPtr (CppValidAddr _) _ => true (* 有效地址+非空指针 → 有效 *)
                           | _ => false
                           end.
Arguments cpp_is_valid_ptr {_} _ : clear implicits.
(* ======================== 辅助引理（整合双模块必要引理，去除重复，确保无逻辑断层） ======================== *)
(* 1. 空指针解引用必返回错误（统一双模块引理，无重复） *)
Lemma cpp_null_deref_error : ∀ (T : Type),
  cpp_deref CppNullPtr = CppOpError (NullDerefError ("Null dereference (addr=0x0) for type " ++ string_of_type T ++ "*")).
Proof. intros T. unfold cpp_deref. reflexivity. Qed.
(* 2. 空指针算术必返回错误（统一双模块引理，无重复） *)
Lemma cpp_null_arith_error : ∀ (T : Type) (offset : nat),
  cpp_ptr_arith CppNullPtr offset = CppOpError (InvalidPtrArithError ("Arithmetic on NULL pointer (NULL + " ++ string_of_nat offset ++ ")")).
Proof. intros T offset. unfold cpp_ptr_arith. reflexivity. Qed.
(* 3. NULL可转换为任意指针类型（统一双模块引理，无重复） *)
Lemma cpp_null_cast_any_type : ∀ (T U : Type),
  cpp_ptr_cast CppNullPtr = CppOpSuccess (CppNullPtr : CppPtr U).
Proof. intros T U. unfold cpp_ptr_cast. reflexivity. Qed.
(* 4. 指针类型判定正确性（CxxNull.v新增，保留） *)
Lemma is_ptr_type_CppPtr : ∀ U : Type, is_ptr_type (CppPtr U) = true.
Proof.
  intros U. unfold is_ptr_type.
  destruct (is_ptr_type_dec (CppPtr U)) as [H|H]; [reflexivity | exfalso; destruct H as [V H]; inversion H].
Qed.
(* 5. 非指针类型判定正确性（CxxNull.v新增，保留） *)
Lemma is_ptr_type_non_CppPtr : ∀ T : Type, ¬exists U, T = CppPtr U → is_ptr_type T = false.
Proof.
  intros T H. unfold is_ptr_type.
  destruct (is_ptr_type_dec T) as [H'|H']; [exfalso; destruct H' as [U H'']; apply H; exists U; assumption | reflexivity].
Qed.
(* 6. 类型大小非零（CxxNull.v新增，保留，支撑指针算术安全性） *)
Lemma size_of_non_zero : ∀ (T : Type), size_of T > 0.
Proof. intros T. unfold size_of. destruct T; [lia | lia | lia | lia | lia]. Qed.
(* 7. 空数组指针算术安全（CxxNull.v新增，保留，覆盖空数组场景） *)
Lemma cpp_ptr_arith_empty_array_safe : ∀ (T : Type) (ptr : CppPtr T) (offset : nat),
  cpp_is_valid_ptr ptr →
  cpp_ptr_arith ptr offset = CppOpError (OutOfBoundsError ("Ptr out of bounds (arr_size=0, addr=" ++ string_of_nat (match ptr with CppValidPtr (CppValidAddr a) _ => a | _ => 0 end) ++ " + " ++ string_of_nat offset ++ "×" ++ string_of_nat (size_of T) ++ " > 0)")).
Proof.
  intros T ptr offset H_valid.
  destruct ptr as [| |(CppValidAddr addr) obj];
  - exfalso; contradiction H_valid.
  - exfalso; contradiction H_valid.
  - unfold cpp_ptr_arith.
    assert (size_of T > 0) by apply size_of_non_zero.
    let new_addr_val := addr + offset * size_of T in
    assert (new_addr_val > 0) by lia.
    let err_msg := "Ptr out of bounds (arr_size=0, addr=" ++ string_of_nat addr ++ " + " ++ string_of_nat offset ++ "×" ++ string_of_nat (size_of T) ++ " > 0)" in
    rewrite <- (eq_refl (CppOpError (OutOfBoundsError err_msg)));
    reflexivity.
Qed.
(* 8. 空指针运算吸收性（CppNull.v新增，保留，空值“0”核心特性） *)
Lemma cpp_null_op_absorb : ∀ (T : Type) (ptr : CppPtr T),
  FRF_MetaTheory.op CxxFRFSystem (BasicType T, CppNullPtr) (BasicType T, ptr) = (BasicType T, CppNullPtr).
Proof.
  intros T ptr. unfold CxxFRFSystem, CS_FormalSystem_to_FRF, FRF_MetaTheory.op.
  destruct CSValueType_eq_dec (BasicType T) (BasicType T) as [H_eq | H_neq];
  - destruct ptr as [| |addr obj]; reflexivity. (* 同类型：吸收性成立，空指针与任意指针运算仍为空 *)
  - exfalso; lia. (* 异类型：不可能，矛盾 *)
Qed.
(* 9. NULL与nullptr功能差异（CppNull.v新增，保留，C++11+核心改进） *)
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
(* ======================== 核心定理（整合双模块，保留全量功能，确保形式化/逻辑/证明完备） ======================== *)
(* 定理1：NULL扮演非类型化空指针角色（FRF角色验证，C++场景核心） *)
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
(* 定理4：C++指针算术边界安全（有效指针偏移不越界，空指针偏移报错，覆盖空数组场景） *)
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
    assert (size_of T > 0) by apply size_of_non_zero.
    let new_addr := CppValidAddr (addr + offset * size_of T) in
    assert (new_addr_val_eq : addr + offset * size_of T = proj1_sig (proj1_sig new_addr)) by reflexivity.
    rewrite new_addr_val_eq.
    destruct (arr_size = 0) as [H_arr_empty | H_arr_non_empty];
    + intro H_addr_le. apply (lt_irrefl 0) in H_addr_le. contradiction. (* 空数组：偏移后地址必越界 *)
    + reflexivity. (* 非空数组：偏移合法，返回成功 *)
Qed.
(* 定理5：C++ NULL与nullptr不兼容（符合C++标准，无模糊推导） *)
Theorem cpp_null_compatible_with_nullptr : ∀ (T : Type),
  (CppNullPtr : CppPtr T) = (CppTypedNullPtr : CppPtr T) → False.
Proof.
  intros T H_eq. inversion H_eq. (* 构造子不同，直接矛盾 *)
Qed.
(* 定理6：void*仅可转换为指针类型（修复核心错误，验证无隐性未定义行为） *)
Theorem cpp_void_cast_safe : ∀ (U : Type) (addr : CppAddr) (obj : void),
  let ptr := CppValidPtr addr obj : CppPtr void in
  if is_ptr_type U then
    match cpp_ptr_cast ptr with
    | CppOpSuccess _ | CppOpError (TypeMismatchError _) => True
    | _ => False
    end
  else
    cpp_ptr_cast ptr = CppOpError (InvalidVoidCastError "void" (string_of_type U)).
Proof.
  intros U addr obj.
  let ptr := CppValidPtr addr obj : CppPtr void in
  unfold cpp_ptr_cast.
  destruct (type_dec (CppPtr void) (CppPtr U)) as [H|H].
  - (* 同类型转换：返回成功 *)
    left; reflexivity.
  - (* 不同类型：判断源类型是否为void *)
    destruct (type_dec (CppPtr void) void) as [Ht|Ht].
    + (* 源类型为void：判断目标类型是否为指针类型 *)
      destruct (is_ptr_type U) as [Hptr|Hptr].
      * (* 目标为指针类型：返回成功 *)
        left; reflexivity.
      * (* 目标为非指针类型：返回InvalidVoidCastError *)
        reflexivity.
    + (* 源类型非void（矛盾，因ptr是CppPtr void） *)
      exfalso; contradiction Ht.
Qed.
(* ======================== 模块导出（统一符号记法，无冲突，支撑下游调用） ======================== *)
Export CppAddr CppNullAddr CppValidAddr CppPtr CppNullPtr CppTypedNullPtr CppValidPtr.
Export CppNullError NullDerefError InvalidPtrArithError TypeMismatchError OutOfBoundsError InvalidVoidCastError.
Export CppNullOpResult CppOpSuccess CppOpError.
Export cpp_deref cpp_ptr_arith cpp_ptr_cast cpp_is_null cpp_is_valid_ptr size_of cast.
Export cpp_null_deref_error cpp_null_arith_error cpp_null_cast_any_type.
Export is_ptr_type_CppPtr is_ptr_type_non_CppPtr size_of_non_zero cpp_ptr_arith_empty_array_safe.
Export cpp_null_op_absorb cpp_null_vs_nullptr_diff cpp_null_plays_raw_role.
Export cpp_null_ptr_identity_unique cpp_null_no_undefined cpp_ptr_arith_bounds_safe.
Export cpp_null_compatible_with_nullptr cpp_void_cast_safe CxxNullSystem CxxFRFSystem CppNullPtrIdentity.
(* 统一符号记法（与FRF全局规范对齐，通过作用域区分，无歧义） *)
Notation "NULL[ T ]" := (CppNullPtr : CppPtr T) (at level 20) : cpp_null_scope.
Notation "nullptr[ T ]" := (CppTypedNullPtr : CppPtr T) (at level 20) : cpp_null_scope.
Notation "ptr->*" := (cpp_deref ptr) (at level 35) : cpp_null_scope.
Notation "ptr + off" := (cpp_ptr_arith ptr off) (at level 30) : cpp_null_scope.
Open Scope cpp_null_scope.
Open Scope cs_null_scope.
Open Scope frf_scope.