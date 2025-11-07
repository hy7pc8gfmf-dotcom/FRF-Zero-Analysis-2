(* theories/FRF_MetaTheory.v *)
(* 使用模块的版本 *)
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Module FRF_MetaTheory.

  (* 基础类型定义 *)
  Definition AxiomType : Type := Prop.

  Inductive PropertyCategory : Type :=
    | SafeNullCat
    | PointerNullCat
    | JavaRefNullCat
    | PythonNoneCat
    | LogicCat.

  (* 核心记录类型定义 *)
  Record FormalSystem : Type := {
    system_name : string;
    carrier : Type;
    axioms : list AxiomType;
    prop_category : PropertyCategory;
  }.

  Record FunctionalRole (S : FormalSystem) : Type := {
    role_id : string;
    core_features : list string;
  }.

End FRF_MetaTheory.

(* 导出整个模块 *)
Export FRF_MetaTheory.