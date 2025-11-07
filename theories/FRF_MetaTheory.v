(* theories/FRF_MetaTheory.v *)
(* 确保编译通过的版本 *)
Require Import Coq.Strings.String.  (* 关键：导入string类型 *)
Require Import Coq.Lists.List.

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