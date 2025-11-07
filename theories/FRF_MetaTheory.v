(* theories/FRF_MetaTheory.v - 步骤1：基本关系定义 *)
Require Import Coq.Strings.String.  (* 关键修复：导入string类型 *)
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

(* ======================== *)
(* 步骤1：添加基本关系定义 *)
(* ======================== *)

Record DefinitiveRelation (S : FormalSystem) : Type := {
  rel_id : string;
  related_objs : list (carrier S);  (* 使用carrier S而不是S.(carrier) *)
  rel_rule : carrier S -> carrier S -> Prop;
}.

Record ConceptIdentity (S : FormalSystem) (obj : carrier S) : Type := {
  ci_role : FunctionalRole S;
  ci_rels : list (DefinitiveRelation S);
  ci_unique : forall (y : carrier S), Prop;
}.

(* 模块导出 *)
Export FormalSystem.
Export FunctionalRole.
Export DefinitiveRelation.
Export ConceptIdentity.