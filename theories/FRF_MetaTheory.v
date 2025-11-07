(* theories/FRF_MetaTheory.v - 步骤2：修复字段访问语法 *)
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

(* ======================== *)
(* 步骤2：添加核心功能接口 *)
(* ======================== *)

(* 核心功能定义 *)
Definition PlaysFunctionalRole (S : FormalSystem) (obj : carrier S) 
  (r : FunctionalRole S) : Prop :=
  exists (cid : ConceptIdentity S obj), (ci_role cid) = r.

Definition core_feat_equiv {S : FormalSystem} (r1 r2 : FunctionalRole S) : Prop :=
  (core_features r1) = (core_features r2).

(* 基础引理 - 使用简单的证明 *)
Lemma functional_role_reflexive {S : FormalSystem} :
  forall (r : FunctionalRole S), core_feat_equiv r r.
Proof.
  intros r. unfold core_feat_equiv. reflexivity.
Qed.

Lemma role_identity_preserved {S : FormalSystem} :
  forall (r1 r2 : FunctionalRole S),
  (role_id r1) = (role_id r2) -> core_feat_equiv r1 r2 -> r1 = r2.
Proof.
  intros r1 r2 H_id H_feat.
  destruct r1, r2.
  simpl in *.
  congruence.
Qed.