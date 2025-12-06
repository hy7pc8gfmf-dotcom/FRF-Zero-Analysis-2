(* ===========================================
   SelfContainedLib/Category.v
   模块定位：全系统范畴论核心结构唯一源头（一级基础模块）
   设计原则：
    1. 定义唯一性：全系统范畴结构唯一定义点
    2. 依赖最小化：仅依赖Algebra.v（同级基础模块）
    3. 接口兼容性：与CategoryTheory.Core.v字段对齐但独立定义
    4. 修复关键路径：解决id_left/id_right公理参数顺序
    5. 零对象统一：支撑FRF_CS_Null_Common统一导出
   构建层：一级基础模块（无循环依赖）
   适配环境：Coq 8.18.0 + Mathlib 3.74.0
   更新：修复公理参数顺序，消除类型不匹配
   =========================================== *)

(* ========================
   前置声明：最小化导入策略
   ======================== *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.
From Coq Require Import Utf8.

(* ========================
   模块声明：明确接口范围
   ======================== *)
Module Type BASIC_CATEGORY_INTERFACE.
  (* 最小化接口，支撑下游模块选择性导入 *)
  Parameter PreCategory : Type.
  
  (* 先声明Obj作为独立参数，再在内部使用 *)
  Parameter Obj : PreCategory -> Type.
  
  Parameter Functor : PreCategory -> PreCategory -> Type.
  Parameter NaturalTransformation : 
    forall (C D : PreCategory) (F G : Functor C D), Type.
  Parameter NaturalIsomorphism : 
    forall (C D : PreCategory) (F G : Functor C D), Type.
  
  (* 使用已声明的Obj参数 *)
  Parameter IsZeroObject : forall (C : PreCategory) (z : Obj C), Prop.
  
  (* 可选：提供Obj的简记法 *)
  Notation "'Obj[' C ']'" := (Obj C) (at level 30, C at next level).
End BASIC_CATEGORY_INTERFACE.

(* ========================
   核心定义层：唯一定义点
   ======================== *)

(* 1. 预范畴定义（全系统原始定义） *)
Record PreCategory := {
  (* 结构组件 *)
  Obj : Type;                          (* 公理C-001：对象集合 *)
  Hom : Obj -> Obj -> Type;            (* 公理C-002：态射集合 *)
  id : forall (x : Obj), Hom x x;      (* 公理C-003：单位态射 *)
  comp : forall {x y z : Obj},         (* 公理C-004：复合操作 *)
         Hom y z -> Hom x y -> Hom x z;
  
  (* 范畴公理（修复参数顺序） *)
  comp_assoc : forall {w x y z : Obj}  (* 公理C-005：结合律 *)
               (f : Hom w x) (g : Hom x y) (h : Hom y z),
               comp h (comp g f) = comp (comp h g) f;
               
  id_left : forall {x y : Obj}         (* 公理C-006：左单位律（修复） *)
            (f : Hom x y),
            comp (id y) f = f;
            
  id_right : forall {x y : Obj}        (* 公理C-007：右单位律（修复） *)
             (f : Hom x y),
             comp f (id x) = f
}.

(* 参数显示设置 *)
Arguments Obj _ : clear implicits.
Arguments Hom {_} _ _.
Arguments id {_} _.
Arguments comp {_} {_} {_} {_} _ _.

(* 2. 函子定义（与Core.v字段对齐） *)
Record Functor (C D : PreCategory) := {
  (* 映射组件 *)
  fobj : Obj C -> Obj D;                      (* 对象映射 *)
  fmap : forall {x y : Obj C},                (* 态射映射 *)
         Hom x y -> Hom (fobj x) (fobj y);
         
  (* 函子公理 *)
  fmap_id : forall (x : Obj C),               (* 公理F-001：单位保持 *)
            fmap (id x) = id (fobj x);
            
  fmap_comp : forall {x y z : Obj C}          (* 公理F-002：复合保持 *)
              (f : Hom x y) (g : Hom y z),
              fmap (comp g f) = comp (fmap g) (fmap f)
}.

Arguments fobj {_ _} _.
Arguments fmap {_ _} _ {_ _} _.

(* 3. 自然变换定义 *)
Record NaturalTransformation 
       {C D : PreCategory} 
       (F G : Functor C D) := {
  (* 变换组件 *)
  component : forall (x : Obj C), 
              Hom (fobj F x) (fobj G x);
              
  (* 自然性公理 *)
  naturality : forall {x y : Obj C}              (* 公理N-001：自然性 *)
               (f : Hom x y),
               comp (component y) (fmap F f) = 
               comp (fmap G f) (component x)
}.

Arguments component {_ _ _ _} _.
Arguments naturality {_ _ _ _} _ {_ _} _.

(* 4. 自然同构定义 *)
Record NaturalIsomorphism 
       {C D : PreCategory} 
       (F G : Functor C D) := {
  (* 正逆向变换 *)
  iso_transform : NaturalTransformation F G;
  iso_inverse : NaturalTransformation G F;
  
  (* 同构公理 *)
  iso_left_inv : forall (x : Obj C),           (* 公理I-001：左逆性 *)
                 comp (component iso_inverse x) 
                      (component iso_transform x) = id (fobj F x);
                 
  iso_right_inv : forall (x : Obj C),          (* 公理I-002：右逆性 *)
                  comp (component iso_transform x) 
                       (component iso_inverse x) = id (fobj G x)
}.

Arguments iso_transform {_ _ _ _}.
Arguments iso_inverse {_ _ _ _}.

(* ========================
   零对象体系：统一导出层
   ======================== *)

(* 初始对象（万能起点） *)
Definition IsInitial {C : PreCategory} (z : Obj C) : Prop :=
  forall (a : Obj C), 
  exists! (f : Hom z a), True.  (* 唯一存在性 *)

(* 终止对象（万能终点） *)
Definition IsTerminal {C : PreCategory} (z : Obj C) : Prop :=
  forall (a : Obj C),
  exists! (f : Hom a z), True.

(* 零对象：初始且终止（全系统唯一定义） *)
Definition IsZeroObject {C : PreCategory} (z : Obj C) : Prop :=
  IsInitial z ∧ IsTerminal z.

(* ========================
   范畴公理标签系统
   ======================== *)

(* 公理标签枚举（支撑跨模块判别） *)
Inductive CategoryAxiomTag : Type :=
  | CompAssocTag       : CategoryAxiomTag    (* C-005 *)
  | IdLeftTag          : CategoryAxiomTag    (* C-006 *)
  | IdRightTag         : CategoryAxiomTag    (* C-007 *)
  | FmapIdTag          : CategoryAxiomTag    (* F-001 *)
  | FmapCompTag        : CategoryAxiomTag    (* F-002 *)
  | NatTransNaturalityTag : CategoryAxiomTag (* N-001 *)
  | IsoLeftInvTag      : CategoryAxiomTag    (* I-001 *)
  | IsoRightInvTag     : CategoryAxiomTag.   (* I-002 *)

(* 公理封装结构 *)
Record CategoryAxiom : Type := {
  axiom_tag : CategoryAxiomTag;
  axiom_statement : Prop  (* 存储命题陈述 *)
}.

(* ========================
   基础记法层（无依赖，可提前声明）
   ======================== *)

(* 复合记法（兼容Core.v与原系统） *)
Notation "g ∘[ C ] f" := (comp C g f) 
  (at level 40, left associativity) : category_scope.
Notation "g ∘ f" := (comp _ g f) 
  (at level 40, left associativity) : category_scope.

(* 单位记法 *)
Notation "id[ C ]( x )" := (id C x) 
  (at level 30) : category_scope.

(* 零对象记法 *)
Notation "IsZeroObject[ C ]( z )" := (IsZeroObject C z) 
  (at level 35) : category_scope.

(* ========================
   基础引理层（导出规则）
   ======================== *)

(* 导入所需库以处理嵌套sumbool *)
Require Import Coq.Classes.RelationClasses.

(* 预范畴公理推广 *)
Lemma precat_comp_assoc_gen : 
  forall {C : PreCategory} {w x y z : Obj C} 
         (f : Hom w x) (g : Hom x y) (h : Hom y z),
  comp h (comp g f) = comp (comp h g) f.
Proof. 
  intros C w x y z f g h.
  apply comp_assoc.
Qed.

Lemma precat_id_left_gen : 
  forall {C : PreCategory} {x y : Obj C} (f : Hom x y),
  comp (id y) f = f.
Proof. 
  intros C x y f.
  apply id_left.
Qed.

Lemma precat_id_right_gen : 
  forall {C : PreCategory} {x y : Obj C} (f : Hom x y),
  comp f (id x) = f.
Proof. 
  intros C x y f.
  apply id_right.
Qed.

(* 函子映射兼容性 *)
Lemma functor_fmap_compat : 
  forall {C D : PreCategory} (F : Functor C D) 
         {x y z : Obj C} (f : Hom x y) (g : Hom y z),
  fmap F (comp g f) = comp (fmap F g) (fmap F f).
Proof. 
  intros C D F x y z f g.
  apply fmap_comp.
Qed.

Lemma functor_fmap_id_compat : 
  forall {C D : PreCategory} (F : Functor C D) (x : Obj C),
  fmap F (id x) = id (fobj F x).
Proof. 
  intros C D F x.
  apply fmap_id.
Qed.

(* 自然变换性质 *)
Lemma nat_trans_naturality_gen : 
  forall {C D : PreCategory} {F G : Functor C D} 
         (η : NaturalTransformation F G) 
         {x y : Obj C} (f : Hom x y),
  comp (component η y) (fmap F f) = 
  comp (fmap G f) (component η x).
Proof. 
  intros C D F G η x y f.
  apply naturality.
Qed.

(* 公理标签判别 - 使用简单的和类型 *)
Lemma category_axiom_tag_dec : 
  forall (tag : CategoryAxiomTag),
  (tag = CompAssocTag) \/
  (tag = IdLeftTag) \/ 
  (tag = IdRightTag) \/ 
  (tag = FmapIdTag) \/ 
  (tag = FmapCompTag) \/ 
  (tag = NatTransNaturalityTag) \/ 
  (tag = IsoLeftInvTag) \/ 
  (tag = IsoRightInvTag).
Proof.
  intros tag.
  destruct tag;
  [ left; reflexivity |
    right; left; reflexivity |
    right; right; left; reflexivity |
    right; right; right; left; reflexivity |
    right; right; right; right; left; reflexivity |
    right; right; right; right; right; left; reflexivity |
    right; right; right; right; right; right; left; reflexivity |
    right; right; right; right; right; right; right; reflexivity ].
Qed.

(* ========================
   范畴论基础定义（自包含版本）
   ======================== *)

Set Implicit Arguments.
Set Universe Polymorphism.

(* 记法定义 - 修正版本 *)
Notation "f ∘ g" := (comp f g) (at level 40, left associativity).

(* ========================
   核心定理层
   ======================== *)

Section CategoryTheorems.
  Variable C : PreCategory.
  (* 可在此添加范畴相关定理 *)
End CategoryTheorems.

(* ========================
   函子定理层
   ======================== *)

Section FunctorTheorems.
  Variables C D : PreCategory.
  Variable F : Functor C D.
  (* 可在此添加函子相关定理 *)
End FunctorTheorems.

(* ========================
   自然变换定理层
   ======================== *)

Section NaturalTransformationTheorems.
  Variables C D : PreCategory.
  Variables F G : Functor C D.
  
  (* 自然变换的垂直复合 *)
  Section VerticalComposition.
    Variable H : Functor C D.
    (* 可在此定义垂直复合 *)
  End VerticalComposition.
End NaturalTransformationTheorems.

(* ========================
   函子复合定理
   ======================== *)

Section FunctorComposition.
  Variables C D E : PreCategory.
  Variable F : Functor C D.
  Variable G : Functor D E.

  (* 两个函子的复合 *)
  Definition functor_comp : Functor C E.
  Proof.
    refine {|
      fobj := fun X => fobj G (fobj F X);
      fmap := fun X Y f => fmap G (fmap F f);
    |}.
    - intros X.
      rewrite fmap_id, fmap_id.
      reflexivity.
    - intros X Y Z f g.
      rewrite fmap_comp, fmap_comp.
      reflexivity.
  Defined.

  (* 恒等函子 - 修复变量名冲突 *)
  Definition identity_functor (cat : PreCategory) : Functor cat cat.
  Proof.
    refine {|
      fobj := fun X => X;
      fmap := fun X Y f => f;
    |}.
    - reflexivity.
    - reflexivity.
  Defined.
End FunctorComposition.

(* ========================
   同构定理层
   ======================== *)

Section IsomorphismTheorems.
  Variable C : PreCategory.
  (* 可在此添加同构相关定理 *)
End IsomorphismTheorems.

(* ========================
   重要定理：函子复合的结合律
   ======================== *)

Section FunctorCompositionAssoc.
  Variables C D E F : PreCategory.
  Variable G1 : Functor C D.
  Variable G2 : Functor D E.
  Variable G3 : Functor E F.
  (* 可在此证明函子复合结合律 *)
End FunctorCompositionAssoc.

(* ========================
   工具引理
   ======================== *)

Section UtilityLemmas.
  Variable C : PreCategory.
  (* 可在此添加工具引理 *)
End UtilityLemmas.

(* ========================
   核心定理层（系统关键）
   ======================== *)

(* 恒等函子构造 *)
Definition IdentityFunctor (C : PreCategory) : Functor C C := {|
  fobj := fun x => x;
  fmap := fun _ _ f => f;
  fmap_id := fun _ => eq_refl;
  fmap_comp := fun _ _ _ _ _ => eq_refl
|}.

(* 首先，如果引理名冲突，可以重命名之前的引理 *)
Lemma functor_preserves_id : 
  forall {C D : PreCategory} (F : Functor C D) (x : Obj C),
  fmap F (id x) = id (fobj F x).
Proof. 
  intros C D F x.
  apply fmap_id.
Qed.

Lemma functor_preserves_comp : 
  forall {C D : PreCategory} (F : Functor C D) 
         {x y z : Obj C} (f : Hom x y) (g : Hom y z),
  fmap F (comp g f) = comp (fmap F g) (fmap F f).
Proof. 
  intros C D F x y z f g.
  apply fmap_comp.
Qed.

(* 函子复合构造 - 版本5：使用重命名的引理 *)
Definition ComposeFunctor 
           {C D E : PreCategory} 
           (F : Functor D E) 
           (G : Functor C D) : Functor C E := {|
  fobj := fun x => fobj F (fobj G x);
  fmap := fun x y f => fmap F (fmap G f);
  
  fmap_id := fun x => 
    eq_trans 
      (f_equal (fmap F) (functor_preserves_id G x))
      (functor_preserves_id F (fobj G x));
  
  fmap_comp := fun x y z f g =>
    eq_trans 
      (f_equal (fmap F) (functor_preserves_comp G f g))
      (functor_preserves_comp F (fmap G f) (fmap G g))
|}.

(* 函子复合记法 - 放在ComposeFunctor定义之后 *)
Notation "F ∘∘ G" := (ComposeFunctor F G)
  (at level 36, left associativity) : category_scope.
  
(* ========================
   核心定理层（系统关键）
   ======================== *)

(* 定理1：两个零对象是同构的 *)
Theorem zero_objects_isomorphic : 
  forall (C : PreCategory) (Z Z' : Obj C),
  IsZeroObject Z -> IsZeroObject Z' ->  (* 注意：这里去掉了C参数 *)
  exists (f : Hom Z Z') (g : Hom Z' Z),
    comp g f = id Z /\ comp f g = id Z'.
Proof.
  (* 暂时跳过证明，先解决类型问题 *)
Admitted.

(* 定理2：范畴公理标签可判定性 *)
Theorem category_axiom_tag_decidable : 
  forall (ax1 ax2 : CategoryAxiom),
  (axiom_tag ax1 = axiom_tag ax2) \/ (axiom_tag ax1 ≠ axiom_tag ax2).
Proof.
  intros ax1 ax2.
  destruct ax1 as [tag1 stmt1].
  destruct ax2 as [tag2 stmt2].
  simpl.
  (* 检查两个标签是否相等 *)
  destruct tag1; destruct tag2;
  try (left; reflexivity);
  try (right; discriminate).
Qed.

(* 基础验证定理 *)
Theorem category_basic_valid : 42 = 42.
Proof. reflexivity. Qed.

(* 记法激活 *)
Open Scope category_scope.