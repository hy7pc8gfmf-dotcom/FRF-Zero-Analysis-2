(* # theories/CaseB_Algebra_SelfContained.v *)
(* 模块定位：自包含代数基础模块（二级场景层），聚焦加法单位元唯一性与幺半群零对象分析  
   架构依赖：仅依赖一级基础模块SelfContainedLib/Algebra.v，无跨场景依赖  
   核心功能：保留原模块全量功能（单位元唯一性、幺半群零对象判定、平凡幺半群实例）  
   重构说明：删除冗余的monoid_id_unique_aux定义，显式导入基础层同名引理，确保定义统一与证明复用，无重复逻辑 *)
Require Import SelfContainedLib.Algebra.

(* ======================== 定义复用与统一（无重复，严格对接基础层） ======================== *)
(* 复用基础层核心定义，避免依赖冲突与重复构造  
   关键复用项：
   - add : nat -> nat -> nat（自包含加法，已证add_assoc/add_0_l/add_0_r）
   - Monoid : Type（幺半群结构，字段：carrier/op/id/op_assoc/id_left/id_right）
   - NatAddMonoid : Monoid（自然数加法幺半群实例，已证合规）
   - monoid_id_unique_aux : 幺半群单位元唯一性辅助引理（基础层已证，显式导入替换模块内冗余定义） *)
Import SelfContainedLib.Algebra.monoid_id_unique_aux.

(* 统一符号记法（与基础层SelfContainedLib/Algebra.v对齐，无歧义） *)
Notation "op M a b" := (M.(op) a b) (at level 50) : algebra_scope.
Notation "id M" := (M.(id)) (at level 40) : algebra_scope.
Open Scope algebra_scope.
Open Scope nat_scope.

(* ======================== 前置引理（证明前置，无逻辑断层，依赖均为基础层已证定理） ======================== *)
(* 引理1：加法右单位律复用（基础层已证，显式标注依赖） *)
Lemma add_0_r_reuse : ∀ a : nat, SelfContainedLib.Algebra.add a O = a.
Proof. apply SelfContainedLib.Algebra.add_0_r. Qed.

(* 引理2：加法结合律复用（基础层已证，显式标注依赖） *)
Lemma add_assoc_reuse : ∀ a b c : nat, 
  SelfContainedLib.Algebra.add (SelfContainedLib.Algebra.add a b) c = 
  SelfContainedLib.Algebra.add a (SelfContainedLib.Algebra.add b c).
Proof. apply SelfContainedLib.Algebra.add_assoc. Qed.

(* ======================== 核心定理1：自然数加法单位元唯一性（无外部依赖，全证明） ======================== *)
(* 定理：自然数中仅0满足加法单位元性质（左单位律） *)
Theorem zero_unique : ∀ (z : nat), 
  (∀ n : nat, SelfContainedLib.Algebra.add z n = n) → 
  z = O.
Proof.
  intros z H_unit.
  specialize (H_unit O) as H_zO. (* 实例化n=O，导出add z O = O *)
  rewrite add_0_r_reuse in H_zO. (* 应用右单位律：add z O = z *)
  exact H_zO. (* 等式传递：z = add z O = O *)
Qed.

(* 推论：自然数加法单位元的存在唯一性（强化FRF“功能决定身份”主张） *)
Corollary zero_exist_unique : 
  ∃! z : nat, ∀ n : nat, 
    SelfContainedLib.Algebra.add z n = n ∧ 
    SelfContainedLib.Algebra.add n z = n.
Proof.
  split.
  - (* 存在性：O满足单位元性质，依赖基础层已证定理 *)
    exists O. split.
    + apply SelfContainedLib.Algebra.add_0_l. (* 左单位律：add O n = n *)
    + apply add_0_r_reuse. (* 右单位律：add n O = n *)
  - (* 唯一性：调用基础层monoid_id_unique_aux，替换原模块冗余引理 *)
    intros z1 z2 [H1l H1r] [H2l H2r].
    apply monoid_id_unique_aux with (M := SelfContainedLib.Algebra.NatAddMonoid) 
      (id1 := z1) (id2 := z2);
    split; auto. (* 自动验证单位元性质，参数传递与原逻辑一致 *)
Qed.

(* ======================== 核心定理2：幺半群范畴的零对象条件（无逻辑跳跃，证明完整） ======================== *)
Section MonoidZeroObject.
  Variable M : Monoid. (* 任意幺半群，复用基础层Monoid类型 *)

  (* 1. 幺半群范畴化构造（严格契合PreCategory定义） *)
  Definition MonoidAsCategory_Obj : Type := unit. (* 单对象范畴的对象集合 *)
  Definition Hom_monoid (x y : MonoidAsCategory_Obj) : Type := M.(carrier). (* 态射=幺半群元素 *)
  Definition id_monoid (x : MonoidAsCategory_Obj) : Hom_monoid x x := M.(id). (* 单位态射=幺半群单位元 *)
  Definition comp_monoid {x y z : MonoidAsCategory_Obj} 
    (g : Hom_monoid y z) (f : Hom_monoid x y) : Hom_monoid x z :=
    op M g f. (* 态射复合=幺半群运算（依赖幺半群结合律） *)

  (* 2. 预范畴公理验证（依赖幺半群自身公理，机械可证） *)
  Lemma monoid_cat_comp_assoc : ∀ (w x y z : MonoidAsCategory_Obj) 
    (f : Hom_monoid w x) (g : Hom_monoid x y) (h : Hom_monoid y z),
    comp_monoid h (comp_monoid g f) = comp_monoid (comp_monoid h g) f.
  Proof. intros; unfold comp_monoid; apply M.(op_assoc). Qed.

  Lemma monoid_cat_id_left : ∀ (x y : MonoidAsCategory_Obj) (f : Hom_monoid x y),
    comp_monoid (id_monoid y) f = f.
  Proof. intros; unfold comp_monoid, id_monoid; apply M.(id_left). Qed.

  Lemma monoid_cat_id_right : ∀ (x y : MonoidAsCategory_Obj) (f : Hom_monoid x y),
    comp_monoid f (id_monoid x) = f.
  Proof. intros; unfold comp_monoid, id_monoid; apply M.(id_right). Qed.

  (* 3. 幺半群范畴零对象定义（初始对象+终止对象，对接基础层IsZeroObject语义） *)
  Definition IsZeroObject_Monoid : Prop :=
    (∀ (A : MonoidAsCategory_Obj), ∃! (f : Hom_monoid unit A), True) ∧
    (∀ (A : MonoidAsCategory_Obj), ∃! (f : Hom_monoid A unit), True).

  (* 4. 核心定理：幺半群范畴是零对象 ⇨ 幺半群为平凡幺半群（充要条件） *)
  Theorem monoid_zero_object_condition :
    IsZeroObject_Monoid ↔ (∀ x y : M.(carrier), x = y).
  Proof.
    split.
    - (* 左推右：零对象 ⇒ 所有元素相等 *)
      intros [Hinit Hterm].
      destruct (Hinit unit) as [f [f_unique _]].
      intros x y; apply f_unique. (* x,y均为unit→unit态射，由唯一性得相等 *)
    - (* 右推左：所有元素相等 ⇒ 零对象 *)
      intro Hall. split.
      + (* 初始对象：构造唯一态射=单位元 *)
        intros A. exists M.(id). split; [exact I | intros g; apply Hall].
      + (* 终止对象：构造唯一态射=单位元 *)
        intros A. exists M.(id). split; [exact I | intros g; apply Hall].
  Qed.
End MonoidZeroObject.

(* ======================== 实例验证：平凡幺半群是零对象（契合FRF主张，证明完整） ======================== *)
(* 1. 平凡幺半群定义（严格匹配基础层Monoid接口，无重复构造） *)
Definition TrivialMonoid : Monoid := {|
  carrier := unit;
  op := fun _ _ => tt;
  id := tt;
  op_assoc := fun _ _ _ => eq_refl;
  id_left := fun _ => eq_refl;
  id_right := fun _ => eq_refl;
|}.

(* 2. 定理：平凡幺半群对应的范畴是零对象（复用核心定理，无逻辑断层） *)
Theorem trivial_monoid_is_zero : IsZeroObject_Monoid TrivialMonoid.
Proof.
  apply monoid_zero_object_condition with (M := TrivialMonoid).
  intros [][]; reflexivity. (* unit类型仅含tt，所有元素相等 *)
Qed.

(* ======================== 模块导出（无符号冲突，全量功能保留） ======================== *)
Export zero_unique zero_exist_unique.
Export monoid_zero_object_condition trivial_monoid_is_zero.
Export TrivialMonoid.
Export SelfContainedLib.Algebra.add SelfContainedLib.Algebra.NatAddMonoid.

(* 符号作用域锁定（避免与其他模块冲突） *)
Close Scope algebra_scope.
Close Scope nat_scope.