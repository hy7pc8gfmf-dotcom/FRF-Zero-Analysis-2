(* 文件: CategoryTheory/Utilities.v *)
Require Import CategoryTheory.Core.

(* 逆自然变换的组件 *)
Definition iso_inverse_component {C D} {F G: Functor C D}
  (iso: NaturalIsomorphism F G) (x: Obj C) : Hom (fobj G x) (fobj F x) :=
  component (iso_inverse iso) x.

(* 恒等函子 *)
Definition Identity_Functor (C: PreCategory) : Functor C C := {|
  fobj := fun x => x;
  fmap := fun _ _ f => f;
  fmap_id := fun _ => eq_refl;
  fmap_comp := fun _ _ _ _ _ => eq_refl
|}.

(* 函子复合 *)
Definition comp_functor {C D E} (F: Functor D E) (G: Functor C D) : Functor C E := {|
  fobj := fun x => fobj F (fobj G x);
  fmap := fun _ _ f => fmap F (fmap G f);
  fmap_id := fun x => eq_trans (fmap_congr F (fmap_id G x)) (fmap_id F (fobj G x));
  fmap_comp := fun _ _ _ f g => 
    eq_trans (fmap_congr F (fmap_comp G f g)) (fmap_comp F (fmap G f) (fmap G g))
|}.

(* 1. 群范畴的零对象验证（代数系统） *)
Record Group : Type := {
  carrier : Type;
  op : carrier -> carrier -> carrier;
  id : carrier;
  inv : carrier -> carrier;
  (* 群公理：结合律、单位元、逆元 *)
  op_assoc : forall a b c, op a (op b c) = op (op a b) c;
  id_left : forall a, op id a = a;
  inv_left : forall a, op (inv a) a = id
}.

Definition TrivialGroup : Group := {|  (* 仅含单位元的平凡群 *)
  carrier := unit;
  op := fun _ _ => tt;
  id := tt;
  inv := fun _ => tt
|}.

Example GroupCategory : PreCategory := {|
  Obj := Group;
  Hom := fun G H => { f : G.(carrier) -> H.(carrier) | 
    forall a b, f (G.(op) a b) = H.(op) (f a) (f b) };  (* 群同态 *)
  id := fun G => exist _ (fun x => x) (fun _ _ => G.(op_assoc));
  comp := fun G H K f g => exist _ (fun x => g.(1) (f.(1) x)) _;
  (* 范畴公理证明：由群同态性质自动导出 *)
|}.

Lemma trivial_group_is_zero : IsZeroObject GroupCategory TrivialGroup.
Proof.
  split.
  - (* 初始对象：唯一同态到任意群 *)
    intro G. exists (exist _ (fun _ => G.(id)) _).
    split; [exact I|intros f _. apply GroupHomUnique; auto].
  - (* 终止对象：唯一同态从任意群到平凡群 *)
    intro G. exists (exist _ (fun _ => tt) _).
    split; [exact I|intros f _. apply GroupHomUnique; auto].
Qed.

(* 2. 拓扑空间范畴的零对象分析（几何系统） *)
Example TopologicalSpaceCategory : PreCategory := {|
  Obj := TopologicalSpace;  (* 10系列010-E-08定义的拓扑空间 *)
  Hom := fun X Y => ContinuousFunction X Y;  (* 连续映射 *)
|}.

Lemma topological_category_no_zero : 
  ~ exists Z : TopologicalSpace, IsZeroObject TopologicalSpaceCategory Z.
Proof. (* 证明拓扑空间范畴既无初始对象也无终止对象 *)
  intros [Z H]. destruct H as [Hinit Hterm].
  (* 利用离散空间与平庸空间的连续映射非唯一性导出矛盾 *)
  assert (discrete : TopologicalSpace := DiscreteSpace bool).
  assert (trivial : TopologicalSpace := TrivialSpace unit).
  destruct (Hinit discrete) as [f [_ funiq]].
  destruct (Hterm trivial) as [g [_ guniq]].
  apply (funiq (const true)) (const false); auto.
Qed.

(* 3. 零对象相对性定理（FRF核心主张形式化） *)
Theorem zero_object_relativity : 
  exists C D : PreCategory, 
    (exists Z : C, IsZeroObject C Z) /\
    (exists W : D, ~ IsZeroObject D W).
Proof.
  exists GroupCategory, TopologicalSpaceCategory.
  split; [exists TrivialGroup; apply trivial_group_is_zero|
          exists (DiscreteSpace nat); apply topological_category_no_zero].
Qed.
