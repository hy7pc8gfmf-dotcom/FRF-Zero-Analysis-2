(* SelfContainedLib/Category.v *)

From Coq Require Import Utf8.
From Coq Require Import FunctionalExtensionality.

(** 范畴论基础模块 *)
Module Type BasicCategory.
  Parameter Obj : Type.
  Parameter Hom : Obj -> Obj -> Type.
  Parameter id : forall A, Hom A A.
  Parameter comp : forall A B C, Hom B C -> Hom A B -> Hom A C.
  
  (* 左单位律：id_B ∘ f = f *)
  Axiom id_left : forall A B (f : Hom A B), comp A B B (id B) f = f.
  
  (* 右单位律：f ∘ id_A = f *)
  Axiom id_right : forall A B (f : Hom A B), comp A A B f (id A) = f.
  
  (* 结合律 *)
  Axiom assoc : forall A B C D (f : Hom A B) (g : Hom B C) (h : Hom C D),
    comp A C D h (comp A B C g f) = comp A B D (comp B C D h g) f.
End BasicCategory.

(** 集合范畴实现 *)
Module SetCategory <: BasicCategory.
  Definition Obj := Type.
  Definition Hom (A B : Type) := A -> B.
  Definition id A (x : A) := x.
  Definition comp A B C (g : B -> C) (f : A -> B) := fun x => g (f x).

  Lemma id_left A B (f : A -> B) : comp A B B (id B) f = f.
  Proof. 
    apply functional_extensionality; 
    intro x; 
    reflexivity. 
  Qed.

  Lemma id_right A B (f : A -> B) : comp A A B f (id A) = f.
  Proof.
    apply functional_extensionality;
    intro x;
    reflexivity.
  Qed.

  Lemma assoc A B C D (f : A -> B) (g : B -> C) (h : C -> D) :
    comp A C D h (comp A B C g f) = comp A B D (comp B C D h g) f.
  Proof.
    apply functional_extensionality;
    intro x;
    reflexivity.
  Qed.
End SetCategory.

(** 离散范畴实现 *)
Module DiscreteCategory (T : Type) <: BasicCategory.
  Definition Obj := T.
  Definition Hom (A B : T) := A = B.
  
  Definition id A : Hom A A := eq_refl.
  
  Definition comp A B C (g : Hom B C) (f : Hom A B) :=
    match f, g with
    | eq_refl, eq_refl => eq_refl
    end.

  Lemma id_left A B (f : Hom A B) : comp A B B (id B) f = f.
  Proof.
    intros.
    destruct f.
    reflexivity.
  Qed.

  Lemma id_right A B (f : Hom A B) : comp A A B f (id A) = f.
  Proof.
    intros.
    destruct f.
    reflexivity.
  Qed.

  Lemma assoc A B C D (f : Hom A B) (g : Hom B C) (h : Hom C D) :
    comp A C D h (comp A B C g f) = comp A B D (comp B C D h g) f.
  Proof.
    intros.
    destruct f, g, h.
    reflexivity.
  Qed.
End DiscreteCategory.

(** 对偶范畴 *)
Module OppositeCategory (C : BasicCategory) <: BasicCategory.
  Definition Obj := C.Obj.
  
  Definition Hom (A B : C.Obj) := C.Hom B A.
  
  Definition id A : Hom A A := C.id A.
  
  Definition comp A B C (g : Hom B C) (f : Hom A B) := 
    C.comp B A C f g.  (* 注意：这里顺序交换了 *)

  Lemma id_left A B (f : Hom A B) : comp A B B (id B) f = f.
  Proof.
    apply C.id_right.
  Qed.

  Lemma id_right A B (f : Hom A B) : comp A A B f (id A) = f.
  Proof.
    apply C.id_left.
  Qed.

  Lemma assoc A B C D (f : Hom A B) (g : Hom B C) (h : Hom C D) :
    comp A C D h (comp A B C g f) = comp A B D (comp B C D h g) f.
  Proof.
    (* 注意：在opposite范畴中结合律的方向会改变 *)
    intros.
    simpl.
    rewrite C.assoc.
    reflexivity.
  Qed.
End OppositeCategory.

(** 函子定义 *)
Module Type BasicFunctor.
  Parameter Dom : BasicCategory.
  Parameter Cod : BasicCategory.
  
  Parameter F_Obj : Dom.Obj -> Cod.Obj.
  Parameter F_Hom : forall A B, Dom.Hom A B -> Cod.Hom (F_Obj A) (F_Obj B).
  
  (* 函子保持恒等态射 *)
  Axiom preserves_id : forall A, 
    F_Hom A A (Dom.id A) = Cod.id (F_Obj A).
  
  (* 函子保持复合 *)
  Axiom preserves_comp : forall A B C (f : Dom.Hom A B) (g : Dom.Hom B C),
    F_Hom A C (Dom.comp A B C g f) = 
    Cod.comp (F_Obj A) (F_Obj B) (F_Obj C) 
      (F_Hom B C g) (F_Hom A B f).
End BasicFunctor.

(** 恒等函子 *)
Module IdentityFunctor (C : BasicCategory) <: BasicFunctor.
  Definition Dom := C.
  Definition Cod := C.
  
  Definition F_Obj (A : C.Obj) := A.
  
  Definition F_Hom (A B : C.Obj) (f : C.Hom A B) := f.
  
  Lemma preserves_id A : 
    F_Hom A A (Dom.id A) = Cod.id (F_Obj A).
  Proof.
    reflexivity.
  Qed.

  Lemma preserves_comp : forall A B C (f : C.Hom A B) (g : C.Hom B C) := f.
  
  Lemma preserves_comp A B C (f : Dom.Hom A B) (g : Dom.Hom B C),
    F_Hom A C (Dom.comp A B C g f) = 
    Cod.comp (F_Obj A) (F_Obj B) (F_Obj C) 
      (F_Hom B C g) (F_Hom A B f).
  Proof.
    reflexivity.
  Qed.
End IdentityFunctor.

(** 复合函子 *)
Module ComposeFunctor 
  (F : BasicFunctor) 
  (G : BasicFunctor with Definition Dom := F.Cod) <: BasicFunctor.
  
  Definition Dom := F.Dom.
  Definition Cod := G.Cod.
  
  Definition F_Obj (A : Dom.Obj) := 
    G.F_Obj (F.F_Obj A).

  Definition F_Hom (A B : Dom.Obj) (f : Dom.Hom A B) := 
    G.F_Hom (F.F_Obj A) (F.F_Obj B) (F.F_Hom A B f).
  
  Lemma preserves_id A : 
    F_Hom A A (Dom.id A) = Cod.id (F_Obj A).
  Proof.
    rewrite F.preserves_id.
    rewrite G.preserves_id.
    reflexivity.
  Qed.

  Lemma preserves_comp : forall A B C (f : Dom.Hom A B) (g : Dom.Hom B C) := 
    G.F_Hom (F.F_Obj A) (F.F_Obj A) (G.F_Hom (F.F_Obj A) (F.F_Obj A) (F.F_Hom A A (Dom.id A)) = 
    Cod.id (F_Obj A).
  Proof.
    intros.
    rewrite F.preserves_comp.
    rewrite G.preserves_comp.
    reflexivity.
  Qed.
End ComposeFunctor.

(** 自然变换定义 *)
Module Type NaturalTransformation.
  Parameter F G : BasicFunctor.
  Parameter Dom := F.Dom.
  Parameter Cod := F.Cod.
  
  (* 自然变换的分量 *)
  Parameter component : forall A : Dom.Obj, Cod.Hom (F.F_Obj A) (G.F_Obj A).
  
  Axiom naturality : forall A B (f : F.Dom.Hom A B),
    Cod.comp (F.F_Obj A) (F.F_Obj B) (G.F_Hom A B f) -> 
    forall A, component A = F_Hom A A (Dom.id A)).
End NaturalTransformation.

(** 测试定理 *)
Theorem category_test_id : SetCategory.id nat 42 = 42.
Proof. reflexivity. Qed.

Theorem category_test_comp : 
  let f := fun (x : nat) => x + 1 in
  let g := fun (x : nat) => x * 2 in
  SetCategory.comp nat nat nat g f 3 = 8.
Proof. reflexivity. Qed.

(** 范畴等价性定义 *)
Definition CategoryEquiv (C D : BasicCategory) : Prop :=
  exists (F : BasicFunctor with Definition Dom := C and Definition Cod := D),
  exists (G : BasicFunctor with Definition Dom := D and Definition Cod := C),
  forall A, F.F_Obj (G.F_Obj A) = A /\
  forall A B (f : C.Hom A B),
    F.F_Hom A B f = G.F_Hom A B f.

(** 零对象定义 *)
Class HasZeroObject (C : BasicCategory) := {
  zero_obj : C.Obj;
  zero_to_any : forall A, C.Hom zero_obj A;
  any_to_zero : forall A, C.Hom A zero_obj;
  zero_unique : forall (z : C.Obj),
    (forall A, exists! (f : C.Hom zero_obj A) /\
  (forall A, exists! (f : C.Hom A zero_obj);
}.

(** 终对象定义 *)
Class HasTerminalObject (C : BasicCategory) := {
  terminal_obj : C.Obj;
  terminal_morphism : forall A, C.Hom A terminal_obj;
  terminal_unique : forall A, C.Hom A terminal_obj -> A = terminal_obj;
}.

(** 测试终对象 *)
Module TestTerminal.
  Definition One : Type := unit.
  
  Instance OneCategory : BasicCategory := {
    Obj := Type;
    Hom A B := A -> B;
    id A := fun x => x;
    comp A B C g f := fun x => g (f x);
}.
