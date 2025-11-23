(* SelfContainedLib/Category.v *)

From Coq Require Import Utf8.
From Coq Require Import FunctionalExtensionality.

(** 范畴论基础模块 *)

Module Type BasicCategory.
  Parameter Obj : Type.
  Parameter Hom : Obj -> Obj -> Type.
  Parameter id : forall A, Hom A A.
  Parameter comp : forall A B C, Hom B C -> Hom A B -> Hom A C.
  
  (* 范畴公理 *)
  Axiom comp_assoc : forall A B C D (f : Hom A B) (g : Hom B C) (h : Hom C D),
      comp A C D h (comp A B C g f) = comp A B D (comp B C D h g) f.
  
  Axiom id_left : forall A B (f : Hom A B),
      comp A A B f (id A) = f.
  
  Axiom id_right : forall A B (f : Hom A B),
      comp A B B (id B) f = f.
End BasicCategory.

(** 集合范畴实现 *)
Module SetCategory <: BasicCategory.
  Definition Obj := Type.
  Definition Hom (A B : Type) := A -> B.
  
  Definition id (A : Type) : Hom A A := fun x => x.
  
  Definition comp (A B C : Type) (g : Hom B C) (f : Hom A B) : Hom A C :=
    fun x => g (f x).
  
  Lemma comp_assoc : forall A B C D (f : Hom A B) (g : Hom B C) (h : Hom C D),
      comp A C D h (comp A B C g f) = comp A B D (comp B C D h g) f.
  Proof.
    intros A B C D f g h.
    apply functional_extensionality.
    intro x.
    unfold comp.
    reflexivity.
  Qed.
  
  Lemma id_left : forall A B (f : Hom A B),
      comp A A B f (id A) = f.
  Proof.
    intros A B f.
    apply functional_extensionality.
    intro x.
    unfold comp, id.
    reflexivity.
  Qed.
  
  Lemma id_right : forall A B (f : Hom A B),
      comp A B B (id B) f = f.
  Proof.
    intros A B f.
    apply functional_extensionality.
    intro x.
    unfold comp, id.
    reflexivity.
  Qed.
End SetCategory.

(** 离散范畴实现 - 每个对象只有恒等态射 *)
Module DiscreteCategory (T : Type) <: BasicCategory.
  Definition Obj := T.
  
  Inductive Hom (A B : T) : Type :=
  | identity : A = B -> Hom A B.
  
  Definition id (A : T) : Hom A A := identity A A (eq_refl A).
  
  Definition comp (A B C : T) (g : Hom B C) (f : Hom A B) : Hom A C :=
    match f, g with
    | identity _ _ pf, identity _ _ pg =>
        identity A C (eq_trans pf pg)
    end.
  
  Lemma comp_assoc : forall A B C D (f : Hom A B) (g : Hom B C) (h : Hom C D),
      comp A C D h (comp A B C g f) = comp A B D (comp B C D h g) f.
  Proof.
    intros A B C D f g h.
    destruct f as [pf].
    destruct g as [pg].
    destruct h as [ph].
    unfold comp.
    f_equal.
    apply eq_trans_assoc.
  Qed.
  
  Lemma id_left : forall A B (f : Hom A B),
      comp A A B f (id A) = f.
  Proof.
    intros A B f.
    destruct f as [pf].
    unfold comp, id.
    f_equal.
    apply eq_trans_refl_l.
  Qed.
  
  Lemma id_right : forall A B (f : Hom A B),
      comp A B B (id B) f = f.
  Proof.
    intros A B f.
    destruct f as [pf].
    unfold comp, id.
    f_equal.
    apply eq_trans_refl_r.
  Qed.
End DiscreteCategory.

(** 函子定义 *)
Module Type Functor (C1 C2 : BasicCategory).
  Parameter F_Obj : C1.(Obj) -> C2.(Obj).
  Parameter F_Hom : forall A B, C1.(Hom) A B -> C2.(Hom) (F_Obj A) (F_Obj B).
  
  Axiom preserves_comp : forall A B C (f : C1.(Hom) A B) (g : C1.(Hom) B C),
      F_Hom A C (C1.(comp) A B C g f) = 
      C2.(comp) (F_Obj A) (F_Obj B) (F_Obj C) (F_Hom B C g) (F_Hom A B f).
  
  Axiom preserves_id : forall A,
      F_Hom A A (C1.(id) A) = C2.(id) (F_Obj A).
End Functor.

(** 恒等函子实现 *)
Module IdentityFunctor (C : BasicCategory) <: Functor C C.
  Definition F_Obj (A : C.(Obj)) : C.(Obj) := A.
  
  Definition F_Hom (A B : C.(Obj)) (f : C.(Hom) A B) : C.(Hom) A B := f.
  
  Lemma preserves_comp : forall A B C (f : C.(Hom) A B) (g : C.(Hom) B C),
      F_Hom A C (C.(comp) A B C g f) = 
      C.(comp) (F_Obj A) (F_Obj B) (F_Obj C) (F_Hom B C g) (F_Hom A B f).
  Proof.
    intros A B C f g.
    unfold F_Hom, F_Obj.
    reflexivity.
  Qed.
  
  Lemma preserves_id : forall A,
      F_Hom A A (C.(id) A) = C.(id) (F_Obj A).
  Proof.
    intros A.
    unfold F_Hom, F_Obj.
    reflexivity.
  Qed.
End IdentityFunctor.

(** 自然变换定义 *)
Module Type NaturalTransformation (C1 C2 : BasicCategory) (F G : Functor C1 C2).
  Parameter eta : forall A, C2.(Hom) (F.(F_Obj) A) (G.(F_Obj) A).
  
  Axiom naturality : forall A B (f : C1.(Hom) A B),
      C2.(comp) (F.(F_Obj) A) (F.(F_Obj) B) (G.(F_Obj) B) (G.(F_Hom) A B f) (eta A) =
      C2.(comp) (F.(F_Obj) A) (G.(F_Obj) A) (G.(F_Obj) B) (eta B) (F.(F_Hom) A B f).
End NaturalTransformation.

(** 恒等自然变换实现 *)
Module IdentityNaturalTransformation (C1 C2 : BasicCategory) (F : Functor C1 C2) 
       <: NaturalTransformation C1 C2 F F.
  Definition eta (A : C1.(Obj)) : C2.(Hom) (F.(F_Obj) A) (F.(F_Obj) A) :=
    C2.(id) (F.(F_Obj) A).
  
  Lemma naturality : forall A B (f : C1.(Hom) A B),
      C2.(comp) (F.(F_Obj) A) (F.(F_Obj) B) (F.(F_Obj) B) (F.(F_Hom) A B f) (eta A) =
      C2.(comp) (F.(F_Obj) A) (F.(F_Obj) A) (F.(F_Obj) B) (eta B) (F.(F_Hom) A B f).
  Proof.
    intros A B f.
    unfold eta.
    rewrite C2.(id_left).
    rewrite C2.(id_right).
    reflexivity.
  Qed.
End IdentityNaturalTransformation.

(** 一些基础的范畴论引理 *)

Section CategoryLemmas.
  Context (C : BasicCategory).
  
  Lemma comp_id_id : forall A,
      C.(comp) A A A (C.(id) A) (C.(id) A) = C.(id) A.
  Proof.
    intros A.
    rewrite C.(id_left).
    reflexivity.
  Qed.
  
  Lemma unique_id : forall A (f : C.(Hom) A A),
      (forall B (g : C.(Hom) A B), C.(comp) A A B g f = g) ->
      (forall B (h : C.(Hom) B A), C.(comp) B A A f h = h) ->
      f = C.(id) A.
  Proof.
    intros A f H1 H2.
    specialize (H1 A (C.(id) A)).
    rewrite C.(id_left) in H1.
    rewrite <- H1.
    apply H2.
  Qed.
End CategoryLemmas.

Export SetCategory.