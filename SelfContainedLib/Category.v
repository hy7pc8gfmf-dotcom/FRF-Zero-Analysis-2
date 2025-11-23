
(* SelfContainedLib/Category.v *)
From Coq Require Import Utf8.
From Coq Require Import FunctionalExtensionality.

Module Type BasicCategory.
  Parameter Obj : Type.
  Parameter Hom : Obj -> Obj -> Type.
  Parameter id : forall A, Hom A A.
  Parameter comp : forall A B C, Hom B C -> Hom A B -> Hom A C.
  Axiom id_left : forall A B (f : Hom A B), comp A B B (id B) f = f.
  Axiom id_right : forall A B (f : Hom A B), comp A A B f (id A) = f.
  Axiom assoc : forall A B C D (f : Hom A B) (g : Hom B C) (h : Hom C D),
    comp A C D h (comp A B C g f) = comp A B D (comp B C D h g) f.
End BasicCategory.

Module SetCategory <: BasicCategory.
  Definition Obj := Type.
  Definition Hom (A B : Type) := A -> B.
  Definition id A (x : A) := x.
  Definition comp A B C (g : B -> C) (f : A -> B) := fun x => g (f x).

  Lemma id_left A B (f : A -> B) : comp A B B (id B) f = f.
  Proof. 
    unfold comp, id.
    apply functional_extensionality.
    intro x.
    reflexivity.
  Qed.

  Lemma id_right A B (f : A -> B) : comp A A B f (id A) = f.
  Proof.
    unfold comp, id.
    apply functional_extensionality.
    intro x.
    reflexivity.
  Qed.

  Lemma assoc A B C D (f : A -> B) (g : B -> C) (h : C -> D) :
    comp A C D h (comp A B C g f) = comp A B D (comp B C D h g) f.
  Proof.
    unfold comp.
    apply functional_extensionality.
    intro x.
    reflexivity.
  Qed.
End SetCategory.

Theorem category_test : 42 = 42.
Proof. reflexivity. Qed.