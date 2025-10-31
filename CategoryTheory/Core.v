(* 文件: CategoryTheory/Core.v *)
Require Import Coq.Unicode.Utf8.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
[文件功能描述...]

Methodology Note:
This self-contained definition of core categorical structures is used
in place of larger external libraries (e.g., Coq-Category-Theory) to
ensure philosophical transparency and direct alignment with the FRF
framework's analysis. See the project README for a detailed rationale.
*)

(* 预范畴定义 *)
Record PreCategory := {
  Obj : Type;
  Hom : Obj → Obj → Type;
  
  id : ∀ x, Hom x x;
  comp : ∀ {x y z}, Hom y z → Hom x y → Hom x z;
  
  comp_assoc : ∀ {w x y z} (f: Hom w x) (g: Hom x y) (h: Hom y z),
    comp h (comp g f) = comp (comp h g) f;
  id_left : ∀ {x y} (f: Hom x y), comp (id y) f = f;
  id_right : ∀ {x y} (f: Hom x y), comp f (id x) = f
}.

Arguments Obj _ : clear implicits.
Arguments Hom {_} _ _.
Arguments id {_} _.
Arguments comp {_} {_} {_} {_} _ _.

Notation "g ∘ f" := (comp g f) (at level 40, left associativity).
Notation "id[ x ]" := (id x).

(* 函子定义 *)
Record Functor (C D : PreCategory) := {
  fobj : Obj C → Obj D;
  fmap : ∀ {x y}, Hom x y → Hom (fobj x) (fobj y);
  
  fmap_id : ∀ x, fmap (id x) = id (fobj x);
  fmap_comp : ∀ {x y z} (f: Hom x y) (g: Hom y z),
    fmap (g ∘ f) = fmap g ∘ fmap f
}.

Arguments fobj {_ _} _ _.
Arguments fmap {_ _} _ {_ _} _.

(* 自然变换定义 *)
Record NaturalTransformation {C D: PreCategory} (F G: Functor C D) := {
  component : ∀ x, Hom (fobj F x) (fobj G x);
  naturality : ∀ {x y} (f: Hom x y),
    component y ∘ fmap F f = fmap G f ∘ component x
}.

Arguments component {_ _ _ _} _ _.
Arguments naturality {_ _ _ _} _ {_ _} _.

(* 自然同构定义 *)
Record NaturalIsomorphism {C D: PreCategory} (F G: Functor C D) := {
  iso_transform : NaturalTransformation F G;
  iso_inverse : NaturalTransformation G F;
  iso_left_inv : ∀ x, component iso_inverse x ∘ component iso_transform x = id _;
  iso_right_inv : ∀ x, component iso_transform x ∘ component iso_inverse x = id _
}.