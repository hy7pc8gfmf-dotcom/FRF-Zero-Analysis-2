(* # theories/FRF_MetaTheory.v *)
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import SelfContainedLib.Algebra.
Require Import SelfContainedLib.Category.
Require Import SelfContainedLib.Geometry.

(* ======================== 核心定义 ======================== *)

(* 公理即命题，无需重命名 *)
Definition Theory : Type := list Prop.

Inductive AxiomTag : Type :=
  | AlgebraTag : AlgebraAxiomTag -> AxiomTag
  | CategoryTag : CategoryAxiomTag -> AxiomTag
  | GeometryTag : GeometryAxiomTag -> AxiomTag.

Record TaggedAxiom : Type := {
  tag : AxiomTag;
  content : Prop
}.

Definition Interpretation (T₁ T₂ : Theory) : Type :=
  forall (φ : Prop), In φ T₁ -> exists ψ : Prop, In ψ T₂ /\ (φ -> ψ).

Definition Consistent (T : Theory) : Prop :=
  ~ exists (φ : Prop), In φ T /\ In (~φ) T.

Definition Extension (T₁ T₂ : Theory) : Prop :=
  forall φ, In φ T₁ -> In φ T₂.

(* ======================== 辅助引理 ======================== *)

Lemma algebra_tag_inj : forall t1 t2 : AlgebraAxiomTag,
  AlgebraTag t1 = AlgebraTag t2 -> t1 = t2.
Proof. intros; inversion H; reflexivity. Qed.

Lemma category_tag_inj : forall t1 t2 : CategoryAxiomTag,
  CategoryTag t1 = CategoryTag t2 -> t1 = t2.
Proof. intros; inversion H; reflexivity. Qed.

Lemma geometry_tag_inj : forall t1 t2 : GeometryAxiomTag,
  GeometryTag t1 = GeometryTag t2 -> t1 = t2.
Proof. intros; inversion H; reflexivity. Qed.

Lemma cross_domain_tags_neq :
  forall (a : AlgebraAxiomTag) (c : CategoryAxiomTag),
    AlgebraTag a <> CategoryTag c.
Proof. intros; intro H; discriminate H. Qed.

Theorem tagged_axiom_disjoint :
  forall (ax1 ax2 : TaggedAxiom),
    ax1.(tag) <> ax2.(tag) ->
    ax1.(content) <> ax2.(content).
Proof.
  intros ax1 ax2 H_tag_neq H_content_eq.
  destruct ax1 as [t1 φ1], ax2 as [t2 φ2]; simpl in *.
  rewrite H_content_eq in *.
  destruct t1, t2;
    try (apply algebra_axiom_disjoint; apply algebra_tag_inj; congruence);
    try (apply category_axiom_disjoint; apply category_tag_inj; congruence);
    try (apply geometry_axiom_disjoint; apply geometry_tag_inj; congruence);
    try (exfalso; apply cross_domain_tags_neq; congruence).
Qed.

Lemma empty_theory_consistent : Consistent [].
Proof. unfold Consistent; intros [φ [Hin _]]; inversion Hin. Qed.

Lemma subtheory_consistent :
  forall T₁ T₂, Extension T₁ T₂ -> Consistent T₂ -> Consistent T₁.
Proof.
  intros T₁ T₂ H_ext H_cons.
  unfold Consistent in *; intros [φ [Hin_neg Hin_pos]].
  apply H_cons; exists φ.
  split; [apply H_ext; assumption | assumption].
Qed.

(* ======================== 核心定理 ======================== *)

Definition FRF_BaseAxioms : list TaggedAxiom :=
  (* 代数公理 *)
  (AlgebraTag AddAssocTag, add_assoc) ::
  (AlgebraTag AddIdLeftTag, add_0_l) ::
  (AlgebraTag AddIdRightTag, add_0_r) ::
  (AlgebraTag MulAssocTag, Int.add_assoc) ::
  (AlgebraTag MulIdLeftTag, Int.add_zero) ::
  (AlgebraTag MulIdRightTag, Int.zero_add) ::
  (AlgebraTag MulLeftInvTag, Int.neg_add_self) ::
  (* 范畴公理 *)
  (CategoryTag CompAssocTag, fun C w x y z f g h => comp_assoc C f g h) ::
  (CategoryTag IdLeftTag, fun C x y f => id_left C f) ::
  (CategoryTag IdRightTag, fun C x y f => id_right C f) ::
  (CategoryTag FmapIdTag, fun C D F x => fmap_id F x) ::
  (CategoryTag FmapCompTag, fun C D F x y z f g => fmap_comp F f g) ::
  (CategoryTag NatTransNaturalityTag, fun C D F G η x y f => naturality η f) ::
  (CategoryTag IsoLeftInvTag, fun C D F G iso x => iso_left_inv iso x) ::
  (CategoryTag IsoRightInvTag, fun C D F G iso x => iso_right_inv iso x) ::
  (* 几何公理 *)
  (GeometryTag SphereMetricTag, fun M v => sphere_metric_pos_def M v) ::
  (GeometryTag HyperbolicMetricTag, fun M v => hyperbolic_metric_pos_def M v) ::
  (GeometryTag ChristoffelTag, fun M i j k H => sphere_christoffel_symmetric M i j k H) ::
  (GeometryTag HyperbolicChristoffelTag, fun M i j k H => hyperbolic_christoffel_symmetric M i j k H) ::
  (GeometryTag RiemannCurvatureTag, fun M r H => sphere_curvature_radius_relation M r H) ::
  (GeometryTag SphereManifoldTag, fun r θ φ H => sphere_manifold_valid r θ φ H) ::
  (GeometryTag HyperbolicManifoldTag, fun κ θ φ H => hyperbolic_manifold_valid κ θ φ H) ::
  nil.

Theorem FRF_base_axioms_disjoint :
  forall (ax1 ax2 : TaggedAxiom),
    In ax1 FRF_BaseAxioms ->
    In ax2 FRF_BaseAxioms ->
    ax1.(tag) <> ax2.(tag) ->
    ax1.(content) <> ax2.(content).
Proof.
  intros ax1 ax2 Hin1 Hin2 Hneq.
  apply tagged_axiom_disjoint; assumption.
Qed.

Axiom AlgebraConsistent : Consistent (map (fun ax : AlgebraAxiom => ax.(axiom_content))
  [(Build_AlgebraAxiom AddAssocTag add_assoc);
   (Build_AlgebraAxiom AddIdLeftTag add_0_l);
   (Build_AlgebraAxiom AddIdRightTag add_0_r)]).

Axiom CategoryConsistent : Consistent (map (fun ax : CategoryAxiom => ax.(axiom_content))
  [(Build_CategoryAxiom CompAssocTag (fun _ _ _ _ _ _ _ => I));
   (Build_CategoryAxiom IdLeftTag (fun _ _ _ => I));
   (Build_CategoryAxiom IdRightTag (fun _ _ _ => I))]).

Axiom GeometryConsistent : Consistent (map (fun ax : GeometryAxiom => ax.(axiom_content))
  [(Build_GeometryAxiom SphereMetricTag (fun _ _ => I));
   (Build_GeometryAxiom HyperbolicMetricTag (fun _ _ => I))]).

Theorem FRF_base_consistent : Consistent (map (fun ta : TaggedAxiom => ta.(content)) FRF_BaseAxioms).
Proof. admit. Admitted.

Definition compose_interpretation :
  forall T₁ T₂ T₃,
    Interpretation T₂ T₃ ->
    Interpretation T₁ T₂ ->
    Interpretation T₁ T₃.
Proof.
  intros T₁ T₂ T₃ I23 I12 φ Hin1.
  destruct (I12 φ Hin1) as [ψ [Hin2 Himp12]].
  destruct (I23 ψ Hin2) as [χ [Hin3 Himp23]].
  exists χ; split; [assumption | intro Hφ; apply Himp23; apply Himp12; assumption].
Defined.

Definition identity_interpretation :
  forall T, Interpretation T T.
Proof.
  intros T φ Hin; exists φ; split; [assumption | intro; assumption].
Defined.

(* ======================== 模块导出 ======================== *)

Export Theory AxiomTag TaggedAxiom Interpretation Consistent Extension.
Export FRF_BaseAxioms.
Export compose_interpretation identity_interpretation.
Export FRF_base_axioms_disjoint.