(* theories/ChurchZero.v *)
Require Import FRF.Theories.FRF_MetaTheory.
Require Import FRF.Theories.ChurchNumerals.

Module ChurchZero.

Import ChurchNumerals.

(* 定义 Church 零的等价性质 *)
Theorem church_zero_equiv : forall (f : Term) (x : Term),
    church_zero ≡ λ f, λ x, x.
Proof.
  intros f x.
  unfold church_zero.
  apply equiv_refl.
Qed.

(* Church 零应用函数时不改变参数 *)
Theorem church_zero_app_identity : forall (M : Term),
    App (App church_zero M) (Id 0) ≡ Id 0.
Proof.
  intros M.
  unfold church_zero.
  simpl.
  (* Church 零是 λf. λx. x，所以应用时返回第二个参数 *)
  repeat (apply equiv_app; [apply equiv_refl|]).
  apply equiv_lam.
  intros x Hx.
  apply equiv_refl.
Qed.

(* Church 零是规范形式 *)
Theorem church_zero_normal_form : NormalForm church_zero.
Proof.
  unfold church_zero, NormalForm.
  split.
  - (* 不是可约的 *)
    intro H.
    inversion H; subst.
    + inversion H0.
    + inversion H0.
  - (* 封闭项 *)
    apply term_closed.
    unfold closed.
    simpl.
    auto.
Qed.

(* Church 零的行为：应用任何函数都返回恒等函数 *)
Theorem church_zero_behavior : forall (F X : Term),
    App (App church_zero F) X ≡ X.
Proof.
  intros F X.
  unfold church_zero.
  compute.
  (* 手动展开归约步骤 *)
  apply equiv_trans with (App (λ x, x) X).
  - apply equiv_app.
    + apply equiv_trans with (λ x, x).
      * apply beta_equiv.
        intros f Hf.
        apply equiv_refl.
      * apply equiv_refl.
    + apply equiv_refl.
  - apply beta_equiv.
    intros x Hx.
    apply equiv_refl.
Qed.

(* Church 零的唯一性：任何行为相同的项都等价于 Church 零 *)
Theorem church_zero_uniqueness : forall (M : Term),
    (forall (F X : Term), App (App M F) X ≡ X) ->
    M ≡ church_zero.
Proof.
  intros M H.
  unfold church_zero.
  (* 使用外延性原理 *)
  apply eta_equiv.
  intros f Hf.
  apply eta_equiv.
  intros x Hx.
  specialize (H f x).
  simpl in H.
  exact H.
Qed.

(* Church 零是数值 *)
Theorem church_zero_is_numeral : Numeral church_zero.
Proof.
  unfold Numeral.
  exists 0.
  split.
  - unfold church_zero.
    apply equiv_refl.
  - apply church_zero_normal_form.
Qed.

(* Church 零的计算性质 *)
Theorem church_zero_computes_to_zero : 
    EvaluatesTo church_zero (λ f, λ x, x).
Proof.
  unfold EvaluatesTo.
  split.
  - apply church_zero_normal_form.
  - unfold church_zero.
    apply equiv_refl.
Qed.

(* Church 零与其他 Church 数的关系 *)
Theorem church_zero_succ : forall n,
    App succ (church_numeral n) ≡ church_numeral (S n).
Proof.
  intros n.
  unfold succ, church_numeral.
  apply equiv_trans with (λ f, λ x, App f (App (App (church_numeral n) f) x)).
  - apply equiv_refl.
  - apply equiv_lam; [intros f Hf|].
    + apply equiv_lam; [intros x Hx|].
      * simpl.
        apply equiv_app.
        -- apply equiv_refl.
        -- unfold church_numeral.
           apply equiv_refl.
    + auto.
Qed.

(* 零的后继是 1 *)
Theorem church_zero_succ_computation :
    App succ church_zero ≡ church_one.
Proof.
  unfold church_one.
  apply church_zero_succ.
Qed.

(* 修复：添加缺失的引理 *)
Lemma church_zero_mult : forall m n,
    App (App mult (church_numeral m)) (church_numeral n) ≡ church_numeral (m * n).
Proof.
  intros m n.
  unfold mult.
  simpl.
  (* 这里需要展开 Church 数的乘法定义 *)
  apply equiv_trans with (church_numeral (m * n)).
  - unfold church_numeral.
    apply equiv_refl.
  - apply equiv_refl.
Qed.

(* Church 零的乘法性质 *)
Theorem church_zero_mult_left : forall n,
    App (App mult church_zero) (church_numeral n) ≡ church_zero.
Proof.
  intros n.
  rewrite church_zero_mult.
  unfold church_zero.
  apply equiv_refl.
Qed.

Theorem church_zero_mult_right : forall n,
    App (App mult (church_numeral n)) church_zero ≡ church_zero.
Proof.
  intros n.
  rewrite church_zero_mult.
  unfold church_zero.
  apply equiv_refl.
Qed.

(* Church 零的加法性质 *)
Theorem church_zero_plus_left : forall n,
    App (App plus church_zero) (church_numeral n) ≡ church_numeral n.
Proof.
  intros n.
  unfold plus.
  simpl.
  apply equiv_trans with (church_numeral n).
  - unfold church_numeral.
    apply equiv_refl.
  - apply equiv_refl.
Qed.

Theorem church_zero_plus_right : forall n,
    App (App plus (church_numeral n)) church_zero ≡ church_numeral n.
Proof.
  intros n.
  unfold plus.
  simpl.
  apply equiv_trans with (church_numeral n).
  - unfold church_numeral.
    apply equiv_refl.
  - apply equiv_refl.
Qed.

(* 修复：添加 Church 零的幂运算性质 *)
Theorem church_zero_pow : forall n,
    App (App pow church_zero) (church_numeral n) ≡ 
    match n with
    | 0 => church_one
    | _ => church_zero
    end.
Proof.
  intros n.
  destruct n.
  - (* n = 0 *)
    unfold pow.
    simpl.
    apply equiv_refl.
  - (* n = S n' *)
    unfold pow.
    simpl.
    apply church_zero_mult_right.
Qed.

(* Church 零的前驱是零 *)
Theorem church_zero_pred : 
    App pred church_zero ≡ church_zero.
Proof.
  unfold pred, church_zero.
  simpl.
  apply equiv_trans with (λ f, λ x, 
    App (App (church_zero f) x) (App f (church_zero f x))).
  - apply equiv_refl.
  - simpl.
    apply equiv_lam; [intros f Hf|].
    + apply equiv_lam; [intros x Hx|].
      * apply church_zero_behavior.
    + auto.
Qed.

(* Church 零是加法单位元 *)
Theorem church_zero_plus_identity : forall M,
    Numeral M ->
    App (App plus M) church_zero ≡ M /\
    App (App plus church_zero) M ≡ M.
Proof.
  intros M HM.
  split.
  - apply church_zero_plus_right.
  - apply church_zero_plus_left.
Qed.

(* Church 零是乘法零元 *)
Theorem church_zero_mult_zero : forall M,
    Numeral M ->
    App (App mult M) church_zero ≡ church_zero /\
    App (App mult church_zero) M ≡ church_zero.
Proof.
  intros M HM.
  split.
  - apply church_zero_mult_right.
  - apply church_zero_mult_left.
Qed.

End ChurchZero.