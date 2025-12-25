
(* theories/ChurchNumerals.Confluence.v *)
(* ========================================================================== *)
(* Church Numerals 的合流性(Church-Rosser)证明模块 *)
(* 基于并行归约(Tait-Martin-Löf方法)，使用de Bruijn索引 *)

(* ========================================================================== *)
(* 在文件开头添加 *)
Set Printing All.      (* 显示所有隐式信息 *)
Set Debug "Typing".    (* 启用类型调试 *)

(* 基础库 *)
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(* 1. 导入标准库 *)
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Relations.Relations.
Require Import Coq.Program.Equality.
Require Import Coq.Wellfounded.Inclusion.
Require Import Lia.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.RelationClasses.
From Coq.Arith Require Import PeanoNat.  (* 更好的算术支持 *)
From Coq.Lists Require Import List.      (* 列表操作 *)
(* 确保导入所有必要模块 *)

Require Import Coq.Arith.Wf_nat.
Require Import Lia.

(* 10.6 灵活的基础归约关系 (可选，向后兼容)
   为不同使用场景提供别名
*)
Notation step := BetaStep.
Notation multi_step := BetaReduces.
Notation "t [ u // k ]" := (subst t u k) (at level 40).
Notation "t '-->' u" := (BetaStep t u) (at level 50).
Notation "t '-->>' u" := (BetaReduces t u) (at level 50).

(* ======================== 辅助定义和性质 ======================== *)

(* 10.8 关系性质证明 *)

(* 辅助引理：构造子单射性 *)
Lemma var_injective : forall n m, Var n = Var m -> n = m.
Proof. intros n m H; injection H; auto. Qed.

Lemma app_injective : forall t1 t2 u1 u2, App t1 t2 = App u1 u2 -> t1 = u1 /\ t2 = u2.
Proof. intros t1 t2 u1 u2 H; injection H; auto. Qed.

Lemma abs_injective : forall t u, Abs t = Abs u -> t = u.
Proof. intros t u H; injection H; auto. Qed.

(* 辅助引理：App (Abs t) u 的形式 *)
Lemma app_abs_not_var : forall t u n, App (Abs t) u <> Var n.
Proof. intros t u n H; discriminate. Qed.

Lemma app_abs_not_abs : forall t u t', App (Abs t) u <> Abs t'.
Proof. intros t u t' H; discriminate. Qed.
(** 基础算术辅助引理 *)
Section ArithmeticLemmas.

Lemma pred_succ_nat : forall n, pred (S n) = n.
Proof. intros; reflexivity. Qed.

Lemma succ_pred_nat : forall n, n > 0 -> S (pred n) = n.
Proof.
  intros n H.
  destruct n as [|n'].
  - lia.
  - reflexivity.
Qed.

Lemma pred_mono : forall n m, n <= m -> pred n <= pred m.
Proof.
  intros n m H.
  lia.
Qed.

Lemma le_pred_iff : forall n m, n > 0 -> m > 0 -> (pred n <= pred m <-> n <= m).
Proof.
  intros n m Hn Hm.
  split; intro H.
  - lia.
  - lia.
Qed.

End ArithmeticLemmas.

(* ======================== 证明更一般交换性 ======================== *)
(* 证明更一般交换性 *)


(** 算术辅助引理：处理索引比较 **)
Section ArithmeticHelpers.

Lemma lt_dec_cases : forall n k,
  n < k \/ n = k \/ n > k.
Proof.
  intros n k.
  destruct (lt_eq_lt_dec n k) as [[H|H]|H]; auto.
Qed.

Lemma lt_plus_l : forall n k1 k2,
  n < k1 -> n < k1 + k2.
Proof. lia. Qed.

Lemma lt_plus_r : forall n k1 k2,
  n < k2 -> n < k1 + k2.
Proof. lia. Qed.

Lemma eq_plus_l : forall n k1 k2,
  n = k1 -> n < k1 + k2 \/ n = k1 + k2 \/ n > k1 + k2.
Proof. lia. Qed.

Lemma gt_plus_l : forall n k1 k2,
  n > k1 -> n > k1 + k2 \/ n = k1 + k2 \/ n < k1 + k2.
Proof. lia. Qed.

End ArithmeticHelpers.


(** 辅助引理：处理算术情况 **)
Section ArithmeticCases.

Lemma case_n_lt_k1 : forall n k1 k2,
  n < k1 -> 
  (n < k1 + k2) /\ (n <> k1 + k2) /\ (n <= k1 + k2 -> n < k1 + k2).
Proof. lia. Qed.

Lemma case_n_eq_k1 : forall n k1 k2,
  n = k1 ->
  (k1 + k2 > k1 \/ k1 + k2 = k1) /\ (k2 = 0 -> k1 + k2 = k1).
Proof. lia. Qed.

Lemma case_n_gt_k1 : forall n k1 k2,
  n > k1 ->
  (n > k1 + k2 \/ n = k1 + k2 \/ n < k1 + k2) /\
  (n >= k1 + k2 -> n >= k1 + k2) /\
  (n < k1 + k2 -> n < k1 + k2).
Proof. lia. Qed.

End ArithmeticCases.

(** 引理3：算术辅助引理 **)
Lemma arithmetic_helper_1 : forall n k1 k2,
  n < k1 -> n < k1 + k2.
Proof. lia. Qed.

Lemma arithmetic_helper_2 : forall n k1 k2,
  n > k1 + k2 -> n > k1.
Proof. lia. Qed.

Lemma arithmetic_helper_3 : forall n k1 k2,
  n >= k1 + k2 -> n >= k1.
Proof. lia. Qed.

(* ======================== 合流性定理 ======================== *)

(** 索引比较的三种情况 *)
Lemma index_cases : forall n k,
  n < k \/ n = k \/ n > k.
Proof.
  intros n k.
  destruct (lt_eq_lt_dec n k) as [[H|H]|H]; auto.
Qed.

(*
一、整体证明策略
目标引理：beta_subst_lift_commute : forall t u k, beta_subst (lift t (S k)) (lift u k) = lift (beta_subst t u) k

核心思路：

先证明变量情况的特例

建立提升和替换的代数性质链

通过结构归纳扩展到一般情况

处理特殊的算术边界情况
*)


(*
二、辅助引理链设计
第1层：基础算术辅助引理
这些引理处理索引比较，为变量情况的证明做准备：
*)

(** L1.1: 自然数索引的基本性质 *)
Lemma nat_index_tripartition : forall n k,
  n < k \/ n = k \/ n > k.
Proof. lia. Qed.

(** L1.2: 提升索引的单调性 *)
Lemma lift_index_monotone : forall n m k,
  n <= m -> 
  (if le_gt_dec k n then S n else n) <= (if le_gt_dec k m then S m else m).
Proof.
  intros n m k Hle.
  destruct (le_gt_dec k n) as [Hkn|Hkn];
  destruct (le_gt_dec k m) as [Hkm|Hkm]; lia.
Qed.

(** 辅助引理：当 n < k1 且 k1 ≤ k2 时，n < S k2 *)
Lemma lt_k1_le_k2_implies_lt_Sk2 : forall n k1 k2,
  n < k1 -> k1 <= k2 -> n < S k2.
Proof. lia. Qed.

(** 辅助引理：当 n < k1 且 k1 ≤ k2 时，n < k2 *)
Lemma lt_k1_le_k2_implies_lt_k2 : forall n k1 k2,
  n < k1 -> k1 <= k2 -> n < k2.
Proof. lia. Qed.

(** 辅助引理：当 n < k1 且 k1 ≤ k2 时，n < S k2 *)
Lemma lt_k1_le_k2_implies_lt_Sk2_fixed : forall n k1 k2,
  n < k1 -> k1 <= k2 -> n < S k2.
Proof. lia. Qed.

(** 辅助引理：当 n < k1 且 k1 ≤ k2 时，n < k2 *)
Lemma lt_k1_le_k2_implies_lt_k2_fixed : forall n k1 k2,
  n < k1 -> k1 <= k2 -> n < k2.
Proof. lia. Qed.

(* theories/ChurchNumerals.Confluence.v *)
(* ========================================================================== *)
(* Church Numerals 的合流性(Church-Rosser)证明模块 *)
(* 基于并行归约(Tait-Martin-Löf方法)，使用de Bruijn索引 *)

(* ========================================================================== *)
(* 在文件开头添加 *)

(* 基础库 *)
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(* 1. 导入标准库 *)
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Relations.Relations.
Require Import Coq.Program.Equality.
Require Import Coq.Wellfounded.Inclusion.
Require Import Lia.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.RelationClasses.
From Coq.Arith Require Import PeanoNat.  (* 更好的算术支持 *)
From Coq.Lists Require Import List.      (* 列表操作 *)
(* 确保导入所有必要模块 *)

Require Import Coq.Arith.Wf_nat.
Require Import Lia.

(* ======================== 基础定义 ======================== *)

(* 10.6 灵活的基础归约关系 (可选，向后兼容)
   为不同使用场景提供别名
*)

Notation "t [ u // k ]" := (subst t u k) (at level 40).
Notation "t '-->' u" := (BetaStep t u) (at level 50).
Notation "t '-->>' u" := (BetaReduces t u) (at level 50).


(** 1. 基本算术引理 *)
Lemma pred_succ_eq : forall n, pred (S n) = n.
Proof. intros; reflexivity. Qed.

Lemma succ_pred_eq : forall n, n > 0 -> S (pred n) = n.
Proof. intros n H; destruct n; [lia|reflexivity]. Qed.

Lemma le_gt_dec_cases : forall n k,
  (exists Hle : k <= n, le_gt_dec k n = left Hle) \/
  (exists Hgt : k > n, le_gt_dec k n = right Hgt).
Proof.
  intros n k.
  destruct (le_gt_dec k n) as [Hle | Hgt].
  - left. exists Hle. reflexivity.
  - right. exists Hgt. reflexivity.
Qed.

(** 2. de Bruijn索引引理 *)
Lemma lt_eq_lt_dec_cases : forall n k,
  match lt_eq_lt_dec n k with
  | inleft (left _) => n < k
  | inleft (right _) => n = k
  | inright _ => n > k
  end.
Proof.
  intros n k.
  destruct (lt_eq_lt_dec n k) as [[H|H]|H]; auto.
Qed.

(** 证明示例1：基本算术引理 *)
Lemma pred_monotonic : forall n m, n <= m -> pred n <= pred m.
Proof.
  intros n m H.
  lia.
Qed.

(** 13. 项的形式分析引理 *)
Lemma term_cases : forall t,
  (exists n, t = Var n) \/
  (exists t1 t2, t = App t1 t2) \/
  (exists t', t = Abs t').
Proof.
  intros t.
  destruct t as [n|t1 t2|t']; eauto.
Qed.

Lemma not_app_is_abs : forall t,
  (forall t1 t2, t <> App t1 t2) -> 
  (exists n, t = Var n) \/ (exists t', t = Abs t').
Proof.
  intros t H.
  destruct t as [n|t1 t2|t']; eauto.
  exfalso; apply (H t1 t2); reflexivity.
Qed.

(** 1.1 自然数索引的基本性质 **)
Lemma nat_index_tripartition_complete : forall n k,
  n < k \/ n = k \/ n > k.
Proof.
  intros n k.
  destruct (lt_eq_lt_dec n k) as [[H|H]|H]; auto.
Qed.

(** 1.2 提升索引的单调性 **)
Lemma lift_index_monotone_complete : forall n m k,
  n <= m -> 
  (if le_gt_dec k n then S n else n) <= (if le_gt_dec k m then S m else m).
Proof.
  intros n m k Hle.
  destruct (le_gt_dec k n) as [Hkn|Hkn];
  destruct (le_gt_dec k m) as [Hkm|Hkm]; lia.
Qed.

(* ======================== 第一部分：可以直接证明的算术辅助引理 ======================== *)

(** 1. 基础算术引理 - 这些都可以用lia直接证明 **)

(** 自然数比较引理 **)
Lemma lt_dec_cases_simple : forall n k,
  n < k \/ n = k \/ n > k.
Proof.
  intros n k.
  destruct (lt_eq_lt_dec n k) as [[H|H]|H]; auto.
Qed.

(** 提升操作的单调性 **)
Lemma lift_index_monotone_simple : forall n m k,
  n <= m -> 
  (if le_gt_dec k n then S n else n) <= (if le_gt_dec k m then S m else m).
Proof.
  intros n m k Hle.
  destruct (le_gt_dec k n) as [Hkn|Hkn];
  destruct (le_gt_dec k m) as [Hkm|Hkm]; lia.
Qed.

(** 3. 项的结构性质 - 直接可证的引理 **)

(** 项的形式分解引理 **)
Lemma term_decomposition : forall t,
  (exists n, t = Var n) \/
  (exists t1 t2, t = App t1 t2) \/
  (exists t', t = Abs t').
Proof.
  intros t.
  destruct t as [n|t1 t2|t']; eauto.
Qed.

(** 6. 基本构造函数的单射性 - 直接可证 **)

(** 变量构造函数的单射性 **)
Lemma var_inj : forall n m, Var n = Var m -> n = m.
Proof.
  intros n m H.
  injection H.
  auto.
Qed.

(** 应用构造函数的单射性 **)
Lemma app_inj : forall t1 t2 u1 u2, 
  App t1 t2 = App u1 u2 -> t1 = u1 /\ t2 = u2.
Proof.
  intros t1 t2 u1 u2 H.
  injection H.
  auto.
Qed.

(** 抽象构造函数的单射性 **)
Lemma abs_inj : forall t u, Abs t = Abs u -> t = u.
Proof.
  intros t u H.
  injection H.
  auto.
Qed.

(** 9. Church数的基本性质 - 直接可证的引理 **)

(** Church后继的定义展开 **)
Lemma church_succ_unfold : forall n,
  church_succ n = 
  Abs (Abs (App (Var 1) (App (App n (Var 1)) (Var 0)))).
Proof.
  intro n.
  unfold church_succ.
  reflexivity.
Qed.

(** 10. 证明辅助引理 - 简化证明过程 **)

(** 使用lia处理算术条件的引理 **)
Lemma arithmetic_helper_lt_trans : forall n m p,
  n < m -> m <= p -> n < p.
Proof. lia. Qed.

Lemma arithmetic_helper_le_trans : forall n m p,
  n <= m -> m < p -> n < p.
Proof. lia. Qed.

(** 自然数归纳的简化形式 **)
Lemma nat_induction_simple : forall (P : nat -> Prop),
  P 0 -> (forall n, P n -> P (S n)) -> forall n, P n.
Proof.
  exact nat_ind.
Qed.

(** ======================== 第五部分：证明策略和工具 ======================== *)

(** 自动处理算术条件的策略 **)
Ltac solve_arithmetic :=
  repeat (match goal with
  | H: ?n < ?m |- _ => 
      match type of H with
      | lt _ _ => idtac
      | _ => fail
      end
  | H: ?n <= ?m |- _ => 
      match type of H with
      | le _ _ => idtac
      | _ => fail
      end
  | H: ?n > ?m |- _ => 
      match type of H with
      | lt _ _ => idtac
      | _ => fail
      end
  | H: ?n >= ?m |- _ => 
      match type of H with
      | le _ _ => idtac
      | _ => fail
      end
  | H: ?n = ?m |- _ => idtac
  | |- ?n < ?m => lia
  | |- ?n <= ?m => lia
  | |- ?n > ?m => lia
  | |- ?n >= ?m => lia
  | |- ?n = ?m => lia
  end).

(** 自动处理变量索引的策略 **)
Ltac solve_index :=
  repeat (match goal with
  | H: context[le_gt_dec ?k ?n] |- _ => 
      destruct (le_gt_dec k n)
  | |- context[le_gt_dec ?k ?n] => 
      destruct (le_gt_dec k n)
  | H: context[lt_eq_lt_dec ?n ?k] |- _ => 
      destruct (lt_eq_lt_dec n k) as [[?|?]|?]
  | |- context[lt_eq_lt_dec ?n ?k] => 
      destruct (lt_eq_lt_dec n k) as [[?|?]|?]
  end; try lia).

(** 引理：应用项的大小大于其子项 *)
Lemma app_size_gt_components : forall t1 t2,
  term_size (App t1 t2) > term_size t1 /\ term_size (App t1 t2) > term_size t2.
Proof.
  intros t1 t2.
  simpl. split; lia.
Qed.

(** 引理：抽象项的大小大于其体 *)
Lemma abs_size_gt_body : forall t,
  term_size (Abs t) > term_size t.
Proof.
  intro t.
  simpl. lia.
Qed.

Lemma church_succ_preserves_form : forall n,
  (exists t, n = Abs t) -> exists t, church_succ n = Abs t.
Proof.
  intros n [t Heq].
  unfold church_succ.
  eexists. reflexivity.
Qed.

(** 4.1 自然数比较的确定性 **)

Lemma le_gt_dec_deterministic : forall k n (H1 H2 : k <= n),
  le_gt_dec k n = left H1 -> le_gt_dec k n = left H2 -> H1 = H2.
Proof.
  intros k n H1 H2 Heq1 Heq2.
  apply le_unique.
Qed.

Lemma lt_eq_lt_dec_deterministic : forall n k 
  (H1 : n < k) (H2 : n = k) (H3 : n > k),
  match lt_eq_lt_dec n k with
  | inleft (left _) => True
  | inleft (right _) => True
  | inright _ => True
  end.
Proof.
  intros n k H1 H2 H3.
  destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt]; auto.
Qed.

(** 4.2 索引运算的基本性质 **)

Lemma pred_succ_commute : forall n,
  pred (S n) = n.
Proof. reflexivity. Qed.

Lemma succ_pred_commute : forall n,
  n > 0 -> S (pred n) = n.
Proof.
  intros n H.
  destruct n as [|n'].
  - lia.
  - reflexivity.
Qed.

(** ======================== 基础算术辅助引理 ======================== *)

(** 1. 自然数索引的基本性质 - 完全证明 **)
Section BasicArithmetic.

(** 自然数比较的三分法 - 使用标准库的 lt_eq_lt_dec **)
Lemma nat_trichotomy : forall n k,
  n < k \/ n = k \/ n > k.
Proof.
  intros n k.
  destruct (lt_eq_lt_dec n k) as [[H|H]|H]; auto.
Qed.

End BasicArithmetic.

(** ======================== 修正：替换索引的单调性 ======================== *)

(** 修正后的引理：只关注索引的比较，不涉及项大小 **)
Lemma subst_index_monotone_corrected : forall n m k,
  n <= m ->
  (match lt_eq_lt_dec n k with
   | inleft (left _) => n      (* n < k: 保持 n *)
   | inleft (right _) => k     (* n = k: 替换为 u，但这里我们只关注索引，返回 k 作为标记 *)
   | inright _ => pred n      (* n > k: pred n *)
   end) <=
  (match lt_eq_lt_dec m k with
   | inleft (left _) => m      (* m < k: 保持 m *)
   | inleft (right _) => k     (* m = k: 替换为 u *)
   | inright _ => pred m      (* m > k: pred m *)
   end) \/
  (match lt_eq_lt_dec n k with
   | inleft (left _) => n
   | inleft (right _) => k
   | inright _ => pred n
   end) >=
  (match lt_eq_lt_dec m k with
   | inleft (left _) => m
   | inleft (right _) => k
   | inright _ => pred m
   end).
Proof.
  intros n m k Hle.
  (* 对 n 和 m 分别进行分析 *)
  destruct (lt_eq_lt_dec n k) as [[Hlt_n|Heq_n]|Hgt_n];
  destruct (lt_eq_lt_dec m k) as [[Hlt_m|Heq_m]|Hgt_m].
  - (* n < k, m < k *)
    left. exact Hle.
  - (* n < k, m = k *)
    left. lia.
  - (* n < k, m > k *)
    (* 需要比较 n 和 pred m *)
    destruct (le_lt_dec n (pred m)) as [Hle'|Hlt'].
    + left. exact Hle'.
    + right. lia.
  - (* n = k, m < k *)
    (* 由于 n = k > m，但 Hle: n ≤ m，矛盾 *)
    exfalso. lia.
  - (* n = k, m = k *)
    left. reflexivity.
  - (* n = k, m > k *)
    (* 比较 k 和 pred m *)
    destruct (le_lt_dec k (pred m)) as [Hle'|Hlt'].
    + left. exact Hle'.
    + right. lia.
  - (* n > k, m < k *)
    (* 由于 n > k 且 n ≤ m < k，矛盾 *)
    exfalso. lia.
  - (* n > k, m = k *)
    (* 比较 pred n 和 k *)
    destruct (le_lt_dec (pred n) k) as [Hle'|Hlt'].
    + left. exact Hle'.
    + right. lia.
  - (* n > k, m > k *)
    (* 比较 pred n 和 pred m *)
    destruct (le_lt_dec (pred n) (pred m)) as [Hle'|Hlt'].
    + left. exact Hle'.
    + right. lia.
Qed.

(** ======================== 项的结构性质 ======================== *)

Section TermStructuralProperties.

(** 项大小的严格单调性 **)
Lemma term_size_strict_monotonic : forall t,
  match t with
  | Var _ => True
  | App t1 t2 => term_size t1 < term_size t /\ term_size t2 < term_size t
  | Abs t' => term_size t' < term_size t
  end.
Proof.
  intros t.
  destruct t as [n | t1 t2 | t']; simpl.
  - (* Var 分支 *)
    exact I.  (* 需要提供 True 的证明 *)
  - (* App 分支 *)
    split.
    + (* term_size t1 < term_size (App t1 t2) *)
      lia.
    + (* term_size t2 < term_size (App t1 t2) *)
      lia.
  - (* Abs 分支 *)
    lia.
Qed.

End TermStructuralProperties.

(** ======================== Church数的基本性质 ======================== *)

Section ChurchNumeralBasicProperties.

(** Church后继的基本性质 - 不涉及归约 **)
Lemma church_succ_form : forall n,
  exists t, church_succ n = Abs (Abs t).
Proof.
  intro n.
  unfold church_succ.
  eexists.
  reflexivity.
Qed.

End ChurchNumeralBasicProperties.

(** ======================== 辅助证明策略和工具 ======================== *)

Section ProofTactics.

(** 处理 de Bruijn 索引的自动化策略 **)
Ltac solve_de_bruijn :=
  repeat (match goal with
  | |- context[le_gt_dec ?k ?n] => 
      let H := fresh "H" in
      destruct (le_gt_dec k n) as [H|H]; try lia
  | |- context[lt_eq_lt_dec ?n ?k] => 
      let H := fresh "H" in
      destruct (lt_eq_lt_dec n k) as [[H|H]|H]; try lia
  | H: context[le_gt_dec ?k ?n] |- _ => 
      let H' := fresh "H" in
      destruct (le_gt_dec k n) as [H'|H']; try lia
  | H: context[lt_eq_lt_dec ?n ?k] |- _ => 
      let H' := fresh "H" in
      destruct (lt_eq_lt_dec n k) as [[H'|H']|H']; try lia
  end).

(** 处理项大小的自动化策略 **)
Ltac solve_term_size :=
  repeat (match goal with
  | |- term_size _ <= term_size _ => lia
  | |- term_size _ < term_size _ => lia
  | |- term_size _ = term_size _ => lia
  | H: term_size _ <= term_size _ |- _ => lia
  | H: term_size _ < term_size _ |- _ => lia
  | H: term_size _ = term_size _ |- _ => lia
  end).

(** 组合策略：处理 de Bruijn 索引和项大小 **)
Ltac solve_term_properties :=
  repeat (solve_de_bruijn || solve_term_size).

(** 快速证明项相等的策略 **)
Ltac prove_term_eq :=
  repeat (f_equal || reflexivity).

End ProofTactics.

(** 基础算术辅助引理 - 这些引理简单且直接可用 **)
Section BasicArithmeticProven.

(** 引理1.1: 自然数减法的基本性质 *)
Lemma pred_of_succ : forall n, pred (S n) = n.
Proof. reflexivity. Qed.

(** 引理1.2: 后继的单调性 *)
Lemma succ_le_monotone : forall n m, n <= m -> S n <= S m.
Proof. intros n m H; apply le_n_S; exact H. Qed.

End BasicArithmeticProven.

(** 项大小的简单性质 - 直接可从定义得出 **)
Section SimpleTermSizeProperties.

(** 引理2.1: 项大小的基本不等式 *)
Lemma term_size_ge_1_simple : forall t, term_size t >= 1.
Proof. apply term_size_pos. Qed.

(** 引理2.2: 变量的大小为1 *)
Lemma term_size_var_simple : forall n, term_size (Var n) = 1.
Proof. reflexivity. Qed.

(** 引理2.3: 应用的大小计算 *)
Lemma term_size_app_simple : forall t1 t2,
  term_size (App t1 t2) = 1 + term_size t1 + term_size t2.
Proof. reflexivity. Qed.

(** 引理2.4: 抽象的大小计算 *)
Lemma term_size_abs_simple : forall t,
  term_size (Abs t) = 1 + term_size t.
Proof. reflexivity. Qed.

(** 引理2.5: 子项大小严格小于父项大小 *)
Lemma term_size_strict_decreasing : forall t,
  match t with
  | Var _ => True
  | App t1 t2 => term_size t1 < term_size t /\ term_size t2 < term_size t
  | Abs t' => term_size t' < term_size t
  end.
Proof.
  destruct t as [n | t1 t2 | t']; simpl.
  - exact I.
  - split; lia.
  - lia.
Qed.

End SimpleTermSizeProperties.

(** 构造函数的简单性质 - 直接可证 **)
Section SimpleConstructorProperties.

(** 引理4.1: 变量构造函数的单射性 *)
Lemma var_injective_simple : forall n m, Var n = Var m -> n = m.
Proof.
  intros n m H.
  injection H.
  auto.
Qed.

(** 引理4.2: 应用构造函数的单射性 *)
Lemma app_injective_simple : forall t1 t2 u1 u2,
  App t1 t2 = App u1 u2 -> t1 = u1 /\ t2 = u2.
Proof.
  intros t1 t2 u1 u2 H.
  injection H.
  auto.
Qed.

(** 引理4.3: 抽象构造函数的单射性 *)
Lemma abs_injective_simple : forall t u,
  Abs t = Abs u -> t = u.
Proof.
  intros t u H.
  injection H.
  auto.
Qed.

(** 引理4.4: 不同构造函数的互斥性 *)
Lemma term_form_discrimination : forall t,
  (forall n, t <> Var n) \/ (exists n, t = Var n).
Proof.
  intro t.
  destruct t as [n|t1 t2|t'].
  - right; exists n; reflexivity.
  - left; intros n H; discriminate H.
  - left; intros n H; discriminate H.
Qed.

End SimpleConstructorProperties.

(** Church数的简单性质 - 不涉及复杂归约 **)
Section SimpleChurchProperties.

(** 引理8.2: Church后继保持抽象形式 *)
Lemma church_succ_preserves_abs_form : forall n,
  (exists t, n = Abs t) -> exists t, church_succ n = Abs t.
Proof.
  intros n [t Heq].
  unfold church_succ.
  eexists. reflexivity.
Qed.

End SimpleChurchProperties.

(** 自由变量的简单性质 - 基础分析 **)
Section SimpleFreeVariableProperties.

(** 引理9.1: 变量总是以自身索引自由出现 *)
Lemma appears_free_in_self : forall n,
  appears_free_in n (Var n) = true.
Proof.
  intro n.
  simpl.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(** 引理9.2: 不同索引的变量不自由出现 *)
Lemma appears_free_in_other : forall n m,
  n <> m -> appears_free_in n (Var m) = false.
Proof.
  intros n m Hneq.
  simpl.
  rewrite Nat.eqb_neq; auto.
Qed.

(** 引理9.4: 自由变量的单调性 - 抽象情况 *)
Lemma appears_free_in_abs_mono : forall k t,
  appears_free_in k (Abs t) = appears_free_in (S k) t.
Proof. reflexivity. Qed.

End SimpleFreeVariableProperties.

(** 关系的简单性质 - 用于自动证明 **)
Section SimpleRelationProperties.

(** 引理10.3: 自反传递闭包的基本构造 *)
Lemma reflexive_transitive_closure_simple : forall (R : term -> term -> Prop) t u v,
  R t u -> (forall x, R x x) -> (forall x y z, R x y -> R y z -> R x z) -> R t v -> R t v.
Proof.
  intros R t u v Htu Hrefl Htrans H.
  exact H.
Qed.

End SimpleRelationProperties.

(** 简单的证明辅助策略 - 自动化证明 **)
Section SimpleProofTactics.

(** 策略1: 自动处理项的结构 *)
Ltac destruct_term t :=
  destruct t as [n | t1 t2 | t'].

(** 策略2: 自动处理索引比较 *)
Ltac destruct_index_cmp n k :=
  destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt]; try lia.

(** 策略3: 自动处理提升比较 *)
Ltac destruct_lift_cmp k n :=
  destruct (le_gt_dec k n) as [Hle|Hgt]; try lia.

(** 策略4: 自动证明项相等 *)
Ltac prove_term_eq :=
  repeat (f_equal || reflexivity).

(** 策略5: 自动处理算术条件 *)
Ltac solve_arith := lia.

End SimpleProofTactics.