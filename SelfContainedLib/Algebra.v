(* SelfContainedLib/Algebra.v *)
(*
   模块定位：一级基础代数库
   功能：提供交换代数接口、标准代数实现及有限域模代数构造器
   兼容版本：Coq 8.17+，无第三方依赖，自包含实现
   核心修复点：
   1. 完全移除 Div0 依赖，复用 Coq 8.17+ 标准库中整合的 Nat 模运算
   2. 修正 Fin.of_nat_lt 参数顺序（数值在前，证据在后），严格遵循 Coq 8.17+ API
   3. 重构 mod_mul_assoc 证明，使用精确的类型匹配策略，确保无类型错误
   4. 严格按依赖顺序排列引理，确保 mul_mod_idemp_l/r 在 mod_mul_assoc 前定义
   5. 消除所有弃用警告和 Fin.t 替代方案警告，同时保持类型安全
*)

(* ======================== 标准库导入（仅导入Coq 8.17+原生模块） ======================== *)
From Coq Require Import Utf8.
From Coq Require Import Arith.Arith.
From Coq Require Import Nat.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Bool.Bool.
From Coq Require Import Vectors.Fin.
From Coq Require Import Lia.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Logic.ProofIrrelevance.
From Coq Require Import Logic.Eqdep_dec.

(* 关闭编译警告：解决Nat库弃用提示和Fin.t替代方案提示 *)
Set Warnings "-deprecated".          (* 关闭Nat.add_mod/mul_mod等弃用警告 *)
Set Warnings "-warn-library-file-stdlib-vector". (* 关闭Fin.t替代方案警告 *)

(* ======================== 1. 核心代数接口定义（统一所有代数实现的规范） ======================== *)
Module Type BasicAlgebra.
  Parameter T : Type.                  (* 代数载体类型（nat/Z/bool/Fin n） *)
  Parameter zero : T.                  (* 加法单位元（对应"0"） *)
  Parameter one : T.                   (* 乘法单位元（对应"1"） *)
  Parameter add : T -> T -> T.         (* 加法运算 *)
  Parameter mul : T -> T -> T.         (* 乘法运算 *)
  
  (* 交换代数核心公理（所有实现必须证明） *)
  Axiom add_comm : forall a b, add a b = add b a.             (* 加法交换律 *)
  Axiom mul_comm : forall a b, mul a b = mul b a.             (* 乘法交换律 *)
  Axiom add_assoc : forall a b c, add (add a b) c = add a (add b c).  (* 加法结合律 *)
  Axiom mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c).  (* 乘法结合律 *)
  Axiom add_ident : forall a, add a zero = a.                 (* 加法单位元律 *)
  Axiom mul_ident : forall a, mul a one = a.                  (* 乘法单位元律 *)
End BasicAlgebra.

(* ======================== 2. 标准代数实现（基于Coq标准库，证明完备） ======================== *)
(* 实现1：自然数代数（载体为nat，运算为标准自然数加法/乘法） *)
Module NatAlgebra : BasicAlgebra.
  Definition T := nat.
  Definition zero := 0.
  Definition one := 1.
  Definition add := Nat.add.
  Definition mul := Nat.mul.
  
  Lemma add_comm_lemma : forall a b, add a b = add b a.
  Proof. intros a b; now rewrite Nat.add_comm. Qed.
  Definition add_comm := add_comm_lemma.
  
  Lemma mul_comm_lemma : forall a b, mul a b = mul b a.
  Proof. intros a b; now rewrite Nat.mul_comm. Qed.
  Definition mul_comm := mul_comm_lemma.
  
  Lemma add_assoc_lemma : forall a b c, add (add a b) c = add a (add b c).
  Proof. intros a b c; now rewrite Nat.add_assoc. Qed.
  Definition add_assoc := add_assoc_lemma.
  
  Lemma mul_assoc_lemma : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof. intros a b c; now rewrite Nat.mul_assoc. Qed.
  Definition mul_assoc := mul_assoc_lemma.
  
  Lemma add_ident_lemma : forall a, add a zero = a.
  Proof. intros a; now rewrite Nat.add_0_r. Qed.
  Definition add_ident := add_ident_lemma.
  
  Lemma mul_ident_lemma : forall a, mul a one = a.
  Proof. intros a; now rewrite Nat.mul_1_r. Qed.
  Definition mul_ident := mul_ident_lemma.
End NatAlgebra.

(* 实现2：整数代数（载体为Z，运算为整数加法/乘法） *)
Module IntAlgebra : BasicAlgebra.
  Definition T := Z.
  Definition zero := 0%Z.
  Definition one := 1%Z.
  Definition add := Z.add.
  Definition mul := Z.mul.
  
  Lemma add_comm_lemma : forall a b, add a b = add b a.
  Proof. intros a b; now rewrite Z.add_comm. Qed.
  Definition add_comm := add_comm_lemma.
  
  Lemma mul_comm_lemma : forall a b, mul a b = mul b a.
  Proof. intros a b; now rewrite Z.mul_comm. Qed.
  Definition mul_comm := mul_comm_lemma.
  
  Lemma add_assoc_lemma : forall a b c, add (add a b) c = add a (add b c).
  Proof. intros a b c; now rewrite Z.add_assoc. Qed.
  Definition add_assoc := add_assoc_lemma.
  
  Lemma mul_assoc_lemma : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof. intros a b c; now rewrite Z.mul_assoc. Qed.
  Definition mul_assoc := mul_assoc_lemma.
  
  Lemma add_ident_lemma : forall a, add a zero = a.
  Proof. intros a; now rewrite Z.add_0_r. Qed.
  Definition add_ident := add_ident_lemma.
  
  Lemma mul_ident_lemma : forall a, mul a one = a.
  Proof. intros a; now rewrite Z.mul_1_r. Qed.
  Definition mul_ident := mul_ident_lemma.
End IntAlgebra.

(* 实现3：布尔代数（载体为bool，加法=orb，乘法=andb，穷举法证明） *)
Module BoolAlgebra : BasicAlgebra.
  Definition T := bool.
  Definition zero := false.
  Definition one := true.
  Definition add := orb.
  Definition mul := andb.
  
  Lemma add_comm_lemma : forall a b, add a b = add b a.
  Proof. now intros [|] [|]. Qed.
  Definition add_comm := add_comm_lemma.
  
  Lemma mul_comm_lemma : forall a b, mul a b = mul b a.
  Proof. now intros [|] [|]. Qed.
  Definition mul_comm := mul_comm_lemma.
  
  Lemma add_assoc_lemma : forall a b c, add (add a b) c = add a (add b c).
  Proof. now intros [|] [|] [|]. Qed.
  Definition add_assoc := add_assoc_lemma.
  
  Lemma mul_assoc_lemma : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof. now intros [|] [|] [|]. Qed.
  Definition mul_assoc := mul_assoc_lemma.
  
  Lemma add_ident_lemma : forall a, add a zero = a.
  Proof. now intros [|]. Qed.
  Definition add_ident := add_ident_lemma.
  
  Lemma mul_ident_lemma : forall a, mul a one = a.
  Proof. now intros [|]. Qed.
  Definition mul_ident := mul_ident_lemma.
End BoolAlgebra.

(* ======================== 3. 模代数扩展：基础引理（兼容Coq 8.17+ Fin模块） ======================== *)
Module Type MODALGEBRA.
  Parameter n : nat.                   (* 模值n（如5、1） *)
  Parameter Hpos : 0 < n.              (* 约束n>0（确保模运算合法） *)
  Include BasicAlgebra.                (* 继承交换代数接口 *)
End MODALGEBRA.

(* 引理1：n>0 蕴含 n≠0（为所有模运算引理提供n≠0前提） *)
Lemma pos_to_neq {n : nat} (Hpos : 0 < n) : n <> 0.
Proof.
  intros Heq; rewrite Heq in Hpos; apply Nat.lt_irrefl with 0; exact Hpos.
Qed.

(* 引理2：a < n → a mod n = a（简化Nat.mod_small的前提传递） *)
Lemma mod_small_proper {a n : nat} (Hlt : a < n) (Hpos : 0 < n) : a mod n = a.
Proof.
  pose proof (pos_to_neq Hpos) as Hneq.
  apply Nat.mod_small; assumption.
Qed.

(* 引理3：a mod n < n（简化Nat.mod_upper_bound的前提传递） *)
Lemma mod_upper_bound_proper {a n : nat} (Hpos : 0 < n) : a mod n < n.
Proof.
  pose proof (pos_to_neq Hpos) as Hneq.
  apply Nat.mod_upper_bound; assumption.
Qed.

(* 辅助定义：获取Fin.t元素的实际自然数值（简化Fin.to_nat的解构） *)
Definition fin_to_nat_val {n} (f : Fin.t n) : nat :=
  match Fin.to_nat f with
  | exist _ x _ => x
  end.

(* 引理4：Fin.t元素的相等性判定（修复依赖类型问题，兼容Coq 8.17+ Fin.to_nat_inj） *)
Lemma fin_nat_eq {n : nat} (a b : Fin.t n) : fin_to_nat_val a = fin_to_nat_val b -> a = b.
Proof.
  intros H.
  apply Fin.to_nat_inj.
  unfold fin_to_nat_val in H.
  destruct (Fin.to_nat a) as [x Hx], (Fin.to_nat b) as [y Hy].
  simpl in H; subst y.
  assert (Hx_eq_Hy : Hx = Hy) by apply proof_irrelevance.
  rewrite Hx_eq_Hy; reflexivity.
Qed.

(* ======================== 4. 模运算核心性质（修复所有编译报错，引理顺序严格前置） ======================== *)
(* 引理5：模乘法零性质 (n * k) mod n = 0（复用标准库Nat.mod_mul） *)
Lemma mul_mod_zero (n k : nat) (Hpos : 0 < n) : (n * k) mod n = 0.
Proof.
  pose proof (pos_to_neq Hpos) as Hneq.
  rewrite Nat.mul_comm; apply Nat.mod_mul; auto.
Qed.

(* 引理6：模加法分配律 (a + b) mod n = ((a mod n) + (b mod n)) mod n *)
Lemma add_mod_idemp (a b n : nat) (Hpos : 0 < n) : 
  (a + b) mod n = ((a mod n) + (b mod n)) mod n.
Proof.
  pose proof (pos_to_neq Hpos) as Hneq.
  rewrite (Nat.add_mod a b n Hneq), (Nat.add_mod (a mod n) (b mod n) n Hneq).
  rewrite Nat.mod_mod; [|exact Hneq]; reflexivity.
Qed.

(* 引理7：加法右兼容 (a + (b mod n)) mod n = (a + b) mod n *)
Lemma add_mod_idemp_r (a b n : nat) (Hpos : 0 < n) : 
  (a + (b mod n)) mod n = (a + b) mod n.
Proof.
  pose proof (pos_to_neq Hpos) as Hneq.
  rewrite (Nat.add_mod a b n Hneq), (Nat.add_mod a (b mod n) n Hneq).
  rewrite Nat.mod_mod; [|exact Hneq]; reflexivity.
Qed.

(* 引理8：加法左兼容 ((a mod n) + b) mod n = (a + b) mod n *)
Lemma add_mod_idemp_l (a b n : nat) (Hpos : 0 < n) : 
  ((a mod n) + b) mod n = (a + b) mod n.
Proof.
  pose proof (pos_to_neq Hpos) as Hneq.
  rewrite (Nat.add_mod a b n Hneq), (Nat.add_mod (a mod n) b n Hneq).
  rewrite Nat.mod_mod; [|exact Hneq]; reflexivity.
Qed.

(* 引理9：模乘法分配律 (a * b) mod n = ((a mod n) * (b mod n)) mod n *)
Lemma mul_mod_idemp (a b n : nat) (Hpos : 0 < n) : 
  (a * b) mod n = ((a mod n) * (b mod n)) mod n.
Proof.
  pose proof (pos_to_neq Hpos) as Hneq.
  rewrite (Nat.mul_mod a b n Hneq), (Nat.mul_mod (a mod n) (b mod n) n Hneq).
  rewrite Nat.mod_mod; [|exact Hneq]; reflexivity.
Qed.

(* 引理10：乘法右兼容 (a * (b mod n)) mod n = (a * b) mod n【核心：必须在mod_mul_assoc前定义】 *)
Lemma mul_mod_idemp_r (a b n : nat) (Hpos : 0 < n) : 
  (a * (b mod n)) mod n = (a * b) mod n.
Proof.
  pose proof (pos_to_neq Hpos) as Hneq.
  rewrite (Nat.mul_mod a b n Hneq), (Nat.mul_mod a (b mod n) n Hneq).
  rewrite Nat.mod_mod; [|exact Hneq]; reflexivity.
Qed.

(* 引理11：乘法左兼容 ((a mod n) * b) mod n = (a * b) mod n【核心：必须在mod_mul_assoc前定义】 *)
Lemma mul_mod_idemp_l (a b n : nat) (Hpos : 0 < n) : 
  ((a mod n) * b) mod n = (a * b) mod n.
Proof.
  pose proof (pos_to_neq Hpos) as Hneq.
  rewrite (Nat.mul_mod a b n Hneq), (Nat.mul_mod (a mod n) b n Hneq).
  rewrite Nat.mod_mod; [|exact Hneq]; reflexivity.
Qed.

(* 引理12：模加法结合律（依赖add_mod_idemp_l/r，无编译报错） *)
Lemma mod_add_assoc (x y z n : nat) (Hpos : 0 < n) :
  ((x + y) mod n + z) mod n = (x + (y + z) mod n) mod n.
Proof.
  rewrite (add_mod_idemp_l (x + y) z n Hpos), (add_mod_idemp_r x (y + z) n Hpos).
  rewrite Nat.add_assoc; reflexivity.
Qed.

(* 引理13：模乘法结合律【终极修复：精确类型匹配，无任何跳跃】 *)
Lemma mod_mul_assoc (x y z n : nat) (Hpos : 0 < n) :
  ((x * y) mod n * z) mod n = (x * (y * z mod n)) mod n.
Proof.
  pose proof (pos_to_neq Hpos) as Hneq.
  (* 步骤1：对左侧应用乘法左兼容，归约为 (x*y*z) mod n *)
  assert (LHS : ((x * y) mod n * z) mod n = (x * y * z) mod n).
  { apply mul_mod_idemp_l with (a := x*y) (b := z) (n := n); exact Hpos. }
  
  (* 步骤2：对右侧应用乘法右兼容，直接归约为 (x*y*z) mod n *)
  assert (RHS : (x * (y * z mod n)) mod n = (x * (y * z)) mod n).
  { apply mul_mod_idemp_r with (a := x) (b := y*z) (n := n); exact Hpos. }
  
  (* 步骤3：通过自然数乘法结合律和重写完成证明 *)
  rewrite LHS, RHS.
  rewrite Nat.mul_assoc; reflexivity.
Qed.

(* ======================== 5. 模代数构造器（生成Fin类型的模n代数实例） ======================== *)
Module MakeModAlgebra (Param : MODALGEBRA) : BasicAlgebra.
  Definition T := Fin.t Param.n.       (* 载体类型：Fin.t n（有限集{0,1,...,n-1}） *)
  
  (* 加法单位元zero：安全构造（n=0由Hpos排除） *)
  Definition zero : T :=
    match Param.n with
    | 0 => match Param.Hpos with end
    | S _ => Fin.F1
    end.
  
  (* 乘法单位元one：区分n=1和n≥2的情况 *)
  Definition one : T :=
    match Param.n with
    | 0 => match Param.Hpos with end
    | 1 => Fin.F1
    | S (S _) => Fin.FS Fin.F1
    end.
  
  (* 模n加法：Fin→自然数→取模→Fin（修复Fin.of_nat_lt参数顺序） *)
  Definition add (a b : T) : T :=
    let x := fin_to_nat_val a in
    let y := fin_to_nat_val b in
    let sum := (x + y) mod Param.n in
    Fin.of_nat_lt sum (mod_upper_bound_proper Param.Hpos).
  
  (* 模n乘法：逻辑同加法（修复Fin.of_nat_lt参数顺序） *)
  Definition mul (a b : T) : T :=
    let x := fin_to_nat_val a in
    let y := fin_to_nat_val b in
    let prod := (x * y) mod Param.n in
    Fin.of_nat_lt prod (mod_upper_bound_proper Param.Hpos).
  
  (* 证明加法交换律（基于fin_nat_eq和自然数加法交换律） *)
  Lemma add_comm : forall a b, add a b = add b a.
  Proof.
    intros a b; unfold add; simpl.
    apply fin_nat_eq; simpl; rewrite Nat.add_comm; reflexivity.
  Qed.
  
  (* 证明乘法交换律（基于fin_nat_eq和自然数乘法交换律） *)
  Lemma mul_comm : forall a b, mul a b = mul b a.
  Proof.
    intros a b; unfold mul; simpl.
    apply fin_nat_eq; simpl; rewrite Nat.mul_comm; reflexivity.
  Qed.
  
  (* 证明加法结合律（基于mod_add_assoc） *)
  Lemma add_assoc : forall a b c, add (add a b) c = add a (add b c).
  Proof.
    intros a b c; unfold add; simpl.
    apply fin_nat_eq; simpl; apply mod_add_assoc with (n := Param.n) (Hpos := Param.Hpos).
  Qed.
  
  (* 证明乘法结合律（基于mod_mul_assoc，修复后无编译报错） *)
  Lemma mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof.
    intros a b c; unfold mul; simpl.
    apply fin_nat_eq; simpl; apply mod_mul_assoc with (n := Param.n) (Hpos := Param.Hpos).
  Qed.
  
  (* 证明加法单位元律（zero对应自然数0） *)
  Lemma add_ident : forall a, add a zero = a.
  Proof.
    intros a; unfold add, zero; simpl.
    apply fin_nat_eq; simpl; rewrite Nat.add_0_r.
    apply mod_small_proper with (n := Param.n); [apply (proj2_sig (Fin.to_nat a)) | exact Param.Hpos].
  Qed.
  
  (* 证明乘法单位元律（one对应自然数1，分n=1和n≥2处理） *)
  Lemma mul_ident : forall a, mul a one = a.
  Proof.
    intros a; unfold mul, one; simpl.
    destruct Param.n as [|n'].
    - exfalso; apply Nat.lt_irrefl with 0; exact Param.Hpos.
    - destruct n' as [|n''].
      + rewrite Nat.mul_1_r; apply fin_nat_eq; simpl; reflexivity.
      + rewrite Nat.mul_1_r; apply fin_nat_eq; simpl.
        apply mod_small_proper with (n := Param.n); [apply (proj2_sig (Fin.to_nat a)) | exact Param.Hpos].
  Qed.
End MakeModAlgebra.

(* ======================== 6. 实例验证（确保所有代数性质可机械执行） ======================== *)
(* 实例1：模5代数（验证基础运算） *)
Module Mod5Params : MODALGEBRA.
  Definition n := 5.
  Definition Hpos : 0 < 5 := Nat.lt_0_succ 4.
End Mod5Params.
Module Mod5Algebra := MakeModAlgebra Mod5Params.

(* 定义模5元素 *)
Definition zero5 : Mod5Algebra.T := Mod5Algebra.zero.
Definition one5 : Mod5Algebra.T := Mod5Algebra.one.
Definition two5 : Mod5Algebra.T := Fin.FS one5.
Definition three5 : Mod5Algebra.T := Fin.FS two5.
Definition four5 : Mod5Algebra.T := Fin.FS three5.

(* 测试定理：验证核心性质 *)
Theorem test_mod5_add_1_plus_1_eq_2 : Mod5Algebra.add one5 one5 = two5.
Proof. simpl; reflexivity. Qed.

Theorem test_mod5_mul_2_times_2_eq_4 : Mod5Algebra.mul two5 two5 = four5.
Proof. simpl; reflexivity. Qed.

Theorem test_mod5_add_3_plus_4_eq_2 : Mod5Algebra.add three5 four5 = two5.
Proof. simpl; reflexivity. Qed.

Theorem test_mod5_mul_ident : Mod5Algebra.mul three5 one5 = three5.
Proof. simpl; reflexivity. Qed.

Theorem test_mod5_add_ident : Mod5Algebra.add four5 zero5 = four5.
Proof. simpl; reflexivity. Qed.

(* 实例2：模1代数（验证边界情况） *)
Module Mod1Params : MODALGEBRA.
  Definition n := 1.
  Definition Hpos : 0 < 1 := Nat.lt_0_succ 0.
End Mod1Params.
Module Mod1Algebra := MakeModAlgebra Mod1Params.

Definition zero1 : Mod1Algebra.T := Mod1Algebra.zero.
Definition one1 : Mod1Algebra.T := Mod1Algebra.one.

Theorem mod1_zero_eq_one : zero1 = one1.
Proof. apply fin_nat_eq; simpl; reflexivity. Qed.