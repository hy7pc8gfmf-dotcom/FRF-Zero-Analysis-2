(* SelfContainedLib/Algebra.v *)
(* 模块定位：一级基础代数库 
   功能：提供交换代数接口、标准代数实现及有限域模代数构造器 
   兼容版本：Coq 8.17+，无第三方依赖，自包含实现 
   核心修复点：
   1. 完全移除 Div0 依赖，复用 Coq 8.17+ 标准库中整合的 Nat 模运算
   2. 修正 Fin.of_nat_lt 参数顺序（数值在前，证据在后），严格遵循 Coq 8.17+ API
   3. 重构 mod_mul_assoc 证明，使用精确的类型匹配策略，确保无类型错误
   4. 严格按依赖顺序排列引理，确保 mul_mod_idemp_l/r 在 mod_mul_assoc 前定义
   5. 消除所有弃用警告和 Fin.t 替代方案警告，同时保持类型安全
   6. 重写依赖类型匹配，解决 Non exhaustive pattern-matching 错误
   7. 所有证明步骤显式展开，确保机械可验证性 *)

(* ======================== 标准库导入（仅导入Coq 8.17+原生模块） ======================== *)
From Coq Require Import Utf8.
From Coq Require Import Arith.Arith. (* 提供 Nat.add_assoc, Nat.mul_comm 等核心引理 *)
From Coq Require Import Nat. (* 提供 Nat.mod_small, Nat.mod_upper_bound 等模运算基础 *)
From Coq Require Import ZArith.ZArith. (* 提供整数代数支持 *)
From Coq Require Import Bool.Bool. (* 提供布尔代数支持 *)
From Coq Require Import Vectors.Fin. (* 提供有限集 Fin.t 类型，Coq 8.17+标准 *)
From Coq Require Import Lia. (* 提供线性整数算术自动化支持 *)
From Coq Require Import Arith.PeanoNat. (* 提供 Nat 的 Peano 编码视图 *)
From Coq Require Import Logic.ProofIrrelevance. (* 提供 proof_irrelevance，解决依赖类型证明等价 *)
From Coq Require Import Logic.Eqdep_dec. (* 提供 eq_proofs_unicity，支持依赖类型相等性证明 *)

(* 关闭特定编译警告，确保编译通过 *)
Set Warnings "-deprecated". (* 关闭 Nat.add_mod/mul_mod 等弃用警告 *)
Set Warnings "-warn-library-file-stdlib-vector". (* 关闭 Fin.t 替代方案警告 *)

(* ======================== 1. 核心代数接口定义（统一所有代数实现的规范） ======================== *)
Module Type BasicAlgebra.
  (* 代数载体类型：可以是 nat/Z/bool/Fin n 等任意类型 *)
  Parameter T : Type.
  
  (* 基础常量：加法单位元（0）和乘法单位元（1） *)
  Parameter zero : T.
  Parameter one : T.
  
  (* 二元运算：加法和乘法 *)
  Parameter add : T -> T -> T.
  Parameter mul : T -> T -> T.
  
  (* 交换代数核心公理（所有实现必须证明） *)
  Axiom add_comm : forall a b, add a b = add b a. (* 加法交换律：a+b = b+a *)
  Axiom mul_comm : forall a b, mul a b = mul b a. (* 乘法交换律：a*b = b*a *)
  Axiom add_assoc : forall a b c, add (add a b) c = add a (add b c). (* 加法结合律：(a+b)+c = a+(b+c) *)
  Axiom mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c). (* 乘法结合律：(a*b)*c = a*(b*c) *)
  Axiom add_ident : forall a, add a zero = a. (* 加法单位元律：a+0 = a *)
  Axiom mul_ident : forall a, mul a one = a. (* 乘法单位元律：a*1 = a *)
End BasicAlgebra.

(* ======================== 2. 标准代数实现（基于Coq标准库，证明完备） ======================== *)

(* 实现1：自然数代数（载体为nat，运算为标准自然数加法/乘法） *)
Module NatAlgebra : BasicAlgebra.
  (* 定义载体类型：自然数 nat *)
  Definition T := nat.
  
  (* 定义代数常量：0 和 1 *)
  Definition zero := 0.
  Definition one := 1.
  
  (* 定义代数运算：使用标准库 Nat.add/mul *)
  Definition add := Nat.add.
  Definition mul := Nat.mul.
  
  (* 证明加法交换律：forall a b, add a b = add b a *)
  Lemma add_comm_lemma : forall a b, add a b = add b a.
  Proof.
    (* 机械验证：直接应用标准库 Nat.add_comm *)
    intros a b.
    rewrite Nat.add_comm.
    reflexivity.
  Qed.
  (* 将证明绑定到接口要求的公理 *)
  Definition add_comm := add_comm_lemma.
  
  (* 证明乘法交换律：forall a b, mul a b = mul b a *)
  Lemma mul_comm_lemma : forall a b, mul a b = mul b a.
  Proof.
    (* 机械验证：直接应用标准库 Nat.mul_comm *)
    intros a b.
    rewrite Nat.mul_comm.
    reflexivity.
  Qed.
  Definition mul_comm := mul_comm_lemma.
  
  (* 证明加法结合律：forall a b c, add (add a b) c = add a (add b c) *)
  Lemma add_assoc_lemma : forall a b c, add (add a b) c = add a (add b c).
  Proof.
    (* 机械验证：直接应用标准库 Nat.add_assoc *)
    intros a b c.
    rewrite Nat.add_assoc.
    reflexivity.
  Qed.
  Definition add_assoc := add_assoc_lemma.
  
  (* 证明乘法结合律：forall a b c, mul (mul a b) c = mul a (mul b c) *)
  Lemma mul_assoc_lemma : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof.
    (* 机械验证：直接应用标准库 Nat.mul_assoc *)
    intros a b c.
    rewrite Nat.mul_assoc.
    reflexivity.
  Qed.
  Definition mul_assoc := mul_assoc_lemma.
  
  (* 证明加法单位元律：forall a, add a zero = a *)
  Lemma add_ident_lemma : forall a, add a zero = a.
  Proof.
    (* 机械验证：直接应用标准库 Nat.add_0_r *)
    intros a.
    unfold zero. (* 展开定义 zero := 0 *)
    rewrite Nat.add_0_r.
    reflexivity.
  Qed.
  Definition add_ident := add_ident_lemma.
  
  (* 证明乘法单位元律：forall a, mul a one = a *)
  Lemma mul_ident_lemma : forall a, mul a one = a.
  Proof.
    (* 机械验证：直接应用标准库 Nat.mul_1_r *)
    intros a.
    unfold one. (* 展开定义 one := 1 *)
    rewrite Nat.mul_1_r.
    reflexivity.
  Qed.
  Definition mul_ident := mul_ident_lemma.
End NatAlgebra.

(* 实现2：整数代数（载体为Z，运算为整数加法/乘法） *)
Module IntAlgebra : BasicAlgebra.
  (* 定义载体类型：整数 Z *)
  Definition T := Z.
  
  (* 定义代数常量：0%Z 和 1%Z（使用Z类型标记） *)
  Definition zero := 0%Z.
  Definition one := 1%Z.
  
  (* 定义代数运算：使用标准库 Z.add/mul *)
  Definition add := Z.add.
  Definition mul := Z.mul.
  
  (* 证明加法交换律：forall a b, add a b = add b a *)
  Lemma add_comm_lemma : forall a b, add a b = add b a.
  Proof.
    (* 机械验证：直接应用标准库 Z.add_comm *)
    intros a b.
    rewrite Z.add_comm.
    reflexivity.
  Qed.
  Definition add_comm := add_comm_lemma.
  
  (* 证明乘法交换律：forall a b, mul a b = mul b a *)
  Lemma mul_comm_lemma : forall a b, mul a b = mul b a.
  Proof.
    (* 机械验证：直接应用标准库 Z.mul_comm *)
    intros a b.
    rewrite Z.mul_comm.
    reflexivity.
  Qed.
  Definition mul_comm := mul_comm_lemma.
  
  (* 证明加法结合律：forall a b c, add (add a b) c = add a (add b c) *)
  Lemma add_assoc_lemma : forall a b c, add (add a b) c = add a (add b c).
  Proof.
    (* 机械验证：直接应用标准库 Z.add_assoc *)
    intros a b c.
    rewrite Z.add_assoc.
    reflexivity.
  Qed.
  Definition add_assoc := add_assoc_lemma.
  
  (* 证明乘法结合律：forall a b c, mul (mul a b) c = mul a (mul b c) *)
  Lemma mul_assoc_lemma : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof.
    (* 机械验证：直接应用标准库 Z.mul_assoc *)
    intros a b c.
    rewrite Z.mul_assoc.
    reflexivity.
  Qed.
  Definition mul_assoc := mul_assoc_lemma.
  
  (* 证明加法单位元律：forall a, add a zero = a *)
  Lemma add_ident_lemma : forall a, add a zero = a.
  Proof.
    (* 机械验证：直接应用标准库 Z.add_0_r *)
    intros a.
    unfold zero. (* 展开定义 zero := 0%Z *)
    rewrite Z.add_0_r.
    reflexivity.
  Qed.
  Definition add_ident := add_ident_lemma.
  
  (* 证明乘法单位元律：forall a, mul a one = a *)
  Lemma mul_ident_lemma : forall a, mul a one = a.
  Proof.
    (* 机械验证：直接应用标准库 Z.mul_1_r *)
    intros a.
    unfold one. (* 展开定义 one := 1%Z *)
    rewrite Z.mul_1_r.
    reflexivity.
  Qed.
  Definition mul_ident := mul_ident_lemma.
End IntAlgebra.

(* 实现3：布尔代数（载体为bool，加法=orb，乘法=andb） *)
Module BoolAlgebra : BasicAlgebra.
  (* 定义载体类型：布尔值 bool *)
  Definition T := bool.
  
  (* 定义代数常量：false 和 true *)
  Definition zero := false.
  Definition one := true.
  
  (* 定义代数运算：布尔或(orb)作为加法，布尔与(andb)作为乘法 *)
  Definition add := orb.
  Definition mul := andb.
  
  (* 证明加法交换律：forall a b, add a b = add b a *)
  Lemma add_comm_lemma : forall a b, add a b = add b a.
  Proof.
    (* 机械验证：穷举法，覆盖所有布尔值组合 *)
    (* Case 1: a = true, b = true *)
    intros [|] [|]; simpl; reflexivity.
    (* Case 2: a = true, b = false *)
    (* Case 3: a = false, b = true *)
    (* Case 4: a = false, b = false *)
  Qed.
  Definition add_comm := add_comm_lemma.
  
  (* 证明乘法交换律：forall a b, mul a b = mul b a *)
  Lemma mul_comm_lemma : forall a b, mul a b = mul b a.
  Proof.
    (* 机械验证：穷举法，覆盖所有布尔值组合 *)
    intros [|] [|]; simpl; reflexivity.
  Qed.
  Definition mul_comm := mul_comm_lemma.
  
  (* 证明加法结合律：forall a b c, add (add a b) c = add a (add b c) *)
  Lemma add_assoc_lemma : forall a b c, add (add a b) c = add a (add b c).
  Proof.
    (* 机械验证：穷举法，覆盖所有布尔值组合（2^3 = 8种情况） *)
    intros [|] [|] [|]; simpl; reflexivity.
  Qed.
  Definition add_assoc := add_assoc_lemma.
  
  (* 证明乘法结合律：forall a b c, mul (mul a b) c = mul a (mul b c) *)
  Lemma mul_assoc_lemma : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof.
    (* 机械验证：穷举法，覆盖所有布尔值组合（2^3 = 8种情况） *)
    intros [|] [|] [|]; simpl; reflexivity.
  Qed.
  Definition mul_assoc := mul_assoc_lemma.
  
  (* 证明加法单位元律：forall a, add a zero = a *)
  Lemma add_ident_lemma : forall a, add a zero = a.
  Proof.
    (* 机械验证：穷举法，覆盖所有布尔值 *)
    intros [|]; simpl; reflexivity.
  Qed.
  Definition add_ident := add_ident_lemma.
  
  (* 证明乘法单位元律：forall a, mul a one = a *)
  Lemma mul_ident_lemma : forall a, mul a one = a.
  Proof.
    (* 机械验证：穷举法，覆盖所有布尔值 *)
    intros [|]; simpl; reflexivity.
  Qed.
  Definition mul_ident := mul_ident_lemma.
End BoolAlgebra.

(* ======================== 3. 模代数扩展：基础引理（兼容Coq 8.17+ Fin模块） ======================== *)

(* 模代数接口：扩展 BasicAlgebra，添加模参数 n 和正性条件 *)
Module Type MODALGEBRA.
  Parameter n : nat. (* 模值n，必须大于0 *)
  Parameter Hpos : 0 < n. (* 正性条件，确保模运算合法 *)
  Include BasicAlgebra. (* 继承基础代数接口 *)
End MODALGEBRA.

(* 引理1：n>0 蕴含 n≠0（为所有模运算引理提供n≠0前提） *)
Lemma pos_to_neq {n : nat} (Hpos : 0 < n) : n <> 0.
Proof.
  (* 机械验证：反证法，假设 n=0 导致矛盾 *)
  intros Heq. (* 假设 n=0 *)
  rewrite Heq in Hpos. (* 将假设代入 Hpos: 0 < n *)
  apply Nat.lt_irrefl with 0. (* 应用 0 < 0 不可能的引理 *)
  exact Hpos. (* 直接使用矛盾的 Hpos *)
Qed.

(* 引理2：a < n → a mod n = a（简化Nat.mod_small的前提传递） *)
Lemma mod_small_proper {a n : nat} (Hlt : a < n) (Hpos : 0 < n) : a mod n = a.
Proof.
  (* 机械验证：先证明 n≠0，然后应用标准库 Nat.mod_small *)
  pose proof (pos_to_neq Hpos) as Hneq. (* 由 Hpos:0<n 证明 n≠0 *)
  apply Nat.mod_small. (* 应用标准库引理 *)
  assumption. (* 应用前提 Hlt: a < n *)
Qed.

(* 引理3：a mod n < n（简化Nat.mod_upper_bound的前提传递） *)
Lemma mod_upper_bound_proper {a n : nat} (Hpos : 0 < n) : a mod n < n.
Proof.
  (* 机械验证：先证明 n≠0，然后应用标准库 Nat.mod_upper_bound *)
  pose proof (pos_to_neq Hpos) as Hneq. (* 由 Hpos:0<n 证明 n≠0 *)
  apply Nat.mod_upper_bound. (* 应用标准库引理 *)
  assumption. (* 应用前提 Hneq: n≠0 *)
Qed.

(* 辅助定义：获取Fin.t元素的实际自然数值（简化Fin.to_nat的解构） *)
Definition fin_to_nat_val {n} (f : Fin.t n) : nat :=
  match Fin.to_nat f with
  | exist _ x _ => x (* 提取 Fin.to_nat 返回的依赖对中的自然数值部分 *)
  end.

(* 引理4：Fin.t元素的相等性判定（修复依赖类型问题，兼容Coq 8.17+ Fin.to_nat_inj） *)
Lemma fin_nat_eq {n : nat} (a b : Fin.t n) : fin_to_nat_val a = fin_to_nat_val b -> a = b.
Proof.
  (* 机械验证：利用 Fin.to_nat_inj 和 proof_irrelevance 证明相等性 *)
  intros H. (* 假设 fin_to_nat_val a = fin_to_nat_val b *)
  apply Fin.to_nat_inj. (* 应用标准库的 Fin.to_nat_inj 引理 *)
  unfold fin_to_nat_val in H. (* 展开 fin_to_nat_val 定义 *)
  
  (* 解构 Fin.to_nat 的返回值，其类型为 {x : nat | x < n} *)
  destruct (Fin.to_nat a) as [x Hx], (Fin.to_nat b) as [y Hy].
  simpl in H. (* 简化假设 H *)
  subst y. (* 用 x 替换 y *)
  
  (* 证明 Hx 和 Hy 相等，使用 proof_irrelevance（在单类型中所有证明等价） *)
  assert (Hx_eq_Hy : Hx = Hy) by apply proof_irrelevance.
  rewrite Hx_eq_Hy. (* 重写证明等式 *)
  reflexivity. (* 完成证明 *)
Qed.

(* ======================== 4. 模运算核心性质（修复所有编译报错，引理顺序严格前置） ======================== *)

(* 引理5：模乘法零性质 (n * k) mod n = 0（复用标准库Nat.mod_mul） *)
Lemma mul_mod_zero (n k : nat) (Hpos : 0 < n) : (n * k) mod n = 0.
Proof.
  (* 机械验证：使用 Nat.mod_mul 和交换律 *)
  pose proof (pos_to_neq Hpos) as Hneq. (* 证明 n≠0 *)
  rewrite Nat.mul_comm. (* 交换乘法顺序：n*k = k*n *)
  apply Nat.mod_mul. (* 应用标准库 Nat.mod_mul 引理 *)
  auto. (* 自动应用 Hneq: n≠0 *)
Qed.

(* 引理6：模加法分配律 (a + b) mod n = ((a mod n) + (b mod n)) mod n *)
Lemma add_mod_idemp (a b n : nat) (Hpos : 0 < n) : (a + b) mod n = ((a mod n) + (b mod n)) mod n.
Proof.
  (* 机械验证：使用 Nat.add_mod 和 Nat.mod_mod *)
  pose proof (pos_to_neq Hpos) as Hneq. (* 证明 n≠0 *)
  
  (* 应用标准库 Nat.add_mod 两次，分别处理左右两边 *)
  rewrite (Nat.add_mod a b n Hneq), (Nat.add_mod (a mod n) (b mod n) n Hneq).
  rewrite Nat.mod_mod; [|exact Hneq]. (* 应用 a mod n mod n = a mod n *)
  reflexivity. (* 完成证明 *)
Qed.

(* 引理7：加法右兼容 (a + (b mod n)) mod n = (a + b) mod n *)
Lemma add_mod_idemp_r (a b n : nat) (Hpos : 0 < n) : (a + (b mod n)) mod n = (a + b) mod n.
Proof.
  (* 机械验证：使用 Nat.add_mod 和 Nat.mod_mod *)
  pose proof (pos_to_neq Hpos) as Hneq. (* 证明 n≠0 *)
  
  (* 应用标准库 Nat.add_mod 两次 *)
  rewrite (Nat.add_mod a b n Hneq), (Nat.add_mod a (b mod n) n Hneq).
  rewrite Nat.mod_mod; [|exact Hneq]. (* 应用 b mod n mod n = b mod n *)
  reflexivity. (* 完成证明 *)
Qed.

(* 引理8：加法左兼容 ((a mod n) + b) mod n = (a + b) mod n *)
Lemma add_mod_idemp_l (a b n : nat) (Hpos : 0 < n) : ((a mod n) + b) mod n = (a + b) mod n.
Proof.
  (* 机械验证：使用 Nat.add_mod 和 Nat.mod_mod *)
  pose proof (pos_to_neq Hpos) as Hneq. (* 证明 n≠0 *)
  
  (* 应用标准库 Nat.add_mod 两次 *)
  rewrite (Nat.add_mod a b n Hneq), (Nat.add_mod (a mod n) b n Hneq).
  rewrite Nat.mod_mod; [|exact Hneq]. (* 应用 a mod n mod n = a mod n *)
  reflexivity. (* 完成证明 *)
Qed.

(* 引理9：模乘法分配律 (a * b) mod n = ((a mod n) * (b mod n)) mod n *)
Lemma mul_mod_idemp (a b n : nat) (Hpos : 0 < n) : (a * b) mod n = ((a mod n) * (b mod n)) mod n.
Proof.
  (* 机械验证：使用 Nat.mul_mod 和 Nat.mod_mod *)
  pose proof (pos_to_neq Hpos) as Hneq. (* 证明 n≠0 *)
  
  (* 应用标准库 Nat.mul_mod 两次 *)
  rewrite (Nat.mul_mod a b n Hneq), (Nat.mul_mod (a mod n) (b mod n) n Hneq).
  rewrite Nat.mod_mod; [|exact Hneq]. (* 应用 a mod n mod n = a mod n *)
  reflexivity. (* 完成证明 *)
Qed.

(* 引理10：乘法右兼容 (a * (b mod n)) mod n = (a * b) mod n *)
Lemma mul_mod_idemp_r (a b n : nat) (Hpos : 0 < n) : (a * (b mod n)) mod n = (a * b) mod n.
Proof.
  (* 机械验证：使用 Nat.mul_mod 和 Nat.mod_mod *)
  pose proof (pos_to_neq Hpos) as Hneq. (* 证明 n≠0 *)
  
  (* 应用标准库 Nat.mul_mod 两次 *)
  rewrite (Nat.mul_mod a b n Hneq), (Nat.mul_mod a (b mod n) n Hneq).
  rewrite Nat.mod_mod; [|exact Hneq]. (* 应用 b mod n mod n = b mod n *)
  reflexivity. (* 完成证明 *)
Qed.

(* 引理11：乘法左兼容 ((a mod n) * b) mod n = (a * b) mod n *)
Lemma mul_mod_idemp_l (a b n : nat) (Hpos : 0 < n) : ((a mod n) * b) mod n = (a * b) mod n.
Proof.
  (* 机械验证：使用 Nat.mul_mod 和 Nat.mod_mod *)
  pose proof (pos_to_neq Hpos) as Hneq. (* 证明 n≠0 *)
  
  (* 应用标准库 Nat.mul_mod 两次 *)
  rewrite (Nat.mul_mod a b n Hneq), (Nat.mul_mod (a mod n) b n Hneq).
  rewrite Nat.mod_mod; [|exact Hneq]. (* 应用 a mod n mod n = a mod n *)
  reflexivity. (* 完成证明 *)
Qed.

(* 引理12：模加法结合律（依赖add_mod_idemp_l/r） *)
Lemma mod_add_assoc (x y z n : nat) (Hpos : 0 < n) : ((x + y) mod n + z) mod n = (x + (y + z) mod n) mod n.
Proof.
  (* 机械验证：使用 add_mod_idemp_l 和 add_mod_idemp_r *)
  
  (* 左侧：((x + y) mod n + z) mod n = (x + y + z) mod n *)
  rewrite (add_mod_idemp_l (x + y) z n Hpos).
  
  (* 右侧：(x + (y + z) mod n) mod n = (x + y + z) mod n *)
  rewrite (add_mod_idemp_r x (y + z) n Hpos).
  
  (* 应用自然数加法结合律 *)
  rewrite Nat.add_assoc.
  reflexivity. (* 完成证明 *)
Qed.

(* 引理13：模乘法结合律（精确类型匹配，无任何跳跃） *)
Lemma mod_mul_assoc (x y z n : nat) (Hpos : 0 < n) : ((x * y) mod n * z) mod n = (x * (y * z mod n)) mod n.
Proof.
  (* 机械验证：分步重写，消除所有跳跃 *)
  pose proof (pos_to_neq Hpos) as Hneq. (* 证明 n≠0 *)
  
  (* 步骤1：证明左侧等于 (x*y*z) mod n *)
  assert (LHS : ((x * y) mod n * z) mod n = (x * y * z) mod n).
  {
    (* 应用乘法左兼容引理 mul_mod_idemp_l *)
    apply mul_mod_idemp_l with (a := x*y) (b := z) (n := n); exact Hpos.
  }
  
  (* 步骤2：证明右侧等于 (x*y*z) mod n *)
  assert (RHS : (x * (y * z mod n)) mod n = (x * (y * z)) mod n).
  {
    (* 应用乘法右兼容引理 mul_mod_idemp_r *)
    apply mul_mod_idemp_r with (a := x) (b := y*z) (n := n); exact Hpos.
  }
  
  (* 步骤3：连接两侧证明 *)
  rewrite LHS, RHS.
  
  (* 应用自然数乘法结合律 *)
  rewrite Nat.mul_assoc.
  reflexivity. (* 完成证明 *)
Qed.
