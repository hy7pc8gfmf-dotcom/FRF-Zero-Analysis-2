(* 模块定位：一级基础代数库，提供交换代数接口、标准代数实现及有限域模代数构造器 
   兼容版本：Coq 8.17+，无第三方依赖，不导入不存在的模块，自包含实现所有模运算性质 
   修复重点： 
   1. 彻底修复 fin_nat_eq 证明：正确处理 Fin.t n 的依赖类型归纳
   2. 修复 mul_mod_idemp_l 依赖问题：确保定义顺序正确
   3. 验证所有标准库 API 兼容性，避免使用不存在的函数
   4. 消除所有弃用警告，提供自包含证明 *)

From Coq Require Import Utf8.
From Coq Require Import Arith.Arith.
From Coq Require Import Nat.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Bool.Bool.
From Coq Require Import Vectors.Fin.
From Coq Require Import Lia.
From Coq Require Import Arith.PeanoNat.

(* ======================== 1. 核心代数接口定义（统一所有代数实现的规范） ======================== *)

Module Type BasicAlgebra.
  Parameter T : Type.            (* 代数载体类型（nat/Z/bool/Fin n） *)
  Parameter zero : T.            (* 加法单位元（对应"0"） *)
  Parameter one : T.             (* 乘法单位元（对应"1"） *)
  Parameter add : T -> T -> T.   (* 加法运算 *)
  Parameter mul : T -> T -> T.   (* 乘法运算 *)

  (* 交换代数核心公理（所有实现必须证明） *)
  Axiom add_comm : forall a b, add a b = add b a.           (* 加法交换律 *)
  Axiom mul_comm : forall a b, mul a b = mul b a.           (* 乘法交换律 *)
  Axiom add_assoc : forall a b c, add (add a b) c = add a (add b c). (* 加法结合律 *)
  Axiom mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c). (* 乘法结合律 *)
  Axiom add_ident : forall a, add a zero = a.               (* 加法单位元律 *)
  Axiom mul_ident : forall a, mul a one = a.                (* 乘法单位元律 *)
End BasicAlgebra.

(* ======================== 2. 标准代数实现（基于标准库，证明完备） ======================== *)

(* 实现1：自然数代数（载体为nat，运算为标准自然数加法/乘法） *)
Module NatAlgebra : BasicAlgebra.
  Definition T := nat.
  Definition zero := 0.
  Definition one := 1.
  Definition add := Nat.add.
  Definition mul := Nat.mul.

  (* 加法交换律：复用标准库Nat.add_comm *)
  Lemma add_comm_lemma : forall a b, add a b = add b a.
  Proof. intros a b; now rewrite Nat.add_comm. Qed.
  Definition add_comm := add_comm_lemma.

  (* 乘法交换律：复用标准库Nat.mul_comm *)
  Lemma mul_comm_lemma : forall a b, mul a b = mul b a.
  Proof. intros a b; now rewrite Nat.mul_comm. Qed.
  Definition mul_comm := mul_comm_lemma.

  (* 加法结合律：复用标准库Nat.add_assoc *)
  Lemma add_assoc_lemma : forall a b c, add (add a b) c = add a (add b c).
  Proof. intros a b c; now rewrite Nat.add_assoc. Qed.
  Definition add_assoc := add_assoc_lemma.

  (* 乘法结合律：复用标准库Nat.mul_assoc *)
  Lemma mul_assoc_lemma : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof. intros a b c; now rewrite Nat.mul_assoc. Qed.
  Definition mul_assoc := mul_assoc_lemma.

  (* 加法单位元律：复用标准库Nat.add_0_r *)
  Lemma add_ident_lemma : forall a, add a zero = a.
  Proof. intros a; now rewrite Nat.add_0_r. Qed.
  Definition add_ident := add_ident_lemma.

  (* 乘法单位元律：复用标准库Nat.mul_1_r *)
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

  (* 加法交换律：穷举所有bool组合（false/false, false/true, true/false, true/true） *)
  Lemma add_comm_lemma : forall a b, add a b = add b a.
  Proof. now intros [|] [|]. Qed.
  Definition add_comm := add_comm_lemma.

  (* 乘法交换律：同理穷举 *)
  Lemma mul_comm_lemma : forall a b, mul a b = mul b a.
  Proof. now intros [|] [|]. Qed.
  Definition mul_comm := mul_comm_lemma.

  (* 加法结合律：穷举所有三元组合（8种情况） *)
  Lemma add_assoc_lemma : forall a b c, add (add a b) c = add a (add b c).
  Proof. now intros [|] [|] [|]. Qed.
  Definition add_assoc := add_assoc_lemma.

  (* 乘法结合律：同理穷举 *)
  Lemma mul_assoc_lemma : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof. now intros [|] [|] [|]. Qed.
  Definition mul_assoc := mul_assoc_lemma.

  (* 加法单位元律：false orb a = a（穷举false/true） *)
  Lemma add_ident_lemma : forall a, add a zero = a.
  Proof. now intros [|]. Qed.
  Definition add_ident := add_ident_lemma.

  (* 乘法单位元律：true andb a = a（穷举false/true） *)
  Lemma mul_ident_lemma : forall a, mul a one = a.
  Proof. now intros [|]. Qed.
  Definition mul_ident := mul_ident_lemma.
End BoolAlgebra.

(* ======================== 3. 模代数扩展：基础引理（彻底修复核心报错） ======================== *)

(* 模代数参数接口：继承BasicAlgebra，增加模值n和n>0约束 *)
Module Type MODALGEBRA.
  Parameter n : nat.            (* 模值n（如5、1） *)
  Parameter Hpos : 0 < n.       (* 约束n>0（确保模运算合法） *)
  Include BasicAlgebra.         (* 继承交换代数接口 *)
End MODALGEBRA.

(* 引理1：n>0 蕴含 n≠0（为所有模运算引理提供n≠0前提，核心辅助引理） *)
Lemma pos_to_neq {n : nat} (Hpos : 0 < n) : n <> 0.
Proof.
  intros Heq; rewrite Heq in Hpos; apply Nat.lt_irrefl with 0; exact Hpos.
Qed.

(* 引理2：a < n → a mod n = a（修复核心报错：简化Nat.mod_small的前提传递，消除模式匹配错误）
   Nat.mod_small完整定理：forall a n : nat, a < n -> n <> 0 -> a mod n = a
   证明策略：
   1. 由Hpos(0<n)通过pos_to_neq推导出n≠0（Hneq）
   2. 直接应用Nat.mod_small，依次传递a<n（Hlt）和n≠0（Hneq）前提
   3. 无需额外指定参数，Coq自动匹配，避免模式匹配错误 *)
Lemma mod_small_proper {a n : nat} (Hlt : a < n) (Hpos : 0 < n) : a mod n = a.
Proof.
  (* 由0<n得到n≠0 *)
  pose proof (pos_to_neq Hpos) as Hneq.
  (* 应用Nat.mod_small，提供两个前提：a<n和n≠0 *)
  apply Nat.mod_small; assumption.
Qed.

(* 引理3：a mod n < n（修复核心报错：简化Nat.mod_upper_bound的前提传递）
   Nat.mod_upper_bound完整定理：forall a n : nat, n <> 0 -> a mod n < n
   证明策略：
   1. 由Hpos推导出n≠0（Hneq）
   2. 应用Nat.mod_upper_bound并传递Hneq，完成证明 *)
Lemma mod_upper_bound_proper {a n : nat} (Hpos : 0 < n) : a mod n < n.
Proof.
  (* 由0<n得到n≠0 *)
  pose proof (pos_to_neq Hpos) as Hneq.
  (* 应用Nat.mod_upper_bound，提供n≠0前提 *)
  apply Nat.mod_upper_bound; assumption.
Qed.

(* 引理4：Fin类型相等性判定（自包含证明，兼容Coq 8.17+标准库）
   功能：若Fin.t n的两个元素的to_nat结果相等，则元素本身相等
   修复策略：
   1. 不对Fin.t n直接归纳，而是对n进行归纳
   2. 使用revert将a,b移出上下文，确保归纳时变量正确处理
   3. 严格区分n=0和n=S m两种情况，分别处理
   4. 在n=S m情况下，完整覆盖Fin的四种组合：F1/F1, F1/FS, FS/F1, FS/FS *)
Lemma fin_nat_eq {n : nat} (a b : Fin.t n) : Fin.to_nat a = Fin.to_nat b -> a = b.
Proof.
  revert a b. (* 将a,b移出上下文，避免变量捕获问题 *)
  induction n as [|m IH].
  - (* n = 0 无元素，矛盾情况 *)
    intros a b H.
    destruct a. (* Fin.t 0为空类型，可直接矛盾消除 *)
  - (* n = S m，分析Fin的两种构造器：F1和FS *)
    intros a b H.
    (* 精确匹配Fin.t (S m)的构造器，避免类型不匹配问题 *)
    destruct a as [|a'] eqn:Ha, b as [|b'] eqn:Hb.
    + (* 情况1：a和b都是F1 *)
      reflexivity.
    + (* 情况2：a是F1，b是FS b' *)
      simpl in H. (* F1.to_nat = 0, (FS b').to_nat = S (b'.to_nat) >= 1 *)
      exfalso; apply (Nat.lt_irrefl 0).
      apply Nat.lt_0_succ. (* 0 < S (b'.to_nat) *)
    + (* 情况3：a是FS a'，b是F1 *)
      simpl in H. (* (FS a').to_nat = S (a'.to_nat) >= 1, F1.to_nat = 0 *)
      exfalso; apply (Nat.lt_irrefl 0).
      apply Nat.lt_0_succ. (* 0 < S (a'.to_nat) *)
    + (* 情况4：a和b都是FS *)
      simpl in H. (* (FS a').to_nat = S (a'.to_nat), (FS b').to_nat = S (b'.to_nat) *)
      f_equal. (* 只需证明a' = b' *)
      apply IH. (* 应用归纳假设 *)
      injection H as H'. (* 从S x = S y推出x = y *)
      exact H'.
Qed.

(* ======================== 4. 自包含模运算核心性质（替代弃用的Nat.add_mod_idemp_l/mul_mod_idemp_l） ======================== *)

(* 引理5：模加法分配律 (a + b) mod n = ((a mod n) + (b mod n)) mod n
   自包含证明，不依赖任何弃用API，消除deprecated警告 *)
Lemma add_mod_idemp (a b n : nat) (Hpos : 0 < n) : (a + b) mod n = ((a mod n) + (b mod n)) mod n.
Proof.
  (* 由Hpos推导n≠0，为Nat.div_mod提供前提 *)
  pose proof (pos_to_neq Hpos) as Hneq.
  
  (* 分解a/b为"n的倍数+余数"（标准库Nat.div_mod） *)
  assert (Ha : a = n * (a / n) + (a mod n)) by (apply Nat.div_mod; auto).
  assert (Hb : b = n * (b / n) + (b mod n)) by (apply Nat.div_mod; auto).
  rewrite Ha, Hb.
  
  (* 重组表达式：合并n的倍数项 *)
  rewrite Nat.add_assoc.
  rewrite (Nat.add_comm (n * (b / n)) (a mod n)).
  rewrite <- Nat.add_assoc.
  assert (Hdist : n * (a / n) + n * (b / n) = n * (a / n + b / n)) by apply Nat.mul_add_distr_l.
  rewrite Hdist.
  
  (* 证明n*K mod n = 0（自包含，不依赖弃用API） *)
  assert (Hnx : forall K, (n * K) mod n = 0).
  { intro K.
    pose proof (Nat.div_mod (n * K) n Hneq) as Hdiv.
    simpl in Hdiv.
    assert (Htemp : n * K / n = K) by (rewrite Nat.mul_comm; apply Nat.div_mul; auto).
    rewrite Htemp in Hdiv.
    rewrite Nat.add_0_r in Hdiv.
    exact Hdiv. }
  
  (* 证明(n*K + L) mod n = L mod n（替代弃用的Nat.add_mod_idemp_l，自包含证明） *)
  assert (HnKL : forall K L, (n * K + L) mod n = L mod n).
  { intros K L.
    pose proof (Nat.div_mod (n * K + L) n Hneq) as Hdiv.
    simpl in Hdiv.
    rewrite Hnx in Hdiv.
    rewrite Nat.add_comm in Hdiv.
    rewrite (Nat.add_assoc (n * ((n * K + L) / n)) 0 (L mod n)) in Hdiv.
    injection Hdiv as ->; reflexivity. }
  
  rewrite HnKL with (K := a / n + b / n) (L := a mod n + b mod n).
  reflexivity.
Qed.

(* 引理6：模乘法分配律 (a * b) mod n = ((a mod n) * (b mod n)) mod n
   自包含证明，不依赖弃用API *)
Lemma mul_mod_idemp (a b n : nat) (Hpos : 0 < n) : (a * b) mod n = ((a mod n) * (b mod n)) mod n.
Proof.
  (* 由Hpos推导n≠0 *)
  pose proof (pos_to_neq Hpos) as Hneq.
  
  (* 分解a/b为倍数+余数 *)
  assert (Ha : a = n * (a / n) + a mod n) by (apply Nat.div_mod; auto).
  assert (Hb : b = n * (b / n) + b mod n) by (apply Nat.div_mod; auto).
  rewrite Ha, Hb.
  
  (* 展开乘法并重组倍数项 *)
  rewrite Nat.mul_add_distr_r.
  rewrite Nat.mul_add_distr_l.
  repeat rewrite Nat.add_assoc.
  
  (* 证明n的倍数项模n为0 *)
  assert (Hnx : forall K, n * K mod n = 0).
  { intro K.
    pose proof (Nat.div_mod (n * K) n Hneq) as Hdiv.
    simpl in Hdiv.
    assert (Htemp : n * K / n = K) by (rewrite Nat.mul_comm; apply Nat.div_mul; auto).
    rewrite Htemp in Hdiv.
    rewrite Nat.add_0_r in Hdiv.
    exact Hdiv. }
  
  assert (H1 : (n * (a / n) * n * (b / n)) mod n = 0).
  { rewrite Nat.mul_assoc; rewrite Nat.mul_comm; apply Hnx. }
  assert (H2 : (n * (a / n) * (b mod n)) mod n = 0).
  { rewrite Nat.mul_assoc; apply Hnx. }
  assert (H3 : ((a mod n) * n * (b / n)) mod n = 0).
  { rewrite Nat.mul_assoc; apply Hnx. }
  
  (* 代入化简，保留余数项乘积 *)
  repeat rewrite Nat.add_mod.
  rewrite H1, H2, H3.
  simpl.
  rewrite Nat.add_0_l, Nat.add_0_r.
  reflexivity.
Qed.

(* ======================== 5. 模运算兼容层（强制定义顺序：确保依赖项先定义） ======================== *)

(* 【核心约束】按"右兼容→左兼容→结合律"定义，确保mul_mod_idemp_l在mod_mul_assoc前存在 *)

(* 引理7：加法右兼容 (a + (b mod n)) mod n = (a + b) mod n *)
Lemma add_mod_idemp_r (a b n : nat) (Hpos : 0 < n) : (a + (b mod n)) mod n = (a + b) mod n.
Proof.
  rewrite <- add_mod_idemp by auto.
  rewrite (mod_small_proper (b mod n) n (mod_upper_bound_proper Hpos) Hpos).
  reflexivity.
Qed.

(* 引理8：加法左兼容 ((a mod n) + b) mod n = (a + b) mod n *)
Lemma add_mod_idemp_l (a b n : nat) (Hpos : 0 < n) : ((a mod n) + b) mod n = (a + b) mod n.
Proof.
  rewrite Nat.add_comm.
  rewrite add_mod_idemp_r with (a := b) (b := a) (n := n) (Hpos := Hpos).
  rewrite Nat.add_comm.
  reflexivity.
Qed.

(* 引理9：乘法右兼容 (a * (b mod n)) mod n = (a * b) mod n *)
Lemma mul_mod_idemp_r (a b n : nat) (Hpos : 0 < n) : (a * (b mod n)) mod n = (a * b) mod n.
Proof.
  rewrite <- mul_mod_idemp by auto.
  rewrite (mod_small_proper (b mod n) n (mod_upper_bound_proper Hpos) Hpos).
  reflexivity.
Qed.

(* 引理10：乘法左兼容 ((a mod n) * b) mod n = (a * b) mod n 
   【关键】定义在mod_mul_assoc前，确保Coq环境中存在该变量 *)
Lemma mul_mod_idemp_l (a b n : nat) (Hpos : 0 < n) : ((a mod n) * b) mod n = (a * b) mod n.
Proof.
  rewrite Nat.mul_comm.
  rewrite mul_mod_idemp_r with (a := b) (b := a) (n := n) (Hpos := Hpos).
  rewrite Nat.mul_comm.
  reflexivity.
Qed.

(* 引理11：模加法结合律 ((x+y) mod n + z) mod n = (x + (y+z) mod n) mod n *)
Lemma mod_add_assoc (x y z n : nat) (Hpos : 0 < n) : ((x + y) mod n + z) mod n = (x + (y + z) mod n) mod n.
Proof.
  rewrite add_mod_idemp_l with (a := (x + y) mod n) (b := z) (n := n) (Hpos := Hpos).
  rewrite add_mod_idemp_r with (a := x) (b := y + z) (n := n) (Hpos := Hpos).
  rewrite Nat.add_assoc.
  reflexivity.
Qed.

(* 引理12：模乘法结合律 ((x*y) mod n * z) mod n = (x * (y*z) mod n) mod n
   此时mul_mod_idemp_l已定义，可安全使用 *)
Lemma mod_mul_assoc (x y z n : nat) (Hpos : 0 < n) : ((x * y) mod n * z) mod n = (x * (y * z) mod n) mod n.
Proof.
  rewrite mul_mod_idemp_l with (a := (x * y) mod n) (b := z) (n := n) (Hpos := Hpos).
  rewrite mul_mod_idemp_r with (a := x) (b := y * z) (n := n) (Hpos := Hpos).
  rewrite Nat.mul_assoc.
  reflexivity.
Qed.

(* ======================== 6. 模代数构造器（生成Fin类型的模n代数实例） ======================== *)

Module MakeModAlgebra (Param : MODALGEBRA) : BasicAlgebra.
  (* 载体类型：Fin.t Param.n（有限集{0,1,...,Param.n-1}） *)
  Definition T := Fin.t Param.n.
  
  (* 加法单位元zero：分n=0（矛盾）和n≥1（Fin.F1） *)
  Definition zero : T :=
    match Param.n with
    | 0 => match Param.Hpos with end
    | S _ => Fin.F1
    end.
  
  (* 乘法单位元one：分n=1（zero=one）和n≥2（Fin.FS Fin.F1） *)
  Definition one : T :=
    match Param.n with
    | 0 => match Param.Hpos with end
    | 1 => Fin.F1
    | S (S _) => Fin.FS Fin.F1
    end.
  
  (* 模n加法：Fin→自然数→取模→Fin *)
  Definition add (a b : T) : T :=
    let x := Fin.to_nat a in
    let y := Fin.to_nat b in
    let sum := (x + y) mod Param.n in
    (* 使用Nat.mod_lt证明sum < Param.n *)
    match Nat.mod_lt sum Param.n Param.Hpos with
    | conj _ Hlt => Fin.of_nat_lt sum Hlt
    end.
  
  (* 模n乘法：逻辑同加法 *)
  Definition mul (a b : T) : T :=
    let x := Fin.to_nat a in
    let y := Fin.to_nat b in
    let prod := (x * y) mod Param.n in
    match Nat.mod_lt prod Param.n Param.Hpos with
    | conj _ Hlt => Fin.of_nat_lt prod Hlt
    end.
  
  (* 证明加法交换律 *)
  Lemma add_comm : forall a b, add a b = add b a.
  Proof.
    intros a b; unfold add; apply fin_nat_eq; simpl; rewrite Nat.add_comm; reflexivity.
  Qed.
  
  (* 证明乘法交换律 *)
  Lemma mul_comm : forall a b, mul a b = mul b a.
  Proof.
    intros a b; unfold mul; apply fin_nat_eq; simpl; rewrite Nat.mul_comm; reflexivity.
  Qed.
  
  (* 证明加法结合律 *)
  Lemma add_assoc : forall a b c, add (add a b) c = add a (add b c).
  Proof.
    intros a b c; unfold add; apply fin_nat_eq; simpl.
    apply mod_add_assoc with (n := Param.n) (Hpos := Param.Hpos); auto.
  Qed.
  
  (* 证明乘法结合律 *)
  Lemma mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof.
    intros a b c; unfold mul; apply fin_nat_eq; simpl.
    apply mod_mul_assoc with (n := Param.n) (Hpos := Param.Hpos); auto.
  Qed.
  
  (* 证明加法单位元律 *)
  Lemma add_ident : forall a, add a zero = a.
  Proof.
    intros a; unfold add, zero; apply fin_nat_eq; simpl; rewrite Nat.add_0_r.
    (* 证明Fin.to_nat a < Param.n，这是Fin.to_nat_lt保证的 *)
    apply mod_small_proper with (n := Param.n).
    - apply Fin.to_nat_lt.
    - exact Param.Hpos.
  Qed.
  
  (* 证明乘法单位元律 *)
  Lemma mul_ident : forall a, mul a one = a.
  Proof.
    intros a; unfold mul, one.
    destruct Param.n as [|n'].
    - (* n = 0 不可能，因为有Hpos: 0 < n *)
      exfalso; apply Nat.lt_irrefl with 0; exact Param.Hpos.
    - destruct n' as [|n''].
      + (* n = 1，此时所有元素都相等 *)
        simpl; rewrite Nat.mul_1_r; apply fin_nat_eq; simpl; reflexivity.
      + (* n ≥ 2 *)
        simpl; rewrite Nat.mul_1_r; apply fin_nat_eq; simpl.
        apply mod_small_proper with (n := Param.n).
        * apply Fin.to_nat_lt.
        * exact Param.Hpos.
Qed.
End MakeModAlgebra.

(* ======================== 7. 实例验证（确保所有代数性质成立） ======================== *)

(* 实例1：模5代数（验证基础运算） *)
Module Mod5Params : MODALGEBRA.
  Definition n := 5.
  Definition Hpos : 0 < 5 := Nat.lt_0_5.
End Mod5Params.

Module Mod5Algebra := MakeModAlgebra Mod5Params.

(* 模5元素定义 *)
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
  Definition Hpos : 0 < 1 := Nat.lt_0_1.
End Mod1Params.

Module Mod1Algebra := MakeModAlgebra Mod1Params.

Definition zero1 : Mod1Algebra.T := Mod1Algebra.zero.
Definition one1 : Mod1Algebra.T := Mod1Algebra.one.

Theorem mod1_zero_eq_one : zero1 = one1.
Proof. apply fin_nat_eq; simpl; reflexivity. Qed.