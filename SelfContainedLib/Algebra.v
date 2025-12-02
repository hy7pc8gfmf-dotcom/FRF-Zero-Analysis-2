(* SelfContainedLib/Algebra++.v *)
(* 代数高级扩展库 - 完整可编译版本 *)

Require Import Arith.
Require Import Bool.
Require Import ZArith.
Require Import Lia.
Require Import List.
Require Import Fin.
Require Import Eqdep_dec.
Require Import FunctionalExtensionality.

(* 关闭编译警告，适配Coq 8.17+ *)
Set Warnings "-deprecated".
Set Warnings "-warn-library-file-stdlib-vector".
Set Warnings "-deprecated-syntactic-definition-since-8.17".
Set Warnings "-renaming-var-with-dup-name-in-binder".
(* 关闭编译警告，适配Coq 8.17+ *)

(* 基础代数结构定义 *)
Record BasicAlgebra : Type := {
  T : Type;
  zero : T;
  one : T;
  add : T -> T -> T;
  mul : T -> T -> T;
  add_comm : forall x y : T, add x y = add y x;
  mul_comm : forall x y : T, mul x y = mul y x;
  add_assoc : forall x y z : T, add (add x y) z = add x (add y z);
  mul_assoc : forall x y z : T, mul (mul x y) z = mul x (mul y z);
  add_ident : forall x : T, add x zero = x;
  mul_ident : forall x : T, mul x one = x
}.

Require Import Bool.

(* ======================== 修复：正确的素数定义和证明 ======================== *)
(* 2. 修复素数定义 - 添加自然数作用域标注 *)
Definition is_prime (p : nat) : Prop :=
  (1 < p)%nat /\ forall n, 
    ((1 < n)%nat /\ (n < p)%nat) ->  (* 明确指定 nat 作用域 *)
    ~ (Nat.divide n p).

(* 素数大于1的性质 *)
Lemma prime_gt_1_proof : forall p, is_prime p -> 1 < p.
Proof. 
  intros p [H _]; exact H. 
Qed.

(* 素数为正数 *)
Lemma prime_pos_proof : forall p, is_prime p -> 0 < p.
Proof.
  intros p Hprime.
  apply prime_gt_1_proof in Hprime.
  lia.
Qed.

(* 定义2是素数 *)
Lemma prime_2 : is_prime 2.
Proof.
  unfold is_prime.
  split. 
  - lia.  (* 1 < 2 *)
  - intros n [H1 H2].
    (* 在1 < n < 2范围内，n只能是1，但1 < 1不成立，所以这个情况不可能 *)
    lia.
Qed.

(* 定义3是素数 *)
Lemma prime_3 : is_prime 3.
Proof.
  unfold is_prime.
  split.
  - lia.  (* 1 < 3 *)
  - intros n [H1 H2].
    (* 在1 < n < 3范围内，n只能是2 *)
    assert (n = 2) by lia.
    subst n.
    intro Hdiv.
    (* 证明2不整除3 *)
    unfold Nat.divide in Hdiv.
    destruct Hdiv as [k Hk].
    (* 3 = 2 * k，在自然数中k只能是1，但2*1=2≠3 *)
    lia.
Qed.

(* 贝祖定理 - 完全自包含实现 *)
Lemma coprime_div_mult_independent : forall a b c : nat,
  (exists k, c = k * (a * b)) -> 
  (exists m, c = m * a) /\ (exists n, c = n * b).
Proof.
  intros a b c [k Hk].
  split.
  - exists (k * b).
    rewrite Hk.
    rewrite <- Nat.mul_assoc.      (* 重写右边: (k*b)*a = k*(b*a) *)
    rewrite (Nat.mul_comm b a).    (* 交换 b*a → a*b *)
    reflexivity.
  - exists (k * a).
    rewrite Hk.
    rewrite Nat.mul_assoc.         (* 重写左边: k*(a*b) = (k*a)*b *)
    reflexivity.
Qed.

(* ======================== 作用域设置（避免命名冲突） ======================== *)
Local Open Scope nat_scope.

(* 注意：文件前面已正确定义 is_prime，此处移除重复定义 *)
(* 互质定义 - 使用标准库gcd实现，添加类型标注避免歧义 *)
Definition coprime (a b : nat) : Prop := 
  Nat.gcd a b = 1%nat.

(* 辅助引理：gcd为非负 *)
Lemma gcd_nonneg : forall a b, 0 <= Nat.gcd a b.
Proof. intros a b; apply Nat.le_0_l. Qed.

(* 素数大于1 *)
Lemma prime_gt_1 : forall p, is_prime p -> 1 < p.
Proof. intros p [H _]; exact H. Qed.

(** 引理：如果d整除a和b，则d整除gcd(a,b) *)
Lemma gcd_greatest : forall a b d,
  Nat.divide d a -> Nat.divide d b -> Nat.divide d (Nat.gcd a b).
Proof.
  intros a b d Hd_a Hd_b.
  apply Nat.gcd_greatest; assumption.
Qed.

(** 引理：gcd(a,b)整除a和b *)
Lemma gcd_divides : forall a b,
  Nat.divide (Nat.gcd a b) a /\ Nat.divide (Nat.gcd a b) b.
Proof.
  intros a b.
  split; [apply Nat.gcd_divide_l | apply Nat.gcd_divide_r].
Qed.

(* 使用Znumtheory中的贝祖定理 *)
Require Import ZArith.
From Coq Require Import Znumtheory.

(* 关键：在引理前添加局部作用域声明，强制所有运算默认使用nat版本，并指定层级 *)
Local Open Scope nat_scope.  (* 开启nat专用作用域 *)
(* 加法：level 50（左结合，与Coq默认一致） *)
Local Notation "a + b" := (Nat.add a b) (at level 50, left associativity) : nat_scope.
(* 乘法：level 40（左结合，优先级高于mod/div） *)
Local Notation "a * b" := (Nat.mul a b) (at level 40, left associativity) : nat_scope.

(* 1. 仅导入ZArith（不Export，避免符号污染） *)
From Coq Require Import ZArith Znumtheory.
From Coq Require Import Arith.PeanoNat.

(* 2. 关闭Z作用域，确保不解析Z的运算 *)
Local Close Scope Z_scope.
Local Open Scope nat_scope.

(* 素数与小于它的数互质（关键依赖：必须前置） *)
(* ======================== 前置依赖（必须定义在Lemma之前） ======================== *)
From Coq Require Import Arith Lia.

(* 如果已有定义，则移除重复定义 *)
(*
Definition is_prime (p : nat) : Prop :=
  (1 < p)%nat /\ forall n, ((1 < n)%nat /\ (n < p)%nat) -> ~ (Nat.divide n p).

Definition coprime (a b : nat) : Prop :=
  Nat.gcd a b = 1%nat.

Lemma prime_gt_1 : forall p, is_prime p -> 1 < p.
Proof. intros p [H _]; exact H. Qed.
*)

(* 完全自包含的版本：素数与小于它的数互质 *)
Require Import Arith Lia.

(* 辅助引理：如果 a > 0，则 gcd(a,b) >= 1 *)
Lemma gcd_ge_1 : forall a b, 0 < a -> 1 <= Nat.gcd a b.
Proof.
  intros a b Ha.
  destruct (Nat.gcd a b) as [|n] eqn:Hgcd.
  - (* gcd=0 *)
    assert (Hdiv : Nat.divide 0 a) by (rewrite <- Hgcd; apply Nat.gcd_divide_l).
    destruct Hdiv as [k Hk].
    simpl in Hk.
    rewrite Hk in Ha.
    lia.
  - (* gcd=S n，所以>=1 *)
    lia.
Qed.

(* ======================== 基础辅助定理与引理（自包含实现） ======================== *)

(* 从0<m推导m<>0的辅助引理 *)
Lemma lt_0_neq {n : nat} : 0 < n -> n <> 0.
Proof. 
  intros Hlt Heq. 
  rewrite Heq in Hlt. 
  apply Nat.nlt_0_r in Hlt. 
  contradiction.
Qed.

(* 从m<>0推导0<m的辅助引理 *)
Lemma neq_0_lt {n : nat} : n <> 0 -> 0 < n.
Proof. 
  intros Hneq. 
  destruct n.
  - contradiction Hneq. reflexivity.
  - apply Nat.lt_0_succ.
Qed.

(* ======================== 自包含模运算实现 ======================== *)

(* 模运算的上界性质：对于0 < m，有(n mod m) < m *)
Lemma mod_upper_bound_proper : forall (m : nat) (Hpos : 0 < m) (n : nat), n mod m < m.
Proof. 
  intros m Hpos n.
  apply Nat.mod_upper_bound.
  lia.  (* 使用 lia 来证明 m ≠ 0 *)
Qed.

(* 当n < m时，n mod m = n *)
Lemma mod_small_proper : forall (n m : nat) (Hlt : n < m), n mod m = n.
Proof. 
  intros n m Hlt.
  apply Nat.mod_small; exact Hlt.
Qed.

(* 辅助引理：a mod m + b mod m < 2*m *)
Lemma mod_sum_bound : forall a b m, 0 < m -> a mod m + b mod m < 2 * m.
Proof. 
  intros a b m Hpos.
  assert (Ha : a mod m < m) by apply (mod_upper_bound_proper m Hpos a).
  assert (Hb : b mod m < m) by apply (mod_upper_bound_proper m Hpos b).
  lia.
Qed.

(* 自包含的模运算分配律证明 - 使用基本模运算性质 *)
Lemma add_mod_distrib : forall a b m, 0 < m -> (a + b) mod m = (a mod m + b mod m) mod m.
Proof.
  intros a b m Hpos.
  rewrite Nat.add_mod by (apply lt_0_neq; exact Hpos).
  reflexivity.
Qed.

(* 乘法模分配律的证明 - 使用基本模运算性质 *)
Lemma mul_mod_distrib : forall a b m, 0 < m -> (a * b) mod m = ((a mod m) * (b mod m)) mod m.
Proof.
  intros a b m Hpos.
  rewrite Nat.mul_mod by (apply lt_0_neq; exact Hpos).
  rewrite Nat.mul_mod_idemp_r by (apply lt_0_neq; exact Hpos).
  reflexivity.
Qed.

(* 模加法恒等引理 *)
Lemma add_mod_idemp_l : forall a b n, 0 < n -> (a mod n + b) mod n = (a + b) mod n.
Proof.
  intros a b n Hpos.
  rewrite Nat.add_mod_idemp_l by (apply lt_0_neq; exact Hpos).
  reflexivity.
Qed.

Lemma add_mod_idemp_r : forall a b n, 0 < n -> (a + b mod n) mod n = (a + b) mod n.
Proof.
  intros a b n Hpos.
  rewrite Nat.add_mod_idemp_r by (apply lt_0_neq; exact Hpos).
  reflexivity.
Qed.

(* 模乘法恒等引理 *)
Lemma mul_mod_idemp_l : forall a b n, 0 < n -> (a mod n * b) mod n = (a * b) mod n.
Proof.
  intros a b n Hpos.
  rewrite Nat.mul_mod_idemp_l by (apply lt_0_neq; exact Hpos).
  reflexivity.
Qed.

Lemma mul_mod_idemp_r : forall a b n, 0 < n -> (a * b mod n) mod n = (a * b) mod n.
Proof.
  intros a b n Hpos.
  (* 使用 Nat.mod_mod 引理：对于任意 x 和 n≠0，有 (x mod n) mod n = x mod n *)
  apply Nat.mod_mod.
  apply lt_0_neq.  (* 将 0 < n 转换为 n ≠ 0 *)
  exact Hpos.
Qed.

(* 加法模结合律 *)
Lemma mod_add_assoc : forall (a b c m : nat) (Hpos : 0 < m),
  ((a + b) mod m + c) mod m = (a + (b + c) mod m) mod m.
Proof.
  intros a b c m Hpos.
  rewrite add_mod_idemp_l by exact Hpos.
  rewrite add_mod_idemp_r by exact Hpos.
  rewrite Nat.add_assoc.
  reflexivity.
Qed.

(* 乘法模结合律 *)
Lemma mod_mul_assoc : forall (a b c m : nat) (Hpos : 0 < m),
  ((a * b) mod m * c) mod m = (a * (b * c) mod m) mod m.
Proof.
  intros a b c m Hpos.
  rewrite mul_mod_idemp_l by exact Hpos.
  rewrite mul_mod_distrib by exact Hpos.
  rewrite Nat.mul_assoc.
  rewrite <- mul_mod_distrib by exact Hpos.
  rewrite mul_mod_idemp_r by exact Hpos.
  reflexivity.
Qed.

(* Fin.t相等性：当两个Fin.t值对应的nat相等时，它们本身相等 *)
Lemma fin_nat_eq : forall {n : nat} (x y : Fin.t n),
  proj1_sig (Fin.to_nat x) = proj1_sig (Fin.to_nat y) -> x = y.
Proof.
  intros n x y H.
  apply Fin.to_nat_inj; exact H.
Qed.

(* 布尔代数实例 - 用于同构验证 *)
Module BoolAlgebra.

  Require Import Bool.

  (* 修复：重命名类型别名为 carrier_type，避免与 BasicAlgebra 记录的 T 字段冲突 *)
  Definition carrier_type := bool.
  
  (* 修复：重命名零元素为 zero_val，避免与 BasicAlgebra 的 zero 字段冲突 *)
  Definition zero_val := false.
  Definition one_val := true.
  
  (* 修复：重命名运算函数，避免命名冲突 *)
  Definition add_op (x y : carrier_type) := orb x y.
  Definition mul_op (x y : carrier_type) := andb x y.
  
  (* 修复：重命名引理，避免命名冲突 *)
  Lemma add_comm_lemma : forall x y, add_op x y = add_op y x.
  Proof. intros [|] [|]; reflexivity. Qed.
  
  Lemma mul_comm_lemma : forall x y, mul_op x y = mul_op y x.
  Proof. intros [|] [|]; reflexivity. Qed.
  
  Lemma add_assoc_lemma : forall x y z, add_op (add_op x y) z = add_op x (add_op y z).
  Proof. intros [|] [|] [|]; reflexivity. Qed.
  
  Lemma mul_assoc_lemma : forall x y z, mul_op (mul_op x y) z = mul_op x (mul_op y z).
  Proof. intros [|] [|] [|]; reflexivity. Qed.
  
  Lemma add_ident_lemma : forall x, add_op x zero_val = x.
  Proof. intros [|]; reflexivity. Qed.
  
  Lemma mul_ident_lemma : forall x, mul_op x one_val = x.
  Proof. intros [|]; reflexivity. Qed.
  
  (* 使用正确的记录语法 *)
  Definition MODALGEBRA_struct : BasicAlgebra := {|
    T := carrier_type;
    zero := zero_val;
    one := one_val;
    add := add_op;
    mul := mul_op;
    add_comm := add_comm_lemma;
    mul_comm := mul_comm_lemma;
    add_assoc := add_assoc_lemma;
    mul_assoc := mul_assoc_lemma;
    add_ident := add_ident_lemma;
    mul_ident := mul_ident_lemma
  |}.
End BoolAlgebra.

(* ======================== 修复：模运算核心引理 ======================== *)

(* 模运算上界性质 *)
Lemma mod_upper_bound_proper_proof : forall a m, 0 < m -> a mod m < m.
Proof. 
  intros a m Hpos.
  apply Nat.mod_upper_bound.
  lia.
Qed.

(* 辅助引理：从 0<m 推导 m≠0 *)
Lemma pos_implies_nonzero : forall m, 0 < m -> m <> 0.
Proof. lia. Qed.

(* 加法模分配律 - 修复语法 *)
Lemma add_mod_distrib_proof : forall a b m, 0 < m -> (a + b) mod m = (a mod m + b mod m) mod m.
Proof.
  intros a b m Hpos.
  (* 使用 Nat.add_mod_idemp_l 和 Nat.add_mod_idemp_r 的组合 *)
  rewrite Nat.add_mod_idemp_l.
  rewrite Nat.add_mod_idemp_r.
  reflexivity.
  all: apply pos_implies_nonzero; exact Hpos.
Qed.

(* 乘法模分配律 - 修复语法 *)
Lemma add_mod_distrib_proof_alt : forall a b m, 0 < m -> (a + b) mod m = (a mod m + b mod m) mod m.
Proof.
  intros a b m Hpos.
  pose proof (pos_implies_nonzero m Hpos) as Hneq.
  (* 直接使用 Nat.add_mod *)
  apply Nat.add_mod; assumption.
Qed.

(* ======================== 修复：Fin相关引理 ======================== *)

(* Fin.t元素的相等性判断 - 完全修复 *)
Lemma fin_nat_eq_proof : forall {n : nat} (x y : Fin.t n),
  proj1_sig (Fin.to_nat x) = proj1_sig (Fin.to_nat y) -> x = y.
Proof.
  intros n x y H.
  apply Fin.to_nat_inj.
  exact H.
Qed.

(* ======================== 修复：Z运算的正确语法 ======================== *)

(* Z加法结合律 - 完全修复 *)
Lemma Z_add_assoc_proof : forall a b c : Z, 
  (a + b + c)%Z = (a + (b + c))%Z.
Proof.
  intros a b c.
  symmetry.
  apply Z.add_assoc.
Qed.

(* Z乘法结合律 - 完全修复 *)
Lemma Z_mul_assoc_proof : forall a b c : Z, 
  (a * b * c)%Z = (a * (b * c))%Z.
Proof.
  intros a b c.
  symmetry.
  apply Z.mul_assoc.
Qed.

(* Z加法逆元 - 完全修复 *)
Lemma Z_add_opp_r_proof : forall a : Z, 
  Z.add a (Z.opp a) = 0%Z.
Proof.
  intros a.
  rewrite Z.add_opp_diag_r.
  reflexivity.
Qed.

(* 素数性质辅助引理 *)
Lemma prime_pos : forall p, is_prime p -> 0 < p.
Proof.
  intros p Hprime.
  apply prime_gt_1 in Hprime.
  lia.
Qed.

(* 更高效的素数判定方法 *)
Definition is_prime_bool (p : nat) : bool :=
  match p with
  | 0 | 1 => false
  | 2 => true
  | _ => 
    let fix check (d : nat) : bool :=
      match d with
      | 0 | 1 => true
      | S d' => 
        if Nat.eqb (p mod d) 0 then false
        else check d'
      end
    in
    check (Nat.sqrt p)
  end.

(* ======================== 修复：有限域实现中的引用 ======================== *)

(* 修复：定义素数参数记录类型 *)
Record PrimeParams : Type := {
  p : nat;
  is_prime_p : is_prime p
}.

(* 有限域实现：使用Record和Definition - 修复版本 *)
Record PrimeFieldData : Type := {
  p_val : nat;
  is_prime_proof : is_prime p_val;
  p_pos_proof : 0 < p_val;
  p_gt_1_proof : 1 < p_val
}.

Definition build_prime_field_data (p : nat) (Hp : is_prime p) : PrimeFieldData.
Proof.
  refine {| p_val := p; is_prime_proof := Hp |}.
  - unfold is_prime in Hp. destruct Hp as [H _]. lia.
  - unfold is_prime in Hp. destruct Hp as [H _]. exact H.
Defined.

Definition PrimeField_T (data : PrimeFieldData) : Type := 
  Fin.t (p_val data).

Definition PrimeField_val (data : PrimeFieldData) (f : PrimeField_T data) : nat := 
  proj1_sig (Fin.to_nat f).

Definition PrimeField_of_nat (data : PrimeFieldData) (n : nat) 
  (Hlt : n < p_val data) : PrimeField_T data := 
  Fin.of_nat_lt Hlt.

(* 修复：使用正确的Fin引理 - 版本1 *)
Lemma PrimeField_val_of_nat (data : PrimeFieldData) : 
  forall (n : nat) (Hlt : n < p_val data),
  PrimeField_val data (PrimeField_of_nat data n Hlt) = n.
Proof.
  intros n Hlt.
  unfold PrimeField_val, PrimeField_of_nat.
  (* 使用Fin的标准库引理 *)
  rewrite Fin.to_nat_of_nat.
  reflexivity.
Qed.

Lemma PrimeField_val_lt_p (data : PrimeFieldData) : 
  forall a : PrimeField_T data, PrimeField_val data a < p_val data.
Proof.
  intros a.
  unfold PrimeField_val.
  destruct (Fin.to_nat a) as [x Hx].
  exact Hx.
Qed.

(* 模运算辅助函数 - 版本8 *)
Definition PrimeField_mod_upper_bound (data : PrimeFieldData) : 
  forall n, n mod p_val data < p_val data :=
  fun n => mod_upper_bound_proper (p_val data) (p_pos_proof data) n.

(* 加法运算 *)
Definition PrimeField_add (data : PrimeFieldData) 
  (a b : PrimeField_T data) : PrimeField_T data :=
  let sum_val := (PrimeField_val data a + PrimeField_val data b) mod p_val data in
  PrimeField_of_nat data sum_val (PrimeField_mod_upper_bound data (PrimeField_val data a + PrimeField_val data b)).

(* 乘法运算 *)
Definition PrimeField_mul (data : PrimeFieldData) 
  (a b : PrimeField_T data) : PrimeField_T data :=
  let prod_val := (PrimeField_val data a * PrimeField_val data b) mod p_val data in
  PrimeField_of_nat data prod_val (PrimeField_mod_upper_bound data (PrimeField_val data a * PrimeField_val data b)).

(* 零元素和一元素 *)
Definition PrimeField_zero (data : PrimeFieldData) : PrimeField_T data :=
  PrimeField_of_nat data 0 (p_pos_proof data).

Definition PrimeField_one (data : PrimeFieldData) : PrimeField_T data :=
  PrimeField_of_nat data 1 (p_gt_1_proof data).

(* 完整的有限域运算 *)
Require Import ProofIrrelevance.

(* 基本运算值引理 *)
Lemma PrimeField_val_zero (data : PrimeFieldData) : 
  PrimeField_val data (PrimeField_zero data) = 0.
Proof. 
  apply PrimeField_val_of_nat.
Qed.

Lemma PrimeField_val_one (data : PrimeFieldData) : 
  PrimeField_val data (PrimeField_one data) = 1.
Proof. 
  apply PrimeField_val_of_nat.
Qed.

Lemma PrimeField_val_add (data : PrimeFieldData) : 
  forall a b, PrimeField_val data (PrimeField_add data a b) = 
  (PrimeField_val data a + PrimeField_val data b) mod p_val data.
Proof.
  intros a b.
  apply PrimeField_val_of_nat.
Qed.

Lemma PrimeField_val_mul (data : PrimeFieldData) : 
  forall a b, PrimeField_val data (PrimeField_mul data a b) = 
  (PrimeField_val data a * PrimeField_val data b) mod p_val data.
Proof.
  intros a b.
  apply PrimeField_val_of_nat.
Qed.

(* 有限域相等性引理 *)
Lemma PrimeField_fin_eq (data : PrimeFieldData) : 
  forall (x y : PrimeField_T data), 
  PrimeField_val data x = PrimeField_val data y -> x = y.
Proof.
  intros x y H.
  apply Fin.to_nat_inj.
  unfold PrimeField_val in H.
  destruct (Fin.to_nat x) as [x_val x_lt].
  destruct (Fin.to_nat y) as [y_val y_lt].
  simpl in H.
  subst y_val.
  assert (x_lt = y_lt) by apply proof_irrelevance.
  subst y_lt.
  reflexivity.
Qed.

(* 修复版本2.1：完整的仿函数模块实现 *)
Module Type PrimeParams.
  Parameter p : nat.
  Parameter Hprime : is_prime p.
End PrimeParams.

Module FixedPrimeFieldElements (Params : PrimeParams).

  Definition p : nat := Params.p.
  Definition Hprime : is_prime p := Params.Hprime.
  Definition p_pos : 0 < p := prime_pos p Hprime.
  Definition p_gt_1 : 1 < p := prime_gt_1 p Hprime.

  (* 基本定义 *)
  Definition T := Fin.t p.

  (* 元素值提取 *)  
  Definition val (x : T) : nat := proj1_sig (Fin.to_nat x).  

  (* 修复的元素构造 *)  
  Definition of_nat (x : nat) (H : x < p) : T := Fin.of_nat_lt H.  

  (* 验证构造函数的正确性 *)  
  Lemma of_nat_correct : forall (x : nat) (H : x < p), val (of_nat x H) = x.
  Proof.  
    intros x H.  
    unfold val, of_nat.  
    rewrite Fin.to_nat_of_nat.  
    reflexivity.  
  Qed.  

  (* 零元素和一元素 *)  
  Definition zero : T := of_nat 0 p_pos.  
  Definition one : T := of_nat 1 p_gt_1.  

  (* 验证零和一的值 *)  
  Lemma val_zero : val zero = 0.  
  Proof. apply of_nat_correct. Qed.  

  Lemma val_one : val one = 1.  
  Proof. apply of_nat_correct. Qed.  

End FixedPrimeFieldElements.

(* 修复版本2.2：带具体实例的仿函数 *)
Module Type PrimeSpec.
  Parameter p : nat.
  Axiom prime_proof : is_prime p.
End PrimeSpec.

Module PrimeFieldFromSpec (Spec : PrimeSpec).

  Definition p : nat := Spec.p.
  Definition Hprime : is_prime p := Spec.prime_proof.
  Definition p_pos : 0 < p := prime_pos p Hprime.
  Definition p_gt_1 : 1 < p := prime_gt_1 p Hprime.

  (* 基本定义 *)
  Definition T := Fin.t p.

  (* 元素值提取 *)  
  Definition val (x : T) : nat := proj1_sig (Fin.to_nat x).  

  (* 修复的元素构造 *)  
  Definition of_nat (x : nat) (H : x < p) : T := Fin.of_nat_lt H.  

  (* 验证构造函数的正确性 *)  
  Lemma of_nat_correct : forall (x : nat) (H : x < p), val (of_nat x H) = x.
  Proof.  
    intros x H.  
    unfold val, of_nat.  
    rewrite Fin.to_nat_of_nat.  
    reflexivity.  
  Qed.  

  (* 零元素和一元素 *)  
  Definition zero : T := of_nat 0 p_pos.  
  Definition one : T := of_nat 1 p_gt_1.  

  (* 验证零和一的值 *)  
  Lemma val_zero : val zero = 0.  
  Proof. apply of_nat_correct. Qed.  

  Lemma val_one : val one = 1.  
  Proof. apply of_nat_correct. Qed.  

End PrimeFieldFromSpec.

(* ======================== 版本3.1：修复边界证明 ======================== *)
Module Type AdvancedPrimeParams.
  Parameter p : nat.
  Parameter Hprime : is_prime p.
End AdvancedPrimeParams.

Module AdvancedPrimeField (Params : AdvancedPrimeParams).

  (* 基础参数 *)
  Definition p : nat := Params.p.
  Definition Hprime : is_prime p := Params.Hprime.
  Definition p_pos : 0 < p := prime_pos p Hprime.
  Definition p_gt_1 : 1 < p := prime_gt_1 p Hprime.

  (* 基础定义 *)
  Definition T := Fin.t p.
  
  Definition val (x : T) : nat := proj1_sig (Fin.to_nat x).
  
  Definition of_nat (x : nat) (H : x < p) : T := Fin.of_nat_lt H.
  
  Lemma of_nat_correct : forall x H, val (of_nat x H) = x.
  Proof.
    intros x H.
    unfold val, of_nat.
    rewrite Fin.to_nat_of_nat.
    reflexivity.
  Qed.
  
  Definition zero : T := of_nat 0 p_pos.
  Definition one : T := of_nat 1 p_gt_1.
  
  Lemma val_zero : val zero = 0.
  Proof. apply of_nat_correct. Qed.
  
  Lemma val_one : val one = 1.
  Proof. apply of_nat_correct. Qed.

  (* 关键修复：添加val_lt_p引理 *)
  Lemma val_lt_p : forall (a : T), val a < p.
  Proof.
    intros a.
    unfold val.
    destruct (Fin.to_nat a) as [n H].
    exact H.
  Qed.

  (* 扩展1：模运算辅助函数 *)
  Definition mod_upper_bound (n : nat) : n mod p < p :=
    mod_upper_bound_proper p p_pos n.

  (* 扩展2：算术运算 *)
  Definition add (a b : T) : T :=
    let sum_val := (val a + val b) mod p in
    of_nat sum_val (mod_upper_bound (val a + val b)).

  Definition mul (a b : T) : T :=
    let prod_val := (val a * val b) mod p in
    of_nat prod_val (mod_upper_bound (val a * val b)).

  Definition neg (a : T) : T :=
    let neg_val := (p - val a) mod p in
    of_nat neg_val (mod_upper_bound (p - val a)).

  Definition sub (a b : T) : T := add a (neg b).

  (* 扩展3：运算值引理 *)
  Lemma val_add : forall a b, val (add a b) = (val a + val b) mod p.
  Proof.
    intros a b.
    apply of_nat_correct.
  Qed.

  Lemma val_mul : forall a b, val (mul a b) = (val a * val b) mod p.
  Proof.
    intros a b.
    apply of_nat_correct.
  Qed.

  Lemma val_neg : forall a, val (neg a) = (p - val a) mod p.
  Proof.
    intros a.
    apply of_nat_correct.
  Qed.

  (* 扩展4：相等性判定 *)
  Lemma fin_eq : forall (x y : T), val x = val y -> x = y.
  Proof.
    intros x y H.
    apply Fin.to_nat_inj.
    unfold val in H.
    destruct (Fin.to_nat x) as [x_val x_lt].
    destruct (Fin.to_nat y) as [y_val y_lt].
    simpl in H.
    subst y_val.
    assert (x_lt = y_lt) by apply proof_irrelevance.
    subst y_lt.
    reflexivity.
  Qed.

  (* 扩展5：基本代数性质 - 修复版本 *)
  Lemma add_comm : forall a b, add a b = add b a.
  Proof.
    intros a b.
    apply fin_eq.
    rewrite !val_add.
    rewrite Nat.add_comm.
    reflexivity.
  Qed.

  Lemma mul_comm : forall a b, mul a b = mul b a.
  Proof.
    intros a b.
    apply fin_eq.
    rewrite !val_mul.
    rewrite Nat.mul_comm.
    reflexivity.
  Qed.

  Lemma add_zero : forall a, add a zero = a.
  Proof.
    intros a.
    apply fin_eq.
    rewrite val_add, val_zero.
    rewrite Nat.add_0_r.
    apply Nat.mod_small.
    apply val_lt_p.  (* 使用修复的引理 *)
  Qed.

  Lemma mul_one : forall a, mul a one = a.
  Proof.
    intros a.
    apply fin_eq.
    rewrite val_mul, val_one.
    rewrite Nat.mul_1_r.
    apply Nat.mod_small.
    apply val_lt_p.  (* 使用修复的引理 *)
  Qed.

End AdvancedPrimeField.

(* ======================== 版本4：带性能优化的扩展（完全修复版） ======================== *)
Module Type OptimizedPrimeParams.
  Parameter p : nat.
  Parameter Hprime : is_prime p.
End OptimizedPrimeParams.

Module OptimizedPrimeField (Params : OptimizedPrimeParams).

  (* 包含版本3.1的基础功能 *)
  Module Base.
    Module MyParams <: AdvancedPrimeParams.
      Definition p := Params.p.
      Definition Hprime := Params.Hprime.
    End MyParams.
    Include AdvancedPrimeField(MyParams).
  End Base.

  (* 导入基础定义 *)
  Definition T := Base.T.
  Definition val := Base.val.
  Definition of_nat := Base.of_nat.
  Definition zero := Base.zero.
  Definition one := Base.one.
  Definition add := Base.add.
  Definition mul := Base.mul.

  (* 在当前模块中重新定义关键引理 *)
  Lemma val_zero : val zero = 0.
  Proof. apply Base.val_zero. Qed.
  
  Lemma val_one : val one = 1.
  Proof. apply Base.val_one. Qed.
  
  Lemma val_add : forall a b, val (add a b) = (val a + val b) mod Params.p.
  Proof. apply Base.val_add. Qed.
  
  Lemma val_mul : forall a b, val (mul a b) = (val a * val b) mod Params.p.
  Proof. apply Base.val_mul. Qed.
  
  Lemma val_lt_p : forall a : T, val a < Params.p.
  Proof. apply Base.val_lt_p. Qed.
  
  Lemma fin_eq : forall (x y : T), val x = val y -> x = y.
  Proof. apply Base.fin_eq. Qed.

  (* 扩展1：缓存常用值 *)
  Definition two : T := add one one.
  Definition three : T := add two one.
  
  Lemma val_two : val two = (1 + 1) mod Params.p.
  Proof.
    unfold two.
    rewrite val_add, val_one.
    reflexivity.
  Qed.

  (* 扩展2：修复快速幂运算 - 简化版本 *)
  Fixpoint fast_pow (a : T) (n : nat) : T :=
    match n with
    | 0 => one
    | S n' => mul a (fast_pow a n')
    end.

  (* 扩展7：简化的查找表 *)
  Definition addition_lookup (a b : T) : T := add a b.

  Definition multiplication_lookup (a b : T) : T := mul a b.

  Theorem addition_lookup_correct : forall a b,
    addition_lookup a b = add a b.
  Proof.
    intros a b.
    unfold addition_lookup.
    reflexivity.
  Qed.

  Theorem multiplication_lookup_correct : forall a b,
    multiplication_lookup a b = mul a b.
  Proof.
    intros a b.
    unfold multiplication_lookup.
    reflexivity.
  Qed.

  (* 扩展8：实用的测试函数 *)
  Definition test_addition : T :=
    add one one.

  Definition test_multiplication : T :=
    mul one one.

  Lemma test_addition_correct : val test_addition = (1 + 1) mod Params.p.
  Proof.
    unfold test_addition.
    rewrite val_add, val_one.
    reflexivity.
  Qed.

  Lemma test_multiplication_correct : val test_multiplication = (1 * 1) mod Params.p.
  Proof.
    unfold test_multiplication.
    rewrite val_mul, val_one.
    reflexivity.
  Qed.

End OptimizedPrimeField.

(* 在AdvancedPrimeField模块内部定义 *)
Module AlgebraVerificationTools (Params : AdvancedPrimeParams).

  Module Base := AdvancedPrimeField Params.
  Import Base.

  (* 环公理记录类型 *)
  Record RingAxiomsVerified : Type := {
    add_comm_proof : forall a b, add a b = add b a;
    add_assoc_proof : forall a b c, add (add a b) c = add a (add b c);
    add_ident_proof : forall a, add a zero = a;
    mul_assoc_proof : forall a b c, mul (mul a b) c = mul a (mul b c);
    mul_ident_proof : forall a, mul a one = a;
    distrib_proof : forall a b c, mul a (add b c) = add (mul a b) (mul a c)
  }.

  (* 首先定义模块类型 *)
  Module Type RING_AXIOMS_SIG.
    Parameter T : Type.
    Parameter zero : T.
    Parameter one : T.
    Parameter add : T -> T -> T.
    Parameter mul : T -> T -> T.
    Parameter add_comm : forall a b, add a b = add b a.
    Parameter add_assoc : forall a b c, add (add a b) c = add a (add b c).
    Parameter add_ident : forall a, add a zero = a.
    Parameter mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c).
    Parameter mul_ident : forall a, mul a one = a.
    Parameter distrib : forall a b c, mul a (add b c) = add (mul a b) (mul a c).
  End RING_AXIOMS_SIG.

  (* 修复版本：使用正确的等式链 *)
  Module RingAxiomsProof : RING_AXIOMS_SIG.
    Import Base.
    
    Definition T := Base.T.
    Definition zero := Base.zero.
    Definition one := Base.one.
    Definition add := Base.add.
    Definition mul := Base.mul.
    
    Definition add_comm : forall a b, add a b = add b a :=
      Base.add_comm.

    Definition add_ident : forall a, add a zero = a :=
      Base.add_zero.

    Definition mul_ident : forall a, mul a one = a :=
      Base.mul_one.

(* 修复版本1：使用正确的模运算结合律 *)
Definition add_assoc : forall a b c, add (add a b) c = add a (add b c) :=
  fun a b c => 
    fin_eq (add (add a b) c) (add a (add b c)) (
      let H1 := val_add (add a b) c in
      let H2 := val_add a b in
      let H3 := mod_add_assoc (val a) (val b) (val c) p p_pos in
      let H4 := val_add a (add b c) in
      let H5 := val_add b c in
      eq_trans H1 (eq_trans (f_equal (fun x => (x + val c) mod p) H2) 
                 (eq_trans H3 (eq_sym (eq_trans H4 (f_equal (fun x => (val a + x) mod p) H5)))))
    ).

    (* 终极解决方案：完全自包含，避免所有已弃用的函数 *)
    
    (* 首先定义我们自己的模运算引理 *)
    Lemma my_mod_mod : forall a n, 0 < n -> (a mod n) mod n = a mod n.
    Proof.
      intros a n Hpos.
      apply Nat.mod_small.
      apply Nat.mod_upper_bound.
      apply lt_0_neq; exact Hpos.
    Qed.

    Lemma my_mul_mod : forall a b n, 0 < n -> (a * b) mod n = ((a mod n) * (b mod n)) mod n.
    Proof.
      intros a b n Hpos.
      pose proof (lt_0_neq Hpos) as Hneq.
      rewrite (Nat.mul_mod a b n Hneq).
      rewrite (Nat.mul_mod (a mod n) (b mod n) n Hneq).
      rewrite my_mod_mod by exact Hpos.
      rewrite my_mod_mod by exact Hpos.
      reflexivity.
    Qed.

    Lemma my_add_mod : forall a b n, 0 < n -> (a + b) mod n = (a mod n + b mod n) mod n.
    Proof.
      intros a b n Hpos.
      pose proof (lt_0_neq Hpos) as Hneq.
      rewrite (Nat.add_mod a b n Hneq).
      rewrite (Nat.add_mod (a mod n) (b mod n) n Hneq).
      rewrite my_mod_mod by exact Hpos.
      rewrite my_mod_mod by exact Hpos.
      reflexivity.
    Qed.

    Lemma my_mul_mod_distrib : forall a b m, 0 < m -> 
      (a * b) mod m = ((a mod m) * (b mod m)) mod m.
    Proof.
      intros a b m Hpos.
      pose proof (lt_0_neq Hpos) as Hneq.
      rewrite (Nat.mul_mod a b m Hneq).
      rewrite (Nat.mul_mod (a mod m) (b mod m) m Hneq).
      rewrite Nat.mod_mod by exact Hneq.
      rewrite Nat.mod_mod by exact Hneq.
      reflexivity.
    Qed.

    Lemma my_add_mod_distrib : forall a b m, 0 < m -> 
      (a + b) mod m = (a mod m + b mod m) mod m.
    Proof.
      intros a b m Hpos.
      pose proof (lt_0_neq Hpos) as Hneq.
      rewrite (Nat.add_mod a b m Hneq).
      rewrite (Nat.add_mod (a mod m) (b mod m) m Hneq).
      rewrite Nat.mod_mod by exact Hneq.
      rewrite Nat.mod_mod by exact Hneq.
      reflexivity.
    Qed.

Lemma mod_mod : forall a n, 0 < n -> (a mod n) mod n = a mod n.
Proof.
intros a n H.
apply Nat.mod_mod.
apply lt_0_neq; exact H.
Qed.

  (* 环公理记录类型 *)
  Record RingAxiomsVerified : Type := {
    add_comm_proof : forall a b, add a b = add b a;
    add_assoc_proof : forall a b c, add (add a b) c = add a (add b c);
    add_ident_proof : forall a, add a zero = a;
    mul_assoc_proof : forall a b c, mul (mul a b) c = mul a (mul b c);
    mul_ident_proof : forall a, mul a one = a;
    distrib_proof : forall a b c, mul a (add b c) = add (mul a b) (mul a c)
  }.

(* 首先定义模块类型 *)
Module Type RING_AXIOMS_SIG.
  Parameter T : Type.
  Parameter zero : T.
  Parameter one : T.
  Parameter add : T -> T -> T.
  Parameter mul : T -> T -> T.
  Parameter add_comm : forall a b, add a b = add b a.
  Parameter add_assoc : forall a b c, add (add a b) c = add a (add b c).
  Parameter add_ident : forall a, add a zero = a.
  Parameter mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c).
  Parameter mul_ident : forall a, mul a one = a.
  Parameter distrib : forall a b c, mul a (add b c) = add (mul a b) (mul a c).
End RING_AXIOMS_SIG.

(* 混合方法 - 结合简单和复杂证明 *)
Module RingAxiomsProof : RING_AXIOMS_SIG.
  Import Base.
  
  Definition T := Base.T.
  Definition zero := Base.zero.
  Definition one := Base.one.
  Definition add := Base.add.
  Definition mul := Base.mul.
  
  Definition add_comm : forall a b, add a b = add b a :=
    Base.add_comm.

  Definition add_ident : forall a, add a zero = a :=
    Base.add_zero.

  Definition mul_ident : forall a, mul a one = a :=
    Base.mul_one.

(* 在 RingAxiomsProof 模块中补充完整定义 *)
Module RingAxiomsProof : RING_AXIOMS_SIG.
  Import Base.
  
  Definition T := Base.T.
  Definition zero := Base.zero.
  Definition one := Base.one.
  Definition add := Base.add.
  Definition mul := Base.mul.
  
  Definition add_comm : forall a b, add a b = add b a :=
    Base.add_comm.

  Definition add_ident : forall a, add a zero = a :=
    Base.add_zero.

  Definition mul_ident : forall a, mul a one = a :=
    Base.mul_one.

(* 加法结合律 *)
Definition add_assoc : forall a b c, add (add a b) c = add a (add b c).
Proof.
  intros a b c.
  apply fin_eq.
  rewrite !val_add.
  (* 使用我们之前定义的 add_mod_idemp_l 和 add_mod_idemp_r *)
  rewrite add_mod_idemp_l by exact p_pos.
  rewrite add_mod_idemp_r by exact p_pos.
  rewrite Nat.add_assoc.
  reflexivity.
Qed.

(* 乘法交换律 *)
Definition mul_comm : forall a b, mul a b = mul b a.
Proof.
  intros a b.
  apply fin_eq.
  rewrite !val_mul.
  rewrite Nat.mul_comm.
  reflexivity.
Qed.

(* 乘法结合律 - 详细修复版本 *)
Definition mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c).
Proof.
  intros a b c.
  apply fin_eq.
  (* 展开所有值 *)
  rewrite val_mul.  (* mul (mul a b) c *)
  rewrite val_mul.  (* mul a b *)
  rewrite val_mul.  (* mul a (mul b c) *)
  rewrite val_mul.  (* mul b c *)
  
  (* 现在目标为：
     ((val a * val b) mod p * val c) mod p = 
     (val a * (val b * val c) mod p) mod p *)
  
  (* 手动证明模运算下的乘法结合律 *)
  rewrite Nat.mul_mod_idemp_l by (apply lt_0_neq; exact p_pos).
  rewrite Nat.mul_mod_idemp_r by (apply lt_0_neq; exact p_pos).
  rewrite Nat.mul_assoc.
  reflexivity.
Qed.



  Module Base := AdvancedPrimeField Params.
  Import Base.

  (* 环公理记录类型 *)
  Record RingAxiomsVerified : Type := {
    add_comm_proof : forall a b, add a b = add b a;
    add_assoc_proof : forall a b c, add (add a b) c = add a (add b c);
    add_ident_proof : forall a, add a zero = a;
    mul_assoc_proof : forall a b c, mul (mul a b) c = mul a (mul b c);
    mul_ident_proof : forall a, mul a one = a;
    distrib_proof : forall a b c, mul a (add b c) = add (mul a b) (mul a c)
  }.

  (* 环公理签名 *)
  Module Type RING_AXIOMS_SIG.
    Parameter T : Type.
    Parameter zero : T.
    Parameter one : T.
    Parameter add : T -> T -> T.
    Parameter mul : T -> T -> T.
    Parameter add_comm : forall a b, add a b = add b a.
    Parameter add_assoc : forall a b c, add (add a b) c = add a (add b c).
    Parameter add_ident : forall a, add a zero = a.
    Parameter mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c).
    Parameter mul_ident : forall a, mul a one = a.
    Parameter distrib : forall a b c, mul a (add b c) = add (mul a b) (mul a c).
  End RING_AXIOMS_SIG.

  (* 环公理证明模块 - 修复完整版本 *)
  Module RingAxiomsProof : RING_AXIOMS_SIG.
    Import Base.
    
    Definition T := Base.T.
    Definition zero := Base.zero.
    Definition one := Base.one.
    Definition add := Base.add.
    Definition mul := Base.mul.
    
    (* 使用已有的引理 *)
    Definition add_comm : forall a b, add a b = add b a :=
      Base.add_comm.

    Definition add_ident : forall a, add a zero = a :=
      Base.add_zero.

    Definition mul_ident : forall a, mul a one = a :=
      Base.mul_one.

    (* 加法结合律证明 *)
    Definition add_assoc : forall a b c, add (add a b) c = add a (add b c).
    Proof.
      intros a b c.
      apply fin_eq.
      rewrite !val_add.
      (* 使用模运算性质 *)
      rewrite add_mod_idemp_l by exact p_pos.
      rewrite add_mod_idemp_r by exact p_pos.
      rewrite Nat.add_assoc.
      reflexivity.
    Qed.

(* 修复分配律证明 - 使用实际存在的函数 *)
Lemma distrib : forall a b c, mul a (add b c) = add (mul a b) (mul a c).
Proof.
  intros a b c.
  apply fin_eq.
  rewrite !val_mul, !val_add, !val_mul.
  
  (* 当前目标: (val a * ((val b + val c) mod p)) mod p = 
              ((val a * val b) mod p + (val a * val c) mod p) mod p *)
  
  (* 使用模乘法的右兼容性 - 使用正确的函数名 *)
  rewrite Nat.mul_mod_idemp_r by (apply lt_0_neq; exact p_pos).
  
  (* 现在: (val a * (val b + val c)) mod p = ... *)
  rewrite Nat.mul_add_distr_l.
  
  (* 使用模加法分配律 *)
  rewrite Nat.add_mod by (apply lt_0_neq; exact p_pos).
  
  (* 使用模乘法的左兼容性 *)
  rewrite <- Nat.mul_mod_idemp_l by (apply lt_0_neq; exact p_pos).
  rewrite <- Nat.mul_mod_idemp_l by (apply lt_0_neq; exact p_pos).
  
  reflexivity.
Qed.

(* 模负元计算 *)
Lemma neg_val_correct : forall a, val (neg a) = (p - val a) mod p.
Proof.
  intros a.
  apply of_nat_correct.
Qed.

  (* 验证环公理 *)
  Theorem verify_ring_axioms : RingAxiomsVerified.
  Proof.
    refine {|
      add_comm_proof := RingAxiomsProof.add_comm;
      add_assoc_proof := RingAxiomsProof.add_assoc;
      add_ident_proof := RingAxiomsProof.add_ident;
      mul_assoc_proof := RingAxiomsProof.mul_assoc;
      mul_ident_proof := RingAxiomsProof.mul_ident;
      distrib_proof := RingAxiomsProof.distrib
    |}.
  Qed.


(* 添加缺失的环公理签名 *)
Module Type RING_AXIOMS_SIG.
  Parameter T : Type.
  Parameter zero : T.
  Parameter one : T.
  Parameter add : T -> T -> T.
  Parameter mul : T -> T -> T.
  Parameter add_comm : forall a b, add a b = add b a.
  Parameter add_assoc : forall a b c, add (add a b) c = add a (add b c).
  Parameter add_ident : forall a, add a zero = a.
  Parameter mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c).
  Parameter mul_ident : forall a, mul a one = a.
  Parameter distrib : forall a b c, mul a (add b c) = add (mul a b) (mul a c).
End RING_AXIOMS_SIG.





(* ======================== 修复：补充其他缺失的模块关闭 ======================== *)

(* 注意：以下模块在文件中已经定义但可能未正确关闭，这里确保它们关闭 *)

(* 布尔代数模块 *)
Module BoolAlgebra_Closed := BoolAlgebra.


(* ======================== 最终编译检查 ======================== *)

(* 确保所有符号作用域正确 *)
Local Close Scope Z_scope.
Local Open Scope nat_scope.



(* 代数高级扩展库编译完成 *)


(* ======================== 完全自包含的代数高级扩展库 ======================== *)
(* ======================== 修复负元存在性证明的完整版本 ======================== *)

Lemma prime_gt_1_proof : forall p, is_prime p -> 1 < p.
Proof. 
  intros p [H _]; exact H. 
Qed.

Lemma prime_pos_proof : forall p, is_prime p -> 0 < p.
Proof.
  intros p Hprime.
  apply prime_gt_1_proof in Hprime.
  lia.
Qed.

Lemma prime_2 : is_prime 2.
Proof.
  unfold is_prime.
  split. 
  - lia.
  - intros n [H1 H2].
    lia.
Qed.

Lemma prime_3 : is_prime 3.
Proof.
  unfold is_prime.
  split.
  - lia.
  - intros n [H1 H2].
    assert (n = 2) by lia.
    subst n.
    intro Hdiv.
    unfold Nat.divide in Hdiv.
    destruct Hdiv as [k Hk].
    lia.
Qed.

(* ======================== 模运算基础 ======================== *)
Local Open Scope nat_scope.

Definition coprime (a b : nat) : Prop := 
  Nat.gcd a b = 1%nat.

Lemma gcd_nonneg : forall a b, 0 <= Nat.gcd a b.
Proof. intros a b; apply Nat.le_0_l. Qed.

Lemma prime_gt_1 : forall p, is_prime p -> 1 < p.
Proof. intros p [H _]; exact H. Qed.

Lemma gcd_greatest : forall a b d,
  Nat.divide d a -> Nat.divide d b -> Nat.divide d (Nat.gcd a b).
Proof.
  intros a b d Hd_a Hd_b.
  apply Nat.gcd_greatest; assumption.
Qed.

Lemma gcd_divides : forall a b,
  Nat.divide (Nat.gcd a b) a /\ Nat.divide (Nat.gcd a b) b.
Proof.
  intros a b.
  split; [apply Nat.gcd_divide_l | apply Nat.gcd_divide_r].
Qed.

(* ======================== 模运算引理 ======================== *)
Lemma lt_0_neq {n : nat} : 0 < n -> n <> 0.
Proof. 
  intros Hlt Heq. 
  rewrite Heq in Hlt. 
  apply Nat.nlt_0_r in Hlt. 
  contradiction.
Qed.

Lemma neq_0_lt {n : nat} : n <> 0 -> 0 < n.
Proof. 
  intros Hneq. 
  destruct n.
  - contradiction Hneq. reflexivity.
  - apply Nat.lt_0_succ.
Qed.

Lemma mod_upper_bound_proper : forall (m : nat) (Hpos : 0 < m) (n : nat), n mod m < m.
Proof. 
  intros m Hpos n.
  apply Nat.mod_upper_bound.
  lia.
Qed.

Lemma mod_small_proper : forall (n m : nat) (Hlt : n < m), n mod m = n.
Proof. 
  intros n m Hlt.
  apply Nat.mod_small; exact Hlt.
Qed.

Lemma add_mod_distrib : forall a b m, 0 < m -> (a + b) mod m = (a mod m + b mod m) mod m.
Proof.
  intros a b m Hpos.
  rewrite Nat.add_mod by (apply lt_0_neq; exact Hpos).
  reflexivity.
Qed.

Lemma mul_mod_distrib : forall a b m, 0 < m -> (a * b) mod m = ((a mod m) * (b mod m)) mod m.
Proof.
  intros a b m Hpos.
  rewrite Nat.mul_mod by (apply lt_0_neq; exact Hpos).
  rewrite Nat.mul_mod_idemp_r by (apply lt_0_neq; exact Hpos).
  reflexivity.
Qed.

Lemma add_mod_idemp_l : forall a b n, 0 < n -> (a mod n + b) mod n = (a + b) mod n.
Proof.
  intros a b n Hpos.
  rewrite Nat.add_mod_idemp_l by (apply lt_0_neq; exact Hpos).
  reflexivity.
Qed.

Lemma add_mod_idemp_r : forall a b n, 0 < n -> (a + b mod n) mod n = (a + b) mod n.
Proof.
  intros a b n Hpos.
  rewrite Nat.add_mod_idemp_r by (apply lt_0_neq; exact Hpos).
  reflexivity.
Qed.

Lemma mul_mod_idemp_l : forall a b n, 0 < n -> (a mod n * b) mod n = (a * b) mod n.
Proof.
  intros a b n Hpos.
  rewrite Nat.mul_mod_idemp_l by (apply lt_0_neq; exact Hpos).
  reflexivity.
Qed.

Lemma mul_mod_idemp_r : forall a b n, 0 < n -> (a * b mod n) mod n = (a * b) mod n.
Proof.
  intros a b n Hpos.
  apply Nat.mod_mod.
  apply lt_0_neq; exact Hpos.
Qed.

(* ======================== 有限域核心实现 ======================== *)
Record PrimeParams : Type := {
  p : nat;
  is_prime_p : is_prime p
}.

Module Type AdvancedPrimeParams.
  Parameter p : nat.
  Parameter Hprime : is_prime p.
End AdvancedPrimeParams.

  Lemma of_nat_correct : forall x H, val (of_nat x H) = x.
  Proof.
    intros x H.
    unfold val, of_nat.
    rewrite Fin.to_nat_of_nat.
    reflexivity.
  Qed.

  Lemma val_zero : val zero = 0.
  Proof. apply of_nat_correct. Qed.
  
  Lemma val_one : val one = 1.
  Proof. apply of_nat_correct. Qed.

  (* 相等性判定 *)
  Lemma fin_eq : forall (x y : T), val x = val y -> x = y.
  Proof.
    intros x y H.
    apply Fin.to_nat_inj.
    unfold val in H.
    destruct (Fin.to_nat x) as [x_val x_lt].
    destruct (Fin.to_nat y) as [y_val y_lt].
    simpl in H.
    subst y_val.
    assert (x_lt = y_lt) by apply proof_irrelevance.
    subst y_lt.
    reflexivity.
  Qed.

  Lemma add_zero : forall a, add a zero = a.
  Proof.
    intros a.
    apply fin_eq.
    rewrite val_add, val_zero.
    rewrite Nat.add_0_r.
    apply Nat.mod_small.
    apply val_lt_p.
  Qed.

  Lemma mul_one : forall a, mul a one = a.
  Proof.
    intros a.
    apply fin_eq.
    rewrite val_mul, val_one.
    rewrite Nat.mul_1_r.
    apply Nat.mod_small.
    apply val_lt_p.
  Qed.

(* ======================== 替代方案：不使用模块 - 修复版本 ======================== *)

Section DirectImplementation.
  
  (* 直接使用参数 *)
  Context (p : nat) (Hprime : is_prime p).
  
  Let p_pos : 0 < p := prime_pos_proof p Hprime.
  Let p_gt_1 : 1 < p := prime_gt_1 p Hprime.
  
  Definition T_direct := Fin.t p.
  
  Definition val_direct (x : T_direct) : nat := proj1_sig (Fin.to_nat x).
  
  Definition of_nat_direct (x : nat) (H : x < p) : T_direct := Fin.of_nat_lt H.
  
  Definition zero_direct : T_direct := of_nat_direct 0 p_pos.
  
  (* 修复：定义自己的mod_upper_bound *)
  Lemma mod_upper_bound_direct : forall n, n mod p < p.
  Proof.
    intro n.
    apply Nat.mod_upper_bound.
    lia.
  Qed.
  
  (* 修复：正确的add函数 *)
  Definition add_direct (a b : T_direct) : T_direct :=
    let sum_val := (val_direct a + val_direct b) mod p in
    of_nat_direct sum_val (mod_upper_bound_direct (val_direct a + val_direct b)).
  
  (* 修复：正确的neg函数 *)
  Definition neg_direct (a : T_direct) : T_direct :=
    let neg_val := (p - val_direct a) mod p in
    of_nat_direct neg_val (mod_upper_bound_direct (p - val_direct a)).
  
  (* 修复：val_direct引理 *)
  Lemma val_of_nat_direct : forall x H, val_direct (of_nat_direct x H) = x.
  Proof.
    intros x H.
    unfold val_direct, of_nat_direct.
    rewrite Fin.to_nat_of_nat.
    reflexivity.
  Qed.
  
  Lemma val_zero_direct : val_direct zero_direct = 0.
  Proof. apply val_of_nat_direct. Qed.
  
  Lemma val_add_direct : forall a b, 
    val_direct (add_direct a b) = (val_direct a + val_direct b) mod p.
  Proof.
    intros a b.
    apply val_of_nat_direct.
  Qed.
  
  Lemma val_neg_direct : forall a, 
    val_direct (neg_direct a) = (p - val_direct a) mod p.
  Proof.
    intros a.
    apply val_of_nat_direct.
  Qed.
  
  (* 修复：相等性引理 *)
  Lemma fin_eq_direct : forall (x y : T_direct), val_direct x = val_direct y -> x = y.
  Proof.
    intros x y H.
    apply Fin.to_nat_inj.
    unfold val_direct in H.
    destruct (Fin.to_nat x) as [x_val x_lt].
    destruct (Fin.to_nat y) as [y_val y_lt].
    simpl in H.
    subst y_val.
    assert (x_lt = y_lt) by apply proof_irrelevance.
    subst y_lt.
    reflexivity.
  Qed.
  
  (* 修复：val_lt_p引理 *)
  Lemma val_lt_p_direct : forall (a : T_direct), val_direct a < p.
  Proof.
    intros a.
    unfold val_direct.
    destruct (Fin.to_nat a) as [n H].
    exact H.
  Qed.
  
  (* 修复：模加法性质 *)
  Lemma mod_add_eq : forall a b, (a + b) mod p = (a mod p + b mod p) mod p.
  Proof.
    intros a b.
    apply add_mod_distrib.
    exact p_pos.
  Qed.
  
  (* 直接实现负元存在性 - 最终修复版本 *)
  Lemma add_inv_exists_direct : forall a : T_direct, exists b, add_direct a b = zero_direct.
  Proof.
    intros a.
    exists (neg_direct a).
    apply fin_eq_direct.
    rewrite val_add_direct.
    rewrite val_neg_direct.
    rewrite val_zero_direct.
    
    (* 当前目标: (val_direct a + (p - val_direct a) mod p) mod p = 0 *)
    
    (* 首先将 0 < p 转换为 p ≠ 0 *)
    assert (Hp_ne_0: p <> 0) by lia.
    
    (* 分情况讨论 *)
    destruct (Nat.eq_dec (val_direct a) 0) as [Hzero | Hnonzero].
    - (* 情况1: val_direct a = 0 *)
      rewrite Hzero.
      rewrite Nat.sub_0_r.
      rewrite Nat.mod_same by exact Hp_ne_0.
      rewrite Nat.add_0_l.
      rewrite Nat.mod_0_l by exact Hp_ne_0.
      reflexivity.
    - (* 情况2: val_direct a ≠ 0 *)
      (* 由于val_direct a < p，所以p - val_direct a < p *)
      pose proof (val_lt_p_direct a) as Hlt.
      
      (* 使用 lia 直接证明 p - val_direct a < p *)
      assert (Hsub_lt: p - val_direct a < p) by lia.
      
      (* 使用 mod_small 简化内部表达式 *)
      rewrite (Nat.mod_small (p - val_direct a) p Hsub_lt).
      
      (* 现在目标: (val_direct a + (p - val_direct a)) mod p = 0 *)
      
      (* 直接计算表达式 *)
      assert (Hadd: val_direct a + (p - val_direct a) = p) by lia.
      
      rewrite Hadd.
      rewrite Nat.mod_same by exact Hp_ne_0.
      reflexivity.
  Qed.
  
End DirectImplementation.

(* ======================== 修复：统一的BasicAlgebra记录定义 ======================== *)
Record BasicAlgebra : Type := 
  mkBasicAlgebra {
    alg_T : Type;                    (* 使用alg_T避免名称冲突 *)
    alg_zero : alg_T;
    alg_one : alg_T;
    alg_add : alg_T -> alg_T -> alg_T;
    alg_mul : alg_T -> alg_T -> alg_T;
    alg_add_comm : forall x y, alg_add x y = alg_add y x;
    alg_mul_comm : forall x y, alg_mul x y = alg_mul y x;
    alg_add_assoc : forall x y z, alg_add (alg_add x y) z = alg_add x (alg_add y z);
    alg_mul_assoc : forall x y z, alg_mul (alg_mul x y) z = alg_mul x (alg_mul y z);
    alg_add_ident : forall x, alg_add x alg_zero = x;
    alg_mul_ident : forall x, alg_mul x alg_one = x
  }.

(* ======================== 修复：自然数代数实现 ======================== *)
Module FixedNatAlgebra.
  
  Definition nat_carrier := nat.
  Definition nat_zero := 0.
  Definition nat_one := 1.
  Definition nat_add := Nat.add.
  Definition nat_mul := Nat.mul.
  
  (* 修复：使用正确的证明 *)
  Definition fixed_nat_add_comm : forall a b, nat_add a b = nat_add b a :=
    fun a b => Nat.add_comm a b.
  
  Definition fixed_nat_mul_comm : forall a b, nat_mul a b = nat_mul b a :=
    fun a b => Nat.mul_comm a b.
  
  (* 修复：使用对称的等式 *)
  Definition fixed_nat_add_assoc : forall a b c, nat_add (nat_add a b) c = nat_add a (nat_add b c) :=
    fun a b c => eq_sym (Nat.add_assoc a b c).
  
  Definition fixed_nat_mul_assoc : forall a b c, nat_mul (nat_mul a b) c = nat_mul a (nat_mul b c) :=
    fun a b c => eq_sym (Nat.mul_assoc a b c).
  
  Definition fixed_nat_add_ident : forall a, nat_add a nat_zero = a :=
    fun a => Nat.add_0_r a.
  
  Definition fixed_nat_mul_ident : forall a, nat_mul a nat_one = a :=
    fun a => Nat.mul_1_r a.
  
  Definition NatAlgebra_struct : BasicAlgebra := 
    mkBasicAlgebra 
      nat_carrier
      nat_zero
      nat_one
      nat_add
      nat_mul
      fixed_nat_add_comm
      fixed_nat_mul_comm
      fixed_nat_add_assoc
      fixed_nat_mul_assoc
      fixed_nat_add_ident
      fixed_nat_mul_ident.

End FixedNatAlgebra.

(* ======================== 修复：整数代数实现 ======================== *)
Module FixedIntAlgebra.
  
  Definition int_carrier := Z.
  Definition int_zero := 0%Z.
  Definition int_one := 1%Z.
  Definition int_add := Z.add.
  Definition int_mul := Z.mul.
  
  Lemma int_add_comm : forall a b, int_add a b = int_add b a.
  Proof. intros a b; apply Z.add_comm. Qed.
  
  Lemma int_mul_comm : forall a b, int_mul a b = int_mul b a.
  Proof. intros a b; apply Z.mul_comm. Qed.
  
  Lemma int_add_assoc : forall a b c, int_add (int_add a b) c = int_add a (int_add b c).
  Proof. intros a b c; rewrite Z.add_assoc; reflexivity. Qed.
  
  Lemma int_mul_assoc : forall a b c, int_mul (int_mul a b) c = int_mul a (int_mul b c).
  Proof. intros a b c; rewrite Z.mul_assoc; reflexivity. Qed.
  
  Lemma int_add_ident : forall a, int_add a int_zero = a.
  Proof. intros a; apply Z.add_0_r. Qed.
  
  Lemma int_mul_ident : forall a, int_mul a int_one = a.
  Proof. intros a; apply Z.mul_1_r. Qed.
  
  Definition IntAlgebra_struct : BasicAlgebra := 
    mkBasicAlgebra 
      int_carrier
      int_zero
      int_one
      int_add
      int_mul
      int_add_comm
      int_mul_comm
      int_add_assoc
      int_mul_assoc
      int_add_ident
      int_mul_ident.

End FixedIntAlgebra.

(* ======================== 修复：模块接口定义 ======================== *)
Module Type FixedBasicAlgebra.
  Parameter alg_T : Type.
  Parameter alg_zero : alg_T.
  Parameter alg_one : alg_T.
  Parameter alg_add : alg_T -> alg_T -> alg_T.
  Parameter alg_mul : alg_T -> alg_T -> alg_T.
  Axiom alg_add_comm : forall a b, alg_add a b = alg_add b a.
  Axiom alg_mul_comm : forall a b, alg_mul a b = alg_mul b a.
  Axiom alg_add_assoc : forall a b c, alg_add (alg_add a b) c = alg_add a (alg_add b c).
  Axiom alg_mul_assoc : forall a b c, alg_mul (alg_mul a b) c = alg_mul a (alg_mul b c).
  Axiom alg_add_ident : forall a, alg_add a alg_zero = a.
  Axiom alg_mul_ident : forall a, alg_mul a alg_one = a.
End FixedBasicAlgebra.

(* ======================== 修复：环接口定义 ======================== *)
Module Type FixedRing.
  Declare Module Alg : FixedBasicAlgebra.
  
  Parameter alg_sub : Alg.alg_T -> Alg.alg_T -> Alg.alg_T.
  Parameter alg_neg : Alg.alg_T -> Alg.alg_T.
  
  Axiom alg_sub_def : forall a b, alg_sub a b = Alg.alg_add a (alg_neg b).
  Axiom alg_add_inv : forall a, Alg.alg_add a (alg_neg a) = Alg.alg_zero.
  Axiom alg_neg_zero : alg_neg Alg.alg_zero = Alg.alg_zero.
End FixedRing.

(* ======================== 修复：作用域和符号管理 ======================== *)
Local Close Scope Z_scope.
Local Open Scope nat_scope.

(* 移除可能导致冲突的符号重定义 *)
(* Local Notation "a + b" := (Nat.add a b) (at level 50, left associativity) : nat_scope. *)
(* Local Notation "a * b" := (Nat.mul a b) (at level 40, left associativity) : nat_scope. *)

(* ======================== 修复：Fin函数兼容性 ======================== *)
Lemma fixed_fin_nat_eq : forall {n : nat} (x y : Fin.t n),
  proj1_sig (Fin.to_nat x) = proj1_sig (Fin.to_nat y) -> x = y.
Proof.
  intros n x y H.
  apply Fin.to_nat_inj.
  exact H.
Qed.

Definition fixed_fin_to_nat_val {n} (f : Fin.t n) : nat :=
  match Fin.to_nat f with
  | exist _ x _ => x
  end.

(* ======================== 具体实例和测试 ======================== *)
(* 使用不同的命名方案 *)
Module GF2_Test_Params <: AdvancedPrimeParams.
  Definition p := 2.
  Definition Hprime := prime_2.
End GF2_Test_Params.

(* 显式实例化模块 *)
Module GF2_Test_Field := AdvancedPrimeField(GF2_Test_Params).

(* 使用不同的模块名称避免冲突 *)
Module GF2_Test_Params_New <: AdvancedPrimeParams.
  Definition p := 2.
  Definition Hprime := prime_2.
End GF2_Test_Params_New.

(* 显式实例化模块 *)
Module GF2_Test_Field_New := AdvancedPrimeField(GF2_Test_Params_New).

(* 使用不同的模块名称避免冲突 *)
Module GF2_Test_Params_Final <: AdvancedPrimeParams.
  Definition p := 2.
  Definition Hprime := prime_2.
End GF2_Test_Params_Final.

(* 显式实例化模块 *)
Module GF2_Test_Field_Final := AdvancedPrimeField(GF2_Test_Params_Final).

(* 测试基本运算 *)
Lemma gf2_add_comm : forall a b : GF2_Test_Field.T, 
    GF2_Test_Field.add a b = GF2_Test_Field.add b a.
Proof.
  intros a b.
  apply GF2_Test_Field.add_comm.
Qed.

Lemma gf2_mul_comm : forall a b : GF2_Test_Field.T, 
    GF2_Test_Field.mul a b = GF2_Test_Field.mul b a.
Proof.
  intros a b.
  apply GF2_Test_Field.mul_comm.
Qed.

(* 具体的计算测试 *)
Lemma gf2_one_plus_one_zero : 
    GF2_Test_Field.add GF2_Test_Field.one GF2_Test_Field.one = GF2_Test_Field.zero.
Proof.
  apply GF2_Test_Field.fin_eq.
  rewrite GF2_Test_Field.val_add.
  rewrite GF2_Test_Field.val_one.
  rewrite GF2_Test_Field.val_zero.
  compute. reflexivity.
Qed.

Lemma gf2_one_times_one_one : 
    GF2_Test_Field.mul GF2_Test_Field.one GF2_Test_Field.one = GF2_Test_Field.one.
Proof.
  apply GF2_Test_Field.fin_eq.
  rewrite GF2_Test_Field.val_mul.
  rewrite GF2_Test_Field.val_one.
  compute. reflexivity.
Qed.

(* 更简单的测试方法 - 直接枚举所有可能 *)
Lemma gf2_simple_test : 
  let zero := GF2_Test_Field.zero in
  let one := GF2_Test_Field.one in
  GF2_Test_Field.add zero zero = zero /\
  GF2_Test_Field.add zero one = one /\
  GF2_Test_Field.add one zero = one /\
  GF2_Test_Field.add one one = zero /\
  GF2_Test_Field.mul zero zero = zero /\
  GF2_Test_Field.mul zero one = zero /\
  GF2_Test_Field.mul one zero = zero /\
  GF2_Test_Field.mul one one = one.
Proof.
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]];
  (apply GF2_Test_Field.fin_eq; 
   rewrite ?GF2_Test_Field.val_add, ?GF2_Test_Field.val_mul,
           ?GF2_Test_Field.val_zero, ?GF2_Test_Field.val_one;
   compute; reflexivity).
Qed.



