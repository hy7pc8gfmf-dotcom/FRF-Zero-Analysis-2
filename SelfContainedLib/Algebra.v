(* SelfContainedLib/Algebra.v *)

From Coq Require Import Utf8.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Arith.Arith.

(** 代数结构基础模块 *)
Module Type BasicAlgebra.
  Parameter T : Type.
  Parameter zero : T.
  Parameter one : T.
  Parameter add : T -> T -> T.
  Parameter mul : T -> T -> T.
  
  (* 加法交换律 *)
  Axiom add_comm : forall a b, add a b = add b a.
  
  (* 乘法交换律 *)
  Axiom mul_comm : forall a b, mul a b = mul b a.
  
  (* 加法结合律 *)
  Axiom add_assoc : forall a b c, add (add a b) c = add a (add b c).
  
  (* 乘法结合律 *)
  Axiom mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c).
  
  (* 加法单位元 *)
  Axiom add_zero : forall a, add a zero = a.
  
  (* 乘法单位元 *)
  Axiom mul_one : forall a, mul a one = a.
  
  (* 分配律 *)
  Axiom distr : forall a b c, mul a (add b c) = add (mul a b) (mul a c).
  
  (* 零乘法性质 *)
  Axiom mul_zero : forall a, mul a zero = zero.
  
End BasicAlgebra.

(** 自然数代数实现 *)
Module NatAlgebra <: BasicAlgebra.
  Definition T := nat.
  Definition zero := 0.
  Definition one := 1.
  Definition add := Nat.add.
  Definition mul := Nat.mul.

  Lemma add_comm : forall a b, add a b = add b a.
  Proof. apply Nat.add_comm. Qed.

  Lemma mul_comm : forall a b, mul a b = mul b a.
  Proof. apply Nat.mul_comm. Qed.

  Lemma add_assoc : forall a b c, add (add a b) c = add a (add b c).
  Proof. apply Nat.add_assoc. Qed.

  Lemma mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof. apply Nat.mul_assoc. Qed.

  Lemma add_zero : forall a, add a zero = a.
  Proof. intros; rewrite Nat.add_0_r; reflexivity. Qed.

  Lemma mul_one : forall a, mul a one = a.
  Proof. apply Nat.mul_1_r. Qed.

  Lemma distr : forall a b c, mul a (add b c) = add (mul a b) (mul a c).
  Proof. apply Nat.mul_add_distr_l. Qed.

  Lemma mul_zero : forall a, mul a zero = zero.
  Proof. apply Nat.mul_0_r. Qed.

End NatAlgebra.

(** 整数代数实现 *)
Module IntAlgebra <: BasicAlgebra.
  (* 这里我们使用Coq标准库中的Z *)
  Require Import Coq.ZArith.ZArith.
  
  Definition T := Z.
  Definition zero := Z0.
  Definition one := Z1.
  Definition add := Z.add.
  Definition mul := Z.mul.

  Lemma add_comm : forall a b, add a b = add b a.
  Proof. apply Z.add_comm. Qed.

  Lemma mul_comm : forall a b, mul a b = mul b a.
  Proof. apply Z.mul_comm. Qed.

  Lemma mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof. apply Z.mul_assoc. Qed.

  Lemma add_assoc : forall a b c, add (add a b) c = add a (add b c).
  Proof. apply Z.add_assoc. Qed.

  Lemma add_zero : forall a, add a zero = a.
  Proof. apply Z.add_0_r. Qed.

  Lemma mul_one : forall a, mul a one = a.
  Proof. apply Z.mul_1_r. Qed.

  Lemma distr : forall a b c, mul a (add b c) = add (mul a b) (mul a c).
  Proof. apply Z.mul_add_distr_r. Qed.

  Lemma mul_zero : forall a, mul a zero = zero.
  Proof. apply Z.mul_0_r. Qed.

End IntAlgebra.

(** 布尔代数实现 *)
Module BoolAlgebra <: BasicAlgebra.
  Definition T := bool.
  Definition zero := false.
  Definition one := true.
  
  Definition add (a b : bool) : bool :=
    match a, b with
    | true, true => true
    | true, false => true
    | false, true => true
    | false, false => false
    end.
  
  Definition mul (a b : bool) : bool :=
    match a, b with
    | true, true => true
    | true, false => false
    | false, true => false
    | false, false => false
    end.

  Lemma add_comm : forall a b, add a b = add b a.
  Proof.
    intros a b.
    destruct a, b; reflexivity.
  Qed.

  Lemma mul_comm : forall a b, mul a b = mul b a.
  Proof.
    intros a b.
    destruct a, b; reflexivity.
  Qed.

  Lemma mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof.
    intros a b c.
    destruct a, b, c; reflexivity.
  Qed.

  Lemma add_assoc : forall a b c, add (add a b) c = add a (add b c).
  Proof.
    intros a b c.
    destruct a, b, c; reflexivity.
  Qed.

  Lemma add_zero : forall a, add a zero = a.
  Proof.
    intros a.
    destruct a; reflexivity.
  Qed.

  Lemma mul_one : forall a, mul a one = a.
  Proof.
    intros a.
    destruct a; reflexivity.
  Qed.

  Lemma mul_one : forall a, mul a one = a.
  Proof.
    intros a.
    destruct a; reflexivity.
  Qed.

  Lemma distr : forall a b c, mul a (add b c) = add (mul a b) (mul a c).
  Proof.
    intros a b c.
    destruct a, b, c; reflexivity.
  Qed.

  Lemma mul_zero : forall a, mul a zero = zero.
  Proof.
    intros a.
    destruct a; reflexivity.
  Qed.

End BoolAlgebra.

(** 代数结构测试定理 *)
Theorem algebra_test_nat : NatAlgebra.one = 1.
Proof. reflexivity. Qed.

Theorem algebra_test_bool : BoolAlgebra.one = true.
Proof. reflexivity. Qed.

Theorem add_comm_test : forall a b : nat, NatAlgebra.add a b = NatAlgebra.add b a.
Proof. apply Nat.add_comm. Qed.

Theorem mul_comm_test : forall a b : nat, NatAlgebra.mul a b = NatAlgebra.mul b a.
Proof. apply Nat.mul_comm. Qed.

(** 零元素的唯一性定理 *)
Theorem zero_uniqueness : forall (A : BasicAlgebra) (z : A.T), 
  (forall a : A.T, A.add a z = a) -> z = A.zero.
Proof.
  intros A z H.
  specialize (H A.zero).
  simpl in H.
  rewrite H.
  reflexivity.
Qed.

(** 单位元的唯一性定理 *)
Theorem one_uniqueness : forall (A : BasicAlgebra) (u : A.T),
  (forall a : A.T, A.mul a u = a) -> u = A.one.
Proof.
  intros A u H.
  specialize (H A.one).
  simpl in H.
  rewrite H.
  reflexivity.
Qed.

(** 代数结构等价性定义 *)
Definition AlgebraEquiv (A B : BasicAlgebra) : Prop :=
  exists (f : A.T -> B.T),
  (forall x y, f (A.add x y) = B.add (f x) (f y) /\
  exists (g : B.T -> A.T),
  (forall x y, g (B.add x y) = A.add (g x) (g y) /\
  f A.zero = B.zero /\ f A.one = B.one.