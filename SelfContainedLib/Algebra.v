(* SelfContainedLib/Algebra.v *)

From Coq Require Import Utf8.
From Coq Require Import Arith.Arith.
From Coq Require Import ZArith.ZArith. (* Ensure ZArith is available globally *)

(** 代数结构基础模块 *)
Module Type BasicAlgebra.
  Parameter T : Type.
  Parameter zero : T.
  Parameter one : T.
  Parameter add : T -> T -> T.
  Parameter mul : T -> T -> T.

  Axiom add_comm : forall a b, add a b = add b a.
  Axiom mul_comm : forall a b, mul a b = mul b a.
  Axiom add_assoc : forall a b c, add (add a b) c = add a (add b c).
  Axiom mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c).
  Axiom add_zero : forall a, add a zero = a.
  Axiom mul_one : forall a, mul a one = a.
  Axiom distr : forall a b c, mul a (add b c) = add (mul a b) (mul a c).
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
  Definition T := Z.
  Definition zero := Z0.
  Definition one := Z1.
  Definition add := Z.add.
  Definition mul := Z.mul.

  Lemma add_comm : forall a b, add a b = add b a.
  Proof. apply Z.add_comm. Qed.

  Lemma mul_comm : forall a b, mul a b = mul b a.
  Proof. apply Z.mul_comm. Qed.

  Lemma add_assoc : forall a b c, add (add a b) c = add a (add b c).
  Proof. apply Z.add_assoc. Qed.

  Lemma mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof. apply Z.mul_assoc. Qed.

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
    orb a b.  (* 更简洁：等价于你写的 match *)

  Definition mul (a b : bool) : bool :=
    andb a b. (* 同上 *)

  Lemma add_comm : forall a b, add a b = add b a.
  Proof. intros a b; apply Bool.orb_comm. Qed.

  Lemma mul_comm : forall a b, mul a b = mul b a.
  Proof. intros a b; apply Bool.andb_comm. Qed.

  Lemma add_assoc : forall a b c, add (add a b) c = add a (add b c).
  Proof. intros a b c; apply Bool.orb_assoc. Qed.

  Lemma mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof. intros a b c; apply Bool.andb_assoc. Qed.

  Lemma add_zero : forall a, add a zero = a.
  Proof. intros a; simpl; destruct a; reflexivity. Qed.

  Lemma mul_one : forall a, mul a one = a.
  Proof. intros a; simpl; destruct a; reflexivity. Qed.

  Lemma mul_zero : forall a, mul a zero = zero.
  Proof. intros a; simpl; destruct a; reflexivity. Qed.

  Lemma distr : forall a b c, mul a (add b c) = add (mul a b) (mul a c).
  Proof.
    intros a b c.
    destruct a, b, c; simpl; reflexivity.
  Qed.
End BoolAlgebra.

(* 可选：导出模块以便外部使用 *)
Export NatAlgebra IntAlgebra BoolAlgebra.