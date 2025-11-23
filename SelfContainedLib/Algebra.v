(* SelfContainedLib/Algebra.v *)
From Coq Require Import Utf8.
From Coq Require Import Arith.Arith.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Bool.

(** 代数结构基础模块 *)
Module Type BasicAlgebra.
  Parameter T : Type.
  Parameter zero : T.
  Parameter one : T.
  Parameter add : T -> T -> T.
  Parameter mul : T -> T -> T.
  Axiom add_comm : forall a b, add a b = add b a.
  Axiom mul_comm : forall a b, mul a b = mul b a.
End BasicAlgebra.

(** 自然数代数实现 *)
Module NatAlgebra <: BasicAlgebra.
  Definition T := nat.
  Definition zero := 0.
  Definition one := 1.
  Definition add := Nat.add.
  Definition mul := Nat.mul.

  Lemma add_comm : forall a b, add a b = add b a.
  Proof.
    intros a b.
    apply Nat.add_comm.
  Qed.

  Lemma mul_comm : forall a b, mul a b = mul b a.
  Proof.
    intros a b.
    apply Nat.mul_comm.
  Qed.
End NatAlgebra.

(** 整数代数实现 *)
Module IntAlgebra <: BasicAlgebra.
  Definition T := Z.
  Definition zero := 0%Z.
  Definition one := 1%Z.
  Definition add := Z.add.
  Definition mul := Z.mul.

  Lemma add_comm : forall a b, add a b = add b a.
  Proof.
    intros a b.
    apply Z.add_comm.
  Qed.

  Lemma mul_comm : forall a b, mul a b = mul b a.
  Proof.
    intros a b.
    apply Z.mul_comm.
  Qed.
End IntAlgebra.

(** 布尔代数实现 *)
Module BoolAlgebra <: BasicAlgebra.
  Definition T := bool.
  Definition zero := false.
  Definition one := true.
  Definition add := orb.
  Definition mul := andb.

  Lemma add_comm : forall a b, add a b = add b a.
  Proof.
    intros a b.
    apply Bool.orb_comm.
  Qed.

  Lemma mul_comm : forall a b, mul a b = mul b a.
  Proof.
    intros a b.
    apply Bool.andb_comm.
  Qed.
End BoolAlgebra.
