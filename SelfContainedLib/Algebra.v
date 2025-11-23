(* SelfContainedLib/Algebra.v *)
From Coq Require Import Utf8.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Arith.Arith.

Module Type BasicAlgebra.
  Parameter T : Type.
  Parameter zero : T.
  Parameter one : T.
  Parameter add : T -> T -> T.
  Parameter mul : T -> T -> T.
  
  Axiom add_comm : forall a b, add a b = add b a.
  Axiom mul_comm : forall a b, mul a b = mul b a.
End BasicAlgebra.

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
End NatAlgebra.

Theorem algebra_test : NatAlgebra.one = 1.
Proof. reflexivity. Qed.