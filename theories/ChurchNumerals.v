(*  theories/ChurchNumerals.v *)
From Coq Require Import Utf8.

(** Church 数值定义 *)
Definition ChurchNumeral := forall A : Type, (A -> A) -> A -> A.

Definition zero : ChurchNumeral :=
  fun A f x => x.

Definition succ (n : ChurchNumeral) : ChurchNumeral :=
  fun A f x => f (n A f x).

Definition one : ChurchNumeral := succ zero.
Definition two : ChurchNumeral := succ one.

(** 数值操作 *)
Definition add (m n : ChurchNumeral) : ChurchNumeral :=
  fun A f x => m A f (n A f x).

Definition mul (m n : ChurchNumeral) : ChurchNumeral :=
  fun A f => m A (n A f).

(** 测试 - 避免使用functional_extensionality *)
Theorem zero_test : zero = (fun A f x => x).
Proof. reflexivity. Qed.

Theorem one_test : one = (fun A f x => f x).
Proof. reflexivity. Qed.

(** 简化测试，避免复杂的等式证明 *)
Definition apply_two (A : Type) (f : A -> A) (x : A) : A :=
  two A f x.

Theorem two_applies_twice : forall A (f : A -> A) (x : A),
  apply_two A f x = f (f x).
Proof.
  intros A f x.
  unfold apply_two, two, one, succ, zero.
  reflexivity.
Qed.