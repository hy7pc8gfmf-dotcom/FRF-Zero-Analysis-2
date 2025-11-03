(* Test/Test_Basic.v *)
From Coq Require Import Utf8.

Theorem test_true : True.
Proof. exact I. Qed.

Theorem test_false_implies_anything : False -> 1 = 2.
Proof. intros H; contradiction. Qed.

Theorem test_nat_arithmetic : 2 + 2 = 4.
Proof. reflexivity. Qed.