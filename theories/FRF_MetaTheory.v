(* theories/FRF_MetaTheory.v - 极度简化版本 *)
From Coq Require Import List.

Record FormalSystem : Type := {
  system_name : string;
  carrier : Type;
  axioms : list Prop;
}.

Record FunctionalRole (S : FormalSystem) : Type := {
  role_id : string;
  core_features : list string;
}.

Export FormalSystem.
Export FunctionalRole.