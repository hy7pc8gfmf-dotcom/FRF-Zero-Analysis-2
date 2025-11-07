(* theories/FRF_MetaTheory.v *)

Require Import Coq.Init.Datatypes.
Require Import Coq.Logic.FunctionalExtensionality.

Create Scope frf_meta_scope.
Open Scope frf_meta_scope.

Definition sum_edge_weights (edges : list (string * R)) : R := 
  fold_left (fun acc f => acc + snd f) edges 0.0.

Record FormalSystem : Type := {
  system_name : string;
  carrier : Type;
  op : carrier -> carrier -> carrier;
}.

Record FunctionalRole (S : FormalSystem) : Type := {
  role_id : string;
  core_features : list string;
}.