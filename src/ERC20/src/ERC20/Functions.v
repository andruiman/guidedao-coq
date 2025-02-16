
Require Import ERC20.CommonHeader.

Require Import ERC20.Run.
Require Import ERC20.Common.

Definition execs_for_roots_ := Eval compute in (execs_for_roots roots_eval roots_exec graph2).
Definition evals_for_roots_ := Eval compute in (evals_for_roots roots_eval roots_exec graph2).

(* compute import-map: what imports are needed for each proof *)
(* instead of Datatypes.nil, you can add "common" evals and execs -- which all proofs must import *)
Definition imports_execs_ := Eval compute in (imports_execs Datatypes.nil Datatypes.nil graph2).
Definition imports_evals_ := Eval compute in (imports_evals Datatypes.nil Datatypes.nil graph2).

(* compute unfold-map: what unfolds are needed for each eval/exec *)
Definition unfold_strings_' := Eval compute in (create_unfold_strings roots_eval roots_exec graph1 graph2).

AddExternalCallUnfolds unfold_strings_'.


Elpi CreateFunctions - ERC20 "/Users/andruiman/devel/guidedao-coq/" "src/ERC20/src" "ERC20" "Functions" "Execs" "Evals" "Tactics" "Functions" "_FakeProofs" .

