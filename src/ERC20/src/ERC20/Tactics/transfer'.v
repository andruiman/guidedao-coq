
Require Import ERC20.ProofsHeader.

Require Import ERC20.Functions1.
Require Import ERC20.Common. 
(* Require Import CommonTactics. *)

Require Import ERC20.Functions.transfer'.

Require Export ERC20.Execs.transfer'_cbv_0 ERC20.Evals.transfer'_cbv_0 .
Require Export ERC20.Execs.transfer'_cbv_0_exec_prf ERC20.Evals.transfer'_cbv_0_eval_prf .


 

Tactic Notation "transfer'_start" :=
  prepare_goal  @transfer';
  continue_all  @transfer' 
                  ;
  simplify_tails  .

Time Print I.

