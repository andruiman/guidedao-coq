
Require Import ERC20.ProofsHeader.

Require Import ERC20.Functions.
Require Import ERC20.Common. 
(* Require Import CommonTactics. *)

Require Import ERC20.Functions.transferFrom.

Require Export ERC20.Execs.transferFrom_cbv_0 ERC20.Evals.transferFrom_cbv_0 .
Require Export ERC20.Execs.transferFrom_cbv_0_exec_prf ERC20.Evals.transferFrom_cbv_0_eval_prf .


 

Tactic Notation "transferFrom_start" :=
  prepare_goal  @transferFrom;
  continue_all  @transferFrom 
                  ;
  simplify_tails  .

Time Print I.

