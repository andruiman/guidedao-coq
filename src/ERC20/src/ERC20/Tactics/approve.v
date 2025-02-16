
Require Import ERC20.ProofsHeader.

Require Import ERC20.Functions.
Require Import ERC20.Common. 
(* Require Import CommonTactics. *)

Require Import ERC20.Functions.approve.

Require Export ERC20.Execs.approve_cbv_0 ERC20.Evals.approve_cbv_0 .
Require Export ERC20.Execs.approve_cbv_0_exec_prf ERC20.Evals.approve_cbv_0_eval_prf .


 

Tactic Notation "approve_start" :=
  prepare_goal  @approve;
  continue_all  @approve 
                  ;
  simplify_tails  .

Time Print I.

