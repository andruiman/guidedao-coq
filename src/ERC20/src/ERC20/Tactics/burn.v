
Require Import ERC20.ProofsHeader.

Require Import ERC20.Functions.
Require Import ERC20.Common. 
(* Require Import CommonTactics. *)

Require Import ERC20.Functions.burn.

Require Export ERC20.Execs.burn_cbv_0 ERC20.Evals.burn_cbv_0 .
Require Export ERC20.Execs.burn_cbv_0_exec_prf ERC20.Evals.burn_cbv_0_eval_prf .


Require Export ERC20.Tactics.burn_  . 

Tactic Notation "burn_start" :=
  prepare_goal  @burn;
  continue_all  @burn 
                  ;
  simplify_tails  .

Time Print I.

