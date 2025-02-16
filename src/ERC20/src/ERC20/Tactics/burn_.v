
Require Import ERC20.ProofsHeader.

Require Import ERC20.Functions.
Require Import ERC20.Common. 
(* Require Import CommonTactics. *)

Require Import ERC20.Functions.burn_.

Require Export ERC20.Execs.burn__cbv_0 ERC20.Evals.burn__cbv_0 .
Require Export ERC20.Execs.burn__cbv_0_exec_prf ERC20.Evals.burn__cbv_0_eval_prf .


 

Tactic Notation "burn__start" :=
  prepare_goal  @burn_;
  continue_all  @burn_ 
                  ;
  simplify_tails  .

Time Print I.

