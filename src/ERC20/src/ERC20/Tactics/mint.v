
Require Import ERC20.ProofsHeader.

Require Import ERC20.Functions.
Require Import ERC20.Common. 
(* Require Import CommonTactics. *)

Require Import ERC20.Functions.mint.

Require Export ERC20.Execs.mint_cbv_0 ERC20.Evals.mint_cbv_0 .
Require Export ERC20.Execs.mint_cbv_0_exec_prf ERC20.Evals.mint_cbv_0_eval_prf .


Require Export ERC20.Tactics.mint_  . 

Tactic Notation "mint_start" :=
  prepare_goal  @mint;
  continue_all  @mint 
                  ;
  simplify_tails  .

Time Print I.

