
Require Import ERC20.ProofsHeader.

Require Import ERC20.Functions.
Require Import ERC20.Common. 
(* Require Import CommonTactics. *)

Require Import ERC20.Functions.mint_.

Require Export ERC20.Execs.mint__cbv_0 ERC20.Evals.mint__cbv_0 .
Require Export ERC20.Execs.mint__cbv_0_exec_prf ERC20.Evals.mint__cbv_0_eval_prf .


 

Tactic Notation "mint__start" :=
  prepare_goal  @mint_;
  continue_all  @mint_ 
                  ;
  simplify_tails  .

Time Print I.

