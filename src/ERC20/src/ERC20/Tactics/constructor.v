
Require Import ERC20.ProofsHeader.

Require Import ERC20.Functions.
Require Import ERC20.Common. 
(* Require Import CommonTactics. *)

Require Import ERC20.Functions.constructor.

Require Export ERC20.Execs.constructor_cbv_0 ERC20.Evals.constructor_cbv_0 .
Require Export ERC20.Execs.constructor_cbv_0_exec_prf ERC20.Evals.constructor_cbv_0_eval_prf .


 

Tactic Notation "constructor_start" :=
  prepare_goal  @constructor;
  continue_all  @constructor 
                  ;
  simplify_tails  .

Time Print I.

