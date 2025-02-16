Require Import ProofsHeader.
Require Import Tactics.mint.

SetDefaultOpaques "ERC20".

Definition mint_balance_def (to__ : address) (amount : uint256) 
                            (ll: LedgerLRecord rec): Prop.
  execs0 (mint rec def to__ amount) : ll | "balanceOf" -> l1 | "balanceOf".
  con (balanceOf'[to__] = xIntPlus (balanceOf[to__]) amount).
Defined.

Lemma  mint_balance_prf (to__ : address) (amount : uint256)  (ll: LedgerLRecord rec):
       mint_balance_def to__ amount ll.
Proof.
  start_proof.
  mint_start.
  continue_all @mint_.
  time prepare_all ll P. 
  (* compute_destructed_ledgers loc_. *)

  time
  bottom_up_goal_solver. (* 0.412 secs *)

  erewrite lookup_addAdjust.
  reflexivity.
Time Qed.


Definition mint_totalSupply_def (to__ : address) (amount : uint256) 
                            (ll: LedgerLRecord rec): Prop.
  execs0 (mint rec def to__ amount) : ll | "totalSupply" -> l1 | "totalSupply".
  con (totalSupply' = xIntPlus totalSupply amount).
Defined.

Lemma mint_totalSupply_prf (to__ : address) (amount : uint256)  (ll: LedgerLRecord rec):
      mint_totalSupply_def to__ amount ll.
Proof.
  start_proof.
  mint_start.
  continue_all @mint_.
  time prepare_all ll P. 
  (* compute_destructed_ledgers loc_. *)

  time
  bottom_up_goal_solver. (* 0.305 secs *)
Time Qed.
