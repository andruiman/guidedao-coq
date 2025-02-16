Require Import ProofsHeader.
Require Import Tactics.transfer.

SetDefaultOpaques "ERC20".

Definition transfer_balance_sender1_def (recipient : address) (amount : uint256) 
                                       (ll: LedgerLRecord rec): Prop.
  execs0 (transfer rec def recipient amount) : ll | "balanceOf" "msg_sender" -> l1 | "balanceOf".
  hyp (msg_sender <> recipient).
  con (balanceOf'[msg_sender] = xIntMinus (balanceOf[msg_sender]) amount).
Defined.

Lemma transfer_balance_sender1_prf (recipient : address) (amount : uint256)   
                                  (ll: LedgerLRecord rec):
      transfer_balance_sender1_def recipient amount ll.
Proof.
  start_proof.
  transfer_start.
  time prepare_all ll P.
  compute in H1. subst y1. 
  compute_destructed_ledgers _loc.

  time bottom_up_goal_solver.

  (* ********************* *)

  remember (s1 [msg11] ?).
  setoid_rewrite <- Heqy.
  destruct y.
  - erewrite lookup_addAdjust_another.
  2: assumption.
  erewrite lookup_addAdjust.
  reflexivity.
  - erewrite lookup_addAdjust_another.
  2: assumption.
  erewrite lookup_addAdjust.
  reflexivity.
Time Qed.

Definition transfer_balance_sender2_def (recipient : address) (amount : uint256) 
                                       (ll: LedgerLRecord rec): Prop.
  execs0 (transfer rec def recipient amount) : ll | "balanceOf" "msg_sender" -> l1 | "balanceOf".
  hyp (msg_sender = recipient).
  hyp (xIntGeb (balanceOf[msg_sender]) amount  = true).

  con (balanceOf'[msg_sender] = balanceOf[msg_sender]).
Defined.

Lemma transfer_balance_sender2_prf (recipient : address) (amount : uint256)   
                                  (ll: LedgerLRecord rec):
      transfer_balance_sender2_def recipient amount ll.
Proof.
  start_proof.
  transfer_start.
  time prepare_all ll P.
  compute in H1. subst y1. 
  compute_destructed_ledgers _loc.

  time bottom_up_goal_solver.
  
  (* ********************* *)

  rewrite <- ?C in *.
  remember (s1 [msg11] ?).
  setoid_rewrite <- Heqy.
  destruct y.
  - 
  erewrite lookup_addAdjust.
  erewrite lookup_addAdjust.
  destruct x, amount.
  f_equal.
  unfold Common.hmapFindWithDefault in C0.
  setoid_rewrite <- Heqy in C0.
  apply N.leb_le in C0.
  with_strategy opaque [N.le]
  compute in C0.
  lia.
  - 
  erewrite lookup_addAdjust.
  erewrite lookup_addAdjust.
  destruct amount.
  unfold Common.hmapFindWithDefault in C0.
  setoid_rewrite <- Heqy in C0.
  f_equal.
  apply N.leb_le in C0.
  with_strategy opaque [N.le]
  compute in C0.
  lia.
Time Qed.


Definition transfer_balance_recipient_def (recipient : address) (amount : uint256) 
                                          (ll: LedgerLRecord rec): Prop.
  execs0 (transfer rec def recipient amount) : ll | "balanceOf" "msg_sender" -> l1 | "balanceOf".
  hyp (recipient <> msg_sender).

  con (balanceOf'[recipient] = xIntPlus (balanceOf[recipient]) amount).
Defined.

Lemma transfer_balance_recipient_prf (recipient : address) (amount : uint256)   
                                  (ll: LedgerLRecord rec):
      transfer_balance_recipient_def recipient amount ll.
Proof.
  start_proof.
  transfer_start.
  time prepare_all ll P.
  compute in H1. subst y1. 
  compute_destructed_ledgers _loc.

  time bottom_up_goal_solver.
  
  (* ********************* *)

  erewrite lookup_addAdjust.
  erewrite lookup_addAdjust_another.
  2: assumption.
  reflexivity.
Time Qed.