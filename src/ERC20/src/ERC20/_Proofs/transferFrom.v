Require Import ProofsHeader.
Require Import Tactics.transferFrom.

SetDefaultOpaques "ERC20".


Definition transferFrom_balance_sender1_def (sender : address) (recipient : address) (amount : uint256) 
                                       (ll: LedgerLRecord rec): Prop.
  execs0 (transferFrom rec def sender recipient amount) : ll | "balanceOf" -> l1 | "balanceOf".
  hyp (sender <> recipient).
  con (balanceOf'[sender] = xIntMinus (balanceOf[sender]) amount).
Defined.

Lemma transferFrom_balance_sender1_prf (sender : address) (recipient : address) (amount : uint256)   
                                  (ll: LedgerLRecord rec):
      transferFrom_balance_sender1_def sender recipient amount ll.
Proof.
  start_proof.
  transferFrom_start.
  time prepare_all ll P.
  compute in H1. subst y1. 
  compute_destructed_ledgers _loc.

  time bottom_up_goal_solver.

  (* ********************* *)

  remember (s1 [sender] ?).
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

Definition transferFrom_balance_sender2_def (sender : address) (recipient : address) (amount : uint256) 
                                            (ll: LedgerLRecord rec): Prop.
  execs0 (transferFrom rec def sender recipient amount) : ll | "balanceOf"  -> l1 | "balanceOf".
  hyp (sender = recipient).
  hyp (xIntGeb (balanceOf[sender]) amount  = true).

  con (balanceOf'[sender] = balanceOf[sender]).
Defined.

Lemma transferFrom_balance_sender2_prf (sender : address) (recipient : address) (amount : uint256)   
                                  (ll: LedgerLRecord rec):
      transferFrom_balance_sender2_def sender recipient amount ll.
Proof.
  start_proof.
  transferFrom_start.
  time prepare_all ll P.
  compute in H1. subst y1. 
  compute_destructed_ledgers _loc.

  time bottom_up_goal_solver.

  (* ********************* *)

  remember (s1 [recipient] ?).
  setoid_rewrite <- Heqy.
  destruct y.
  - erewrite lookup_addAdjust.
    erewrite lookup_addAdjust.
    destruct x, amount.
    f_equal.
    unfold Common.hmapFindWithDefault in C.
    setoid_rewrite <- Heqy in C.
    apply N.leb_le in C.
    with_strategy opaque [N.le]
    compute in C.
    lia.
  - erewrite lookup_addAdjust.
    erewrite lookup_addAdjust.
    destruct amount.
    unfold Common.hmapFindWithDefault in C.
    setoid_rewrite <- Heqy in C.
    apply N.leb_le in C.
    with_strategy opaque [N.le]
    compute in C.
    f_equal.
    lia.
Time Qed.

Definition transferFrom_balance_recipient_def (sender : address) (recipient : address) (amount : uint256) 
                                          (ll: LedgerLRecord rec): Prop.
  execs0 (transferFrom rec def sender recipient amount) : ll | "balanceOf"  -> l1 | "balanceOf".
  hyp (recipient <> sender).

  con (balanceOf'[recipient] = xIntPlus (balanceOf[recipient]) amount).
Defined.

Lemma transferFrom_balance_recipient_prf (sender : address) (recipient : address) (amount : uint256)   
                                  (ll: LedgerLRecord rec):
      transferFrom_balance_recipient_def sender recipient amount ll.
Proof.
  start_proof.
  transferFrom_start.
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


Definition transferFrom_allowance_def (sender : address) (recipient : address) (amount : uint256) 
                                                (ll: LedgerLRecord rec): Prop.
  execs0 (transferFrom rec def sender recipient amount) : ll | "allowance" "msg_sender"  -> l1 | "allowance".

  con (allowance'[sender][msg_sender]= xIntMinus (allowance[sender][msg_sender]) amount).
Defined.

Lemma transferFrom_allowance_prf (sender : address) (recipient : address) (amount : uint256)   
                                  (ll: LedgerLRecord rec):
      transferFrom_allowance_def sender recipient amount ll.
Proof.
  start_proof.
  transferFrom_start.
  time prepare_all ll P.
  compute in H1. subst y1. 
  compute_destructed_ledgers _loc.

  time bottom_up_goal_solver.

  (* ********************* *)

  erewrite lookup_addAdjust.
  erewrite lookup_addAdjust.
  reflexivity.
Time Qed.