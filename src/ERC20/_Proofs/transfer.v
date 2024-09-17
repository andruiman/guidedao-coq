Require Import UrsusEnvironment.Solidity.current.Environment.
From Hammer Require Import Tactics Hammer. 

Require Import UMLang.ExecGenerator.

Require Import ERC20.ERC20.
Import ERC20.
Require Import Common.
Require Import Tactics.
Require Import SpecLang.
Require Import CommonProofs.

Require Import Tactics.transfer.

SetDefaultOpaques "ERC20".

Opaque LedgerLRecord.

Definition transfer_balance_sender1_def (recipient : address) (amount : uint256) 
                                       (ll: LedgerLRecord rec): Prop.
  execs0 (transfer rec def recipient amount) : ll | "balanceOf" "msg_sender" -> l1 | "balanceOf".
  condition (msg_sender <> recipient).
  con (balanceOf'[msg_sender] = xIntMinus (balanceOf[msg_sender]) amount).
Defined.

Lemma transfer_balance_sender1_prf (recipient : address) (amount : uint256)   
                                  (ll: LedgerLRecord rec):
      transfer_balance_sender1_def recipient amount ll.
Proof.
  intros. unfold transfer_balance_sender1_def. intros.

  transfer_start_new_exec. simplify_all.

  destruct_ledger ll. subst P. rewrite ?toValue_false. rewrite ?toValue_uni_false.
  destruct pcd3. destruct msg14. destruct v9.
  (* simpl_ledger_fields (LedgerLRecord rec).  *)
  
  time (solve_exec_prop; compute).

  compute in H.
  remember (s1 [msg12] ?).
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
  condition (msg_sender = recipient).
  condition (xIntGeb (balanceOf[msg_sender]) amount  = true).

  con (balanceOf'[msg_sender] = balanceOf[msg_sender]).
Defined.

Lemma transfer_balance_sender2_prf (recipient : address) (amount : uint256)   
                                  (ll: LedgerLRecord rec):
      transfer_balance_sender2_def recipient amount ll.
Proof.
  intros. unfold transfer_balance_sender2_def. intros.

  transfer_start_new_exec. simplify_all.

  destruct_ledger ll. subst P. rewrite ?toValue_false. rewrite ?toValue_uni_false.
  destruct pcd3. destruct msg14. destruct v9.
  (* simpl_ledger_fields (LedgerLRecord rec).  *)
  
  time (solve_exec_prop; compute).

  compute in H.
  rewrite <- ?H.
  remember (s1 [msg12] ?).
  setoid_rewrite <- Heqy.
  destruct y.
  - erewrite lookup_addAdjust.
  erewrite lookup_addAdjust.
  destruct x3, amount.
  f_equal.
  compute in H0.
  setoid_rewrite <- Heqy in H0.
  apply N.leb_le in H0.
  lia.
  - erewrite lookup_addAdjust.
  erewrite lookup_addAdjust.
  destruct amount.
  compute in H0.
  setoid_rewrite <- Heqy in H0.
  f_equal.
  apply N.leb_le in H0.
  lia.
Time Qed.


Definition transfer_balance_recipient_def (recipient : address) (amount : uint256) 
                                          (ll: LedgerLRecord rec): Prop.
  execs0 (transfer rec def recipient amount) : ll | "balanceOf" "msg_sender" -> l1 | "balanceOf".
  condition (recipient <> msg_sender).

  con (balanceOf'[recipient] = xIntPlus (balanceOf[recipient]) amount).
Defined.

Lemma transfer_balance_recipient_prf (recipient : address) (amount : uint256)   
                                  (ll: LedgerLRecord rec):
      transfer_balance_recipient_def recipient amount ll.
Proof.
  intros. unfold transfer_balance_recipient_def. intros.

  transfer_start_new_exec. simplify_all.

  destruct_ledger ll. subst P. rewrite ?toValue_false. rewrite ?toValue_uni_false.
  destruct pcd3. destruct msg14. destruct v9.
  (* simpl_ledger_fields (LedgerLRecord rec).  *)
  
  time (solve_exec_prop; compute).

  compute in H.
  erewrite lookup_addAdjust.
  erewrite lookup_addAdjust_another.
  2: assumption.
  reflexivity.
Time Qed.