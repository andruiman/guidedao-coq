Require Import UrsusEnvironment.Solidity.current.Environment.
From Hammer Require Import Tactics Hammer. 

Require Import UMLang.ExecGenerator.

Require Import ERC20.ERC20.
Import ERC20.
Require Import Common.
Require Import Tactics.
Require Import SpecLang.
Require Import CommonProofs.

Require Import Tactics.transferFrom.

SetDefaultOpaques "ERC20".

Opaque LedgerLRecord.

Definition transferFrom_balance_sender1_def (sender : address) (recipient : address) (amount : uint256) 
                                       (ll: LedgerLRecord rec): Prop.
  execs0 (transferFrom rec def sender recipient amount) : ll | "balanceOf" -> l1 | "balanceOf".
  condition (sender <> recipient).
  con (balanceOf'[sender] = xIntMinus (balanceOf[sender]) amount).
Defined.

Lemma transferFrom_balance_sender1_prf (sender : address) (recipient : address) (amount : uint256)   
                                  (ll: LedgerLRecord rec):
      transferFrom_balance_sender1_def sender recipient amount ll.
Proof.
  intros. unfold transferFrom_balance_sender1_def. intros.

  transferFrom_start_new_exec. simplify_all.

  destruct_ledger ll. subst P. rewrite ?toValue_false. rewrite ?toValue_uni_false.
  destruct pcd3. destruct msg14. destruct v9.
  (* simpl_ledger_fields (LedgerLRecord rec).  *)
  
  time (solve_exec_prop; compute).

  compute in H.
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
  condition (sender = recipient).
  condition (xIntGeb (balanceOf[sender]) amount  = true).

  con (balanceOf'[sender] = balanceOf[sender]).
Defined.

Lemma transferFrom_balance_sender2_prf (sender : address) (recipient : address) (amount : uint256)   
                                  (ll: LedgerLRecord rec):
      transferFrom_balance_sender2_def sender recipient amount ll.
Proof.
  intros. unfold transferFrom_balance_sender2_def. intros.

  transferFrom_start_new_exec. simplify_all.

  destruct_ledger ll. subst P. rewrite ?toValue_false. rewrite ?toValue_uni_false.
  destruct pcd3. destruct msg14. destruct v9.
  (* simpl_ledger_fields (LedgerLRecord rec).  *)
  
  time (solve_exec_prop; compute).

  remember (s1 [recipient] ?).
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

Definition transferFrom_balance_recipient_def (sender : address) (recipient : address) (amount : uint256) 
                                          (ll: LedgerLRecord rec): Prop.
  execs0 (transferFrom rec def sender recipient amount) : ll | "balanceOf"  -> l1 | "balanceOf".
  condition (recipient <> sender).

  con (balanceOf'[recipient] = xIntPlus (balanceOf[recipient]) amount).
Defined.

Lemma transferFrom_balance_recipient_prf (sender : address) (recipient : address) (amount : uint256)   
                                  (ll: LedgerLRecord rec):
      transferFrom_balance_recipient_def sender recipient amount ll.
Proof.
  intros. unfold transferFrom_balance_recipient_def. intros.

  transferFrom_start_new_exec. simplify_all.

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


Definition transferFrom_allowance_def (sender : address) (recipient : address) (amount : uint256) 
                                                (ll: LedgerLRecord rec): Prop.
  execs0 (transferFrom rec def sender recipient amount) : ll | "allowance" "msg_sender"  -> l1 | "allowance".
  (* condition (recipient <> sender). *)

  con (allowance'[sender][msg_sender]= xIntMinus (allowance[sender][msg_sender]) amount).
Defined.

Lemma transferFrom_allowance_prf (sender : address) (recipient : address) (amount : uint256)   
                                  (ll: LedgerLRecord rec):
      transferFrom_allowance_def sender recipient amount ll.
Proof.
  intros. unfold transferFrom_allowance_def. intros.

  transferFrom_start_new_exec. simplify_all.

  destruct_ledger ll. subst P. rewrite ?toValue_false. rewrite ?toValue_uni_false.
  destruct pcd3. destruct msg14. destruct v9.
  (* simpl_ledger_fields (LedgerLRecord rec).  *)
  
  time (solve_exec_prop; compute).

  erewrite lookup_addAdjust.
  erewrite lookup_addAdjust.
  reflexivity.
Time Qed.