Require Import UrsusEnvironment.Solidity.current.Environment.
From Hammer Require Import Tactics Hammer. 

Require Import UMLang.ExecGenerator.

Require Import ERC20.ERC20.
Import ERC20.
Require Import Common.
Require Import Tactics.
Require Import SpecLang.
Require Import CommonProofs.

Require Import Tactics.mint.

SetDefaultOpaques "ERC20".


Opaque LedgerLRecord.

Definition mint_balance_def (to__ : address) (amount : uint256) 
                            (ll: LedgerLRecord rec): Prop.
  execs0 (mint rec def to__ amount) : ll | "balanceOf" -> l1 | "balanceOf".
  con (balanceOf'[to__] = xIntPlus (balanceOf[to__]) amount).
Defined.

Lemma  mint_balance_prf (to__ : address) (amount : uint256)  (ll: LedgerLRecord rec):
       mint_balance_def to__ amount ll.
Proof.
  intros. unfold mint_balance_def. intros.

  mint_start_new_exec. mint_continue_all. simplify_all.

  destruct_ledger ll. subst P. rewrite ?toValue_false. rewrite ?toValue_uni_false.
 
  destruct pcd3. destruct msg14. destruct v9.
  (* simpl_ledger_fields (LedgerLRecord rec).  *)

  time (solve_exec_prop; compute).
  
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
  intros. unfold mint_totalSupply_def. intros.

  mint_start_new_exec. mint_continue_all. simplify_all.

  destruct_ledger ll. subst P. rewrite ?toValue_false. rewrite ?toValue_uni_false.
 
  destruct pcd3. destruct msg14. destruct v9.
  (* simpl_ledger_fields (LedgerLRecord rec).  *)

  time (solve_exec_prop; compute).
Time Qed.
