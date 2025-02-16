
Require Import ERC20.CommonHeader .

Require Import Tactics.transfer.
Require Import UrsusProofs.CommonTactics.

SetDefaultOpaques "ERC20".

Notation ULValue := (@ULValueP XBool XUInteger XMaybe XProd _ _ LocalStateLRecord _ _ _).

Definition transfer_fake_eval_def (ll: LedgerLRecord rec) (recipient : address)(amount : uint256) : Prop.
evals0 ( transfer rec def  recipient amount): ll -> v1.
con (v1 = ControlValue _ default).
Defined.

Definition transfer_fake_exec_def (ll: LedgerLRecord rec) (recipient : address)(amount : uint256) : Prop.
execs0 (transfer rec def  recipient amount): ll -> l1.
con (l1 = l0).
Defined.

Set Keyed Unification.

Lemma transfer_fake_eval_prf (ll: LedgerLRecord rec) (recipient : address)(amount : uint256) :
      transfer_fake_eval_def ll  recipient amount .
Proof.
  unfold transfer_fake_eval_def. intros.
  transfer_start_new_eval.
  transfer_continue_all.
  transfer_simpl_tail.
  simplify_all.
Abort.

Lemma transfer_fake_exec_prf (ll: LedgerLRecord rec) (recipient : address)(amount : uint256) :
      transfer_fake_exec_def ll  recipient amount .
Proof.
  unfold transfer_fake_exec_def. intros.
  time "transfer_start_new_exec" transfer_start_new_exec.
  time "transfer_continue_all" transfer_continue_all.
  transfer_simpl_tail.
  simplify_all.
Abort.


