
Require Import ERC20.CommonHeader .

Require Import Tactics.transferFrom.
Require Import UrsusProofs.CommonTactics.

SetDefaultOpaques "ERC20".

Notation ULValue := (@ULValueP XBool XUInteger XMaybe XProd _ _ LocalStateLRecord _ _ _).

Definition transferFrom_fake_eval_def (ll: LedgerLRecord rec) (sender : address)(recipient : address)(amount : uint256) : Prop.
evals0 ( transferFrom rec def  sender recipient amount): ll -> v1.
con (v1 = ControlValue _ default).
Defined.

Definition transferFrom_fake_exec_def (ll: LedgerLRecord rec) (sender : address)(recipient : address)(amount : uint256) : Prop.
execs0 (transferFrom rec def  sender recipient amount): ll -> l1.
con (l1 = l0).
Defined.

Set Keyed Unification.

Lemma transferFrom_fake_eval_prf (ll: LedgerLRecord rec) (sender : address)(recipient : address)(amount : uint256) :
      transferFrom_fake_eval_def ll  sender recipient amount .
Proof.
  unfold transferFrom_fake_eval_def. intros.
  transferFrom_start_new_eval.
  transferFrom_continue_all.
  transferFrom_simpl_tail.
  simplify_all.
Abort.

Lemma transferFrom_fake_exec_prf (ll: LedgerLRecord rec) (sender : address)(recipient : address)(amount : uint256) :
      transferFrom_fake_exec_def ll  sender recipient amount .
Proof.
  unfold transferFrom_fake_exec_def. intros.
  time "transferFrom_start_new_exec" transferFrom_start_new_exec.
  time "transferFrom_continue_all" transferFrom_continue_all.
  transferFrom_simpl_tail.
  simplify_all.
Abort.


