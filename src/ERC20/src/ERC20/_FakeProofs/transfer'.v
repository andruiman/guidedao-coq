
Require Import ERC20.CommonHeader .

Require Import Tactics.transfer'.
Require Import UrsusProofs.CommonTactics.

SetDefaultOpaques "ERC20".

Notation ULValue := (@ULValueP XBool XUInteger XMaybe XProd _ _ LocalStateLRecord _ _ _).

Definition transfer'_fake_eval_def (ll: LedgerLRecord rec) (recipient : address)(amount : uint256) : Prop.
evals0 ( transfer' rec def  recipient amount): ll -> v1.
con (v1 = ControlValue _ default).
Defined.

Definition transfer'_fake_exec_def (ll: LedgerLRecord rec) (recipient : address)(amount : uint256) : Prop.
execs0 (transfer' rec def  recipient amount): ll -> l1.
con (l1 = l0).
Defined.

Set Keyed Unification.

Lemma transfer'_fake_eval_prf (ll: LedgerLRecord rec) (recipient : address)(amount : uint256) :
      transfer'_fake_eval_def ll  recipient amount .
Proof.
  unfold transfer'_fake_eval_def. intros.
  transfer'_start_new_eval.
  transfer'_continue_all.
  transfer'_simpl_tail.
  simplify_all.
Abort.

Lemma transfer'_fake_exec_prf (ll: LedgerLRecord rec) (recipient : address)(amount : uint256) :
      transfer'_fake_exec_def ll  recipient amount .
Proof.
  unfold transfer'_fake_exec_def. intros.
  time "transfer'_start_new_exec" transfer'_start_new_exec.
  time "transfer'_continue_all" transfer'_continue_all.
  transfer'_simpl_tail.
  simplify_all.
Abort.


