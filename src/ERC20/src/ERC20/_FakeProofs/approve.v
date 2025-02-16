
Require Import ERC20.CommonHeader .

Require Import Tactics.approve.
Require Import UrsusProofs.CommonTactics.

SetDefaultOpaques "ERC20".

Notation ULValue := (@ULValueP XBool XUInteger XMaybe XProd _ _ LocalStateLRecord _ _ _).

Definition approve_fake_eval_def (ll: LedgerLRecord rec) (spender : address)(amount : uint256) : Prop.
evals0 ( approve rec def  spender amount): ll -> v1.
con (v1 = ControlValue _ default).
Defined.

Definition approve_fake_exec_def (ll: LedgerLRecord rec) (spender : address)(amount : uint256) : Prop.
execs0 (approve rec def  spender amount): ll -> l1.
con (l1 = l0).
Defined.

Set Keyed Unification.

Lemma approve_fake_eval_prf (ll: LedgerLRecord rec) (spender : address)(amount : uint256) :
      approve_fake_eval_def ll  spender amount .
Proof.
  unfold approve_fake_eval_def. intros.
  approve_start_new_eval.
  approve_continue_all.
  approve_simpl_tail.
  simplify_all.
Abort.

Lemma approve_fake_exec_prf (ll: LedgerLRecord rec) (spender : address)(amount : uint256) :
      approve_fake_exec_def ll  spender amount .
Proof.
  unfold approve_fake_exec_def. intros.
  time "approve_start_new_exec" approve_start_new_exec.
  time "approve_continue_all" approve_continue_all.
  approve_simpl_tail.
  simplify_all.
Abort.


