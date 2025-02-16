
Require Import ERC20.CommonHeader .

Require Import Tactics.burn.
Require Import UrsusProofs.CommonTactics.

SetDefaultOpaques "ERC20".

Notation ULValue := (@ULValueP XBool XUInteger XMaybe XProd _ _ LocalStateLRecord _ _ _).

Definition burn_fake_eval_def (ll: LedgerLRecord rec) (from : address)(amount : uint256) : Prop.
evals0 ( burn rec def  from amount): ll -> v1.
con (v1 = ControlValue _ default).
Defined.

Definition burn_fake_exec_def (ll: LedgerLRecord rec) (from : address)(amount : uint256) : Prop.
execs0 (burn rec def  from amount): ll -> l1.
con (l1 = l0).
Defined.

Set Keyed Unification.

Lemma burn_fake_eval_prf (ll: LedgerLRecord rec) (from : address)(amount : uint256) :
      burn_fake_eval_def ll  from amount .
Proof.
  unfold burn_fake_eval_def. intros.
  burn_start_new_eval.
  burn_continue_all.
  burn_simpl_tail.
  simplify_all.
Abort.

Lemma burn_fake_exec_prf (ll: LedgerLRecord rec) (from : address)(amount : uint256) :
      burn_fake_exec_def ll  from amount .
Proof.
  unfold burn_fake_exec_def. intros.
  time "burn_start_new_exec" burn_start_new_exec.
  time "burn_continue_all" burn_continue_all.
  burn_simpl_tail.
  simplify_all.
Abort.


