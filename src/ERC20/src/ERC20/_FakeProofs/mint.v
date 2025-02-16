
Require Import ERC20.CommonHeader .

Require Import Tactics.mint.
Require Import UrsusProofs.CommonTactics.

SetDefaultOpaques "ERC20".

Notation ULValue := (@ULValueP XBool XUInteger XMaybe XProd _ _ LocalStateLRecord _ _ _).

Definition mint_fake_eval_def (ll: LedgerLRecord rec) (to__ : address)(amount : uint256) : Prop.
evals0 ( mint rec def  to__ amount): ll -> v1.
con (v1 = ControlValue _ default).
Defined.

Definition mint_fake_exec_def (ll: LedgerLRecord rec) (to__ : address)(amount : uint256) : Prop.
execs0 (mint rec def  to__ amount): ll -> l1.
con (l1 = l0).
Defined.

Set Keyed Unification.

Lemma mint_fake_eval_prf (ll: LedgerLRecord rec) (to__ : address)(amount : uint256) :
      mint_fake_eval_def ll  to__ amount .
Proof.
  unfold mint_fake_eval_def. intros.
  mint_start_new_eval.
  mint_continue_all.
  mint_simpl_tail.
  simplify_all.
Abort.

Lemma mint_fake_exec_prf (ll: LedgerLRecord rec) (to__ : address)(amount : uint256) :
      mint_fake_exec_def ll  to__ amount .
Proof.
  unfold mint_fake_exec_def. intros.
  time "mint_start_new_exec" mint_start_new_exec.
  time "mint_continue_all" mint_continue_all.
  mint_simpl_tail.
  simplify_all.
Abort.


