
Require Import ERC20.CommonHeader .

Require Import Tactics.burn_.
Require Import UrsusProofs.CommonTactics.

SetDefaultOpaques "ERC20".

Notation ULValue := (@ULValueP XBool XUInteger XMaybe XProd _ _ LocalStateLRecord _ _ _).

Definition burn__fake_eval_def (ll: LedgerLRecord rec) (from : address)(amount : uint256) : Prop.
evals0 ( burn_ rec def  from amount): ll -> v1.
con (v1 = ControlValue _ default).
Defined.

Definition burn__fake_exec_def (ll: LedgerLRecord rec) (from : address)(amount : uint256) : Prop.
execs0 (burn_ rec def  from amount): ll -> l1.
con (l1 = l0).
Defined.

Set Keyed Unification.

Lemma burn__fake_eval_prf (ll: LedgerLRecord rec) (from : address)(amount : uint256) :
      burn__fake_eval_def ll  from amount .
Proof.
  unfold burn__fake_eval_def. intros.
  burn__start_new_eval.
  burn__continue_all.
  burn__simpl_tail.
  simplify_all.
Abort.

Lemma burn__fake_exec_prf (ll: LedgerLRecord rec) (from : address)(amount : uint256) :
      burn__fake_exec_def ll  from amount .
Proof.
  unfold burn__fake_exec_def. intros.
  time "burn__start_new_exec" burn__start_new_exec.
  time "burn__continue_all" burn__continue_all.
  burn__simpl_tail.
  simplify_all.
Abort.


