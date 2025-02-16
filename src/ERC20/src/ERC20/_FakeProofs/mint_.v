
Require Import ERC20.CommonHeader .

Require Import Tactics.mint_.
Require Import UrsusProofs.CommonTactics.

SetDefaultOpaques "ERC20".

Notation ULValue := (@ULValueP XBool XUInteger XMaybe XProd _ _ LocalStateLRecord _ _ _).

Definition mint__fake_eval_def (ll: LedgerLRecord rec) (to__ : address)(amount : uint256) : Prop.
evals0 ( mint_ rec def  to__ amount): ll -> v1.
con (v1 = ControlValue _ default).
Defined.

Definition mint__fake_exec_def (ll: LedgerLRecord rec) (to__ : address)(amount : uint256) : Prop.
execs0 (mint_ rec def  to__ amount): ll -> l1.
con (l1 = l0).
Defined.

Set Keyed Unification.

Lemma mint__fake_eval_prf (ll: LedgerLRecord rec) (to__ : address)(amount : uint256) :
      mint__fake_eval_def ll  to__ amount .
Proof.
  unfold mint__fake_eval_def. intros.
  mint__start_new_eval.
  mint__continue_all.
  mint__simpl_tail.
  simplify_all.
Abort.

Lemma mint__fake_exec_prf (ll: LedgerLRecord rec) (to__ : address)(amount : uint256) :
      mint__fake_exec_def ll  to__ amount .
Proof.
  unfold mint__fake_exec_def. intros.
  time "mint__start_new_exec" mint__start_new_exec.
  time "mint__continue_all" mint__continue_all.
  mint__simpl_tail.
  simplify_all.
Abort.


