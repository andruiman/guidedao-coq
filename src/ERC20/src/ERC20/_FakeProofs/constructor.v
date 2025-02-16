
Require Import ERC20.CommonHeader .

Require Import Tactics.constructor.
Require Import UrsusProofs.CommonTactics.

SetDefaultOpaques "ERC20".

Notation ULValue := (@ULValueP XBool XUInteger XMaybe XProd _ _ LocalStateLRecord _ _ _).

Definition constructor_fake_eval_def (ll: LedgerLRecord rec) (name_ : string)(symbol_ : string)(decimals_ : uint8) : Prop.
evals0 ( constructor rec def  name_ symbol_ decimals_): ll -> v1.
con (v1 = ControlValue _ default).
Defined.

Definition constructor_fake_exec_def (ll: LedgerLRecord rec) (name_ : string)(symbol_ : string)(decimals_ : uint8) : Prop.
execs0 (constructor rec def  name_ symbol_ decimals_): ll -> l1.
con (l1 = l0).
Defined.

Set Keyed Unification.

Lemma constructor_fake_eval_prf (ll: LedgerLRecord rec) (name_ : string)(symbol_ : string)(decimals_ : uint8) :
      constructor_fake_eval_def ll  name_ symbol_ decimals_ .
Proof.
  unfold constructor_fake_eval_def. intros.
  constructor_start_new_eval.
  constructor_continue_all.
  constructor_simpl_tail.
  simplify_all.
Abort.

Lemma constructor_fake_exec_prf (ll: LedgerLRecord rec) (name_ : string)(symbol_ : string)(decimals_ : uint8) :
      constructor_fake_exec_def ll  name_ symbol_ decimals_ .
Proof.
  unfold constructor_fake_exec_def. intros.
  time "constructor_start_new_exec" constructor_start_new_exec.
  time "constructor_continue_all" constructor_continue_all.
  constructor_simpl_tail.
  simplify_all.
Abort.


