Require Import UrsusEnvironment.Solidity.current.Environment.
From Hammer Require Import Tactics Hammer. 

Require Import UMLang.ExecGenerator.

Require Import ERC20.ERC20.
Import ERC20.
Require Import Common.
Require Import Tactics.
Require Import SpecLang.
Require Import CommonProofs.

Require Import Tactics.constructor.

SetDefaultOpaques "ERC20".

Opaque LedgerLRecord.

Definition constructor_name_def (name_ : string) (symbol_ : string) (decimals_ : uint8) 
                            (ll: LedgerLRecord rec): Prop.
  execs0 (constructor rec def name_ symbol_ decimals_) : ll -> l1 | "name".
  con (name = name_).
Defined.

Lemma constructor_name_prf (name_ : string) (symbol_ : string) (decimals_ : uint8)  (ll: LedgerLRecord rec):
    constructor_name_def name_ symbol_ decimals_ ll.
Proof.
  intros. unfold constructor_name_def. intros.

  constructor_start_new_exec. simplify_all.

  destruct_ledger ll. subst P. rewrite ?toValue_false. rewrite ?toValue_uni_false.
 
  destruct pcd3. destruct msg14. destruct v9.
  (* simpl_ledger_fields (LedgerLRecord rec).  *)
  compute in H.

  time (solve_exec_prop; compute).
Time Qed.
