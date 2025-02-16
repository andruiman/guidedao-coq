Require Import ProofsHeader.
Require Import Tactics.constructor.

Definition constructor_name_def (name_ : string) (symbol_ : string) (decimals_ : uint8) 
                            (ll: LedgerLRecord rec): Prop.
  execs0 (constructor rec def name_ symbol_ decimals_) : ll -> l1 | "name".
  con (name = name_).
Defined.

Lemma constructor_name_prf 
      (name_ : string) (symbol_ : string) (decimals_ : uint8)  (ll: LedgerLRecord rec):
      constructor_name_def name_ symbol_ decimals_ ll.
Proof.
  start_proof.
  constructor_start.
  time prepare_all ll P. 
  compute_destructed_ledgers loc_.

  time
  bottom_up_goal_solver. (* 0.556 secs *)
Time Qed.
