Require Export CommonTactics.

Require Import ERC20.ERC20.
Import ERC20.

Require Import ERC20.Common.

Module ERC20Ledger <: WithLedger.

Definition Ledger := LedgerLRecord rec.

End ERC20Ledger.

Module Export ContractTactics := ContractTactics ERC20Ledger.


