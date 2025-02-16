Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UMLang.ExecGenerator.
Require Import UrsusContractCreator.IdentParsing.
Require Import UrsusContractCreator.StringHelpers.
Require Import UrsusLibExecs.All.

Require Export UrsusProofs.CommonTactics.

Tactic Notation "subst_needed" "in" hyp(H) :=
  idtac "substing needed in" H;
  repeat match reverse goal with
    | H' : ?y = _ |- _ =>
        match goal with
        | H'' : ?x |- _ =>
            match H'' with
            | H =>
                lazymatch H' with
                | H => fail
                | _ => match x with
                      | context [y] =>
                          subst y
                      end
                end
            end
        end
    end.

Ltac subst_needed :=
  idtac "substing needed in goal";
  clear_unneeded_hyps;
  repeat match reverse goal with
    | H : ?y = _ |- context [?y] =>
        subst y
    end.



(* TODO: still cannot move it somewhere *)
Require Import UrsusEnvironment.Solidity.current.Environment.

Require Import TVMModel.Notations.Loadable.
Require Import TVMModel.Notations.Storeable.
Require Import TVMModel.Base.Proofs.EncodeDecode.
Require Import TVMModel.Base.Definitions.TVMBitString.

Require Import SpecLang.

Ltac process_wellformed' Ledger C x prf :=
  multidestruct C;
  subst x; (* the term structured after decomposition *)
  match goal with
  | H: ?y = ?Y |- _ => let t := type of y in 
                          match Y with
                          | context [decode] =>
                              lazymatch t with
                              | @ControlResultP _ _ _ _ => eassert (y = ControlValue _ _);
                                                            [ > with_strategy opaque 
                                                            [unMaybe encode decode 
                                                            pair_storeable uint_storeable address_storeable
                                                            pair_loadable uint_loadable address_loadable] 
                                                            bottom_up_goal_solver' Ledger;
                                                            setoid_rewrite prf; [| try assumption ..];
                                                            reflexivity | clear H; try (setoid_rewrite prf; [ (* simpl *) | try assumption ..]) ]
                              | _ => idtac "do not have edefault for" t 
                              end   
                          end
  | _ => idtac "no decode found"
  end.

Module Type WithLedger.

Axiom Ledger: Type.

End WithLedger.

Module ContractTactics (WL: WithLedger).
Import WL.

Ltac bottom_up_goal_solver := let Ledger' := eval cbv delta [Ledger] in Ledger in bottom_up_goal_solver' Ledger'.
Ltac process_message_flags := let Ledger' := eval cbv delta [Ledger] in Ledger in process_message_flags' Ledger'.
Ltac compute_destructed_ledgers := let Ledger' := eval cbv delta [Ledger] in Ledger in compute_destructed_ledgers' Ledger'.
Ltac solve_full_error := let Ledger' := eval cbv delta [Ledger] in Ledger in solve_full_error' Ledger'.
Ltac try_auto_pure := let Ledger' := eval cbv delta [Ledger] in Ledger in try_auto_pure' Ledger'.

(* rewrite abtract tactic declared in CommonTactics *)
Ltac equalify_arguments := let Ledger' := eval cbv delta [Ledger] in Ledger in equalify_arguments' Ledger'.
Ltac unify_condition := let Ledger' := eval cbv delta [Ledger] in Ledger in unify_condition' Ledger'.
Ltac equalify_particular_arguments := let Ledger' := eval cbv delta [Ledger] in Ledger in equalify_particular_arguments' Ledger'.
Ltac find_destructed_ledger_subst_compute := let Ledger' := eval cbv delta [Ledger] in Ledger in find_destructed_ledger_subst_compute' Ledger'.
Ltac process_wellformed := let Ledger' := eval cbv delta [Ledger] in Ledger in process_wellformed' Ledger'.

Ltac process_multiexists := let Ledger' := eval cbv delta [Ledger] in Ledger in process_multiexists' Ledger'.

End ContractTactics.
