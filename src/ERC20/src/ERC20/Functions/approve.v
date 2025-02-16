
Require Import ERC20.CommonHeader.

Require Import ERC20.Functions. 
Require Import ERC20.Common. 

(* SetUrsusOptions. *)

Definition approve_cbv (* (LocalStateLRecord : Type )(LocalDefault : XDefault LocalStateLRecord )(H2 : LocalStateField mapping LocalStateLRecord (bool)) *)
                             (LocalStateLRecord : Type )(LocalDefault : XDefault LocalStateLRecord )(H2 : LocalStateField mapping LocalStateLRecord (bool))(spender : address)(amount : uint256)
                 := Eval cbv beta zeta delta [approve staticLocalAssign new_lvalue00 UrsusNotations.new_lvalue00 SML_NG32.new_lvalue00] in 
                   (@approve (*  LocalStateLRecord LocalDefault H2 *) 
                                    LocalStateLRecord LocalDefault H2 spender amount).

Elpi SplitExpression approve_cbv ERC20 .

Definition approve_cbv_00 := Eval cbv beta delta [approve_cbv split_expression] in (approve_cbv).

Lemma approve_split_correct : approve = approve_cbv_00.
Proof.
  reflexivity.
Qed.

Lemma approve_split_correct_head0 : forall
                                    spender amount ,
          Uinterpreter (ledgerClass := (LedgerLLedgerClass rec def))
                       (approve_cbv_00 _ _ _  
                                    spender amount ) = 
          Uinterpreter (ledgerClass := (LedgerLLedgerClass rec def))
                       (approve_cbv_0 _ _ _  
                                    spender amount ) . reflexivity. Qed. 

(* Do not change the next two lines! *) 
Elpi FormingEvalsExecs Evals "Evals" "Execs" "Tactics" "Functions" "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Tactics/" ERC20 ERC20 approve ERC20_execs_for_roots_ "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Evals/" " H2" "(H2 : LocalStateField mapping LocalStateLRecord (bool))"  "_ _ _ " " spender amount" "Functions" "ERC20." .
Elpi FormingEvalsExecs Execs "Evals" "Execs" "Tactics" "Functions" "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Tactics/" ERC20 ERC20 approve ERC20_execs_for_roots_ "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Execs/" " H2" "(H2 : LocalStateField mapping LocalStateLRecord (bool))"  "_ _ _ " " spender amount" "Functions" "ERC20." .

