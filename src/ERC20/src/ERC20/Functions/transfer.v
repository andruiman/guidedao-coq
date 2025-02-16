
Require Import ERC20.CommonHeader.

Require Import ERC20.Functions. 
Require Import ERC20.Common. 

(* SetUrsusOptions. *)

Definition transfer_cbv (* (LocalStateLRecord : Type )(LocalDefault : XDefault LocalStateLRecord )(H : listInfiniteFunRec_gen XList)(H2 : LocalStateField mapping LocalStateLRecord (bool)) *)
                             (LocalStateLRecord : Type )(LocalDefault : XDefault LocalStateLRecord )(H : listInfiniteFunRec_gen XList)(H2 : LocalStateField mapping LocalStateLRecord (bool))(recipient : address)(amount : uint256)
                 := Eval cbv beta zeta delta [transfer staticLocalAssign new_lvalue00 UrsusNotations.new_lvalue00 SML_NG32.new_lvalue00] in 
                   (@transfer (*  LocalStateLRecord LocalDefault H H2 *) 
                                    LocalStateLRecord LocalDefault H H2 recipient amount).

Elpi SplitExpression transfer_cbv ERC20 .

Definition transfer_cbv_00 := Eval cbv beta delta [transfer_cbv split_expression] in (transfer_cbv).

Lemma transfer_split_correct : transfer = transfer_cbv_00.
Proof.
  reflexivity.
Qed.

Lemma transfer_split_correct_head0 : forall
                                    recipient amount ,
          Uinterpreter (ledgerClass := (LedgerLLedgerClass rec def))
                       (transfer_cbv_00 _ _ _ _  
                                    recipient amount ) = 
          Uinterpreter (ledgerClass := (LedgerLLedgerClass rec def))
                       (transfer_cbv_0 _ _ _ _  
                                    recipient amount ) . reflexivity. Qed. 

(* Do not change the next two lines! *) 
Elpi FormingEvalsExecs Evals "Evals" "Execs" "Tactics" "Functions" "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Tactics/" ERC20 ERC20 transfer ERC20_execs_for_roots_ "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Evals/" " H H2" "(H : listInfiniteFunRec_gen XList)(H2 : LocalStateField mapping LocalStateLRecord (bool))"  "_ _ _ _ " " recipient amount" "Functions" "ERC20." .
Elpi FormingEvalsExecs Execs "Evals" "Execs" "Tactics" "Functions" "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Tactics/" ERC20 ERC20 transfer ERC20_execs_for_roots_ "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Execs/" " H H2" "(H : listInfiniteFunRec_gen XList)(H2 : LocalStateField mapping LocalStateLRecord (bool))"  "_ _ _ _ " " recipient amount" "Functions" "ERC20." .

