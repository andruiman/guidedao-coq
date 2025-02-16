
Require Import ERC20.CommonHeader.

Require Import ERC20.Functions. 
Require Import ERC20.Common. 

(* SetUrsusOptions. *)

Definition mint__cbv (* (LocalStateLRecord : Type )(LocalDefault : XDefault LocalStateLRecord )(H : listInfiniteFunRec_gen XList) *)
                             (LocalStateLRecord : Type )(LocalDefault : XDefault LocalStateLRecord )(H : listInfiniteFunRec_gen XList)(to__ : address)(amount : uint256)
                 := Eval cbv beta zeta delta [mint_ staticLocalAssign new_lvalue00 UrsusNotations.new_lvalue00 SML_NG32.new_lvalue00] in 
                   (@mint_ (*  LocalStateLRecord LocalDefault H *) 
                                    LocalStateLRecord LocalDefault H to__ amount).

Elpi SplitExpression mint__cbv ERC20 .

Definition mint__cbv_00 := Eval cbv beta delta [mint__cbv split_expression] in (mint__cbv).

Lemma mint__split_correct : mint_ = mint__cbv_00.
Proof.
  reflexivity.
Qed.

Lemma mint__split_correct_head0 : forall
                                    to__ amount ,
          Uinterpreter (ledgerClass := (LedgerLLedgerClass rec def))
                       (mint__cbv_00 _ _ _  
                                    to__ amount ) = 
          Uinterpreter (ledgerClass := (LedgerLLedgerClass rec def))
                       (mint__cbv_0 _ _ _  
                                    to__ amount ) . reflexivity. Qed. 

(* Do not change the next two lines! *) 
Elpi FormingEvalsExecs Evals "Evals" "Execs" "Tactics" "Functions" "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Tactics/" ERC20 ERC20 mint_ ERC20_execs_for_roots_ "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Evals/" " H" "(H : listInfiniteFunRec_gen XList)"  "_ _ _ " " to__ amount" "Functions" "ERC20." .
Elpi FormingEvalsExecs Execs "Evals" "Execs" "Tactics" "Functions" "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Tactics/" ERC20 ERC20 mint_ ERC20_execs_for_roots_ "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Execs/" " H" "(H : listInfiniteFunRec_gen XList)"  "_ _ _ " " to__ amount" "Functions" "ERC20." .

