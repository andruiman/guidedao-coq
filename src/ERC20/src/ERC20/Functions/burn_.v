
Require Import ERC20.CommonHeader.

Require Import ERC20.Functions. 
Require Import ERC20.Common. 

(* SetUrsusOptions. *)

Definition burn__cbv (* (LocalStateLRecord : Type )(LocalDefault : XDefault LocalStateLRecord )(H : listInfiniteFunRec_gen XList) *)
                             (LocalStateLRecord : Type )(LocalDefault : XDefault LocalStateLRecord )(H : listInfiniteFunRec_gen XList)(from : address)(amount : uint256)
                 := Eval cbv beta zeta delta [burn_ staticLocalAssign new_lvalue00 UrsusNotations.new_lvalue00 SML_NG32.new_lvalue00] in 
                   (@burn_ (*  LocalStateLRecord LocalDefault H *) 
                                    LocalStateLRecord LocalDefault H from amount).

Elpi SplitExpression burn__cbv ERC20 .

Definition burn__cbv_00 := Eval cbv beta delta [burn__cbv split_expression] in (burn__cbv).

Lemma burn__split_correct : burn_ = burn__cbv_00.
Proof.
  reflexivity.
Qed.

Lemma burn__split_correct_head0 : forall
                                    from amount ,
          Uinterpreter (ledgerClass := (LedgerLLedgerClass rec def))
                       (burn__cbv_00 _ _ _  
                                    from amount ) = 
          Uinterpreter (ledgerClass := (LedgerLLedgerClass rec def))
                       (burn__cbv_0 _ _ _  
                                    from amount ) . reflexivity. Qed. 

(* Do not change the next two lines! *) 
Elpi FormingEvalsExecs Evals "Evals" "Execs" "Tactics" "Functions" "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Tactics/" ERC20 ERC20 burn_ ERC20_execs_for_roots_ "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Evals/" " H" "(H : listInfiniteFunRec_gen XList)"  "_ _ _ " " from amount" "Functions" "ERC20." .
Elpi FormingEvalsExecs Execs "Evals" "Execs" "Tactics" "Functions" "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Tactics/" ERC20 ERC20 burn_ ERC20_execs_for_roots_ "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Execs/" " H" "(H : listInfiniteFunRec_gen XList)"  "_ _ _ " " from amount" "Functions" "ERC20." .

