
Require Import ERC20.CommonHeader.

Require Import ERC20.Functions. 
Require Import ERC20.Common. 

(* SetUrsusOptions. *)

Definition constructor_cbv (* (LocalStateLRecord : Type )(LocalDefault : XDefault LocalStateLRecord ) *)
                             (LocalStateLRecord : Type )(LocalDefault : XDefault LocalStateLRecord )(name_ : string)(symbol_ : string)(decimals_ : uint8)
                 := Eval cbv beta zeta delta [constructor staticLocalAssign new_lvalue00 UrsusNotations.new_lvalue00 SML_NG32.new_lvalue00] in 
                   (@constructor (*  LocalStateLRecord LocalDefault *) 
                                    LocalStateLRecord LocalDefault name_ symbol_ decimals_).

Elpi SplitExpression constructor_cbv ERC20 .

Definition constructor_cbv_00 := Eval cbv beta delta [constructor_cbv split_expression] in (constructor_cbv).

Lemma constructor_split_correct : constructor = constructor_cbv_00.
Proof.
  reflexivity.
Qed.

Lemma constructor_split_correct_head0 : forall
                                    name_ symbol_ decimals_ ,
          Uinterpreter (ledgerClass := (LedgerLLedgerClass rec def))
                       (constructor_cbv_00 _ _  
                                    name_ symbol_ decimals_ ) = 
          Uinterpreter (ledgerClass := (LedgerLLedgerClass rec def))
                       (constructor_cbv_0 _ _  
                                    name_ symbol_ decimals_ ) . reflexivity. Qed. 

(* Do not change the next two lines! *) 
Elpi FormingEvalsExecs Evals "Evals" "Execs" "Tactics" "Functions" "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Tactics/" ERC20 ERC20 constructor ERC20_execs_for_roots_ "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Evals/" "" " "  "_ _ " " name_ symbol_ decimals_" "Functions" "ERC20." .
Elpi FormingEvalsExecs Execs "Evals" "Execs" "Tactics" "Functions" "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Tactics/" ERC20 ERC20 constructor ERC20_execs_for_roots_ "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Execs/" "" " "  "_ _ " " name_ symbol_ decimals_" "Functions" "ERC20." .

