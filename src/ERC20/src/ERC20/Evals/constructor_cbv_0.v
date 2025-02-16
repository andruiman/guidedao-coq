
Require Import ERC20.CommonHeader .

Require Import ERC20.Functions.constructor. (* ERC20. *)

Require Import ERC20.Functions.
Require Import ERC20.Common. 

Notation ULValue := (@ULValueP XBool XUInteger XMaybe XProd _ _ LocalStateLRecord _ _ _).

Definition constructor_cbv_0_eval_sig (name_ : string)(symbol_ : string)(decimals_ : uint8) (l : LedgerLRecord rec) :
  {t | t = eval_state (Uinterpreter (constructor_cbv_0 rec def (*  *)   name_ symbol_ decimals_)) l}.
  unfold constructor_cbv_0 .
  unfold constructor, decimals_left, symbol_left, name_left.
  unfold urvalue_expression; fold XHMap XProd XMaybe XUInteger XBool.

  unfold default_with_sigmafield,
  urgenerate_field, generate_field.

  unfold messageLQ, IDefaultMQ, IDefault_left.

  unfold_interfaces. unfold_coercions. unfold_arith. unfold_common.  

  simpl orb. cbv iota. 

 (* αunfold  *)

  (* Check LocalStateField7. *)
  (* time "constructor_cbv_0_exec_sig:" *) repeat auto_build_P listInfinite.
Defined.

Definition constructor_cbv_0_eval_sig_beta 
          := Eval cbv beta zeta delta [constructor_cbv_0_eval_sig] in constructor_cbv_0_eval_sig.

(* Time *) Elpi ClearMatches constructor_cbv_0_eval_sig_beta constructor_cbv_0_eval.


Definition constructor_cbv_0_eval_flat (name_ : string)(symbol_ : string)(decimals_ : uint8) (l: LedgerLRecord rec): ControlResultL (LedgerLRecord rec) ( PhantomType ) (false || false) .
  let t := eval cbv beta delta [constructor_cbv_0_eval_elpi] in 
                         (constructor_cbv_0_eval_elpi  name_ symbol_ decimals_ l) in 
                           flatten_lets_build_without_prop t .
(* Time *) Defined.

(* Time *) Elpi ChangeNonUniqueLets constructor_cbv_0_eval_flat constructor_cbv_0_eval.

 (*ν*)  Elpi GlobalConstExtract Evals constructor_cbv_0_eval constructor_cbv_0 / "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Evals" _eval_prf.v "Functions" "Contract" . (*η*)

