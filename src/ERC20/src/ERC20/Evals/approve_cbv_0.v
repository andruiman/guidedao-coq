
Require Import ERC20.CommonHeader .

Require Import ERC20.Functions.approve. (* ERC20. *)

Require Import ERC20.Functions.
Require Import ERC20.Common. 

Notation ULValue := (@ULValueP XBool XUInteger XMaybe XProd _ _ LocalStateLRecord _ _ _).

Definition approve_cbv_0_eval_sig (spender : address)(amount : uint256) (l : LedgerLRecord rec) :
  {t | t = eval_state (Uinterpreter (approve_cbv_0 rec def (*  *) _   spender amount)) l}.
  unfold approve_cbv_0 .
  unfold approve, allowance_left.
  unfold urvalue_expression; fold XHMap XProd XMaybe XUInteger XBool.

  unfold default_with_sigmafield,
  urgenerate_field, generate_field.

  unfold messageLQ, IDefaultMQ, IDefault_left.

  unfold_interfaces. unfold_coercions. unfold_arith. unfold_common.  

  simpl orb. cbv iota. 

 (* αunfold  *)

  (* Check LocalStateField7. *)
  (* time "approve_cbv_0_exec_sig:" *) repeat auto_build_P listInfinite.
Defined.

Definition approve_cbv_0_eval_sig_beta 
          := Eval cbv beta zeta delta [approve_cbv_0_eval_sig] in approve_cbv_0_eval_sig.

(* Time *) Elpi ClearMatches approve_cbv_0_eval_sig_beta approve_cbv_0_eval.


Definition approve_cbv_0_eval_flat (spender : address)(amount : uint256) (l: LedgerLRecord rec): ControlResultL (LedgerLRecord rec) ( bool ) (false || false) .
  let t := eval cbv beta delta [approve_cbv_0_eval_elpi] in 
                         (approve_cbv_0_eval_elpi  spender amount l) in 
                           flatten_lets_build_without_prop t .
(* Time *) Defined.

(* Time *) Elpi ChangeNonUniqueLets approve_cbv_0_eval_flat approve_cbv_0_eval.

 (*ν*)  Elpi GlobalConstExtract Evals approve_cbv_0_eval approve_cbv_0 / "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Evals" _eval_prf.v "Functions" "Contract" . (*η*)

