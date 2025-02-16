
Require Import ERC20.CommonHeader .

Require Import ERC20.Functions.transfer. (* ERC20. *)

Require Import ERC20.Functions.
Require Import ERC20.Common. 

Notation ULValue := (@ULValueP XBool XUInteger XMaybe XProd _ _ LocalStateLRecord _ _ _).

Definition transfer_cbv_0_eval_sig (recipient : address)(amount : uint256) (l : LedgerLRecord rec) :
  {t | t = eval_state (Uinterpreter (transfer_cbv_0 rec def (*  *) _ _   recipient amount)) l}.
  unfold transfer_cbv_0 .
  unfold transfer, balanceOf_left, plusassign_left, balanceOf_right.
  unfold urvalue_expression; fold XHMap XProd XMaybe XUInteger XBool.

  unfold default_with_sigmafield,
  urgenerate_field, generate_field.

  unfold messageLQ, IDefaultMQ, IDefault_left.

  unfold_interfaces. unfold_coercions. unfold_arith. unfold_common.  

  simpl orb. cbv iota. 

 (* αunfold  *)

  (* Check LocalStateField7. *)
  (* time "transfer_cbv_0_exec_sig:" *) repeat auto_build_P listInfinite.
Defined.

Definition transfer_cbv_0_eval_sig_beta 
          := Eval cbv beta zeta delta [transfer_cbv_0_eval_sig] in transfer_cbv_0_eval_sig.

(* Time *) Elpi ClearMatches transfer_cbv_0_eval_sig_beta transfer_cbv_0_eval.


Definition transfer_cbv_0_eval_flat (recipient : address)(amount : uint256) (l: LedgerLRecord rec): ControlResultL (LedgerLRecord rec) ( bool ) (false || false) .
  let t := eval cbv beta delta [transfer_cbv_0_eval_elpi] in 
                         (transfer_cbv_0_eval_elpi  recipient amount l) in 
                           flatten_lets_build_without_prop t .
(* Time *) Defined.

(* Time *) Elpi ChangeNonUniqueLets transfer_cbv_0_eval_flat transfer_cbv_0_eval.

 (*ν*)  Elpi GlobalConstExtract Evals transfer_cbv_0_eval transfer_cbv_0 / "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Evals" _eval_prf.v "Functions" "Contract" . (*η*)

