
Require Import ERC20.CommonHeader .

Require Import ERC20.Functions.transferFrom. (* ERC20. *)

Require Import ERC20.Functions.
Require Import ERC20.Common. 

Notation ULValue := (@ULValueP XBool XUInteger XMaybe XProd _ _ LocalStateLRecord _ _ _).

Definition transferFrom_cbv_0_eval_sig (sender : address)(recipient : address)(amount : uint256) (l : LedgerLRecord rec) :
  {t | t = eval_state (Uinterpreter (transferFrom_cbv_0 rec def (*  *) _ _   sender recipient amount)) l}.
  unfold transferFrom_cbv_0 .
  unfold transferFrom, balanceOf_left, plusassign_left, minusassign_left, allowance_left.
  unfold urvalue_expression; fold XHMap XProd XMaybe XUInteger XBool.

  unfold default_with_sigmafield,
  urgenerate_field, generate_field.

  unfold messageLQ, IDefaultMQ, IDefault_left.

  unfold_interfaces. unfold_coercions. unfold_arith. unfold_common.  

  simpl orb. cbv iota. 

 (* αunfold  *)

  (* Check LocalStateField7. *)
  (* time "transferFrom_cbv_0_exec_sig:" *) repeat auto_build_P listInfinite.
Defined.

Definition transferFrom_cbv_0_eval_sig_beta 
          := Eval cbv beta zeta delta [transferFrom_cbv_0_eval_sig] in transferFrom_cbv_0_eval_sig.

(* Time *) Elpi ClearMatches transferFrom_cbv_0_eval_sig_beta transferFrom_cbv_0_eval.


Definition transferFrom_cbv_0_eval_flat (sender : address)(recipient : address)(amount : uint256) (l: LedgerLRecord rec): ControlResultL (LedgerLRecord rec) ( bool ) (false || false) .
  let t := eval cbv beta delta [transferFrom_cbv_0_eval_elpi] in 
                         (transferFrom_cbv_0_eval_elpi  sender recipient amount l) in 
                           flatten_lets_build_without_prop t .
(* Time *) Defined.

(* Time *) Elpi ChangeNonUniqueLets transferFrom_cbv_0_eval_flat transferFrom_cbv_0_eval.

 (*ν*)  Elpi GlobalConstExtract Evals transferFrom_cbv_0_eval transferFrom_cbv_0 / "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Evals" _eval_prf.v "Functions" "Contract" . (*η*)

