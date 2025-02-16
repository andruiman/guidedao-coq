
Require Import ERC20.CommonHeader .

Require Import ERC20.Functions.burn. (* ERC20. *)

Require Import ERC20.Functions.
Require Import ERC20.Common. 

Notation ULValue := (@ULValueP XBool XUInteger XMaybe XProd _ _ LocalStateLRecord _ _ _).

Definition burn_cbv_0_eval_sig (from : address)(amount : uint256) (l : LedgerLRecord rec) :
  {t | t = eval_state (Uinterpreter (burn_cbv_0 rec def (*  *) _   from amount)) l}.
  unfold burn_cbv_0 .
  unfold burn, burn__left.
  unfold urvalue_expression; fold XHMap XProd XMaybe XUInteger XBool.

  unfold default_with_sigmafield,
  urgenerate_field, generate_field.

  unfold messageLQ, IDefaultMQ, IDefault_left.

  unfold_interfaces. unfold_coercions. unfold_arith. unfold_common.  

  simpl orb. cbv iota. 

 (* αunfold  *)

  (* Check LocalStateField7. *)
  (* time "burn_cbv_0_exec_sig:" *) repeat auto_build_P listInfinite.
Defined.

Definition burn_cbv_0_eval_sig_beta 
          := Eval cbv beta zeta delta [burn_cbv_0_eval_sig] in burn_cbv_0_eval_sig.

(* Time *) Elpi ClearMatches burn_cbv_0_eval_sig_beta burn_cbv_0_eval.


Definition burn_cbv_0_eval_flat (from : address)(amount : uint256) (l: LedgerLRecord rec): ControlResultL (LedgerLRecord rec) ( PhantomType ) (false || false) .
  let t := eval cbv beta delta [burn_cbv_0_eval_elpi] in 
                         (burn_cbv_0_eval_elpi  from amount l) in 
                           flatten_lets_build_without_prop t .
(* Time *) Defined.

(* Time *) Elpi ChangeNonUniqueLets burn_cbv_0_eval_flat burn_cbv_0_eval.

 (*ν*)  Elpi GlobalConstExtract Evals burn_cbv_0_eval burn_cbv_0 / "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Evals" _eval_prf.v "Functions" "Contract" . (*η*)

