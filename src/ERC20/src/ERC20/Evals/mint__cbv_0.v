
Require Import ERC20.CommonHeader .

Require Import ERC20.Functions.mint_. (* ERC20. *)

Require Import ERC20.Functions.
Require Import ERC20.Common. 

Notation ULValue := (@ULValueP XBool XUInteger XMaybe XProd _ _ LocalStateLRecord _ _ _).

Definition mint__cbv_0_eval_sig (to__ : address)(amount : uint256) (l : LedgerLRecord rec) :
  {t | t = eval_state (Uinterpreter (mint__cbv_0 rec def (*  *) _   to__ amount)) l}.
  unfold mint__cbv_0 .
  unfold mint_, totalSupply_left, plusassign_left, balanceOf_left.
  unfold urvalue_expression; fold XHMap XProd XMaybe XUInteger XBool.

  unfold default_with_sigmafield,
  urgenerate_field, generate_field.

  unfold messageLQ, IDefaultMQ, IDefault_left.

  unfold_interfaces. unfold_coercions. unfold_arith. unfold_common.  

  simpl orb. cbv iota. 

 (* αunfold  *)

  (* Check LocalStateField7. *)
  (* time "mint__cbv_0_exec_sig:" *) repeat auto_build_P listInfinite.
Defined.

Definition mint__cbv_0_eval_sig_beta 
          := Eval cbv beta zeta delta [mint__cbv_0_eval_sig] in mint__cbv_0_eval_sig.

(* Time *) Elpi ClearMatches mint__cbv_0_eval_sig_beta mint__cbv_0_eval.


Definition mint__cbv_0_eval_flat (to__ : address)(amount : uint256) (l: LedgerLRecord rec): ControlResultL (LedgerLRecord rec) ( PhantomType ) (false || false) .
  let t := eval cbv beta delta [mint__cbv_0_eval_elpi] in 
                         (mint__cbv_0_eval_elpi  to__ amount l) in 
                           flatten_lets_build_without_prop t .
(* Time *) Defined.

(* Time *) Elpi ChangeNonUniqueLets mint__cbv_0_eval_flat mint__cbv_0_eval.

 (*ν*)  Elpi GlobalConstExtract Evals mint__cbv_0_eval mint__cbv_0 / "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Evals" _eval_prf.v "Functions" "Contract" . (*η*)

