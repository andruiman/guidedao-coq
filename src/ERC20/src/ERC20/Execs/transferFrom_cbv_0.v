
Require Import ERC20.CommonHeader.

Require Import ERC20.Functions.transferFrom. (* ERC20. *)

Require Import ERC20.Functions.
Require Import ERC20.Common. 

Notation ULValue := (@ULValueP XBool XUInteger XMaybe XProd _ _ LocalStateLRecord _ _ _).

Definition transferFrom_cbv_0_exec_sig (sender : address)(recipient : address)(amount : uint256) (l : LedgerLRecord rec) :
  {t | t = exec_state (Uinterpreter (transferFrom_cbv_0 rec def (*  *) _ _   sender recipient amount)) l}.
  unfold transferFrom_cbv_0 .
  unfold transferFrom, balanceOf_left, plusassign_left, minusassign_left, allowance_left.
  unfold urvalue_expression; fold XHMap XProd XMaybe XUInteger XBool.

  unfold default_with_sigmafield,
  urgenerate_field, generate_field.

  unfold messageLQ, IDefaultMQ, IDefault_left.

  unfold_interfaces. unfold_coercions. unfold_arith. unfold_common.  

  (* αunfold *) 
  simpl orb. cbv iota. 

  (* Check LocalStateField7. *)
  (* time "transferFrom_cbv_0_exec_sig:" *) repeat auto_build_P listInfinite.
Defined.

(* Time *) 
  Definition transferFrom_cbv_0_exec_sig_beta 
          := Eval cbv beta zeta delta [transferFrom_cbv_0_exec_sig] in transferFrom_cbv_0_exec_sig.

(* Time *) Elpi ClearMatches transferFrom_cbv_0_exec_sig_beta transferFrom_cbv_0_exec.

Definition transferFrom_cbv_0_exec_flat (sender : address)(recipient : address)(amount : uint256) (l: LedgerLRecord rec): LedgerLRecord rec.
  let t := eval cbv beta delta [transferFrom_cbv_0_exec_elpi] in 
                         (transferFrom_cbv_0_exec_elpi  sender recipient amount l) in 
                           flatten_lets_build_without_prop t .
(* Time *) Defined.

(* Time *) Elpi ChangeNonUniqueLets transferFrom_cbv_0_exec_flat transferFrom_cbv_0_exec.

(*ν*)  Elpi GlobalConstExtract Execs transferFrom_cbv_0_exec transferFrom_cbv_0 / "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Execs" _exec_prf.v "Functions" "ERC20." . (*η*)

