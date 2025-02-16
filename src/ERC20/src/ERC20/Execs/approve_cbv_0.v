
Require Import ERC20.CommonHeader.

Require Import ERC20.Functions.approve. (* ERC20. *)

Require Import ERC20.Functions.
Require Import ERC20.Common. 

Notation ULValue := (@ULValueP XBool XUInteger XMaybe XProd _ _ LocalStateLRecord _ _ _).

Definition approve_cbv_0_exec_sig (spender : address)(amount : uint256) (l : LedgerLRecord rec) :
  {t | t = exec_state (Uinterpreter (approve_cbv_0 rec def (*  *) _   spender amount)) l}.
  unfold approve_cbv_0 .
  unfold approve, allowance_left.
  unfold urvalue_expression; fold XHMap XProd XMaybe XUInteger XBool.

  unfold default_with_sigmafield,
  urgenerate_field, generate_field.

  unfold messageLQ, IDefaultMQ, IDefault_left.

  unfold_interfaces. unfold_coercions. unfold_arith. unfold_common.  

  (* αunfold *) 
  simpl orb. cbv iota. 

  (* Check LocalStateField7. *)
  (* time "approve_cbv_0_exec_sig:" *) repeat auto_build_P listInfinite.
Defined.

(* Time *) 
  Definition approve_cbv_0_exec_sig_beta 
          := Eval cbv beta zeta delta [approve_cbv_0_exec_sig] in approve_cbv_0_exec_sig.

(* Time *) Elpi ClearMatches approve_cbv_0_exec_sig_beta approve_cbv_0_exec.

Definition approve_cbv_0_exec_flat (spender : address)(amount : uint256) (l: LedgerLRecord rec): LedgerLRecord rec.
  let t := eval cbv beta delta [approve_cbv_0_exec_elpi] in 
                         (approve_cbv_0_exec_elpi  spender amount l) in 
                           flatten_lets_build_without_prop t .
(* Time *) Defined.

(* Time *) Elpi ChangeNonUniqueLets approve_cbv_0_exec_flat approve_cbv_0_exec.

(*ν*)  Elpi GlobalConstExtract Execs approve_cbv_0_exec approve_cbv_0 / "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Execs" _exec_prf.v "Functions" "ERC20." . (*η*)

