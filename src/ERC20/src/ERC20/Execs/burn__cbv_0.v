
Require Import ERC20.CommonHeader.

Require Import ERC20.Functions.burn_. (* ERC20. *)

Require Import ERC20.Functions.
Require Import ERC20.Common. 

Notation ULValue := (@ULValueP XBool XUInteger XMaybe XProd _ _ LocalStateLRecord _ _ _).

Definition burn__cbv_0_exec_sig (from : address)(amount : uint256) (l : LedgerLRecord rec) :
  {t | t = exec_state (Uinterpreter (burn__cbv_0 rec def (*  *) _   from amount)) l}.
  unfold burn__cbv_0 .
  unfold burn_, totalSupply_left, minusassign_left, balanceOf_left.
  unfold urvalue_expression; fold XHMap XProd XMaybe XUInteger XBool.

  unfold default_with_sigmafield,
  urgenerate_field, generate_field.

  unfold messageLQ, IDefaultMQ, IDefault_left.

  unfold_interfaces. unfold_coercions. unfold_arith. unfold_common.  

  (* αunfold *) 
  simpl orb. cbv iota. 

  (* Check LocalStateField7. *)
  (* time "burn__cbv_0_exec_sig:" *) repeat auto_build_P listInfinite.
Defined.

(* Time *) 
  Definition burn__cbv_0_exec_sig_beta 
          := Eval cbv beta zeta delta [burn__cbv_0_exec_sig] in burn__cbv_0_exec_sig.

(* Time *) Elpi ClearMatches burn__cbv_0_exec_sig_beta burn__cbv_0_exec.

Definition burn__cbv_0_exec_flat (from : address)(amount : uint256) (l: LedgerLRecord rec): LedgerLRecord rec.
  let t := eval cbv beta delta [burn__cbv_0_exec_elpi] in 
                         (burn__cbv_0_exec_elpi  from amount l) in 
                           flatten_lets_build_without_prop t .
(* Time *) Defined.

(* Time *) Elpi ChangeNonUniqueLets burn__cbv_0_exec_flat burn__cbv_0_exec.

(*ν*)  Elpi GlobalConstExtract Execs burn__cbv_0_exec burn__cbv_0 / "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Execs" _exec_prf.v "Functions" "ERC20." . (*η*)

