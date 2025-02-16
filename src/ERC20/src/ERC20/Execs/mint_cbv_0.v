
Require Import ERC20.CommonHeader.

Require Import ERC20.Functions.mint. (* ERC20. *)

Require Import ERC20.Functions.
Require Import ERC20.Common. 

Notation ULValue := (@ULValueP XBool XUInteger XMaybe XProd _ _ LocalStateLRecord _ _ _).

Definition mint_cbv_0_exec_sig (to__ : address)(amount : uint256) (l : LedgerLRecord rec) :
  {t | t = exec_state (Uinterpreter (mint_cbv_0 rec def (*  *) _   to__ amount)) l}.
  unfold mint_cbv_0 .
  unfold mint, mint__left.
  unfold urvalue_expression; fold XHMap XProd XMaybe XUInteger XBool.

  unfold default_with_sigmafield,
  urgenerate_field, generate_field.

  unfold messageLQ, IDefaultMQ, IDefault_left.

  unfold_interfaces. unfold_coercions. unfold_arith. unfold_common.  

  (* αunfold *) 
  simpl orb. cbv iota. 

  (* Check LocalStateField7. *)
  (* time "mint_cbv_0_exec_sig:" *) repeat auto_build_P listInfinite.
Defined.

(* Time *) 
  Definition mint_cbv_0_exec_sig_beta 
          := Eval cbv beta zeta delta [mint_cbv_0_exec_sig] in mint_cbv_0_exec_sig.

(* Time *) Elpi ClearMatches mint_cbv_0_exec_sig_beta mint_cbv_0_exec.

Definition mint_cbv_0_exec_flat (to__ : address)(amount : uint256) (l: LedgerLRecord rec): LedgerLRecord rec.
  let t := eval cbv beta delta [mint_cbv_0_exec_elpi] in 
                         (mint_cbv_0_exec_elpi  to__ amount l) in 
                           flatten_lets_build_without_prop t .
(* Time *) Defined.

(* Time *) Elpi ChangeNonUniqueLets mint_cbv_0_exec_flat mint_cbv_0_exec.

(*ν*)  Elpi GlobalConstExtract Execs mint_cbv_0_exec mint_cbv_0 / "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Execs" _exec_prf.v "Functions" "ERC20." . (*η*)

