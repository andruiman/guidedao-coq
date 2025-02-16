Require Import ERC20.CommonHeader.

Require Import ERC20.Functions.transfer'. (* ERC20. *)

Require Import ERC20.Functions1.
Require Import ERC20.Common. 

Require Import ERC20.Evals.transfer'_cbv_0.

Opaque XBool.
 Opaque xbool_default.
 Opaque default.
 Opaque ContainerLocal_xhmap_instance.
 Opaque CommonInstances.pair_xbool_equable.
 Opaque boolFunRec.
 Opaque CommonInstances.nat_xbool_equable.
 Opaque CommonInstances.xstring_booleq.
 Opaque _container_insert.
 Opaque injEmbed.
 Opaque eval_state.
 Opaque toValue.
 Opaque ubint_default.
 Opaque Container_xhmap_instance.
 Opaque XUBInteger_eq.
 Opaque XBInteger_eq.
 Opaque _8.
 Opaque container_lookup_default.
 Opaque Uinterpreter.
 Opaque XList.
 Opaque hmapFunRec.
 Opaque plusassign.
 Opaque uxor.
 Opaque xIntBitOpLeft.
 Opaque xIntDiv.
 Opaque upow.
 Opaque xIntBitOpOr.
 Opaque umax.
 Opaque xIntPlus.
 Opaque umin.
 Opaque xIntBitOpAnd.
 Opaque xIntMult.
 Opaque xIntBitOpRight.
 Opaque urvalue_bind.
 Opaque orb.
 Opaque umod.
 Opaque listInfinite.
 Opaque listFunRec.
 Opaque bool2bool'.
 Opaque _IntError.
 Opaque _NErrorType.
 Opaque right_orify_result.
 Opaque left_orify_result.
 Opaque _container_lookup_default.
 Opaque ERROR_INVALID_ARGUMENT.
 Opaque xBoolIfElse.
 Opaque xIntGeb.
 Opaque container_insert.
 Opaque xIntMinus.
 Opaque xubint_intFunRec.
 Opaque projTransEmbed.
 Opaque ContractLEmbeddedType.
 Opaque ContractLPruvendoRecord.
 Opaque exec_state.
 Opaque LedgerTMonad.
 Opaque XMaybe.
 Opaque maybeFunRec.
 Opaque msg_sender.
 Opaque uintFunRec.
 Opaque prodFunRec.
 Opaque sRReader.
 Opaque LedgerMonadState.
 Opaque XUInteger.
 Opaque SML_NG32.LedgerT.
 Opaque VMLedgerClass.
 Opaque LedgerLVMStateClass.
 Opaque projEmbed.
 Opaque XProd.
 Opaque XHMap.
 Opaque SML_NG32.LedgerEmbedded.
 Opaque iso_local.
 Opaque eq_rect.
 Opaque LocalStateField2.
 Opaque LocalStateLRecord.
 Opaque field_type.
 Opaque LedgerPruvendoRecord.
 Opaque MessagesAndEventsLRecord.
 Opaque LedgerLLedgerClass.
 Opaque def.
 Opaque VMStateLRecord.
 Opaque ContractLRecord.
 Opaque LedgerLRecord.
 Opaque rec.
 Opaque _256.
 Opaque addr_stdLRecord.


(* Elpi FullPrint transfer'_cbv_0_eval(* _sig_beta *). *)

Lemma transfer'_cbv_0_eval_prf: forall (recipient : address)(amount : uint256) (l : LedgerLRecord rec),
  transfer'_cbv_0_eval  recipient amount l = 
  eval_state (Uinterpreter (transfer'_cbv_0 rec def  _ _   recipient amount)) l .
Proof with 
           match goal with
            | |- ?x = ?y => let t := type of x in exact_no_check (eq_refl (A:=t) x)
           end.
  intros.
  replace (eval_state (Uinterpreter (transfer'_cbv_0 rec def _ _   recipient amount)) l ) with 
    (proj1_sig (transfer'_cbv_0_eval_sig_beta  recipient amount l )) 
                 by apply (proj2_sig (transfer'_cbv_0_eval_sig_beta  recipient amount l ))...

  (* Time *) Optimize Proof.
  (* Time *) Optimize Heap.
(* Time Validate Proof. *)
 Time Qed.

#[global] Instance _ev_transfer'_cbv_0: EvalsIndex _ _ _ (@transfer'_cbv_0) :=
{|
  __eval := @transfer'_cbv_0_eval;
  __eval_prf := @transfer'_cbv_0_eval_prf
|}.

(* *)

Lemma transfer'_cbv_eval_prf: forall (recipient : address)(amount : uint256) (l : LedgerLRecord rec),
  transfer'_cbv_0_eval  recipient amount l = 
  eval_state (Uinterpreter ( transfer' rec def  recipient amount )) l .
Proof.
  intros.
  rewrite transfer'_split_correct.
  setoid_rewrite transfer'_split_correct_head0.
  apply   transfer'_cbv_0_eval_prf.
Qed. 

#[global] Instance _ev_transfer'_cbv: EvalsIndex _ _ _ (@transfer') :=
{|
  __eval := @transfer'_cbv_0_eval;
  __eval_prf := @transfer'_cbv_eval_prf
|}.

 (* *)

