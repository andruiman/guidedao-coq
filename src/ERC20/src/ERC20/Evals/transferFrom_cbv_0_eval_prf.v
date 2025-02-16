Require Import ERC20.CommonHeader.

Require Import ERC20.Functions.transferFrom. (* ERC20. *)

Require Import ERC20.Functions.
Require Import ERC20.Common. 

Require Import ERC20.Evals.transferFrom_cbv_0.

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
 Opaque xhmap_default.
 Opaque Container_xhmap_instance.
 Opaque XUBInteger_eq.
 Opaque XBInteger_eq.
 Opaque _8.
 Opaque Uinterpreter.
 Opaque XList.
 Opaque hmapFunRec.
 Opaque minusassign.
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
 Opaque xIntMinus.
 Opaque xIntBitOpRight.
 Opaque urvalue_bind.
 Opaque orb.
 Opaque umod.
 Opaque xubint_intFunRec.
 Opaque listInfinite.
 Opaque listFunRec.
 Opaque projTransEmbed.
 Opaque _container_lookup_default.
 Opaque bool2bool'.
 Opaque plusassign.
 Opaque ubint_default.
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


(* Elpi FullPrint transferFrom_cbv_0_eval(* _sig_beta *). *)

Lemma transferFrom_cbv_0_eval_prf: forall (sender : address)(recipient : address)(amount : uint256) (l : LedgerLRecord rec),
  transferFrom_cbv_0_eval  sender recipient amount l = 
  eval_state (Uinterpreter (transferFrom_cbv_0 rec def  _ _   sender recipient amount)) l .
Proof with 
           match goal with
            | |- ?x = ?y => let t := type of x in exact_no_check (eq_refl (A:=t) x)
           end.
  intros.
  replace (eval_state (Uinterpreter (transferFrom_cbv_0 rec def _ _   sender recipient amount)) l ) with 
    (proj1_sig (transferFrom_cbv_0_eval_sig_beta  sender recipient amount l )) 
                 by apply (proj2_sig (transferFrom_cbv_0_eval_sig_beta  sender recipient amount l ))...

  (* Time *) Optimize Proof.
  (* Time *) Optimize Heap.
(* Time Validate Proof. *)
 Time Qed.

#[global] Instance _ev_transferFrom_cbv_0: EvalsIndex _ _ _ (@transferFrom_cbv_0) :=
{|
  __eval := @transferFrom_cbv_0_eval;
  __eval_prf := @transferFrom_cbv_0_eval_prf
|}.

(* *)

Lemma transferFrom_cbv_eval_prf: forall (sender : address)(recipient : address)(amount : uint256) (l : LedgerLRecord rec),
  transferFrom_cbv_0_eval  sender recipient amount l = 
  eval_state (Uinterpreter ( transferFrom rec def  sender recipient amount )) l .
Proof.
  intros.
  rewrite transferFrom_split_correct.
  setoid_rewrite transferFrom_split_correct_head0.
  apply   transferFrom_cbv_0_eval_prf.
Qed. 

#[global] Instance _ev_transferFrom_cbv: EvalsIndex _ _ _ (@transferFrom) :=
{|
  __eval := @transferFrom_cbv_0_eval;
  __eval_prf := @transferFrom_cbv_eval_prf
|}.

 (* *)

