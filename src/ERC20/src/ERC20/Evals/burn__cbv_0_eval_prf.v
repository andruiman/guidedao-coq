Require Import ERC20.CommonHeader.

Require Import ERC20.Functions.burn_. (* ERC20. *)

Require Import ERC20.Functions.
Require Import ERC20.Common. 

Require Import ERC20.Evals.burn__cbv_0.

Opaque XBool.
 Opaque XMaybe.
 Opaque MessagesAndEventsLRecord.
 Opaque ContractLPruvendoRecord.
 Opaque field_type.
 Opaque ContractLEmbeddedType.
 Opaque VMLedgerClass.
 Opaque LedgerLVMStateClass.
 Opaque def.
 Opaque VMStateLRecord.
 Opaque ContractLRecord.
 Opaque XProd.
 Opaque XUInteger.
 Opaque SML_NG32.LedgerT.
 Opaque LedgerMonadState.
 Opaque Uinterpreter.
 Opaque XList.
 Opaque prodFunRec.
 Opaque uintFunRec.
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
 Opaque maybeFunRec.
 Opaque boolFunRec.
 Opaque LedgerTMonad.
 Opaque exec_state.
 Opaque LedgerLLedgerClass.
 Opaque default.
 Opaque phantom_default.
 Opaque PhantomType.
 Opaque XHMap.
 Opaque _8.
 Opaque XBInteger_eq.
 Opaque XUBInteger_eq.
 Opaque CommonInstances.pair_xbool_equable.
 Opaque Container_xhmap_instance.
 Opaque ubint_default.
 Opaque LedgerLRecord.
 Opaque rec.
 Opaque _256.
 Opaque addr_stdLRecord.


(* Elpi FullPrint burn__cbv_0_eval(* _sig_beta *). *)

Lemma burn__cbv_0_eval_prf: forall (from : address)(amount : uint256) (l : LedgerLRecord rec),
  burn__cbv_0_eval  from amount l = 
  eval_state (Uinterpreter (burn__cbv_0 rec def  _   from amount)) l .
Proof with 
           match goal with
            | |- ?x = ?y => let t := type of x in exact_no_check (eq_refl (A:=t) x)
           end.
  intros.
  replace (eval_state (Uinterpreter (burn__cbv_0 rec def _   from amount)) l ) with 
    (proj1_sig (burn__cbv_0_eval_sig_beta  from amount l )) 
                 by apply (proj2_sig (burn__cbv_0_eval_sig_beta  from amount l ))...

  (* Time *) Optimize Proof.
  (* Time *) Optimize Heap.
(* Time Validate Proof. *)
 Time Qed.

#[global] Instance _ev_burn__cbv_0: EvalsIndex _ _ _ (@burn__cbv_0) :=
{|
  __eval := @burn__cbv_0_eval;
  __eval_prf := @burn__cbv_0_eval_prf
|}.

(* *)

Lemma burn__cbv_eval_prf: forall (from : address)(amount : uint256) (l : LedgerLRecord rec),
  burn__cbv_0_eval  from amount l = 
  eval_state (Uinterpreter ( burn_ rec def  from amount )) l .
Proof.
  intros.
  rewrite burn__split_correct.
  setoid_rewrite burn__split_correct_head0.
  apply   burn__cbv_0_eval_prf.
Qed. 

#[global] Instance _ev_burn__cbv: EvalsIndex _ _ _ (@burn_) :=
{|
  __eval := @burn__cbv_0_eval;
  __eval_prf := @burn__cbv_eval_prf
|}.

 (* *)

