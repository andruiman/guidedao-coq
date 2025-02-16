Require Import ERC20.CommonHeader.

Require Import ERC20.Functions.mint_. (* ERC20. *)

Require Import ERC20.Functions.
Require Import ERC20.Common. 

Require Import ERC20.Evals.mint__cbv_0.

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


(* Elpi FullPrint mint__cbv_0_eval(* _sig_beta *). *)

Lemma mint__cbv_0_eval_prf: forall (to__ : address)(amount : uint256) (l : LedgerLRecord rec),
  mint__cbv_0_eval  to__ amount l = 
  eval_state (Uinterpreter (mint__cbv_0 rec def  _   to__ amount)) l .
Proof with 
           match goal with
            | |- ?x = ?y => let t := type of x in exact_no_check (eq_refl (A:=t) x)
           end.
  intros.
  replace (eval_state (Uinterpreter (mint__cbv_0 rec def _   to__ amount)) l ) with 
    (proj1_sig (mint__cbv_0_eval_sig_beta  to__ amount l )) 
                 by apply (proj2_sig (mint__cbv_0_eval_sig_beta  to__ amount l ))...

  (* Time *) Optimize Proof.
  (* Time *) Optimize Heap.
(* Time Validate Proof. *)
 Time Qed.

#[global] Instance _ev_mint__cbv_0: EvalsIndex _ _ _ (@mint__cbv_0) :=
{|
  __eval := @mint__cbv_0_eval;
  __eval_prf := @mint__cbv_0_eval_prf
|}.

(* *)

Lemma mint__cbv_eval_prf: forall (to__ : address)(amount : uint256) (l : LedgerLRecord rec),
  mint__cbv_0_eval  to__ amount l = 
  eval_state (Uinterpreter ( mint_ rec def  to__ amount )) l .
Proof.
  intros.
  rewrite mint__split_correct.
  setoid_rewrite mint__split_correct_head0.
  apply   mint__cbv_0_eval_prf.
Qed. 

#[global] Instance _ev_mint__cbv: EvalsIndex _ _ _ (@mint_) :=
{|
  __eval := @mint__cbv_0_eval;
  __eval_prf := @mint__cbv_eval_prf
|}.

 (* *)

