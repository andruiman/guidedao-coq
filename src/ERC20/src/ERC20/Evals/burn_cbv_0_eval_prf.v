Require Import ERC20.CommonHeader.

Require Import ERC20.Functions.burn. (* ERC20. *)

Require Import ERC20.Functions.
Require Import ERC20.Common. 

Require Import ERC20.Evals.burn_cbv_0.

Opaque XBool.
 Opaque ContractLRecord.
 Opaque VMStateLRecord.
 Opaque def.
 Opaque LedgerLLedgerClass.
 Opaque MessagesAndEventsLRecord.
 Opaque SML_NG32.LedgerT.
 Opaque XUInteger.
 Opaque PhantomType.
 Opaque LedgerMonadState.
 Opaque Uinterpreter.
 Opaque XList.
 Opaque XHMap.
 Opaque prodFunRec.
 Opaque uintFunRec.
 Opaque hmapFunRec.
 Opaque phantom_default.
 Opaque burn_.
 Opaque listInfinite.
 Opaque listFunRec.
 Opaque maybeFunRec.
 Opaque boolFunRec.
 Opaque XProd.
 Opaque XMaybe.
 Opaque LedgerTMonad.
 Opaque exec_state.
 Opaque default.
 Opaque LedgerLRecord.
 Opaque rec.
 Opaque _256.
 Opaque addr_stdLRecord.


(* Elpi FullPrint burn_cbv_0_eval(* _sig_beta *). *)

Lemma burn_cbv_0_eval_prf: forall (from : address)(amount : uint256) (l : LedgerLRecord rec),
  burn_cbv_0_eval  from amount l = 
  eval_state (Uinterpreter (burn_cbv_0 rec def  _   from amount)) l .
Proof with 
           match goal with
            | |- ?x = ?y => let t := type of x in exact_no_check (eq_refl (A:=t) x)
           end.
  intros.
  replace (eval_state (Uinterpreter (burn_cbv_0 rec def _   from amount)) l ) with 
    (proj1_sig (burn_cbv_0_eval_sig_beta  from amount l )) 
                 by apply (proj2_sig (burn_cbv_0_eval_sig_beta  from amount l ))...

  (* Time *) Optimize Proof.
  (* Time *) Optimize Heap.
(* Time Validate Proof. *)
 Time Qed.

#[global] Instance _ev_burn_cbv_0: EvalsIndex _ _ _ (@burn_cbv_0) :=
{|
  __eval := @burn_cbv_0_eval;
  __eval_prf := @burn_cbv_0_eval_prf
|}.

(* *)

Lemma burn_cbv_eval_prf: forall (from : address)(amount : uint256) (l : LedgerLRecord rec),
  burn_cbv_0_eval  from amount l = 
  eval_state (Uinterpreter ( burn rec def  from amount )) l .
Proof.
  intros.
  rewrite burn_split_correct.
  setoid_rewrite burn_split_correct_head0.
  apply   burn_cbv_0_eval_prf.
Qed. 

#[global] Instance _ev_burn_cbv: EvalsIndex _ _ _ (@burn) :=
{|
  __eval := @burn_cbv_0_eval;
  __eval_prf := @burn_cbv_eval_prf
|}.

 (* *)

