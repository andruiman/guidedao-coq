Require Import ERC20.CommonHeader.

Require Import ERC20.Functions.mint. (* ERC20. *)

Require Import ERC20.Functions.
Require Import ERC20.Common. 

Require Import ERC20.Evals.mint_cbv_0.

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
 Opaque mint_.
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


(* Elpi FullPrint mint_cbv_0_eval(* _sig_beta *). *)

Lemma mint_cbv_0_eval_prf: forall (to__ : address)(amount : uint256) (l : LedgerLRecord rec),
  mint_cbv_0_eval  to__ amount l = 
  eval_state (Uinterpreter (mint_cbv_0 rec def  _   to__ amount)) l .
Proof with 
           match goal with
            | |- ?x = ?y => let t := type of x in exact_no_check (eq_refl (A:=t) x)
           end.
  intros.
  replace (eval_state (Uinterpreter (mint_cbv_0 rec def _   to__ amount)) l ) with 
    (proj1_sig (mint_cbv_0_eval_sig_beta  to__ amount l )) 
                 by apply (proj2_sig (mint_cbv_0_eval_sig_beta  to__ amount l ))...

  (* Time *) Optimize Proof.
  (* Time *) Optimize Heap.
(* Time Validate Proof. *)
 Time Qed.

#[global] Instance _ev_mint_cbv_0: EvalsIndex _ _ _ (@mint_cbv_0) :=
{|
  __eval := @mint_cbv_0_eval;
  __eval_prf := @mint_cbv_0_eval_prf
|}.

(* *)

Lemma mint_cbv_eval_prf: forall (to__ : address)(amount : uint256) (l : LedgerLRecord rec),
  mint_cbv_0_eval  to__ amount l = 
  eval_state (Uinterpreter ( mint rec def  to__ amount )) l .
Proof.
  intros.
  rewrite mint_split_correct.
  setoid_rewrite mint_split_correct_head0.
  apply   mint_cbv_0_eval_prf.
Qed. 

#[global] Instance _ev_mint_cbv: EvalsIndex _ _ _ (@mint) :=
{|
  __eval := @mint_cbv_0_eval;
  __eval_prf := @mint_cbv_eval_prf
|}.

 (* *)

