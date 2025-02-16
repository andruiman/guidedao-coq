Require Import ERC20.CommonHeader.

Require Import ERC20.Functions.constructor. (* ERC20. *)

Require Import ERC20.Functions.
Require Import ERC20.Common. 

Require Import ERC20.Evals.constructor_cbv_0.

Opaque SML_NG32.LedgerEmbedded.
 Opaque ContractLPruvendoRecord.
 Opaque projEmbed.
 Opaque ContractLEmbeddedType.
 Opaque field_type.
 Opaque LedgerPruvendoRecord.
 Opaque MessagesAndEventsLRecord.
 Opaque VMLedgerClass.
 Opaque LedgerLVMStateClass.
 Opaque def.
 Opaque VMStateLRecord.
 Opaque ContractLRecord.
 Opaque XBool.
 Opaque injEmbed.
 Opaque XUInteger.
 Opaque default.
 Opaque phantom_default.
 Opaque PhantomType.
 Opaque LedgerLRecord.
 Opaque rec.
 Opaque _8.
 Opaque XString.


(* Elpi FullPrint constructor_cbv_0_eval(* _sig_beta *). *)

Lemma constructor_cbv_0_eval_prf: forall (name_ : string)(symbol_ : string)(decimals_ : uint8) (l : LedgerLRecord rec),
  constructor_cbv_0_eval  name_ symbol_ decimals_ l = 
  eval_state (Uinterpreter (constructor_cbv_0 rec def    name_ symbol_ decimals_)) l .
Proof with 
           match goal with
            | |- ?x = ?y => let t := type of x in exact_no_check (eq_refl (A:=t) x)
           end.
  intros.
  replace (eval_state (Uinterpreter (constructor_cbv_0 rec def   name_ symbol_ decimals_)) l ) with 
    (proj1_sig (constructor_cbv_0_eval_sig_beta  name_ symbol_ decimals_ l )) 
                 by apply (proj2_sig (constructor_cbv_0_eval_sig_beta  name_ symbol_ decimals_ l ))...

  (* Time *) Optimize Proof.
  (* Time *) Optimize Heap.
(* Time Validate Proof. *)
 Time Qed.

#[global] Instance _ev_constructor_cbv_0: EvalsIndex _ _ _ (@constructor_cbv_0) :=
{|
  __eval := @constructor_cbv_0_eval;
  __eval_prf := @constructor_cbv_0_eval_prf
|}.

(* *)

Lemma constructor_cbv_eval_prf: forall (name_ : string)(symbol_ : string)(decimals_ : uint8) (l : LedgerLRecord rec),
  constructor_cbv_0_eval  name_ symbol_ decimals_ l = 
  eval_state (Uinterpreter ( constructor rec def  name_ symbol_ decimals_ )) l .
Proof.
  intros.
  rewrite constructor_split_correct.
  setoid_rewrite constructor_split_correct_head0.
  apply   constructor_cbv_0_eval_prf.
Qed. 

#[global] Instance _ev_constructor_cbv: EvalsIndex _ _ _ (@constructor) :=
{|
  __eval := @constructor_cbv_0_eval;
  __eval_prf := @constructor_cbv_eval_prf
|}.

 (* *)

