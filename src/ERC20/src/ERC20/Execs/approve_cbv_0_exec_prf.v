Require Import ERC20.CommonHeader.

Require Import ERC20.Functions.approve.
Import approve.

Require Import ERC20.Functions .
Require Import ERC20.Common. 

Require Import ERC20.Execs.approve_cbv_0.

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
 Opaque XUInteger.
 Opaque eval_state.
 Opaque LedgerTMonad.
 Opaque XMaybe.
 Opaque maybeFunRec.
 Opaque msg_sender.
 Opaque uintFunRec.
 Opaque prodFunRec.
 Opaque sRReader.
 Opaque LedgerMonadState.
 Opaque SML_NG32.LedgerT.
 Opaque toValue.
 Opaque exec_state.
 Opaque ContractLPruvendoRecord.
 Opaque container_insert.
 Opaque bool2bool'.
 Opaque container_lookup_default.
 Opaque _8.
 Opaque XBInteger_eq.
 Opaque XUBInteger_eq.
 Opaque Container_xhmap_instance.
 Opaque xhmap_default.
 Opaque ContractLEmbeddedType.
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


(* Elpi FullPrint approve_cbv_0_exec(* _sig_beta *). *)

Lemma approve_cbv_0_exec_prf: forall (spender : address)(amount : uint256) (l : LedgerLRecord rec),
  approve_cbv_0_exec  spender amount l = 
  exec_state (Uinterpreter (approve_cbv_0 rec def  _   spender amount)) l .
Proof with 
           match goal with
            | |- ?x = ?y => let t := type of x in exact_no_check (eq_refl (A:=t) x)
           end.
  intros.
  replace (exec_state (Uinterpreter (approve_cbv_0 rec def _   spender amount)) l ) with 
    (proj1_sig (approve_cbv_0_exec_sig_beta  spender amount l )) 
                 by apply (proj2_sig (approve_cbv_0_exec_sig_beta  spender amount l ))...

  (* Time *) Optimize Proof.
  (* Time *) Optimize Heap.
(* Time Validate Proof. *)
Time Qed.

#[global] Instance _ex_approve_cbv_0: ExecsIndex _ _ _ (@approve_cbv_0) :=
{|
  __exec := @approve_cbv_0_exec;
  __exec_prf := @approve_cbv_0_exec_prf
|}.

(* *)
Lemma approve_cbv_exec_prf: forall (spender : address)(amount : uint256) (l : LedgerLRecord rec),
  approve_cbv_0_exec  spender amount l = 
  exec_state (Uinterpreter ( approve rec def  spender amount )) l .
Proof.
  intros.
  rewrite approve_split_correct.
  setoid_rewrite approve_split_correct_head0.
  apply   approve_cbv_0_exec_prf.
Qed.

#[global] Instance _ex_approve_cbv: ExecsIndex _ _ _ (@approve) :=
{|
  __exec := @approve_cbv_0_exec;
  __exec_prf := @approve_cbv_exec_prf
|}.

 (* *)

 Elpi TacticsGenerate Execs 0 ERC20 ERC20 Execs Evals approve " spender amount" "Tactics" "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Tactics/" "Functions" "Functions" "ERC20." .


