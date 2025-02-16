Require Import ERC20.CommonHeader.

Require Import ERC20.Functions.burn.
Import burn.

Require Import ERC20.Functions .
Require Import ERC20.Common. 

Require Import ERC20.Execs.burn_cbv_0.

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


(* Elpi FullPrint burn_cbv_0_exec(* _sig_beta *). *)

Lemma burn_cbv_0_exec_prf: forall (from : address)(amount : uint256) (l : LedgerLRecord rec),
  burn_cbv_0_exec  from amount l = 
  exec_state (Uinterpreter (burn_cbv_0 rec def  _   from amount)) l .
Proof with 
           match goal with
            | |- ?x = ?y => let t := type of x in exact_no_check (eq_refl (A:=t) x)
           end.
  intros.
  replace (exec_state (Uinterpreter (burn_cbv_0 rec def _   from amount)) l ) with 
    (proj1_sig (burn_cbv_0_exec_sig_beta  from amount l )) 
                 by apply (proj2_sig (burn_cbv_0_exec_sig_beta  from amount l ))...

  (* Time *) Optimize Proof.
  (* Time *) Optimize Heap.
(* Time Validate Proof. *)
Time Qed.

#[global] Instance _ex_burn_cbv_0: ExecsIndex _ _ _ (@burn_cbv_0) :=
{|
  __exec := @burn_cbv_0_exec;
  __exec_prf := @burn_cbv_0_exec_prf
|}.

(* *)
Lemma burn_cbv_exec_prf: forall (from : address)(amount : uint256) (l : LedgerLRecord rec),
  burn_cbv_0_exec  from amount l = 
  exec_state (Uinterpreter ( burn rec def  from amount )) l .
Proof.
  intros.
  rewrite burn_split_correct.
  setoid_rewrite burn_split_correct_head0.
  apply   burn_cbv_0_exec_prf.
Qed.

#[global] Instance _ex_burn_cbv: ExecsIndex _ _ _ (@burn) :=
{|
  __exec := @burn_cbv_0_exec;
  __exec_prf := @burn_cbv_exec_prf
|}.

 (* *)

 Elpi TacticsGenerate Execs 0 ERC20 ERC20 Execs Evals burn " from amount" "Tactics" "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Tactics/" "Functions" "Functions" "ERC20." .


