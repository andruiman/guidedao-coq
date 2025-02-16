Require Import ERC20.CommonHeader.

Require Import ERC20.Functions.mint.
Import mint.

Require Import ERC20.Functions .
Require Import ERC20.Common. 

Require Import ERC20.Execs.mint_cbv_0.

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


(* Elpi FullPrint mint_cbv_0_exec(* _sig_beta *). *)

Lemma mint_cbv_0_exec_prf: forall (to__ : address)(amount : uint256) (l : LedgerLRecord rec),
  mint_cbv_0_exec  to__ amount l = 
  exec_state (Uinterpreter (mint_cbv_0 rec def  _   to__ amount)) l .
Proof with 
           match goal with
            | |- ?x = ?y => let t := type of x in exact_no_check (eq_refl (A:=t) x)
           end.
  intros.
  replace (exec_state (Uinterpreter (mint_cbv_0 rec def _   to__ amount)) l ) with 
    (proj1_sig (mint_cbv_0_exec_sig_beta  to__ amount l )) 
                 by apply (proj2_sig (mint_cbv_0_exec_sig_beta  to__ amount l ))...

  (* Time *) Optimize Proof.
  (* Time *) Optimize Heap.
(* Time Validate Proof. *)
Time Qed.

#[global] Instance _ex_mint_cbv_0: ExecsIndex _ _ _ (@mint_cbv_0) :=
{|
  __exec := @mint_cbv_0_exec;
  __exec_prf := @mint_cbv_0_exec_prf
|}.

(* *)
Lemma mint_cbv_exec_prf: forall (to__ : address)(amount : uint256) (l : LedgerLRecord rec),
  mint_cbv_0_exec  to__ amount l = 
  exec_state (Uinterpreter ( mint rec def  to__ amount )) l .
Proof.
  intros.
  rewrite mint_split_correct.
  setoid_rewrite mint_split_correct_head0.
  apply   mint_cbv_0_exec_prf.
Qed.

#[global] Instance _ex_mint_cbv: ExecsIndex _ _ _ (@mint) :=
{|
  __exec := @mint_cbv_0_exec;
  __exec_prf := @mint_cbv_exec_prf
|}.

 (* *)

 Elpi TacticsGenerate Execs 0 ERC20 ERC20 Execs Evals mint " to__ amount" "Tactics" "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Tactics/" "Functions" "Functions" "ERC20." .


