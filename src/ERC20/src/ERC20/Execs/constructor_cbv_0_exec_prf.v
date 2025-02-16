Require Import ERC20.CommonHeader.

Require Import ERC20.Functions.constructor.
Import constructor.

Require Import ERC20.Functions .
Require Import ERC20.Common. 

Require Import ERC20.Execs.constructor_cbv_0.

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
 Opaque default.
 Opaque phantom_default.
 Opaque PhantomType.
 Opaque LedgerLRecord.
 Opaque rec.
 Opaque _8.
 Opaque XString.


(* Elpi FullPrint constructor_cbv_0_exec(* _sig_beta *). *)

Lemma constructor_cbv_0_exec_prf: forall (name_ : string)(symbol_ : string)(decimals_ : uint8) (l : LedgerLRecord rec),
  constructor_cbv_0_exec  name_ symbol_ decimals_ l = 
  exec_state (Uinterpreter (constructor_cbv_0 rec def    name_ symbol_ decimals_)) l .
Proof with 
           match goal with
            | |- ?x = ?y => let t := type of x in exact_no_check (eq_refl (A:=t) x)
           end.
  intros.
  replace (exec_state (Uinterpreter (constructor_cbv_0 rec def   name_ symbol_ decimals_)) l ) with 
    (proj1_sig (constructor_cbv_0_exec_sig_beta  name_ symbol_ decimals_ l )) 
                 by apply (proj2_sig (constructor_cbv_0_exec_sig_beta  name_ symbol_ decimals_ l ))...

  (* Time *) Optimize Proof.
  (* Time *) Optimize Heap.
(* Time Validate Proof. *)
Time Qed.

#[global] Instance _ex_constructor_cbv_0: ExecsIndex _ _ _ (@constructor_cbv_0) :=
{|
  __exec := @constructor_cbv_0_exec;
  __exec_prf := @constructor_cbv_0_exec_prf
|}.

(* *)
Lemma constructor_cbv_exec_prf: forall (name_ : string)(symbol_ : string)(decimals_ : uint8) (l : LedgerLRecord rec),
  constructor_cbv_0_exec  name_ symbol_ decimals_ l = 
  exec_state (Uinterpreter ( constructor rec def  name_ symbol_ decimals_ )) l .
Proof.
  intros.
  rewrite constructor_split_correct.
  setoid_rewrite constructor_split_correct_head0.
  apply   constructor_cbv_0_exec_prf.
Qed.

#[global] Instance _ex_constructor_cbv: ExecsIndex _ _ _ (@constructor) :=
{|
  __exec := @constructor_cbv_0_exec;
  __exec_prf := @constructor_cbv_exec_prf
|}.

 (* *)

 Elpi TacticsGenerate Execs 0 ERC20 ERC20 Execs Evals constructor " name_ symbol_ decimals_" "Tactics" "/Users/andruiman/devel/guidedao-coq//src/ERC20/src/ERC20/Tactics/" "Functions" "Functions" "ERC20." .


