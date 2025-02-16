
Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusContractCreator.UrsusRunContract.

Require Import ERC20.ERC20.
Import ERC20.

Definition rec := LocalStateLRecord.

Goal LedgerLRecord rec -> True.
intros ll. destruct_ledger ll.
Abort.

#[global, program]
Instance listInfinite : listInfiniteFunRec_gen XList.
Next Obligation.
(* TODO: we need to analyze all while/for cycles
   and find upper bound for number of iterations *)
exact (repeat PhantomPoint 0).
Defined.

Definition computed : LocalStateLRecord := Eval vm_compute in default. 
#[global]
Instance def : XDefault LocalStateLRecord := {
  default := computed 
} . 

Definition EverMessageDefault: EverMessage := Eval vm_compute in default.
Definition VMStateDefault : VMStateLRecord  := Eval vm_compute in default.
Definition LedgerDefault : LedgerLRecord LocalStateLRecord  := Eval vm_compute in default. 

Elpi Accumulate rec_def lp:{{
  get_rec {{ rec }}.
  get_def {{ def }}.
}}.

AddPropLibraryBindings.

(* build call graph for analyzing dependencies *)
Elpi BuildStaticCallGraph ERC20.
Definition graph1 := Eval compute in updateTreeList ERC20StaticTreeList1.
Definition graph2 := Eval compute in updateTreeList ERC20StaticTreeList2.

Elpi Command AddExternalCallUnfolds.
Elpi Accumulate Db readers_utils.
Elpi Accumulate lp:{{

  :before "fold-map:start"
  fold-map (global C) A (global C) A1 :- 
    coq.gref->id C ID,
    if (rex.match "λ.*" ID)
    (A1 = [ID|A]) (A1 = A).

  pred compute_new_unfolds i:string, o:string.
  compute_new_unfolds S NUNF :-
    coq.locate S (const C),
    coq.env.const C (some T) _,
    fold-map T [] _ RES,
    if (RES = []) (NUNF = "")
    (std.string.concat ", " RES NUNF',
    NUNF is " unfold " ^ NUNF' ^ "."),
    coq.say NUNF.

  pred process_old_unfolds i:term, o:term.
  process_old_unfolds {{Datatypes.nil}} {{Datatypes.nil}}.
  process_old_unfolds 
    {{Datatypes.cons (lp:S, lp:OUNF) lp:R }}
    {{Datatypes.cons (lp:S, lp:UNF) lp:R' }} :-
      process_old_unfolds R R',
      term->string_cut S S',
      compute_new_unfolds S' NUNF,
      term->string_cut OUNF OUNF',
      UNF' is OUNF' ^ NUNF,
      coq.string->term UNF' UNF.

  main [str S] :-
    coq.locate S (const C),
    coq.env.const C (some T) _,
    process_old_unfolds T T',
    std.assert-ok! (coq.elaborate-skeleton T' _ TFINAL) "Error",
 ( (TFINAL = {{Datatypes.nil}} ,
      coq.string->term "" CL,
      std.assert-ok! (coq.elaborate-skeleton CL _ CLT) "Error",
      coq.env.add-const "unfold_strings_" CLT _ _ _
  )
  ;
  (coq.env.add-const "unfold_strings_" TFINAL _ _ _) ) .

}} .

Elpi Typecheck.
Elpi Export AddExternalCallUnfolds.


Definition graph_ := Eval compute in (graph2string_nontrans graph2).

(* Print graph_. *)

(* compute terminals (functions that don't call other functions) for use in matryoshka *)
Definition terminals := Eval compute in compute_terminals ERC20StaticTreeList2.

(* starting state definition, nullify state variables, local state and isCommitted field *)
Definition stl (l: LedgerLRecord rec ) : LedgerLRecord rec := 
  Eval vm_compute in let vm_state := getPruvendoRecord Ledger_VMState l in
   {$$ {$$ {$$ l with Ledger_MainState      := default $$} 
                 with Ledger_LocalState     := default $$}
                 with Ledger_VMState        := {$$ vm_state
                 with VMState_ι_isCommitted := false $$} $$}.

Tactic Notation "unfold_coercions" := (
  unfold coerceUAB', coerceAB', coerceAB;
  unfold coerce_int8, coerceUN256, coerceUN200, coerceUN160, coerceUN128, coerceUN64_dep,
 coerceUN32_dep, coerceUN16_dep, coerce_int_uint, coerce_int64, coerce_int32, 
 coerce_int16, coerce_int, coerceZ_BZ, coerceUN_Z, coerceUN64, coerceUN32, 
 coerceUN16, coerceN_UN, coerce_uint_int, coerce_int256, coerce_int128, 
 coerceUUN, coerceUN8, coerceUN256_dep, coerceUN200_dep, coerceUN160_dep, 
 coerceUN128_dep, coerceUUN_dep, coerceUN8_dep;
 unfold forCast_int8_2, forCast_int8_1;
 unfold forCast256_9, forCast256_8, forCast256_7, forCast256_6, forCast256_5, forCast256_4, forCast256_3,
   forCast256_2, forCast256_1, forCast256_12, forCast256_11, forCast256_10;
 unfold forCast200_9, forCast200_8, forCast200_7, forCast200_6, forCast200_5, forCast200_4, 
   forCast200_3, forCast200_2, forCast200_1, forCast200_10;
 unfold forCast160_9, forCast160_8, forCast160_7, forCast160_6, forCast160_5, forCast160_4, 
   forCast160_3, forCast160_2, forCast160_1;
 unfold forCast128_8, forCast128_7, forCast128_6, forCast128_5, forCast128_4, forCast128_3, 
   forCast128_2, forCast128_1;
 unfold forCast64_5_dep, forCast64_4_dep, forCast64_3_dep, forCast64_2_dep, forCast64_1_dep;
 unfold forCast32_4_dep, forCast32_3_dep, forCast32_2_dep, forCast32_1_dep;
 unfold forCast16_3_dep, forCast16_2_dep, forCast16_1_dep;
 unfold forCast_int64_8, forCast_int64_7, forCast_int64_6, forCast_int64_5, forCast_int64_4, 
 forCast_int64_3, forCast_int64_2, forCast_int64_1;
 unfold forCast_int32_6, forCast_int32_5, forCast_int32_4, forCast_int32_3, forCast_int32_2, 
 forCast_int32_1;
 unfold forCast_int16_4, forCast_int16_3, forCast_int16_2, forCast_int16_1;
 unfold forIntCast_2, forIntCast_1;
 unfold forCast64_6, forCast64_5, forCast64_4, forCast64_3, forCast64_2, forCast64_1;
 unfold forCast32_5, forCast32_4, forCast32_3, forCast32_2, forCast32_1;
 unfold forCast16_4, forCast16_3, forCast16_2, forCast16_1;
 unfold forCast_int256_16, forCast_int256_15, forCast_int256_14, forCast_int256_13,
 forCast_int256_12, forCast_int256_11, forCast_int256_10, forCast_int256_9, 
  forCast_int256_8, forCast_int256_7, forCast_int256_6, forCast_int256_5, 
   forCast_int256_4, forCast_int256_3, forCast_int256_2, forCast_int256_1;
 unfold forCast_int128_12, forCast_int128_11, forCast_int128_10, forCast_int128_9,
   forCast_int128_8, forCast_int128_7, forCast_int128_6, forCast_int128_5, 
   forCast_int128_4, forCast_int128_3, forCast_int128_2, forCast_int128_1;
 unfold forCast8_3, forCast8_2, forCast8_1;
 unfold forCast256_9_dep, forCast256_8_dep, forCast256_7_dep, forCast256_6_dep, 
   forCast256_5_dep, forCast256_4_dep, forCast256_3_dep, forCast256_2_dep, 
   forCast256_1_dep, forCast256_10_dep;
 unfold forCast200_9_dep, forCast200_8_dep, forCast200_7_dep, forCast200_6_dep, 
   forCast200_5_dep, forCast200_4_dep, forCast200_3_dep, forCast200_2_dep, 
   forCast200_1_dep;
 unfold forCast160_8_dep, forCast160_7_dep, forCast160_6_dep,  forCast160_5_dep, 
  forCast160_4_dep, forCast160_3_dep, forCast160_2_dep, forCast160_1_dep;
 unfold forCast128_7_dep, forCast128_6_dep, forCast128_5_dep, forCast128_4_dep,
   forCast128_3_dep, forCast128_2_dep, forCast128_1_dep;
 unfold forCast8_2_dep, forCast8_1_dep;
 unfold cast_int8, cast_int16, cast_int32, cast_int64,
        cast_int128, cast_int256, cast_int, cast8,
        cast16, cast32, cast64, cast128, cast256,
        cast160, cast200, cast8_dep, cast16_dep,
        cast32_dep, cast64_dep, cast128_dep, cast256_dep, cast160_dep;
 unfold convert_int, convert_uint_dep, convert_uint, convert_uint_to_int,
        unsafe_cast_int_uint, unsafe_convert_int_to_uint
).                 

Tactic Notation "unfold_arith" := (
  unfold un_eqb', un_uneqb', un_ltb', un_gtb', un_geb', un_leb';
  unfold un_mult', un_plus', un_minus', un_div' ;
  unfold un_right', un_left', un_or', un_and';

  unfold un_eqb, un_uneqb, un_ltb, un_gtb, un_geb, un_leb;
  unfold un_mult, un_plus, un_minus, un_div;
  unfold un_right, un_left, un_or, un_and;
  
  unfold binaryLogicalOperations_0, binaryUintegerOperations_0, binaryUintegerOperations_1,
         eqBinaryLogicalOperations_0, eqBinaryLogicalOperations_1,
         eqBinaryLogicalOperations_2, eqBinaryLogicalOperations_3,
         eqBinaryLogicalOperations_4, eqBinaryLogicalOperations_5;
  unfold binaryLogicalOperations_1, make_universal_operation_from_1;

  unfold ueqb, uneqb, address_eqb, ultb, ugtb, ugeb, uleb;
  unfold uchecked_add, uchecked_sub, uchecked_add_bigint, uchecked_sub_bigint, uto_u64_digits;
  unfold ubitsize, uright;
  unfold umult, uplus, uminus, udiv;
  unfold uright, uleft, uor, uand;
  unfold uneqb, uband, ubor, uneg;
  unfold umaybe_get_default, umaybe_has_value, umaybe_set, umaybe_some;
  unfold uhmap_fetch, uhmap_find_with_default, uhmap_insert, uhmap_add, uhmap_replace, uhmap_min, uhmap_next,
         uhmap_prev, uhmap_exists, uhmap_delete, uhmap_delete_min, uhmap_delete_max, uhmap_max,
         is_empty_; 
  unfold eq_rect, right_or_false
).

Tactic Notation "unfold_common" :=
  (cbv beta iota delta [
              wrapULExpressionL
              wrapULExpression
              ursus_call_with_argsL
              UExpressionP0_LedgerableWithArgsL
              UExpressionP_Next_LedgerableWithRArgsL
              UExpressionP_Next_LedgerableWithLArgsL 
              rvalued_call_with_argsL 
              URValueP0_RValuedWithArgsL
              URValueP_Next_URValuedWithArgsL
              ControlResultL
              dynamicAssignL
              dynamicAssign0L
              fromUReturnExpression
              sInjectL sInject sRInject urvalue_bindL
              wrapURExpressionL
              wrapURExpression
              wrapURValue SML_NG32.wrapURValue 
              urvalue_bindL
              ] ).

Tactic Notation "unfold_interfaces" :=
  (cbv beta iota delta [
              wrapULExpressionL
  ]) . 

#[export]
Instance address_default : XDefault address := _ .

