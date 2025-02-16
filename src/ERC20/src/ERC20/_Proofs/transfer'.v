Require Import ProofsHeader.
Require Import Tactics.transfer'.

SetDefaultOpaques "ERC20".

Definition transfer'_balance_err_def (recipient : address) (amount : uint256) 
                                       (ll: LedgerLRecord rec): Prop.
  err0 (transfer' rec def recipient amount) ll | "balanceOf" "msg_sender".
  set (req1 := xIntGeb (balanceOf[msg_sender]) amount).
  con (negb req1).
Defined.

Lemma transfer'_balance_err_prf (recipient : address) (amount : uint256)   
                                  (ll: LedgerLRecord rec):
      transfer'_balance_err_def recipient amount ll.
Proof.
  start_proof.
  transfer'_start.
  time prepare_all ll P.
  compute in H1. subst y1. 
  compute_destructed_ledgers _loc.

  time solve_full_error.
Time Qed.

Definition transfer'_balance_sender1_def (recipient : address) (amount : uint256) 
                                       (ll: LedgerLRecord rec): Prop.
  execs0 (transfer' rec def recipient amount) : ll | "balanceOf" "msg_sender" 
                                             -> l1 | "balanceOf".
  no_err (transfer' rec def recipient amount) l0.
  hyp (msg_sender <> recipient).
  con (balanceOf'[msg_sender] = xIntMinus (balanceOf[msg_sender]) amount).
Defined.

Lemma transfer'_balance_sender1_prf (recipient : address) (amount : uint256)   
                                  (ll: LedgerLRecord rec):
      transfer'_balance_sender1_def recipient amount ll.
Proof.
  start_proof. process_no_err_hyp C transfer'_balance_err_prf.
  transfer'_start.
  time prepare_all ll P.
  compute in H1. subst y1. 
  compute_destructed_ledgers _loc.

  print_ifs2.
  single_replace y21 true.
  2:{
    rewrite <- C.
    time bottom_up_goal_solver. (* 2.228 secs *)
  }

  time bottom_up_goal_solver.

  (* ********************* *)
  clear - C C0.
  remember (s1 [msg11] ?).
    setoid_rewrite <- Heqy.
    destruct y.
    + erewrite lookup_addAdjust_another.
      2: assumption.
      erewrite lookup_addAdjust.
      reflexivity.
    + erewrite lookup_addAdjust_another.
      2: assumption.
      erewrite lookup_addAdjust.
      reflexivity.
Time Qed.

Definition transfer'_balance_sender2_def (recipient : address) (amount : uint256) 
                                       (ll: LedgerLRecord rec): Prop.
  execs0 (transfer' rec def recipient amount) : ll | "balanceOf" "msg_sender" 
                                             -> l1 | "balanceOf".
  no_err (transfer' rec def recipient amount) l0.
  hyp (msg_sender = recipient).

  con (balanceOf'[msg_sender] = balanceOf[msg_sender]).
Defined.

From Hammer Require Import Tactics Hammer.

Lemma transfer'_balance_sender2_prf (recipient : address) (amount : uint256)   
                                  (ll: LedgerLRecord rec):
      transfer'_balance_sender2_def recipient amount ll.
Proof.
  start_proof. process_no_err_hyp C transfer'_balance_err_prf.
  transfer'_start.
  time prepare_all ll P.
  compute in H1. subst y1. 
  compute_destructed_ledgers _loc.

  print_ifs2.
  single_replace y21 true.
  2:{
    rewrite <- C.
    time bottom_up_goal_solver. (* 2.228 secs *)
  }

  time bottom_up_goal_solver. (* 3.4 secs *)

  (* ********************* *)
  clear - C C0.
  rewrite <- ?C0 in *.
  remember (s1 [msg11] ?).
  setoid_rewrite <- Heqy.
  destruct y.
  - erewrite lookup_addAdjust.
    erewrite lookup_addAdjust.
    destruct x, amount.
    f_equal.
    apply N.leb_le in C.
    unfold Common.hmapFindWithDefault in C.
    setoid_rewrite <- Heqy in C. 
    with_strategy opaque [N.le]
    compute in C.
    lia.
  - erewrite lookup_addAdjust.
    erewrite lookup_addAdjust.
    destruct amount. f_equal.
    unfold Common.hmapFindWithDefault in C.
    setoid_rewrite <- Heqy in C. 
    with_strategy opaque [N.le]
    compute in C.
    apply N.leb_le in C.
    lia.
Time Qed.


Definition transfer'_balance_recipient_def (recipient : address) (amount : uint256) 
                                          (ll: LedgerLRecord rec): Prop.
  execs0 (transfer' rec def recipient amount) : ll | "balanceOf" "msg_sender" -> l1 | "balanceOf".
  no_err (transfer' rec def recipient amount) l0.
  hyp (recipient <> msg_sender).

  con (balanceOf'[recipient] = xIntPlus (balanceOf[recipient]) amount).
Defined.


Ltac pose_mapping_proofs V I:=
(
  let H := fresh "H" in
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  let H3 := fresh "H" in
  epose proof (lookup_some_find (V:=V) (booleq := I)) as H;
  epose proof (lookup_addAdjust_another (V:=V) (xbe := I)) as H1;
  epose proof (lookup_none_find (V:=V) (booleq := I)) as H2;
  epose proof (lookup_addAdjust (V:=V) (xbe := I)) as H3
).

Lemma findwd_adjust_another: forall {K V}`{H:XBoolEquable bool K}`{BoolEq.eqb_spec K}`{XDefault V} 
(k1 k2: K) (v: V) (m: mapping K V),
k1 <> k2 ->
Common.hmapFindWithDefault (H7:=H) default k1 (addAdjustListPair (H:=H) k2 v m) =
Common.hmapFindWithDefault (H7:=H) default k1 m.
Proof.
  intros.
  pose_mapping_proofs V H.
  remember (m[k1]?) as y. destruct y.

  - sauto einv: off sinv: off sapp: off lq: on.
  - rewrite H5; sauto einv: off sinv: off lq: on.
Qed.

Lemma findwd_adjust_same: forall {K V}`{H:XBoolEquable bool K}`{BoolEq.eqb_spec K}`{XDefault V} 
(k1 k2: K) (v: V) (m: mapping K V),
k1 = k2 ->
Common.hmapFindWithDefault (H7:=H) default k1 (addAdjustListPair (H:=H) k2 v m) =
v.
Proof.
  intros.
  pose_mapping_proofs V H.
  sauto einv: off sinv: off sapp: off lq: on.
Qed.

Lemma adjust_existing_with_same: 
forall {K V}`{H:XBoolEquable bool K}`{BoolEq.eqb_spec K}`{XDefault V} 
(k: K) (v: V) (m: mapping K V),
keysDistinct m -> 
hmapLookup (H7:=H) k m = Some v ->
addAdjustListPair (H:=H) k v m = m.
Proof.
  intros.
  pose_mapping_proofs V H.  
  destruct m.
  erewrite member_addAdjust; auto.
Qed.

Lemma adjust_adjust: 
forall {K V}`{H:XBoolEquable bool K}`{BoolEq.eqb_spec K}`{XDefault V} 
(k: K) (v1 v2: V) (m: mapping K V),
keysDistinct m -> 
addAdjustListPair (H:=H) k v1 (addAdjustListPair (H:=H) k v2 m) = 
addAdjustListPair (H:=H) k v1 m.
Proof.
  intros. 
  rewrite insert_insert; auto.
Qed.

Ltac pose_more_mapping_proofs V I:=
(
  (* pose_mapping_proofs V I; *)
  let H := fresh "H" in
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  let H3 := fresh "H" in
  epose proof (findwd_adjust_another (V:=V) (H := I)) as H;
  epose proof (findwd_adjust_same (V:=V) (H := I)) as H1;
  epose proof (adjust_existing_with_same (V:=V) (H := I)) as H2 (* ;
  epose proof (adjust_adjust (V:=V) (H := I)) as H3 *)
).

Lemma transfer'_balance_recipient_prf (recipient : address) (amount : uint256)   
                                  (ll: LedgerLRecord rec):
      transfer'_balance_recipient_def recipient amount ll.
Proof.
  start_proof. process_no_err_hyp C transfer'_balance_err_prf.
  transfer'_start.
  time prepare_all ll P.
  compute in H1. subst y1. 
  compute_destructed_ledgers _loc.

  print_ifs2.
  single_replace y21 true.
  2:{
    rewrite <- C.
    time bottom_up_goal_solver. (* 2.228 secs *)
  }

  time bottom_up_goal_solver. (* 4.021 secs *)

  clear - C C0.

  erewrite lookup_addAdjust.
  erewrite lookup_addAdjust_another.
  2: assumption.
  reflexivity.
Time Qed.