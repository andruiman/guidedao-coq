Require Import UrsusEnvironment.Solidity.current.Environment.
From Hammer Require Import Tactics Hammer. 

Require Import TVMModel.Notations.Loadable.
Require Import TVMModel.Notations.Storeable.
Require Import TVMModel.Base.Proofs.EncodeDecode.
Require Import TVMModel.Base.Proofs.TVMBitString.
Require Import TVMModel.Base.Definitions.TVMBitString.
Require Import TVMModel.Base.Definitions.TVMCell.
Require Import TVMModel.Base.Definitions.StateInit.

Require Import UrsusProofs.CommonProofs.
Require Import UrsusProofs.CommonTactics.

Require Import SpecLang.

Lemma address_eqb_raw_eq: forall a1 a2,
address_eqb_raw a1 a2 = true <-> a1 = a2.
Proof.
  intros. split; intros.
  - destruct a1, a2.
  simpl in H.
  apply andb_true_iff in H.
  f_equal.
  + destruct x,x1. f_equal.
  simpl in H. apply Z.eqb_eq. apply H.
  + destruct x0,x2. f_equal.
  simpl in H. apply N.eqb_eq. apply H.
  - destruct a1, a2.
  simpl.
  apply andb_true_iff.
  inversion H.
  split.
  + destruct x0,x2. simpl.
  apply N.eqb_eq. reflexivity.
  + destruct x,x1. simpl.  
  apply Z.eqb_eq. reflexivity.
Qed.


Transparent deduct_currencies_helper hmapFindWithDefault hmapLookup.

Lemma deduct_currencies_helper_none_implies: forall l c a,
       (deduct_currencies_helper l c) [a] ? = None ->
        c [a] ? = None .
Proof.
    intros.
    remember (c [a] ?). destruct y; auto.
    exfalso.
    induction l.
    - simpl in H. congruence.
    - simpl in H.
    destruct a0.
    apply lookup_none_adjust in H.
    auto.
Qed.

Lemma hmapFindWithDefault_cons_another: forall K V`{XBoolEquable XBool K} (a: K) (d: V) k v l,
(forall x y : K, BoolSpec (x = y) (x <> y) (Common.eqb x y)) ->
a <> k -> 
hmapFindWithDefault d a (wrap Map ((k, v) :: l)) =
hmapFindWithDefault d a (wrap Map l).
Proof.
    intros.
    unfold hmapFindWithDefault.
    simpl. unfold hmapLookup. simpl.
    replace (Common.eqb a k) with false.
    simpl. reflexivity.
    symmetry.
    apply <- BoolEq.boolEqNot.
    auto.
Qed.

Lemma deduct_currencies_helper_prf: forall m c a,
      keysDistinct m ->
      (deduct_currencies_helper (unwrap m) c) [a] = xIntMinus c[a] m[a].
Proof.
  intros.
  destruct m.
  generalize dependent c. generalize dependent H.
  induction l; intros.
  - simpl. remember (hmapFindWithDefault (Build_XUBInteger N.zero)
  a c). destruct x. simpl. f_equal. unfold N.zero. lia.
  - simpl. 
  destruct a0.
  enough (a = x \/ a <> x).
  destruct H0.
  +
  subst x. (* Search adjustListPair. *)
  remember (hmapLookup a (deduct_currencies_helper l c)).
  destruct y.
  * erewrite lookup_some_find.
  2: erewrite lookup_some_adjust.
  3: setoid_rewrite <- Heqy.
  3: reflexivity.
  2: reflexivity.
  unfold hmapFindWithDefault.
  unfold hmapLookup.
  simpl. rewrite N.eqb_refl.
  simpl. unfold hmapFindWithDefault in IHl.
  specialize IHl with c. simpl in IHl.
  setoid_rewrite <- Heqy in IHl.
  simpl in IHl.
  remember (c [a] ?).
  destruct y.
  ** simpl in IHl.
  setoid_rewrite <- Heqy0.
  simpl. enough ((wrap Map l) [a] ? = None).
  rewrite H0 in IHl. simpl in IHl.
  setoid_rewrite IHl. f_equal.
  simpl. unfold N.zero. unfold id.
  lia. { inversion H; assumption. } 
  { erewrite <-  keysDistinct_cons_lookup_none. auto. apply H. }
  ** simpl in IHl.
  setoid_rewrite <- Heqy0.
  simpl. enough ((wrap Map l) [a] ? = None).
  (* rewrite H0 in IHl. simpl in IHl. *)
  setoid_rewrite IHl. f_equal. { inversion H; assumption. } 
  { erewrite <-  keysDistinct_cons_lookup_none. auto. apply H. }
  * enough (c [a] ? = None).
    enough (hmapFindWithDefault (Build_XUBInteger N.zero) a
    (wrap Map ((a, x0) :: l)) =  x0).
    rewrite H1.
    rewrite lookup_none_find.
    f_equal.
    rewrite lookup_none_find.
    simpl. unfold N.zero. lia. assumption.
    rewrite <- lookup_none_adjust.
    setoid_rewrite <- Heqy.
    reflexivity.
    unfold hmapFindWithDefault.
    unfold hmapLookup.
    simpl. rewrite N.eqb_refl.
    simpl. reflexivity.
    {  eapply deduct_currencies_helper_none_implies. now rewrite <- Heqy. }
  + remember (hmapLookup a (deduct_currencies_helper l c)).
  destruct y.
  * erewrite lookup_some_find.
  2: erewrite lookup_adjust_another.
  2: reflexivity.
  2: assumption.
  2: setoid_rewrite <- Heqy.
  2: reflexivity.
  enough (hmapFindWithDefault (Build_XUBInteger N.zero) a
  (wrap Map ((x, x0) :: l)) = hmapFindWithDefault (Build_XUBInteger N.zero) a
  (wrap Map ( l))).
  rewrite H1.
  specialize IHl with c. simpl in IHl.
  unfold hmapFindWithDefault in IHl at 1.
  setoid_rewrite <- Heqy in IHl.
  simpl in IHl. setoid_rewrite IHl.
  reflexivity.
  { inversion H; assumption. } { apply hmapFindWithDefault_cons_another. apply BoolEq.XUBInteger_eqb_spec. assumption. }
  * erewrite lookup_none_find.
  2: rewrite <- lookup_none_adjust.
  2: setoid_rewrite <- Heqy. 2: reflexivity.
  enough (hmapFindWithDefault (Build_XUBInteger N.zero) a
  (wrap Map ((x, x0) :: l)) = hmapFindWithDefault (Build_XUBInteger N.zero) a
  (wrap Map ( l))).
  rewrite H1.
  enough (c [a]? = None).
  rewrite lookup_none_find.
  simpl. unfold N.zero. f_equal.
  assumption.
  { eapply deduct_currencies_helper_none_implies. rewrite <- Heqy. auto. } 
  { apply hmapFindWithDefault_cons_another. apply BoolEq.XUBInteger_eqb_spec. assumption. }
  + repeat decide equality.
Qed.


Lemma deduct_currencies_helper2_prf :
  forall l : Datatypes.list (uint32 * varUint32),
    keysDistinct (wrap Map l) ->
  match (deduct_currencies_helper l (wrap Map l)) [Build_XUBInteger 1] ? with
  | Some x => x
  | None => Build_XUBInteger 0
  end = Build_XUBInteger 0.
Proof using.
  pose proof deduct_currencies_helper_prf.
  intros.
  specialize (H (wrap Map l) (wrap Map l) (Build_XUBInteger 1) H0).
  destruct ((deduct_currencies_helper l (wrap Map l)) [Build_XUBInteger 1] ?) eqn:Heq.
  2: reflexivity.
  apply lookup_some_find with (d:=default) in Heq .
  unfold unwrap in H.
  rewrite Heq in H. clear Heq H0.
  remember ((wrap Map l) [Build_XUBInteger 1]).
  rewrite H.
  unfold xIntMinus.
  unfold xubint_intFunRec.
  f_equal.
  unfold xIntMinus.
  unfold uintFunRec.
  unfold uint2N.
  destruct y.
  lia.
Qed.

Lemma ascii_len (a: Ascii.ascii):
  tvmBitStringLen (ascii2TVMBitString a) = 8%nat.
Proof.
  unfold ascii2TVMBitString.
  rewrite <- N2IBS_len. auto.
Qed.

Lemma string_len (s: string):
  tvmBitStringLen (string2TVMBitString s) =
     (8 * (String.length s))%nat.
Proof.
  induction s.
  simpl. auto.
  simpl. rewrite tvmBitStringCombine_len.
  rewrite IHs.
  rewrite ascii_len. lia.
Qed.

Lemma store_cell_some (b: TVMBuilder) (c: TVMCell) :
exists b',
  (tvmBuilderCellCount b < 4)%nat ->
  store b c = Some b'.
Proof.
  (* intros.
  destruct b.  eexists. simpl.
  unfold tvmBuilderAddCell.
  replace (Datatypes.length (l ++ c :: Datatypes.nil) <=? 4)%nat with true.
  f_equal.
  symmetry. rewrite app_length.
  simpl. simpl in H. apply Nat.leb_le. lia.
Qed *)Admitted.

Lemma store_uint_some {n} (b: TVMBuilder) (x: XUBInteger n) :
exists b',
  (tvmBuilderDataLen b + (N.to_nat n) < 1024)%nat ->
  zFitN_pos (N.to_nat n) (Z.of_N (uint2N x)) = true ->
  store b x = Some b'.
Proof.
  (* intros. destruct b. eexists. simpl.
  unfold tvmBuilderStoreUint. rewrite H0. simpl.
  rewrite tvmBitStringCombine_len.
  simpl in H. rewrite Z2IBS_pos_len.
  unfold TVMCell.tvmCellMaxSize.
  replace (tvmBitStringLen t + N.to_nat n <=? 1023)%nat with true.
  auto. symmetry. apply Nat.leb_le. lia.
Qed *)Admitted.

Lemma store_string_some (b: TVMBuilder) (s: string) :
exists b',
  (tvmBuilderCellCount b + 1 < 4)%nat ->
   store b s = Some b'.
Proof.
  (* intros. destruct b. eexists. simpl.
  rewrite app_length. simpl. simpl in H.
  replace (Datatypes.length l + 1 <=? 4)%nat with true.
  auto. symmetry. apply Nat.leb_le. simpl in H. lia.
Qed *) Admitted.