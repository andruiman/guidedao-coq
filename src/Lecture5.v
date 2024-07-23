(* Require Import HomeWork2.
Require Import Lecture3.
Require Import Lecture2. *)

(*dependent type*)
Inductive even : nat -> Prop :=
    | zero : even 0 
    | double : forall a, even a -> even (S (S a)).

(*

Inductive nat := O | S : nat -> nat.
(* {O, S O, S S O, ....}  = nat *)

even: 
zero: even 0, double zero: even 2, double (double zero) : even 4, ... = even

*)

Fixpoint evenb (n: nat): bool :=
match n with
    | 0 => true
    | 1 => false
    | S (S n) => evenb n
end.

(*
 6 -> 4 -> 2 -> 0 -> true
 7 -> 5 -> 3 -> 1 -> false
*)

Lemma even_evenb: forall n, even n -> evenb n = true .
Proof.
    intros.
    induction H.
    - simpl. reflexivity.
    - simpl. apply IHeven.
Qed.

Lemma evenbS: forall n, (evenb (S n) = true -> evenb n = false) /\ 
                        (evenb (S n) = false -> evenb n = true).
Proof.
    intros.
    induction n.
    - split; intros. 
        + simpl in H. discriminate.
        + simpl. simpl in H. reflexivity.
    - split; intros.
        + simpl in H.
          destruct IHn.
          remember (evenb (S n)) as b.
          destruct b.
          * exfalso.
            rewrite H0 in H.
            discriminate.
            reflexivity.
         * reflexivity.
        + simpl in H.
          destruct IHn.
          remember (evenb (S n)) as b.
          destruct b.
          * reflexivity.
          * exfalso.
            rewrite H1 in H.
            discriminate.
            reflexivity.
Qed.

Lemma not_both: forall (P: Prop), ~ (P /\ ~P).
Proof.
    intros.
    unfold not.
    intros.
    destruct H.
    apply H0.
    apply H.
Qed.

Lemma not_both_even': forall n, ~ (even n /\ ~ even n).
Proof.
    intros.
    apply not_both.
Qed.


Lemma not_both_even: forall n, ~ (even n /\ ~ even n).
Proof.
    intros.
    induction n.
    - 
    unfold not. intros.
    apply H. constructor.
    -
    unfold not. intros.
    destruct H.
    destruct n.
    inversion H.
    inversion H.
    apply H0.
    constructor.
    apply H2.
Qed.

Lemma evenb_even_n_or_Sn: forall n, (evenb n = true -> even n) /\ 
                                    (evenb n = false -> even (S n)).
Proof.
    intros.    
    induction n.
    -
    split; intros.
    + constructor.
    + simpl in H. exfalso. discriminate.
    -
    destruct IHn.
    split; intros.
    +
    apply H0.
    apply evenbS.
    apply H1.
    +
    constructor 2.
    apply H.
    apply evenbS.
    apply H1.
Qed.


Lemma evenb_even: forall n, (evenb n = true -> even n) /\ 
                            (evenb n = false -> ~even n).
Proof.
    intros.
    induction n.
    -   split; intros.
        + constructor. (*apply zero*)
        + simpl in H. discriminate.
    -   destruct IHn.
        split; intros.
        +
        apply evenb_even_n_or_Sn.
        apply evenbS.
        apply H1.
        +
        unfold not. intros.
        apply even_evenb in H2.
        rewrite H1 in H2.
        discriminate.
Qed.


Theorem even_evenb_equiv: forall n, evenb n = true <-> even n.
Proof.
    intros.
    split; intros.
    -
    apply evenb_even.
    apply H.
    - 
    apply even_evenb.
    assumption.
Qed.

Section False_implies_all.

Axiom p: False.

Lemma absurd: 5 = 3.
Proof.
    intros.
    pose proof p.
    destruct H.
Qed.

End False_implies_all.

(*принцип исключенного третьего*)
Axiom excluded_middle: forall (P:Prop), P \/ ~P.

Lemma notnot_implies: forall P, ~~P -> P.
Proof.
    intros.
    pose proof (excluded_middle P).
    destruct H0. 
    - apply H0.
    - exfalso.
      unfold not in H, H0.
      apply H.
      apply H0.
Qed.

(*
 P <-> b = true
*)

Definition reflect (P: Prop): Prop := exists (b: bool), P <-> b = true.

Lemma reflect_exm: forall P, reflect P -> (P \/ ~P).
Proof.
    intros.
    unfold reflect in H.
    destruct H.
    destruct x.
    - left. apply <- H. reflexivity.
    - right. unfold not. intros.
    apply -> H in H0.
    discriminate.
Qed.

Lemma even_dec: forall n, even n \/ ~ even n.
Proof.
(*     intros.
    apply excluded_middle. *)
    intros.
    remember (evenb n).
    destruct b.
    -   left.
        apply evenb_even.
        rewrite Heqb.
        reflexivity.
    -   right.
        apply evenb_even.
        rewrite Heqb.
        reflexivity.
Qed.

Lemma S_a_not_even : forall a, even a -> ~ (even (S a)).
Proof.
    intros.
    unfold not.
    intros.
    apply even_evenb in H.
    apply even_evenb in H0.
    assert (evenb a = false).
    apply evenbS.
    apply H0.
    rewrite H in H1.
    discriminate.
Qed.

Lemma a_even_if_S_a_not : forall a, ~ even (S a) -> even a.
Proof.
    intros.
    remember (evenb a).
    destruct b.
    apply evenb_even.
    rewrite Heqb.
    reflexivity.
    exfalso.
    apply H.
    apply evenb_even_n_or_Sn.
    rewrite Heqb.
    reflexivity.
Qed.

Lemma even_or_smth : forall a, even a \/ ~ (even a).
intros.
induction a.
- left. apply zero.
- destruct IHa.
 + right. apply S_a_not_even. apply H. 
 + left. destruct a.
    * exfalso. unfold not in H. apply H. apply zero.
    * apply double. apply a_even_if_S_a_not. apply H.
Qed.

Inductive odd : nat -> Prop :=
    | one : odd 1
    | plus2 : forall a, odd a -> odd (S (S a)).

Lemma even_odd_S: forall a,  (even (S a) -> odd a) /\ 
                             (odd (S a) -> even a) /\ 
                             (even a -> odd (S a)) /\ 
                             (odd a -> even (S a)).
Proof.
    intros.
    induction a.
    -
    repeat split; intros.
    + exfalso. inversion H.
    + constructor. (*zero*)
    + constructor. (*one*)
    + exfalso. inversion H.
    -
    destruct IHa. destruct H0. destruct H1.
    repeat split; intros.
    + apply H1. inversion H3. apply H5.
    + apply H2. inversion H3. apply H5.
    + apply plus2. apply H. apply H3.
    + apply double. apply H0. apply H3.
Qed.

Lemma even_or_odd : forall a, even a \/ odd a.
Proof.
    intros.
    induction a.
    - left. constructor.
    -
    destruct IHa.
    +
    right. apply even_odd_S. apply H.
    +
    left. apply even_odd_S. apply H.
Qed.

Lemma even_not_odd: forall n, (even n -> ~ (odd n)). (* even n -> (odd n -> False) *)
Proof.
    intros.
    induction n.
    -
    unfold not. intros. inversion H0.
    -
    unfold not. intros.
    destruct n.
    + inversion H.
    +
    unfold not in IHn.
    apply IHn.
    *
    apply even_odd_S. inversion H0. apply H2.
    *
    apply even_odd_S. inversion H. apply H2.
Qed.


(* P -> ~Q  = P -> Q -> False *)
(* Q -> ~P  = Q -> P -> False *)

Lemma odd_not_even: forall n,  (odd n -> ~ (even n)). 
Proof.
    intros.
    unfold not.
    intros.
    pose proof even_not_odd.
    unfold not in H1.
    apply H1 with (n:=n).
    apply H0.
    apply H.
Qed.

Lemma even_or_not_even: forall n, even n \/ ~ even n.
Proof.
    intros.
    pose proof (even_or_odd n).
    inversion H.
    left. apply H0.
    right. apply odd_not_even. apply H0.
Qed.


Inductive lt : nat -> nat -> Prop :=
| base : forall a, lt 0 (S a)
| two_S : forall a b, lt a b -> lt (S a) (S b).

Example test_lt : lt 2 3.
Proof.
    apply two_S.
    apply two_S.
    apply base.
Qed.

Lemma lt_or_eq : forall a b, lt a b -> lt (S a) b \/ S a = b.
Proof.
    intros.
    generalize dependent b.
    induction a.
    - intros. destruct b.
    + inversion H.
    + destruct b. 
        * right. reflexivity.
        * left. apply two_S. apply base.
    - intros.
    destruct b.
    + inversion H.
    + inversion H. apply IHa in H2. destruct H2.
        * left. apply two_S. apply H2.
        * right. rewrite H2. reflexivity.
Qed.

Lemma lt_b_S_a : forall a b, lt a b -> lt a (S b).
Proof.
    intros.
    generalize dependent b.
    induction a.
    - intros. apply base.
    - intros. apply two_S. destruct b.
        * exfalso. inversion H.
        * inversion H. apply IHa. apply H2.
Qed. 

Lemma lt_a_S_a : forall a, lt a (S a).
Proof.
    intros.
    induction a.
    - apply base.
    - apply two_S. apply IHa.
Qed.

Lemma lt_or: forall (a b : nat), lt a b \/ lt b a \/ a = b.
Proof.
    intros.
    induction a.
    - destruct b.
     + repeat right. reflexivity.
     + left. apply base.
    - destruct IHa.
     + apply lt_or_eq in H. destruct H. 
        * left. apply H.
        * repeat right. apply H.
     + destruct H.
        * right. left. apply lt_b_S_a. apply H.
        * right. left. rewrite H. apply lt_a_S_a.
Qed.