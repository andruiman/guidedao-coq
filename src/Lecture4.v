(* логика *)

(* интуиционистская логика *)

(* объекты *)
(* аксиомы *)
(* правила вывода *)

(* modus ponens *)
(* Γ: A -> B , A
   ------------
      B *)

Check Prop.
Check False : Prop.
Check True : Prop.
Check I.
Check 5 = 5.
Print True.
Print nat.

Print eq.
Check eq_refl.

Definition _5_is_5: 5 = 5 := eq_refl.

Check eq_refl: 5 = 5.
Fail Check eq_refl: 5 = 6.

Print False.
(* Inductive False : Prop := . *)
Print True.
(* Inductive True : Prop :=  I : True . *)
Print not.
(* not = fun A : Prop => A -> False : Prop -> Prop. *)
Print or.
(*  
Inductive or (A B : Prop) : Prop :=
	or_introl : A -> A \/ B | or_intror : B -> A \/ B
*)

Lemma left_implies_or: forall (A B: Prop) (H: A), (A \/ B).
Proof.
    intros.
    Check or_introl.
    (* apply or_introl.
    apply H. *)
    left. apply H.
Qed.

Lemma right_implies_or: forall (A B: Prop), B -> (or A B).
Proof.
    intros.
    right.
    apply H.
Qed.

Print and.
(* Inductive and (A B : Prop) : Prop :=  conj : A -> B -> A /\ B *)

Lemma conj_with_self: forall (A: Prop), A -> A /\ A.
Proof.
    intros.
    split.
    apply H.
    apply H.
Qed.

Lemma sum0_all0: forall (a b: nat), a + b = 0 -> a = 0 /\ b = 0. 
Proof.
    intros.
    destruct a.
    -
    split.
    +
    reflexivity.
    +
    apply H.
    -
    exfalso.
    simpl in H.
    discriminate.
Qed.

Lemma or_comm: forall (A B: Prop), (A \/ B) -> (B \/ A).
Proof.
    intros.
    destruct H.
    - right. apply H.
    - left. apply H.
Qed.

Lemma and_comm: forall (A B: Prop), (A /\ B) -> (B /\ A).
Proof.
    intros.
    destruct H.
    split. 
    - apply H0.
    - apply H.
Qed.    


Lemma or_assoc: forall (A B C: Prop), ( (A \/ B) \/ C ) -> ( A \/ ( B \/ C) ).
Proof.
    intros.
    destruct H. 
    -
    destruct H.
    +
    left. apply H.
    +
    right. left. apply H.
    -
    right. right. apply H.
Qed.

Lemma or_assoc2: forall (A B C: Prop), ( A \/ ( B \/ C) ) -> ( (A \/ B) \/ C ).
Proof.
    intros.
    destruct H.
    repeat left.
    apply H.
    destruct H.
    left.
    right.
    apply H.
    right.
    apply H.
Qed.

Lemma and_assoc: forall (A B C: Prop), ( (A /\ B) /\ C ) -> ( A /\ ( B /\ C) ).
Proof.
    intros.
    destruct H.
    destruct H.
    constructor. (* apply conj.*)
    - apply H.
    - apply conj.
        + apply H1.
        + apply H0.
Qed.
Print and.  
    (* Inductive and (A B : Prop) : Prop :=  conj : A -> (B -> A /\ B) *)

Lemma False_implies_all: forall (P: Prop), False -> P.
Proof.
    intros.
    destruct H.
Qed.

Lemma not_False: not False (* это не True*).
Proof.
    unfold not.
    intros. (* destruct H. *)
    apply H.
Qed.

(* Definition not (A: Prop) : Prop := A -> False. *)

(* not (not A) <-> A ? *)

Lemma notnot_implies: forall (P: Prop), P -> ~~ P.
Proof.
    intros.
    unfold not.
    intros.
    apply H0.
    apply H.
Abort.

Lemma notnot_implies: forall P, ~~P -> P.
Proof.
    intros.
    unfold not in H.
Abort.





