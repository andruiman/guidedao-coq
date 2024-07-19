Require Import Lecture2.

Lemma right_plus0_forall: (* ∀ *) forall (a: nat), plus a 0 = a.
Proof. 
    intros.
    induction a.
    - (*база математической индукции*)
    simpl. reflexivity.
    - (*индукционный переход*)
    (*индукционное предположение*)
    simpl. 
    (* подставим - переписать*)
    rewrite IHa.
    reflexivity.
Qed.

Lemma plus_a_Sb : forall a b, a + (S b) = S (a + b).
Proof.
    intros.
    induction a.
    - simpl. reflexivity.
    - simpl. rewrite IHa.
    reflexivity.
Qed.

Theorem plus_comm : forall a b, a + b = b + a.
Proof.
    intros.
    induction a.
    - simpl. rewrite right_plus0_forall. 
    reflexivity.  
    - simpl. rewrite plus_a_Sb.
    rewrite IHa.
    reflexivity.
Qed.

(* plus (plus a b) c *)

Theorem plus_assoc : forall a b c, (a + b) + c = a + (b + c).
Proof.
    intros.
    induction a.
    - simpl. reflexivity.
    - simpl. rewrite IHa. reflexivity.
Qed.

Module Playground.

Fixpoint mul (n m : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => m + (mul n' m)
  end.

Lemma mul_0_a : forall a, mul 0 a = 0.
Admitted.

Lemma mul_comm : forall a b, mul a b = mul b a.
Admitted.

End Playground.

Lemma mul_a_0 : forall a,  a * 0 = 0.
Proof.
  intros.
  induction a.
  - reflexivity.
  - simpl.  (* 0 + ( a * 0  )  *)
    (* rewrite IHa. reflexivity. *)
    apply IHa.
Qed.

Lemma mul_a_Sb: forall a b, b * (S a) = b + b * a.
Proof.
  intros.
  induction b.
  - simpl. reflexivity.
  - simpl. rewrite IHb.

  remember (b*a) as n. 
  generalize n. 
  intros. clear Heqn IHb n.
  
  rewrite <- !plus_assoc.
  rewrite (plus_comm b a). 
  reflexivity.
Qed.

Theorem mul_comm : forall a b, a * b = b * a.
Proof.
  intros.
  induction a.
  - simpl. (* symmetry. apply mul_a_0. *)
  rewrite mul_a_0. reflexivity.
  - simpl. rewrite IHa. rewrite mul_a_Sb. reflexivity.
Qed.


Print nat.
Print Nat.add.
Print minus.

(* Check plus_minus. *)
Print Nat.eqb.  

(* Nat.eqb = 
fix eqb (n m : nat) {struct n} : bool :=
  match n with
  | 0 => match m with
	     | 0 => true
         | S _ => false
         end
  | S n' => match m with
            | 0 => false
            | S m' => eqb n' m'
            end
  end
     : nat -> nat -> bool *)

Fixpoint eqb' (m n: nat): bool :=
    match m with
    | 0 => match n with
           | 0 => true
           | S _ => false 
           end 
    | S m' => match n with
              | 0 => false
              | S n' => eqb' m' n'
              end  
    end.

Lemma eqb_0: forall b, Nat.eqb 0 b = true -> b = 0.
Proof.
    intros.
    destruct b.
    - reflexivity.
    - simpl in H. discriminate.
Qed.

Lemma eqb_eq: forall a b, Nat.eqb a b = true <-> a = b.
Proof.
    intros.
    split.
    - intros. generalize dependent b. induction a; intros.
      + symmetry. apply eqb_0. apply H.
      + destruct b. 
        * simpl in H. discriminate.
        * simpl in H. rewrite IHa with (b:=b). 
          ** reflexivity.
          ** (* apply H. *) assumption.
    - intros. generalize dependent b. induction a; intros.
      + rewrite <- H. simpl. reflexivity.
      + destruct b.
        * discriminate.
        * simpl. apply IHa.
    inversion H. reflexivity.
Qed.