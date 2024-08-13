Require Import Lia.

Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2. apply H1. assumption.
Qed.

Example auto_example_1' : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P -> Q) -> (P -> S)) ->
  T ->
  P ->
  U.
Proof. 
  intros.
  auto. 
Qed.

Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  (* When it cannot solve the goal, auto does nothing *)
  auto.
  (* Let's see where auto gets stuck using debug auto *)
  debug auto.
  (* Optional argument to auto says how deep to search
     (default is 5) *)
  auto 100.
Qed.

Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof.
  intros.
  auto. 
Qed.

Example auto_example_5: 2 = 2.
Proof.
  info_auto.
Qed.


Example auto_example_5' : forall (P Q R S T U W: Prop),
  (U -> T) ->
  (W -> U) ->
  (R -> S) ->
  (S -> T) ->
  (P -> R) ->
  (U -> T) ->
  P ->
  T.
Proof.
  intros.
  info_auto.
  Restart.
  Fail congruence.
  auto.
Qed.

Example auto_example_6: forall X (a b c: X), 
a = b -> b = c -> a = c.
Proof.
    intros.
    Fail progress auto.
    Fail lia.
    congruence.
Qed.

Example auto_example_6': forall (a b c: nat), 
a = b -> b = c -> a = c.
Proof.
    intros.
    (* congruence. *)
    lia.
Qed.

Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof.
    lia. 
Qed.

Example auto_example_7 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  (* lia. *)
  Fail progress auto.
  auto using le_antisym.
Qed.

Example auto_example_7' : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  intros.
  apply le_antisym.
  apply H.
  apply H0.
Qed.

Example auto_example_8: forall X (a b c: X), 
(a = b -> b = c -> a = c) -> a = b -> b = c -> a = c.
Proof.
    intros.
    auto.
Qed.

Example auto_example_8': forall X (a b c: X), 
(forall (a b c: X), a = b -> b = c -> a = c) -> a = b -> b = c -> a = c.
Proof.
    intros.
    Fail progress auto.
    congruence.
Qed.

Require Import NArith.

Local Open Scope N_scope.

Check 5.

Print N.
(* Inductive N : Set :=  N0 : N | Npos : positive -> N. *)

Print positive.
(* Inductive positive : Set :=
	xI : positive -> positive | xO : positive -> positive | xH : positive. *)

Check xO xH.
Check xI xH.

Example lia_example_1: forall (a b c: N), a > b -> b > c -> a > c.
Proof.
    lia.
Qed.


Example lia_example_2: forall (a b c: N), a > c -> a + b > b + c.
Proof.
    lia.
Qed.


Example lia_example_3: forall (a b c: N), a > c -> a * b >= c * b.
Proof.
    Fail lia.
    nia.
Qed.

Example lia_example_4: forall (a b c: N), a > c -> b > 0 -> a * b > c * b.
Proof.
    Fail lia.
    nia.
Qed.

Example congruence_example_1 : forall (A:Type) 
                                      (f:A -> A) 
                                      (g: A -> A -> A) a b, 
                                      a = (f a) -> 
                                      (g b (f a)) = (f (f a)) -> 
                                      (g a b) = (f (g b a)) -> 
                                      (g a b) = a.
Proof.
    intros.
    rewrite H1.
    replace (a) with (f a) at 1.
    rewrite H0.
    rewrite <- 3H.
    reflexivity.
Qed.

Example congruence_example_1' : forall (A:Type) 
                                      (f:A -> A) 
                                      (g: A -> A -> A) a b, 
                                      a = (f a) -> 
                                      (g b (f a)) = (f (f a)) -> 
                                      (g a b) = (f (g b a)) -> 
                                      (g a b) = a.
Proof.
    Fail progress auto.
    congruence.
Qed.

Example congruence_example_2 : forall (A:Type) 
                                      (f: A -> A * A) 
                                      (a c d: A) ,
                                f = pair a -> 
                                Some (f c) = Some (f d) -> 
                                c = d.
Proof.
    intros.
    rewrite H in H0.
    inversion H0.
    reflexivity.
Qed.    

Example congruence_example_2' : forall (A:Type) 
                                      (f: A -> A * A) 
                                      (a c d: A) ,
                                f = pair a -> 
                                Some (f c) = Some (f d) -> 
                                c = d.
Proof.
    congruence.
Qed.


From Hammer Require Import Tactics Hammer.


Example auto_example_1'' : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  sauto.
Qed.


Example auto_example_3' : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  sauto.
Qed.

Example auto_example_6'': forall X (a b c: X), 
a = b -> b = c -> a = c.
Proof.
    sauto.
Qed.

Local Open Scope nat_scope.

Example auto_example_7'' : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  sauto.
Qed.

Example congruence_example_1'' : forall (A:Type) 
                                      (f:A -> A) 
                                      (g: A -> A -> A) a b, 
                                      a = (f a) -> 
                                      (g b (f a)) = (f (f a)) -> 
                                      (g a b) = (f (g b a)) -> 
                                      (g a b) = a.
Proof.
    sauto.
Qed.

Example congruence_example_2'' : forall (A:Type) 
                                      (f: A -> A * A) 
                                      (a c d: A) ,
                                f = pair a -> 
                                Some (f c) = Some (f d) -> 
                                c = d.
Proof.
    sauto.
Qed.

Local Open Scope N_scope.

Example lia_example_1': forall (a b c: N), a > b -> b > c -> a > c.
Proof.
    sauto solve+: lia .
Qed.


Example lia_example_2': forall (a b c: N), a > c -> a + b > b + c.
Proof.
    sauto solve+: lia.
Qed.

Example lia_example_3': forall (a b c: N), a > c -> a * b >= c * b.
Proof.
    sauto solve+: nia.
Qed.

Example lia_example_4': forall (a b c: N), a > c -> b > 0 -> a * b > c * b.
Proof.
    sauto solve+: nia.
Qed.

Example lia_example_4'': forall (a b c: N), a > c -> a * 5 > c * 5.
Proof.
    Fail sauto.
    pose proof lia_example_4'.
    sauto.
Qed.

(* variants *)

Require Import Coq.btauto.Btauto.

Example deMorgan_bool: forall (a b: bool), negb (orb a b) = andb (negb a) (negb b).
Proof.
  Fail progress auto.
  Fail congruence.
  Fail lia.
  intros.
  btauto.
  Restart.
  sauto.
Qed.

Example refl_example: forall X (a: X), a = a .
Proof.
  auto.
  Restart.
  congruence.
  Restart.
  Fail lia.
  Fail btauto.
  reflexivity.
Qed.

Lemma comm_example: forall a b (f: N -> N), 
      (forall x, f x = x) -> (f a) + b = (f b) + a.
Proof.
  intros.
  Fail lia.
  Restart.
  Fail sauto.
  sauto solve+: lia.
Qed.




