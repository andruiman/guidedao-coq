
Require Import Lia.
Require Import List.
Import ListNotations.

Local Open Scope list_scope.
(* 
Require Import Lecture7.
Require Import Lecture8. *)


Lemma app_ass: forall X (l1 l2 l3: list X) , app (app l1 l2) l3 = app l1 (app l2 l3).
Proof.
    intros.
    (* simpl. *)
    induction l1.
    - simpl. reflexivity.
    - simpl. (* "a::x" =  cons a x *)
      rewrite IHl1.
      reflexivity.
Qed.


About length.
Print length.

(* Fixpoint length {X} (l: list X): nat :=
    match l with
    | nil => O
    | cons x xs => S (length xs)
    end. *)

Lemma app_length: forall X (l1 l2: list X), length (l1 ++ l2) = (length l1) + (length l2).
Proof.
    intros.
    induction l1.
    - simpl. reflexivity.
    - simpl. rewrite IHl1. reflexivity.
Qed.

Module Playground.

Fixpoint map {X Y} (f: X -> Y) (l: list X) : list Y :=
    match l with
    | [] => []
    | x::xs => (f x)::(map f xs)
    end.

Check [1; 2; 3]: list nat.

Check plus 1.

Compute map (plus 1) [1; 2; 3].

(* Check evenb.

Compute map evenb [1; 2; 3]. *)

End Playground.

Lemma map_length: forall X Y (l: list X) (f: X->Y), length (map f l) = length l.
Proof.
    intros.
    Fail destruct f.
    induction l.
    - simpl. reflexivity.
    - simpl. rewrite IHl. reflexivity.
Qed.

Module Playground2.

Fixpoint filter {X} (test: X -> bool) (l: list X) : list X :=
    match l with
    | [] => []
    | x::xs => if (test x) then x::(filter test xs) else (filter test xs)
    end.

(* Compute filter evenb [1; 2; 3 ; 5; 8]. *)

End Playground2.

Lemma filter_length: forall X (test: X -> bool) (l: list X),
                     length (filter test l) <= length l.
Proof.
    intros.
    induction l.
    - simpl. (* reflexivity. *)
        Locate "<=".
        Check le.
        Print le.
        constructor 1. (* apply le_n. *)
    - simpl.
      destruct (test a).
    + simpl. lia.  
    + lia. (* remember (length (filter test l)) as m.
    remember (length l) as n. clear Heqm Heqn.
    (* Inductive le (n : nat) : nat -> Prop :=
	le_n : n <= n | le_S : forall m : nat, n <= m -> n <= S m *)
    apply le_S in IHl.
    apply IHl. *)
Qed.


Lemma filter2_length: forall X (test: X -> bool) (l: list X),
                      filter test (filter test l) = filter test l.
Proof.
    intros.
    induction l.
    - simpl.  reflexivity.
    - simpl.
      remember (test a) as ta.
      destruct ta. 
      + simpl.
      rewrite <- Heqta.
      rewrite IHl.
      reflexivity.
      + apply IHl.
Qed.


(*
[1;2;3;4] -> [2, 4] 
? [1, 3]
*)

Definition invf {X} (f: X -> bool) (x:X) : bool := 
    negb (f x).

(* λ абстракция 

λ x . (f x)

λ x . (x + x)

*)    

Compute (fun x => x + x) 5.

(*
f : nat -> V

[ v0, v1, v2, ...]

[ v0, v1, y, ...]

*)


Definition upd {V: Type} (f: nat -> V) (x: nat) (y: V): nat -> V :=
    fun x' => if (Nat.eqb x x') then y else f x'.

Lemma upd_correct: forall {V: Type} (f: nat -> V) (x: nat) (y: V), (upd f x y) x = y.
Proof.
    intros.
    unfold upd.
    enough (Nat.eqb x x = true).
    rewrite H. reflexivity.
Admitted.
    
(* fun x => sin x *)
(* (fun x => f x) y = f y *)


Lemma filter_dec: forall X (test: X -> bool) (l: list X),
            length (filter test l) + length (filter (fun x => negb (test x)) l) = length l .
Proof.
    intros.
    induction l.
    - simpl. reflexivity.
    - simpl.  
    remember (test a) as ta.
    destruct ta.
    + simpl. 
    rewrite IHl.
    reflexivity.
    + simpl.
    rewrite <- plus_n_Sm.
    rewrite IHl.
    reflexivity.
Qed.

Fixpoint forallb {X} (test: X -> bool) (l: list X) : bool :=
    match l with
    | [] => true
    | x::xs => andb (test x) (forallb test xs)
    end.

(* Compute forallb evenb [2;100; 58].    
Compute forallb evenb [2;100; 58; 33].    *) 

Lemma filter_forallb: forall  X (test: X -> bool) (l: list X), forallb test (filter test l) = true.
Proof.
    intros.
    induction l.
    -
    simpl. reflexivity.
    -
    simpl. remember (test a) as ta.
    destruct ta.
    +
    simpl. rewrite <- Heqta.
    simpl. apply IHl.
    +
    apply IHl. 
Qed.

(*

[1;2;3] -> [3;2;1]

*)

Fixpoint rev {X} (l: list X) :=
    match l with
    | [] => []
    | x::xs => (*1::[2;3] => (? ++ [1] *) rev xs ++ [x]
    end.

Compute rev [1; 2; 3; 4].    

Lemma rev_length: forall X (l: list X ), length (rev l) = length l.
Proof.
    intros.
    induction l.
    - simpl. reflexivity.
    - simpl. rewrite app_length.
    simpl. 
    lia.
Qed.

Lemma rev_rev: forall X (l: list X ), rev (rev l) = l.
Proof.
    intros.
    induction l.
    - simpl. reflexivity.
    - simpl.

Abort.

Lemma rev_snoc: forall X (l:list X) a, rev (l ++ [a]) = a::rev l.
Proof.
    intros.
    induction l.
    - simpl. reflexivity.
    - simpl. rewrite IHl. simpl. reflexivity.
    
Qed.


Theorem rev_rev: forall X (l: list X ), rev (rev l) = l.
Proof.
    intros.
    induction l. 
    - simpl. reflexivity.
    - simpl. rewrite rev_snoc. 
    rewrite IHl. reflexivity.
Qed.

Print fold_left.
Print fold_right.


Module Playground3.

Fixpoint fold_left (A B : Type) (f: A -> B -> A) (l:list B) (a: A):  A :=
    match l with
    | [] => a
    | x::xs => fold_left _ _ f xs (f a x)
    end.


Fixpoint fold_right (A B : Type) (f: B -> A -> A)  (a: A) (l:list B) :  A :=
    match l with
    | [] => a
    | x::xs => f x (fold_right _ _ f a xs  )
    end.

End Playground3.