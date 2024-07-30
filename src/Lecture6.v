(*bool, nat*)

Print bool.
Print nat.

(* N = 0..∞, Z=-∞..∞, pos=1..∞ *)

(* Require Import ZArith.
Require Import Psatz.

Local Open Scope Z_scope.

Lemma foo: forall (a b: Z), a > b -> b < a.
Proof.
    intros.
    lia.
Qed.

Lemma bar: forall (a b c: Z), a > b -> b > c -> a + b > 2*c.
Proof.
    intros.
    lia. (*nia*)
Qed. *)

(* list  - список *)

Module Playground.

Inductive nat_list :=
| nnil  : nat_list
| ncons : nat -> nat_list -> nat_list.

Check nnil.
Check (ncons 5 nnil).
Check (ncons 6 (ncons 5 nnil)).
Check (ncons 1 (ncons 6 (ncons 5 nnil))). (* [ 1; 6; 5 ]   *)

Inductive bool_list :=
| bnil  : bool_list
| bcons : bool -> bool_list -> bool_list.

Check (bcons true (bcons false (bcons true bnil))). (* [true; false, true] *)

Inductive Weekday := Monday | Tuesday | Wednesday .

Inductive list (X: Type) :=
| nil  : list X
| cons : X -> list X -> list X.

Check list.

Check (list nat).

Check nil.

Check nil nat.

Check (cons bool true (cons bool false (cons bool true (nil bool)))).

Check cons .

Arguments nil {X}. (*неявный максимально погруженный*)
Arguments cons {X}.

Check (cons true (cons false (cons true nil))).
Check (cons 1 (cons 2 (cons 3 nil))).

(*список гомогенный*)
Fail Check (cons 1 (cons true (cons 3 nil))).

Check nil.

Lemma nil_nat: nil (X:=nat) = @nil nat.
Proof.
    reflexivity.
Qed.

End Playground.

Require Import List.
Import ListNotations.

Local Open Scope list_scope.

Check [1; 2; 3].
Check [true; false; true].

Check true::[true; false; true].

Check eq_refl: true::[true; false; true] = [true; true; false; true].

Example head0: true::[true; false; true] = [true; true; false; true].
Proof.
    reflexivity.
Qed.

Example head1: true::(true::(false::(true::[]))) = [true; true; false; true].
Proof.
    reflexivity.
Qed.

Example length0: [] = [true; true; false; true].
Abort.

(* Fail Example boolnat_eq: 1 = true. *)

Fail Example boolnat_list_eq: [1] = [true; true; false; true].

(*list X -> X*)

(*полиморфизм*)
Definition head {X} (l: list X) (d: X) : X :=
    match l with
    | [ ] => d
    | x :: _ => x
    end.

Compute head [1;2;3] 0.
Compute head [] 123. 


Definition tail {X} (l: list X) : list X :=
    match l with
    | [ ] => [ ]
    | _ :: xs => xs
    end.


Compute tail [1;2;3].
Compute tail [].

Lemma head_tail: forall X (l: list X) d, l <> nil -> head l d :: tail l = l.
Proof.
    intros.
    destruct l.
    - simpl. exfalso.
    unfold not in H.
    apply H.
    reflexivity.
    -
    simpl. reflexivity.
Qed.

Lemma head_tail': forall X (l: list X) d, head l d <> d -> head l d :: tail l = l.
Proof.
    intros.
    destruct l.
    - simpl. exfalso.
    simpl in H.
    unfold not in H.
    apply H.
    reflexivity.
    -
    simpl. reflexivity.
Qed.

Lemma head_default: forall X (l: list X) d, head l d = d -> l = [] .
Proof.
    intros.
    destruct l.
    -
    reflexivity.
    -
    simpl in H.
Abort.


(*forall X, list X -> nat*)
Fixpoint length {X} (l: list X): nat :=
    match l with
    | nil => O
    | cons _ xs => S (length xs)
    end.

Lemma length_nil: forall X (l: list X), length l = 0 <-> l = [] .
Proof.
    intros.
    split; intros.
    -
    destruct l.
    +
    reflexivity.
    +
    simpl in H.
    exfalso.
    discriminate.
    -
    rewrite H.
    simpl.
    reflexivity.
Qed.

(*[1;2;3] ++ [4;5] = [1;2;3;4;5]*)

Fixpoint app {X} (l1 l2: list X): list X :=
    match l1 with
    | [] => l2
    | x::xs => x::(app xs l2)
    end.

(*Fixpoint*) Definition snoc {X} (l:list X) (x:X) : list X.
Abort.

Fixpoint app_right {X} (l1 l2: list X): list X :=
    match l2 with
    | [] => l1
    | x::xs => (*l1 ++ x::l2*)
                app_right (app l1 [x]) xs
    end.    

Lemma app_nil_left: forall X (l: list X), app nil l = l.
Proof.
    intros.
    simpl.
    reflexivity.
Qed.

Lemma app_nil_right: forall X (l: list X), app l nil = l.
Proof.
    intros.
    induction l.
    - simpl. reflexivity.
    - simpl.
    rewrite IHl.
    reflexivity.
Qed.


Inductive option (X: Type) : Type := 
| None (* Nothing *) : option X
| Some (* Just *): X -> option X.

Arguments  None {X}.
Arguments  Some {X}.

Definition head_option {X} (l: list X) (* (d: X) *) : option X :=
    match l with
    | [ ] => None 
    | x :: _ => Some x
    end.

Inductive prod (X Y: Type) := pair : X -> Y -> prod X Y.




    
