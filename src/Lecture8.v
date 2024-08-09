From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.

From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Local Open Scope string_scope.

Check "aaa" : string.

Print string.
Print Ascii.ascii.

Print nat.
(* Inductive nat : Set :=  O : nat | S : nat -> nat. *)

Print list.

(* Inductive list (A : Type) : Type :=
	| nil : list A 
    | cons : A -> list A -> list A. *)

(* Inductive ascii : Set :=
	Ascii : bool ->
            bool ->
            bool -> bool -> bool -> bool -> bool -> bool -> Ascii.ascii. *)

Check  Ascii.Ascii  true true false true false false true true.

(* Inductive string : Set :=
	| EmptyString : string 
    | String : Ascii.ascii -> string -> string. *)

(* string <-> list Ascii.ascii *)


(* Definition foo: nat.
  exact 5.
Defined.

Compute foo. *)


Lemma nat_eq_dec (m n: nat) : {m = n} + {m <> n}.
Proof.
    generalize dependent n.
    induction m; intros.
    -
    destruct n.
    +
    Check left.
    apply left.
    reflexivity.
    +
    apply right.
    unfold not.
    intros.
    discriminate.
    -
    destruct n.
    +
    apply right.
    unfold not.
    intros.
    discriminate.
    +
    remember (IHm n). clear Heqs.
    destruct s.
    *
    apply left.
    rewrite e.
    reflexivity.
    *
    apply right.
    unfold not.
    intros.
    inversion H.
    contradiction.
Defined.


Compute nat_eq_dec 5 5.
Compute nat_eq_dec 100 120.

Check string_dec.
(* string_dec
	 : forall s1 s2 : string, {s1 = s2} + {s1 <> s2} *)
   
Compute string_dec "aaa" "bbb".
Compute string_dec "aaa" "aaa".

Locate "+".

Print sumbool.
Print or.

(* Inductive or (A B : Prop) : Prop :=
	| or_introl : A -> A \/ B 
    | or_intror : B -> A \/ B. *)

(* Inductive sumbool (A B : Prop) : Set :=
	| left : A -> {A} + {B} // = sumbool A B
    | right : B -> {A} + {B}. *)

(* 
 P \/ Q
 {P} + {Q} *)

Print bool.

(* Inductive bool : Set :=
        | false : bool
        | true : bool  *)

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Print string_dec.

Lemma eqb_string_refl : forall s : string, true = eqb_string s s.
Proof.
    intros.
    unfold eqb_string.
    remember (string_dec s s).
    destruct s0. 
    - reflexivity.
    - exfalso.
    (* x<>x == x=x -> False *)
    apply n.
    reflexivity.
Qed.

Lemma eqb_string_true_iff : forall x y : string,
  eqb_string x y = true <-> x = y.
Proof.
    intros.
    split; intros.
    - unfold eqb_string in H.
    remember (string_dec x y).
    destruct s.
    +
    apply e.
    +
    discriminate.
    -
    rewrite H.
    rewrite <- eqb_string_refl.
    reflexivity.
Qed.    

Lemma eqb_string_false_iff : forall x y : string,
  eqb_string x y = false <-> x <> y.
Admitted.


Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Check   (t_empty 4)  "aaa".
Compute (t_empty 4)  "aaa".
Compute (t_empty 10) "aaa".
Compute (t_empty 10) "bbb".


Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) : total_map A :=
  fun x' => if eqb_string x x' then v else m x'.

Check t_update (t_empty 0) "aaa" 5.
Compute (t_update (t_empty 0) "aaa" 5) "bbb".
Compute (t_update (t_empty 0) "aaa" 5) "aaa".

Lemma t_update_correct1: forall A m x (v: A), (t_update m x v) x = v.
Proof.
    intros.
    unfold t_update.
    rewrite <- eqb_string_refl.
    reflexivity.
Qed.

Lemma t_update_correct2: forall A m x y (v: A), x <> y ->
                                (t_update m x v) y = m y.
Proof.
    intros.
    unfold t_update.
    apply eqb_string_false_iff in H.
    rewrite H.
    reflexivity.
Qed.

Notation "'_' '!->' v" := (t_empty v) (at level 100, right associativity).

Example example_empty := (_ !-> false).  

Check example_empty.

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Check "bbb" !-> 17 ;
      ("aaa" !-> 5 ; 
      (_     !-> 0)).

Check "bbb" !-> "X" ;
      "aaa" !-> "Y" ; 
      _     !-> "".      

Compute ("bbb" !-> 17 ;
         "aaa" !-> 5 ; 
         _     !-> 0) "bbb".

Compute ("bbb" !-> 17 ;
         "aaa" !-> 5 ; 
         _     !-> 0) "aaa".

Compute ("bbb" !-> 17 ;
         "aaa" !-> 5 ; 
         _     !-> 0) "ccc".

Definition foo (n: nat) := n + 0.
Definition bar (n: nat) := n - 0.

(* Axiom functional_extensionality : forall X Y (f g: X->Y),
(f = g)  <-> (forall (x: X), f x = g x). *)

Require Import Lia.

Lemma foo_is_bar : foo = bar.
Proof.
  Fail reflexivity.
  extensionality n.
  unfold foo, bar.
  lia.
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros.
  (* Unset Printing Notations. *)
  unfold total_map in m.
  extensionality r.
  remember (eqb_string x r).
  destruct b.
  -
  symmetry in Heqb.
  apply eqb_string_true_iff in Heqb.
  rewrite Heqb.
  rewrite 2t_update_correct1.
  reflexivity.
  -
  symmetry in Heqb.
  apply eqb_string_false_iff in Heqb.
  rewrite 2t_update_correct2.
  rewrite t_update_correct2.
  reflexivity.
  all: apply Heqb.
Qed.

Print reflect.

(* Inductive reflect (P : Prop) : bool -> Set :=
	| ReflectT : P -> reflect P true 
  | ReflectF : ~ P -> reflect P false. *)

Lemma eqb_stringP : forall x y : string,
  reflect (x = y) (eqb_string x y).
Proof. Admitted.


(* m n *)
(* S O = S O *)
(* n + 0 = n - 0 *)

Fixpoint eqb_nat (m n: nat): bool :=
match m, n with
| 0,0 => true
| S n', S m' => eqb_nat n' m'
| _, _ => false
end.

Lemma eqb_nat_eq: forall (m n: nat), m = n <-> eqb_nat m n = true.
Admitted.

Lemma t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof.
  intros.
  unfold total_map in m.
  extensionality r.
  remember (eqb_string x r).
  destruct b.
  -
  symmetry in Heqb.
  apply eqb_string_true_iff in Heqb.
  rewrite Heqb.
  rewrite t_update_correct1.
  reflexivity.
  -
  symmetry in Heqb.
  apply eqb_string_false_iff in Heqb.
  rewrite t_update_correct2.
  reflexivity.
  apply Heqb.
Qed.  

  (* 
    x^2:
    0 - 0
    1 - 1 
    2 - 4
    3 - 9 
    ... - init
    *)
    
Lemma t_update_permute : forall (A : Type) (m : total_map A)
                                v1 v2 x1 x2,
  x2 <> x1  ->  
  (x1 !-> v1 ; x2 !-> v2 ; m) = (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros.
  extensionality y.
  remember (eqb_string x1 y) as b1.
  remember (eqb_string x2 y) as b2.
  destruct b1, b2; symmetry in Heqb1, Heqb2.
  -
  apply eqb_string_true_iff in Heqb1, Heqb2.
  rewrite Heqb1, Heqb2.
  rewrite ?t_update_correct1.
  rewrite Heqb1, Heqb2 in H.
  contradiction.
  (* unfold not in H.
  exfalso.
  apply H.
  reflexivity. *)
  -
  apply eqb_string_true_iff in Heqb1.
  apply eqb_string_false_iff in Heqb2.
  rewrite Heqb1.
  rewrite t_update_correct1 .
  rewrite t_update_correct2 .
  rewrite t_update_correct1 .
  reflexivity.
  apply Heqb2.
  -
  apply eqb_string_true_iff in Heqb2.
  apply eqb_string_false_iff in Heqb1.
  rewrite Heqb2.
  rewrite t_update_correct1 .
  rewrite t_update_correct2 .
  rewrite t_update_correct1 .
  reflexivity.
  apply Heqb1.
  -
  apply eqb_string_false_iff in Heqb1.
  apply eqb_string_false_iff in Heqb2.
  rewrite ?t_update_correct2 .
  reflexivity.
  all: auto.
Qed.

Print option.

(* Inductive option (A : Type) : Type :=
	 | Some : A -> option A 
   | None : option A. *)

Definition partial_map (A : Type) := total_map (option A).

(* int a; *)

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Definition option_join {X} (m: option (option X)) : option X := 
match m with
| None => None
| Some x => x
end.

Notation "x '⊢>' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '⊢>' v" := (update empty x v)
  (at level 100).

Example examplepmap :=
  ("Church" ⊢> true ; "Turing" ⊢> false).

Check examplepmap : partial_map bool. (* ? *)
Check examplepmap : total_map (option bool). (* ? *)
Check examplepmap : string -> option bool.

Lemma apply_empty : forall (A : Type) (x : string),
  @empty A x = None.
Proof.
auto.
Qed.


Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x ⊢> v ; m) x = Some v.
Proof.
  intros.
  Locate "_ ⊢> _ ; _ ".
  Print update.
  unfold update.
  Locate "_ !-> _ ; _".
  unfold t_update.
  Search (true = eqb_string _ _ ).
  rewrite <- eqb_string_refl.
  auto.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
  x2 <> x1 ->
  (x2 ⊢> v ; m) x1 = m x1.
Proof.
  intros.
  unfold update.
  unfold t_update.
  Search (eqb_string _ _ = false <-> _ <> _).
  rewrite <- eqb_string_false_iff in H.
  rewrite H.
  auto.
Qed.


Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x ⊢> v2 ; x ⊢> v1 ; m) = (x ⊢> v2 ; m).
Proof.
  intros.
  unfold update.
  unfold t_update.
  extensionality a.
  destruct (eqb_string x a) eqn: eq.
  all : auto.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
  m x = Some v ->
  (x ⊢> v ; m) = m.
Proof.
  intros.
  unfold update.
  unfold t_update.
  extensionality a.
  destruct (eqb_string x a) eqn: eq.
  Search (eqb_string _ _ = true <-> _ = _ ) .
  rewrite eqb_string_true_iff in eq.
  rewrite eq in H.
  rewrite H.
  all : auto.
Qed.


Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
  x2 <> x1 ->
  (x1 ⊢> v1 ; x2 ⊢> v2 ; m) = (x2 ⊢> v2 ; x1 ⊢> v1 ; m).
Proof.
  intros.
  unfold update.
  unfold t_update.
  extensionality a.
  destruct (eqb_string x1 a) eqn: eq1.
  destruct (eqb_string x2 a) eqn: eq2.
  rewrite eqb_string_true_iff in eq1.
  rewrite eqb_string_true_iff in eq2.
  rewrite <- eq1 in eq2.
  rewrite eq2 in H.
  exfalso.
  Print not.
  Locate "<>".
  unfold not in H.
  apply H. auto.
  auto.
  destruct (eqb_string x2 a) eqn: eq2.
  all : auto.
Qed.

Definition inclusion {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.

Lemma inclusion_update : forall (A : Type) (m m' : partial_map A)
  (x : string) (vx : A),
inclusion m m' ->
inclusion (x ⊢> vx ; m) (x ⊢> vx ; m').
Proof.
  intros.
  unfold update.
  unfold t_update.
  unfold inclusion in *. intros.
  destruct (eqb_string x x0) eqn:eq.
  auto.
  apply H in H0.
  auto.
Qed.