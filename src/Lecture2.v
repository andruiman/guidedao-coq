Require Import Lecture1.

Check bool.
Check nat.

Module Playground.

Inductive bool' := black | white.
(* Inductive bool : Set := true | false. *)

Definition orb' (a b: bool') : bool' := 
(*pattern matching - сравнение с образцом*)    
match a with
| white (*сопоставляем с образцом (конструктор типа) true *) => white
| black (*сопоставляем с образцом (конструктор типа) false *) => b
end.

Print nat.

(*прибавление единицы? *)
Definition incr1 (n: nat) := S n.
Definition incr2 (n: nat) := incr1 (incr1 n).

(*рекурсия*)
(* foo (a : nat) : nat := 
    foo (S a). *)
(* Definition *) 
 (*комбинатор неподвижной точки*)
Fixpoint  plus (a b: nat) : nat := 
match a with
| O => b (* 0 + b = b*)
(* a + b = c =>
   ? (a + 1) + b 
   -------------------------
   (a + 1) + b = c + 1 
   (S a) + b = S c == S (a + b)
*)
| S a' => S (plus a' b)
end.

(* S (plus O b) -> S b   *)

Compute plus (S O) (S O).
Compute plus (S (S O)) (S(S(S O))).

End Playground.

Require Import Datatypes.

Check nat.
Print nat.
Check plus.
Check Playground.plus.

(* Compute plus (S (S O)) (S(S(S O))). *)
Compute plus 2 3.

(* plus 1 a = S a *)

(* Lemma, Theorem , Corollary , Example, Proposition...  *)

Example plus23: plus 2 3 = 5.
Proof.
    simpl.
    reflexivity.
Qed.        

(* 
1. Квантор всеобщности   : ∀
2. Квантор существования : ∃ 
*)

(* ∀ x ∈ X, y ∈ Y, f: X -> Y : ...  *)

Lemma left_plus1_forall: (* ∀ *) forall (a: nat), plus 1 a = S a.
Proof. (*proof mode*)
   (*тактики*)
   (*  Если мы хотим доказать что-то для "любого" то мы можем без ограничения общности 
   доказать это для какого-то конкретного объекта, который мы специально не выбирали *) 
   intros a.
   simpl. (* simplify - упростить *)
   (*тождество*)
   reflexivity. (*рефлексивность*)
Qed. (* quod erat demonstrandum  = что требовалось доказать*)   

(* exercise 1*)
Lemma left_plus0_forall: (* ∀ *) forall (a: nat), plus 0 a = a.
Proof.
    intros.
    simpl.
    reflexivity.
Qed.

Lemma right_plus0_forall: (* ∀ *) forall (a: nat), plus a 0 = a.
Proof.
    intros.
    simpl.
    Fail reflexivity.
Abort.

Lemma deMorgan_bool: forall (a b: bool), negb (orb a b) = andb (negb a) (negb b).
Proof.
   intros a b.
   simpl.
   Fail reflexivity.
   (*a = true | false*)
   (*a = true | false*) 
   destruct a. 
   (*-, +, * ++, *)
   - simpl. reflexivity.
   - simpl. reflexivity.
Qed.

Lemma deMorgan_bool_inverse: forall (a b: bool), negb (andb a b) = orb (negb a) (negb b).
Proof.
   intros a b.
   (*a = true | false*)
   (*a = true | false*) 
   destruct a. 
   (*-, +, * ++, *)
   - simpl. reflexivity.
   - simpl. reflexivity.
Qed.

Lemma right_plus0_forall: (* ∀ *) forall (a: nat), plus a 0 = a.
Proof.
    intros.
    destruct a.
    - simpl. reflexivity.
    - simpl.
    destruct a.
    simpl. reflexivity.
    simpl.
Abort.

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



(* Lemma left_plus1_exists: (* ∃ *) exists (a: nat), plus 1 a = S a.  *)
