Require Export Coq.Lists.List.
Require Export ZArith.
Require Export FunctionalExtensionality.
Require Import Datatypes.
Require Import Coq.Program.Basics.
Require Export Coq.ZArith.BinInt.
Require Export Lia.
Require Export Permutation.

(* Require Import SimpleSortTask.SimpleSortTaskSpec. *)

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Local Definition zlist := list Z.

Local Definition headDefault {X} (a: X) (l: list X) : X :=
match l with
| [] => a
| x :: _ => x
end.

Inductive sorted : zlist -> Prop :=
| sortnil: sorted []
| sortcons: forall (a:Z) m, sorted m -> a <= (headDefault a m) -> sorted (a :: m).

Class Sort := {
 sort: zlist -> zlist;
 sort_perm: forall (l: zlist), Permutation l (sort l);
 sort_sorted: forall (l: zlist), sorted (sort l);
}.

Notation head := headDefault.

Fixpoint insert (n:Z) (ms : zlist) {struct ms} : zlist :=
match ms with
| nil => [n]
| m :: ms' => if (n <=? m) then (n :: ms) 
                           else (m :: (insert n ms'))
end.

Fixpoint fsort (ms : zlist) : zlist :=
match ms with
| [] => []
| m :: ms' => insert m (fsort ms')
end.

Lemma headinsert: forall (a n:Z) (l: zlist),
                  sorted l -> head a (insert n l) = n \/ head a (insert n l) = (head a l).
Proof.
 intros. induction l.
 simpl. left. auto.
 simpl. remember (n <=? a0) as b. destruct b; auto.
Qed.

Lemma insert_sorted: forall (n: Z) (l: zlist),
                     sorted l -> sorted (insert n l).
Proof.
 intros. induction l.
 constructor.  constructor. 
 simpl. lia.
 simpl. remember (n <=? a) as b.
 destruct b. constructor. auto. simpl.
 apply Z.geb_le. rewrite Z.geb_leb. auto.
 constructor. apply IHl.
 inversion H. auto.
 assert (head a (insert n l) = n \/ head a (insert n l) = (head a l)).
 apply headinsert. inversion H. auto.
 inversion H0. erewrite H1. apply Z.geb_le.  unfold Z.leb in Heqb.
 unfold Z.geb.
 remember (n ?= a). destruct c; auto. rewrite H1.
 inversion H. auto.
Qed.

Theorem fsort_sorted: forall (l: zlist),
                     sorted (fsort l).
Proof.
 intros. induction l.
 constructor. simpl. 
 apply insert_sorted. auto.
Qed.

Lemma insertdiv: forall x l, exists l' l'', 
      insert x l = l' ++ [x] ++ l'' /\ l = l' ++ l''.
Proof.
 intros. induction l.
 simpl. exists [], []. split; auto.
 simpl. remember (x <=? a). destruct b.
 exists [], (a::l). split; auto.
 inversion IHl. inversion H. inversion H0.
 rewrite H1. exists (a::x0), x1.
 split; auto. simpl. rewrite H2. auto.
Qed.
 

Theorem fsort_perm: forall (l: zlist),
                   Permutation l (fsort l).
Proof.
 intros. induction l.
 simpl. constructor. simpl. 
 assert (exists l' l'', insert a (fsort l) = l' ++ [a] ++ l'' 
                        /\ fsort l = l' ++ l'').
 apply insertdiv. inversion H. inversion H0. inversion H1.
 rewrite H2. apply perm_trans with (l':= a::(x++x0)).
 constructor. rewrite <- H3. auto. apply Permutation_cons_app.
 apply Permutation_refl.
Qed.

#[local]
Instance  fsort_Sort : Sort := {|
    sort := fsort;
    sort_perm := fsort_perm;
    sort_sorted := fsort_sorted;
|}.




(* 

Ursus Definition fun3 (a b: uint256): UExpression PhantomType true.
{
   ::// require_ ( a < UINT256_5, #{IntError 100} ).

   ::// bbb := ^ bbb .
   ::// require_ ( b > UINT256_1, #{IntError 101} ).
   ::// var0 xxx' :_ := xxx - a ; _ |.
   ::// require_ ( a < xxx', #{IntError 102} ).
   ::// var0 yyy' : _ := yyy - xxx'; _ | .
   ::// require_ ( yyy' < xxx' + b, #{IntError 103} ).

   ::// if test_map () then { map [[ xxx ]] += a } else { map [[ xxx ]] -= b }  .

   ::// yyy ++ .
   
   refine __return__.   
}
return.
Defined.
Sync. 

*)

(* 

Definition fun3_is_error_full_def (ll: LedgerLRecord rec) (a b: uint256): Prop.
  err (fun3 rec def a b) ll | "xxx" "yyy".
  set (req1  := ltb a 5).
  set (req2  := xIntGtb b 1).
  set (xxx_t := xIntMinus xxx a).
  set (req3  := ltb a xxx_t).
  set (yyy_t := xIntMinus yyy xxx_t).
  set (req4  := ltb yyy_t (xIntPlus xxx_t  b)).
  con (negb (req1 && req2 && req3 && req4)).
Defined.
 *)

 (* 
 
Definition fun3_yyy_inc_def (ll: LedgerLRecord rec) (a b: uint256): Prop.
  execs0 (fun3 rec def a b) : ll | "yyy" -> l1 | "yyy".
  con (yyy' = xIntPlus yyy 1).
Defined. 

*)

(* 

Definition fun3_map1_def (ll: LedgerLRecord rec) (a b: uint256): Prop.
  execs0 (fun3 rec def a b) : ll | "map" "xxx" -> l1 | "map".
  evals  (test_map rec def) : l0 -> v'.
  con (map' [xxx] = if (toValue_uni v') then (xIntPlus  (map [xxx]) a) 
                                        else (xIntMinus (map [xxx]) b)).
Defined.

*)