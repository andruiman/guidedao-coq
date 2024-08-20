Require Import List.
Require Import String. Open Scope string_scope.
Require Export FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Basics.
Require Import NArith.

Generalizable All Variables.
Set Implicit Arguments.


Section Typeclasses.

Class Foo (T: Type) :=
{
    foo: T -> T -> T
}.

Instance Foo_nat : Foo nat :=
{
    foo := Nat.add
}.

Print Instances Foo.

Definition foo_double T `{Foo T} (a b: T) := foo (foo a b) (foo b a).

Check foo_double (T:=nat).

Compute foo_double 4 5.

Instance Foo_N : Foo N :=
{
    foo := N.add
}.

Check foo_double (T:=N).

Compute foo_double 4%N 5%N.

Instance Foo_list X : (Foo (list X)) :=
{
    foo := @List.app X
}.

Check foo_double (T:=list nat).


Import ListNotations.
Local Open Scope list_scope.

Compute foo_double [1;2;3] [4;5].

End Typeclasses.


Reserved Notation "x >>= f" (at level 42, left
associativity).

Reserved Notation "x >>- f" (at level 42, left
associativity).

Reserved Notation "m >> n"  (at level 42, left
associativity).

Reserved Notation "m [] n"  (at level 42, left
associativity).

Reserved Notation "m << n"   (at level 42, left
associativity).

Reserved Notation "m <<= n"   (at level 42, left
associativity).

Reserved Notation "return! x"   (at level 42, left
associativity).

Class Monad (M : Type -> Type) := {
  bind : forall A B,
    M A -> (A -> M B) -> M B;
  unit : forall A , A -> M A;
  bind_assoc :
    forall A B C
    (m : M A)
    (f : A -> M B) (g : B -> M C),
    bind (bind m f) g = bind m (fun i => bind (f i) g);
  right_unit : forall A (m : M A),
    bind m (@unit A) = m;
  left_unit : forall A B (x : A) (f : A -> M B),
    bind (unit x) f = f x
}.

Notation "x >>= f" := (bind _  x f).
(* Notation "! x" := (unit x). *)
Notation "return! x" := (unit x).

Definition join (M : Type -> Type) `{Monad M} (X : Type) (m : M (M X)): M X :=
  m >>= id.

Definition map (M:Type->Type)(X Y:Type)(f:X->Y)`{Monad M}(m:M X):M Y :=
  m >>= (fun x => return! (f x)).

Definition bind_  {M A B}`{Monad M} (ma: M A) (mb: M B) : M B :=
 ma >>= fun _ => mb.

 Notation "x >> f" := (bind_ x f).

 Notation "x >>- f" := (map f x).

(*  Lemma bind_assoc2: forall {M X Y T}`{Monad M} (m1: M X) 
                                          (m2: X -> M Y) 
                                          (m3: Y -> M T), 
                   (m1 >>= m2) >>= m3 = m1 >>= (fun x => m2 x >>= m3).
Proof.
 intros. rewrite ?bind_assoc. auto. 
Qed. *)

Lemma bind_assoc3: forall {M X Y T}`{Monad M} (m1: M X) 
                                          (m2: X -> M Y) 
                                          (m3: M T), 
                   m1 >>= (fun x => m2 x >> m3) = 
                   (m1 >>= m2) >> m3.
Proof.
 intros. unfold bind_. rewrite bind_assoc. auto. 
Qed.

Lemma bind_eq: forall {M X Y}`{Monad M} (f g:X-> M Y) (m: M X),
                f = g ->
                         m >>= f =
                         m >>= g.
Proof.
 intros. rewrite H0. auto.
Qed.

Lemma bind_assoc4: forall {M X Y T}`{Monad M} (m1: M X) 
                                          (m2: M Y) 
                                          (m3: X -> M T), 
                   m1 >>= (fun x => m2 >> m3 x) = 
                   (m1 >>= (fun x => m2 >> return! x)) >>= m3.
Proof.
 intros. unfold bind_. rewrite ?bind_assoc.
 replace (fun i : X => m2 >>= (fun _ : Y => return! i) >>= m3) with
         (fun i : X => m2 >>= (fun _ : Y => return! i >>= m3)).        
 apply bind_eq. extensionality x.
 apply bind_eq. extensionality y.
 rewrite left_unit.  auto.
 extensionality x. rewrite bind_assoc. 
 auto.
 Qed.
 

Lemma bind_assoc_: forall {M X Y T}`{Monad M} (m1: M X) 
                                              (m2: M Y) 
                                              (m3: M T), 
                   (m1 >> m2) >> m3 = m1 >> (m2 >> m3).
Proof.
 intros. unfold bind_. rewrite ?bind_assoc. auto. 
Qed.


Lemma bind_bind: forall {M X Y}`{Monad M} (ma: M X) (mb: M Y),
                 ma >> mb = ma >>= (fun _ => mb).
Proof.
 auto.
Qed.

Section Identity.

Definition id_bind {A B}
       (ma: A) 
       (f: A -> B): B := f ma.

Definition id_unit {A} (a: A):  A :=  a.

Lemma id_bind_assoc:   forall (A B C : Type)
                           (m :  A)
                           (f : A ->  B)
                           (g : B ->  C),
       id_bind (id_bind m f) g = id_bind m  (fun i : A => id_bind (f i) g).
Proof.
 intros. unfold id_bind. auto.
Qed.


Lemma id_left_unit: forall (A B : Type) (x : A)
         (f : A -> B), id_bind (id_unit x) f = f x.
Proof.
 intros. (* compute. *) unfold id_bind, id_unit.  auto.
Qed.         


Lemma id_right_unit: forall (A : Type) (m : A),
       id_bind m id_unit = m.
Proof.
 intros. auto.
Qed.

Definition idMonad := @id Type.

Global Instance idMonad_Monad : Monad idMonad :=
{
  bind A B := @id_bind A B;
  unit A := @id_unit A;

  bind_assoc := id_bind_assoc;
  left_unit := id_left_unit;
  right_unit := id_right_unit
}.

Check return! 5: idMonad nat.
Check bind (M := @id Type) .
Check bind.
Check bind _ (return! 5: idMonad nat) (fun x => unit (x + 1)).
Check return! 5 >>= fun x => unit (x + 1).
Compute return! 5 >>= fun x => unit (x + 1).

End Identity.

Section Option.

Definition option_bind {A B}
       (ma: option A) 
       (f: A -> option B): option B :=
match ma with
| None => None
| Some a => f a
end.

Definition option_unit {A} (a: A): option A := Some a.

Lemma option_bind_assoc:   forall (A B C : Type)
                           (m : option A)
                           (f : A -> option B)
                           (g : B -> option C),
       option_bind (option_bind m f) g = option_bind m  (fun i : A => option_bind (f i) g).
Proof.
 intros. destruct m. 
 - simpl. auto.
 - simpl. auto.
Qed.


Lemma option_left_unit: forall (A B : Type) (x : A)
         (f : A -> option B), option_bind (option_unit x) f = f x.
Proof.
 intros. simpl. auto.
Qed.         


Lemma option_right_unit: forall (A : Type) (m : option A),
       option_bind m option_unit = m.
Proof.
 intros. destruct m.
 - simpl. auto. 
 - simpl. auto.
Qed.

Instance option_Monad : Monad option :=
{
  bind A B := @option_bind A B;
  unit A := @option_unit A;
  bind_assoc := option_bind_assoc;
  left_unit := option_left_unit;
  right_unit := option_right_unit
}.


Check return! 5 >>= fun x => return! (x + 1).

Definition sample1 (a: option nat) := a >>= fun x => return! (x + 1).

Compute sample1 (Some 5).
Check sample1 None.
Compute sample1 None.

End Option.

Section State.

Inductive state (S X : Type) :=
  | State : (S -> (X * S)) -> state S X.

Lemma state_eq: forall (S X:Type) (m n: S -> X * S), State m = State n <-> m = n.
Proof.
 intros. split; intros. inversion H. auto. rewrite H. auto.
Qed.

Definition state_unit {S X: Type} (x : X) : state S X := 
           State (fun s => (x, s)).

Definition run {S X : Type} (m : state S X) : (S -> (X * S)) :=
match m with
   State c => c
end.
 
Definition state_bind {S X Y: Type} (m : state S X) (f: X -> state S Y): state S Y:= 
State (fun s =>
      match run m s with
        | (x, s') => run (f x) s'
      end).

Lemma state_bind_unit : forall S X Y (x : X) (f : X -> state S Y),
      state_bind (state_unit x) f = f x.
Proof. 
  intros. unfold state_bind. unfold state_unit. simpl. unfold run.
  destruct (f x). auto.
Qed.

Lemma state_unit_bind : forall S X (m : state S X), state_bind m state_unit = m.
Proof.
 intros. unfold state_bind. destruct m. apply state_eq. extensionality y.
 unfold run. unfold state_unit. simpl. destruct (p y). auto.
Qed.

Lemma state_bind_assoc : 
   forall S X Y Z
         (m : state S X)
         (f : X -> state S Y)
         (g : Y -> state S Z),
    state_bind (state_bind m f) g = state_bind m (fun i=> state_bind (f i) g).
Proof.
 intros. unfold state_bind. unfold run. destruct m.
 apply state_eq. extensionality n. destruct (p n). auto.
Qed.

Definition eval_state {S X} (m : state S X) (init : S) : X :=
  fst (run m init).

Definition exec_state {S X} (m : state S X) (init : S) : S :=
  snd (run m init).

Definition map_state {S X Y} (f : (X * S) -> (Y * S)) (m : state S X) : state S Y :=
  State (fun s => f (run m s)).

Definition with_state {S X} (f : S -> S) (m : state S X) : state S X :=   
  State (fun s => run m (f s)).

#[global]
Instance state_Monad S: Monad (state S):=
{
  bind := @state_bind S;
  unit := @state_unit S;
  bind_assoc := @state_bind_assoc S;
  left_unit := @state_bind_unit S;
  right_unit := @state_unit_bind S
}.


Check State (fun s => (0, s + 1)).

Definition mod_state1 : state nat nat := State (fun s => (0, s + 1)).

Compute eval_state mod_state1 0.
Compute exec_state mod_state1 0.

Definition mod_state2 : state nat nat := State (fun s => (1, s - 1)).

Compute eval_state (mod_state1 >> mod_state2) 0.
Compute exec_state (mod_state1 >> mod_state2) 0.

Definition mod_state3 (x: nat) : state nat nat := State (fun s => (2, s + x)).

Compute eval_state (mod_state1 >> mod_state2 >>= mod_state3) 0.
Compute exec_state (mod_state1 >> mod_state2 >>= mod_state3) 0.


Class Monad_State (S: Type) :=
{ 
  monad_state :> Monad (state S);
  get : state S S;
  put : S -> state S S;
  getput: forall s t, run (put s >>= (fun _ => get)) t = (s, s); 
  putget: forall t, run (get >>= put) t = (t,t)
}.

Definition modify {S: Type} (f: S -> S)`{Monad_State S}: state S S := 
  get >>= (compose put f).

Definition gets {S T: Type} (f: S -> T)`{Monad_State S}: state S T :=
  get >>= (compose state_unit f).

Definition state_get {S:Type} : state S S:= 
  State (fun s => (s,s)).

Definition state_put {S:Type} (s:S) : state S S:= 
  State (fun _ => (s,s)).

Lemma state_getput: forall (S:Type) (s:S) (t:S), 
                 run (state_put s >>= (fun _ => state_get)) t = (s, s).
Proof.
 intros. unfold state_put. unfold state_get. unfold run. unfold bind.
 simpl. auto.
Qed.

Lemma state_putget: forall (S:Type) (t:S), run (state_get >>= state_put) t = (t,t).
Proof.
 intros. unfold state_put. unfold state_get. unfold run. unfold bind. 
 simpl. auto.
Qed.


Lemma eval_bind: forall {X Y S:Type} (u1: state S X) 
                                     (u2: state S Y) (s:S), 
                        eval_state (u1 >> u2) s = eval_state u2 (exec_state u1 s).
Proof.
 intros. compute. destruct u1. destruct u2.
 remember (p s). destruct p1. auto.
Qed.
 
Lemma bind_assoc2: forall {X Y T S: Type} (u1: state S X) 
                                          (u2: state S Y) 
                                          (u3: state S T), 
                   (u1 >> u2) >> u3 = u1 >> (u2 >> u3).
Proof.
 intros. compute. apply state_eq.
 extensionality s0. destruct u1. 
 remember (p s0). destruct p0. destruct u2.
 destruct u3. auto.
 Restart.
 intros. apply bind_assoc_.
Qed.

Lemma eval_bind2: forall (X Y S: Type) 
                         (m: state S X)
                         (f: X -> state S Y) 
                         (s: S), 
           eval_state (state_bind m (fun (x : X) => f x)) s = 
           eval_state (f (eval_state m s)) (exec_state m s).
Proof.
 intros. compute. destruct m. destruct (p s). auto.
Qed.

Lemma exec_bind: forall (X Y S: Type) 
                         (m: state S X)
                         (f: X -> state S Y) 
                         (s: S), 
           exec_state (state_bind m (fun (x : X) => f x)) s = 
           exec_state (f (eval_state m s)) (exec_state m s).
Proof.
 intros. compute. destruct m. destruct (p s).
 auto.
Qed.


Reserved Notation "!! x"   (at level 41, left
associativity).

#[global]
Instance stateM_Monad S: Monad_State S:=
{
   monad_state :=  state_Monad S;
   get := state_get;
   put := state_put;
   getput:= @state_getput S;
   putget:= @state_putget S
}.

Notation "!! x" := (put x).

End State.





