(* Vernac (ular) *)
(* Prelude *)

(* jscoq *)

Check nat.
(* nat: Set *)
Check Set.
(* Set: Type *)
Check Type: Type.
(* Type: Type *)
Check 0.
(* 0 : nat *)

Inductive Empty := .
(* Inductive False := . *)

Inductive Point (*название типа*) : Set := I (*имена конструкторов*) .
Check Point.
Check I.

Inductive bool : Set := true | false.
Check bool.
Check true.
Check false.


(*конечно перечислимые типы*)

(*функции*)

Definition negb (b: bool) : bool := 
(*pattern matching - сравнение с образцом*)    
match b with
| true (*сопоставляем с образцом (конструктор типа) true *) => false
| false (*сопоставляем с образцом (конструктор типа) false *) => true 
end.

Definition negb' b := 
(*pattern matching - сравнение с образцом*)    
match b with
| true (*сопоставляем с образцом (конструктор типа) true *) => false
| false (*сопоставляем с образцом (конструктор типа) false *) => true 
end.

Definition negb'' b := 
(*pattern matching - сравнение с образцом*)    
match b with
| true (*сопоставляем с образцом (конструктор типа) true *) => false
| _ => true
end.


Check negb.
(* negb : bool -> bool (стрелочный тип) *)
(* f : X -> Y *)

Compute (negb true).
(*  = false : bool *)

Compute negb false.
(* = true : bool *)

Definition always_false' (b: bool) : bool := 
(*pattern matching - сравнение с образцом*)    
match b with
| true (*сопоставляем с образцом (конструктор типа) true *) => false
| false (*сопоставляем с образцом (конструктор типа) false *) => false 
end.

Definition always_false'' (b: bool) : bool := 
(*pattern matching - сравнение с образцом*)    
match b with
| _ => false 
end.


Definition always_false (_: bool) : bool := false.
Definition always_true (b: bool) : bool := true.

Definition bool_id' (b: bool) : bool := 
(*pattern matching - сравнение с образцом*)    
match b with
| true (*сопоставляем с образцом (конструктор типа) true *) => true
| false (*сопоставляем с образцом (конструктор типа) false *) => false 
end.

Definition bool_id (b: bool) (* : bool *) := b.

Fail Definition bool_id (* (b: bool) *) b (* : bool *) := b.

Fail Check 0 : bool.

Check (bool -> bool).
(* bool -> bool : Set *)

(*или = orb*)

(* 
false || false = false
true || false = true
false || true = true
true || true = true
*)

Definition orb (a b: bool) : bool := 
(*pattern matching - сравнение с образцом*)    
match a with
| true (*сопоставляем с образцом (конструктор типа) true *) => true
| false (*сопоставляем с образцом (конструктор типа) false *) => b
end.

(* 
false && false = false
true && false = false
false && true = false
true && true = true
*)

Definition andb (a b: bool) : bool := 
(*pattern matching - сравнение с образцом*)    
match a with
| true (*сопоставляем с образцом (конструктор типа) true *) => b
| false (*сопоставляем с образцом (конструктор типа) false *) => false
end.

(*натуральные числа*)
(*арифметика Пеано*)
(* 0, 1, 2, 3 , ...  *)

Inductive nat : Set := 
| O (*простой конструктор*)
| S : nat -> nat (*рекурсивный*).

Check O. (* == 0 *)
(* O : nat *)
Check (S O). (* ==1 *)
Check (S (S O)). (* ==2 *)
Check (S (S (S O))). (* ==3 *)

Check S. (*  nat -> nat *)

