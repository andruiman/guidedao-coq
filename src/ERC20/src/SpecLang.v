Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UMLang.ExecGenerator.


Definition unMaybe {X}`{XDefault X} (x: XMaybe X) :=
  xMaybeMapDefault id x default.

Definition iFit (n: N) (x: XBInteger n) :=
  (TVMBitString.zFitN (N.to_nat n) (int2Z x) = true).

Definition uFit (n: N) (x: XUBInteger n) :=
  (TVMBitString.zFitN_pos (N.to_nat n) (Z.of_N (uint2N x)) = true).

Tactic Notation "con" uconstr(p) := refine p.
Tactic Notation "hyp" uconstr(h) := condition h.
Tactic Notation "con+" uconstr(p) := addConclusion p.

Ltac initialize_ledger ll l :=
  set (l := {$$ {$$ {$$ ll with Ledger_LocalState := default $$} 
                       with Ledger_MessagesState := default $$}
                       with Ledger_MainState := initialize_balances (getPruvendoRecord Ledger_MainState ll) $$}).

Ltac full_error_condition f l := con (ExecGenDefs.isError (eval_state (Uinterpreter f) l) = _).
Ltac add_computation_anyls l' l e := 
     refine (let l' := exec_state (Uinterpreter e) l in _).
Ltac add_evaluation_anyls v l e := 
     refine (let v := eval_state (Uinterpreter e) l in _).


(* doesn't work *)
Tactic Notation "flds"  constr(l) "->" ident_list(fl) := (elpi read_fields (l) fl).

Tactic Notation "fld"  constr(l) "->" constr(f1) := 
                 (elpi read_fields (l) (f1)).
Tactic Notation "fld"  constr(l) "->" constr(f1) constr(f2) := 
                 (elpi read_fields (l) (f1) (f2)).
Tactic Notation "fld"  constr(l) "->" constr(f1) constr(f2) constr(f3) := 
                 (elpi read_fields (l) (f1) (f2) (f3)).
Tactic Notation "fld"  constr(l) "->" constr(f1) constr(f2) constr(f3) constr(f4) := 
                 (elpi read_fields (l) (f1) (f2) (f3) (f4)).
Tactic Notation "fld"  constr(l) "->" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                 (elpi read_fields (l) (f1) (f2) (f3) (f4) (f5)).


Tactic Notation "fld"  constr(l) "->" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) 
                                      constr(f6) := 
                 (elpi read_fields (l) (f1) (f2) (f3) (f4) (f5) (f6)).
Tactic Notation "fld"  constr(l) "->" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) 
                                      constr(f6) constr(f7) := 
                 (elpi read_fields (l) (f1) (f2) (f3) (f4) (f5) (f6) (f7)).
Tactic Notation "fld"  constr(l) "->" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) 
                                      constr(f6) constr(f7) constr(f8) := 
                 (elpi read_fields (l) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8)).
Tactic Notation "fld"  constr(l) "->" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) 
                                      constr(f6) constr(f7) constr(f8) constr(f9) := 
                 (elpi read_fields (l) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9)).
Tactic Notation "fld"  constr(l) "->" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) 
                                      constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                 (elpi read_fields (l) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10)).


Tactic Notation "fld"  constr(l) "->" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) 
                                      constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                      constr(f11) := 
                 (elpi read_fields (l) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11)).
Tactic Notation "fld"  constr(l) "->" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) 
                                      constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                      constr(f11) constr(f12) := 
                 (elpi read_fields (l) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12)).
Tactic Notation "fld"  constr(l) "->" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) 
                                      constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                      constr(f11) constr(f12) constr(f13) := 
                 (elpi read_fields (l) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13)).
Tactic Notation "fld"  constr(l) "->" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) 
                                      constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                      constr(f11) constr(f12) constr(f13) constr(f14) := 
                 (elpi read_fields (l) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14)).
Tactic Notation "fld"  constr(l) "->" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) 
                                      constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                      constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                 (elpi read_fields (l) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15)).
                 

Tactic Notation "fld"  constr(l) "->" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) 
                                      constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                      constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                      constr(f16) := 
                 (elpi read_fields (l) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16)).
Tactic Notation "fld"  constr(l) "->" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) 
                                      constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                      constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                      constr(f16) constr(f17) := 
                 (elpi read_fields (l) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17)).
Tactic Notation "fld"  constr(l) "->" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) 
                                      constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                      constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                      constr(f16) constr(f17) constr(f18) := 
                 (elpi read_fields (l) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18)).
Tactic Notation "fld"  constr(l) "->" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) 
                                      constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                      constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                      constr(f16) constr(f17) constr(f18) constr(f19) := 
                 (elpi read_fields (l) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19)).
Tactic Notation "fld"  constr(l) "->" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) 
                                      constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                      constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                      constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                 (elpi read_fields (l) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20)).

(* eval_state *)
Tactic Notation "evals" constr(fn) ":" constr(l) "->" ident(v) := 
                        add_evaluation_anyls (v) (l) (fn).
Tactic Notation "evals0" constr(fn) ":" constr(l) "->" ident(v) :=
                         let l0 := fresh "l0" in
                         initialize_ledger l l0;
                         evals fn : l0 -> v.

(* messages *)
Tactic Notation "msg" uconstr(N) uconstr(I) uconstr(M):=
       (con ((q2m I)[N]? = Some (OutgoingInternalMessage _ M))).
Tactic Notation "msg-" uconstr(N) uconstr(I) uconstr(M):=
       (con ((q2m I)[length_ I - N]? = Some (OutgoingInternalMessage _ M))).
Tactic Notation "msg_transfer" uconstr(N) uconstr(I) :=
       (con ((q2m I)[N]? = Some (EmptyMessage _ _))).
Tactic Notation "msg_transfer-" uconstr(N) uconstr(I) :=
       (con ((q2m I)[length_ I - N]? = Some (EmptyMessage _ _))).


(* isError *)
Tactic Notation "no_err" constr(fn) constr(l) := 
                hyp (ExecGenDefs.isError (eval_state (Uinterpreter fn) l) = false).
Tactic Notation "err" constr(fn) constr(l) := full_error_condition fn l.
Tactic Notation "err0" constr(fn) constr(l) := 
                let l0 := fresh "l0" in 
                initialize_ledger l l0; 
                err fn l0.
Tactic Notation "err0" constr(fn) constr(l) "|" constr(f1) :=
                 err0 fn l;
                 fld l -> (f1).
Tactic Notation "err0" constr(fn) constr(l) "|" constr(f1) constr(f2) := 
                err0 fn l;
                fld l -> (f1) (f2).
Tactic Notation "err0" constr(fn) constr(l) "|" constr(f1) constr(f2) constr(f3) := 
                err0 fn l;
                fld l -> (f1) (f2) (f3).
Tactic Notation "err0" constr(fn) constr(l) "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                err0 fn l; 
                fld l -> (f1) (f2) (f3) (f4).
Tactic Notation "err0" constr(fn) constr(l) "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                err0 fn l;
                fld l -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "err0" constr(fn) constr(l) "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                constr(f6) := 
                err0 fn l;
                fld l -> (f1) (f2) (f3) (f4) (f5) (f6).
Tactic Notation "err0" constr(fn) constr(l) "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                constr(f6) constr(f7) := 
                err0 fn l;
                fld l -> (f1) (f2) (f3) (f4) (f5) (f6) (f7). 
Tactic Notation "err0" constr(fn) constr(l) "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                constr(f6) constr(f7) constr(f8) := 
                err0 fn l;
                fld l -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "err0" constr(fn) constr(l) "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                constr(f6) constr(f7) constr(f8) constr(f9) := 
                err0 fn l;
                fld l -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9).
Tactic Notation "err0" constr(fn) constr(l) "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                err0 fn l;
                fld l -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "err0" constr(fn) constr(l) "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                constr(f11) := 
                err0 fn l;
                fld l -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "err0" constr(fn) constr(l) "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                constr(f11) constr(f12) := 
                err0 fn l;
                fld l -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12).
Tactic Notation "err0" constr(fn) constr(l) "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                constr(f11) constr(f12) constr(f13) := 
                err0 fn l;
                fld l -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "err0" constr(fn) constr(l) "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                constr(f11) constr(f12) constr(f13) constr(f14) := 
                err0 fn l;
                fld l -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "err0" constr(fn) constr(l) "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                err0 fn l;
                fld l -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "err0" constr(fn) constr(l) "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                constr(f16) := 
                err0 fn l;
                fld l -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "err0" constr(fn) constr(l) "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                constr(f16) constr(f17) := 
                err0 fn l;
                fld l -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "err0" constr(fn) constr(l) "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                constr(f16) constr(f17) constr(f18) := 
                err0 fn l;
                fld l -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "err0" constr(fn) constr(l) "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                constr(f16) constr(f17) constr(f18) constr(f19) := 
                err0 fn l;
                fld l -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "err0" constr(fn) constr(l) "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                err0 fn l;
                fld l -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).                


(* exec_state *)
Tactic Notation "execs" constr(fn) ":" constr(l) "->" ident(l') :=             
                 add_computation_anyls (l') (l) (fn).

(* 0 - ... *)
Tactic Notation "execs0" constr(fn) ":" constr(l) "->" ident(l') :=
                     let l0 := fresh "l0" in
                     initialize_ledger l l0;
                     execs fn : l0 -> l'.
Tactic Notation "execs0" constr(fn) ":" constr(l) "->" ident(l') "|" constr(f1) := 
                     execs0 fn : l -> l';
                     fld l' -> (f1) .
Tactic Notation "execs0" constr(fn) ":" constr(l) "->" ident(l') "|" constr(f1) constr(f2) := 
                     execs0 fn : l -> l';
                     fld l' -> (f1) (f2).
Tactic Notation "execs0" constr(fn) ":" constr(l) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) := 
                     execs0 fn : l -> l';
                     fld l' -> (f1) (f2) (f3).
Tactic Notation "execs0" constr(fn) ":" constr(l) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                     execs0 fn : l -> l';
                     fld l' -> (f1) (f2) (f3) (f4).
Tactic Notation "execs0" constr(fn) ":" constr(l) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                     execs0 fn : l -> l';
                     fld l' -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "execs0" constr(fn) ":" constr(l) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) := 
                     execs0 fn : l -> l';
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) := 
                     execs0 fn : l -> l';
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7).
Tactic Notation "execs0" constr(fn) ":" constr(l) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) := 
                     execs0 fn : l -> l';
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "execs0" constr(fn) ":" constr(l) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) := 
                     execs0 fn : l -> l';
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                     execs0 fn : l -> l';
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "execs0" constr(fn) ":" constr(l) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11)  := 
                     execs0 fn : l -> l';
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "execs0" constr(fn) ":" constr(l) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) := 
                     execs0 fn : l -> l';
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) := 
                     execs0 fn : l -> l';
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "execs0" constr(fn) ":" constr(l) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) := 
                     execs0 fn : l -> l';
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "execs0" constr(fn) ":" constr(l) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                     execs0 fn : l -> l';
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "execs0" constr(fn) ":" constr(l) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) := 
                     execs0 fn : l -> l';
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "execs0" constr(fn) ":" constr(l) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) := 
                     execs0 fn : l -> l';
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "execs0" constr(fn) ":" constr(l) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) := 
                     execs0 fn : l -> l';
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "execs0" constr(fn) ":" constr(l) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) := 
                     execs0 fn : l -> l';
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "execs0" constr(fn) ":" constr(l) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                     execs0 fn : l -> l';
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).


(* 1 - ... *)
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) "->" ident(l') "|" constr(f1) := 
                     execs0 fn : l -> l';
                     fld l -> (e1);
                     fld l' -> (f1) .
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) "->" ident(l') "|" constr(f1) constr(f2) := 
                     execs0 fn : l -> l';
                     fld l -> (e1);
                     fld l' -> (f1) (f2).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) := 
                     execs0 fn : l -> l';
                     fld l -> (e1);
                     fld l' -> (f1) (f2) (f3).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                     execs0 fn : l -> l';
                     fld l -> (e1);
                     fld l' -> (f1) (f2) (f3) (f4).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                     execs0 fn : l -> l';
                     fld l -> (e1);
                     fld l' -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) := 
                     execs0 fn : l -> l';
                     fld l -> (e1);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) := 
                     execs0 fn : l -> l';
                     fld l -> (e1);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) := 
                     execs0 fn : l -> l';
                     fld l -> (e1);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) := 
                     execs0 fn : l -> l';
                     fld l -> (e1);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                     execs0 fn : l -> l';
                     fld l -> (e1);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11)  := 
                     execs0 fn : l -> l';
                     fld l -> (e1);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) := 
                     execs0 fn : l -> l';
                     fld l -> (e1);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) := 
                     execs0 fn : l -> l';
                     fld l -> (e1);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) := 
                     execs0 fn : l -> l';
                     fld l -> (e1);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                     execs0 fn : l -> l';
                     fld l -> (e1);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) := 
                     execs0 fn : l -> l';
                     fld l -> (e1);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) := 
                     execs0 fn : l -> l';
                     fld l -> (e1);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) := 
                     execs0 fn : l -> l';
                     fld l -> (e1);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) := 
                     execs0 fn : l -> l';
                     fld l -> (e1);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                     execs0 fn : l -> l';
                     fld l -> (e1);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).
 
(* 2 - ... *)
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) "->" ident(l') "|" constr(f1) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2);
                     fld l' -> (f1) .
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) "->" ident(l') "|" constr(f1) constr(f2) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2);
                     fld l' -> (f1) (f2).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2);
                     fld l' -> (f1) (f2) (f3).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2);
                     fld l' -> (f1) (f2) (f3) (f4).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2);
                     fld l' -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11)  := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).

(* 3 - ... *)
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3)    "->" ident(l') "|" constr(f1) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3);
                     fld l' -> (f1) .
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3)    "->" ident(l') "|" constr(f1) constr(f2) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3);
                     fld l' -> (f1) (f2).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3)    "->" ident(l') "|" constr(f1) constr(f2) constr(f3) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3);
                     fld l' -> (f1) (f2) (f3).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3)    "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3);
                     fld l' -> (f1) (f2) (f3) (f4).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3)    "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3);
                     fld l' -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3)    "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3)    "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3)    "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3)    "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3)    "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3)    "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11)  := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3)    "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3)    "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3)    "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3)    "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3)    "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3)    "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3)    "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3)    "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3)    "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).

                     
(* 4 - ... *)
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4)   "->" ident(l') "|" constr(f1) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4);
                     fld l' -> (f1) .
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4)   "->" ident(l') "|" constr(f1) constr(f2) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4);
                     fld l' -> (f1) (f2).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4);
                     fld l' -> (f1) (f2) (f3).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4);
                     fld l' -> (f1) (f2) (f3) (f4).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4);
                     fld l' -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11)  := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).

                     
(* 5 - ... *)
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5)   "->" ident(l') "|" constr(f1) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5);
                     fld l' -> (f1) .
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5)   "->" ident(l') "|" constr(f1) constr(f2) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5);
                     fld l' -> (f1) (f2).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5);
                     fld l' -> (f1) (f2) (f3).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5);
                     fld l' -> (f1) (f2) (f3) (f4).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5);
                     fld l' -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11)  := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).


(* 6 - ... *)
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6)   "->" ident(l') "|" constr(f1) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6);
                     fld l' -> (f1) .
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6)   "->" ident(l') "|" constr(f1) constr(f2) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6);
                     fld l' -> (f1) (f2).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6);
                     fld l' -> (f1) (f2) (f3).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6);
                     fld l' -> (f1) (f2) (f3) (f4).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6);
                     fld l' -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11)  := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).


(* 7 - ... *)
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7)   "->" ident(l') "|" constr(f1) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7);
                     fld l' -> (f1) .
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7)   "->" ident(l') "|" constr(f1) constr(f2) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7);
                     fld l' -> (f1) (f2).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7);
                     fld l' -> (f1) (f2) (f3).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7);
                     fld l' -> (f1) (f2) (f3) (f4).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7);
                     fld l' -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11)  := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7)   "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).


(* 8 - ... *)
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8)  "->" ident(l') "|" constr(f1) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8);
                     fld l' -> (f1) .
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8)  "->" ident(l') "|" constr(f1) constr(f2) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8);
                     fld l' -> (f1) (f2).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8)  "->" ident(l') "|" constr(f1) constr(f2) constr(f3) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8);
                     fld l' -> (f1) (f2) (f3).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8)  "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8);
                     fld l' -> (f1) (f2) (f3) (f4).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8)  "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8);
                     fld l' -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8)  "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8)  "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8)  "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8)  "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8)  "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8)  "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11)  := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8)  "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8)  "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8)  "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8)  "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8)  "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8)  "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8)  "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8)  "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8)  "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).


(* 9 - ... *)
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) "->" ident(l') "|" constr(f1) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9);
                     fld l' -> (f1) .
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) "->" ident(l') "|" constr(f1) constr(f2) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9);
                     fld l' -> (f1) (f2).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9);
                     fld l' -> (f1) (f2) (f3).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9);
                     fld l' -> (f1) (f2) (f3) (f4).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9);
                     fld l' -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11)  := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).


(* 10 - ... *)
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) "->" ident(l') "|" constr(f1) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10);
                     fld l' -> (f1) .
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) "->" ident(l') "|" constr(f1) constr(f2) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10);
                     fld l' -> (f1) (f2).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10);
                     fld l' -> (f1) (f2) (f3).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10);
                     fld l' -> (f1) (f2) (f3) (f4).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10);
                     fld l' -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11)  := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).


(* 11 - ... *)
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) "->" ident(l') "|" constr(f1) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11);
                     fld l' -> (f1) .
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) "->" ident(l') "|" constr(f1) constr(f2) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11);
                     fld l' -> (f1) (f2).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11);
                     fld l' -> (f1) (f2) (f3).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11);
                     fld l' -> (f1) (f2) (f3) (f4).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11);
                     fld l' -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11)  := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).


(* 12 - ... *)
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) "->" ident(l') "|" constr(f1) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12);
                     fld l' -> (f1) .
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) "->" ident(l') "|" constr(f1) constr(f2) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12);
                     fld l' -> (f1) (f2).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12);
                     fld l' -> (f1) (f2) (f3).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12);
                     fld l' -> (f1) (f2) (f3) (f4).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12);
                     fld l' -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11)  := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).


(* 13 - ... *)
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) "->" ident(l') "|" constr(f1) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13);
                     fld l' -> (f1) .
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) "->" ident(l') "|" constr(f1) constr(f2) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13);
                     fld l' -> (f1) (f2).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13);
                     fld l' -> (f1) (f2) (f3).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13);
                     fld l' -> (f1) (f2) (f3) (f4).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13);
                     fld l' -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11)  := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).


(* 14 - ... *)
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) "->" ident(l') "|" constr(f1) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14);
                     fld l' -> (f1) .
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) "->" ident(l') "|" constr(f1) constr(f2) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14);
                     fld l' -> (f1) (f2).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14);
                     fld l' -> (f1) (f2) (f3).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14);
                     fld l' -> (f1) (f2) (f3) (f4).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14);
                     fld l' -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11)  := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).


(* 15 - ... *)
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) "->" ident(l') "|" constr(f1) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15);
                     fld l' -> (f1) .
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) "->" ident(l') "|" constr(f1) constr(f2) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15);
                     fld l' -> (f1) (f2).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15);
                     fld l' -> (f1) (f2) (f3).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15);
                     fld l' -> (f1) (f2) (f3) (f4).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15);
                     fld l' -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11)  := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).



(* 16 - ... *)
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) "->" ident(l') "|" constr(f1) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16);
                     fld l' -> (f1) .
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) "->" ident(l') "|" constr(f1) constr(f2) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16);
                     fld l' -> (f1) (f2).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16);
                     fld l' -> (f1) (f2) (f3).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16);
                     fld l' -> (f1) (f2) (f3) (f4).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16);
                     fld l' -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11)  := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).


(* 17 - ... *)
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) "->" ident(l') "|" constr(f1) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17);
                     fld l' -> (f1) .
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) "->" ident(l') "|" constr(f1) constr(f2) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17);
                     fld l' -> (f1) (f2).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17);
                     fld l' -> (f1) (f2) (f3).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17);
                     fld l' -> (f1) (f2) (f3) (f4).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17);
                     fld l' -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11)  := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).


(* 18 - ... *)
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) "->" ident(l') "|" constr(f1) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18);
                     fld l' -> (f1) .
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) "->" ident(l') "|" constr(f1) constr(f2) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18);
                     fld l' -> (f1) (f2).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18);
                     fld l' -> (f1) (f2) (f3).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18);
                     fld l' -> (f1) (f2) (f3) (f4).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18);
                     fld l' -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11)  := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).


(* 19 - ... *)
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) "->" ident(l') "|" constr(f1) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19);
                     fld l' -> (f1) .
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) "->" ident(l') "|" constr(f1) constr(f2) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19);
                     fld l' -> (f1) (f2).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19);
                     fld l' -> (f1) (f2) (f3).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19);
                     fld l' -> (f1) (f2) (f3) (f4).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19);
                     fld l' -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11)  := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).


(* 20 - ... *)
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) constr(e20) "->" ident(l') "|" constr(f1) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19) (e20);
                     fld l' -> (f1) .
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) constr(e20) "->" ident(l') "|" constr(f1) constr(f2) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19) (e20);
                     fld l' -> (f1) (f2).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) constr(e20) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19) (e20);
                     fld l' -> (f1) (f2) (f3).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) constr(e20) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19) (e20);
                     fld l' -> (f1) (f2) (f3) (f4).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) constr(e20) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19) (e20);
                     fld l' -> (f1) (f2) (f3) (f4) (f5).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) constr(e20) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19) (e20);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) constr(e20) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19) (e20);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) constr(e20) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19) (e20);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) constr(e20) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19) (e20);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) constr(e20) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19) (e20);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) constr(e20) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11)  := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19) (e20);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) constr(e20) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19) (e20);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12). 
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) constr(e20) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19) (e20);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) constr(e20) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19) (e20);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) constr(e20) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19) (e20);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) constr(e20) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19) (e20);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) constr(e20) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19) (e20);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) constr(e20) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19) (e20);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) constr(e20) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19) (e20);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19).
Tactic Notation "execs0" constr(fn) ":" constr(l) "|" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) constr(e6) constr(e7) constr(e8) constr(e9) constr(e10) constr(e11) constr(e12) constr(e13) constr(e14) constr(e15) constr(e16) constr(e17) constr(e18) constr(e19) constr(e20) "->" ident(l') "|" constr(f1) constr(f2) constr(f3) constr(f4) constr(f5)
                                                                     constr(f6) constr(f7) constr(f8) constr(f9) constr(f10) 
                                                                     constr(f11) constr(f12) constr(f13) constr(f14) constr(f15) 
                                                                     constr(f16) constr(f17) constr(f18) constr(f19) constr(f20) := 
                     execs0 fn : l -> l';
                     fld l -> (e1) (e2) (e3) (e4) (e5) (e6) (e7) (e8) (e9) (e10) (e11) (e12) (e13) (e14) (e15) (e16) (e17) (e18) (e19) (e20);
                     fld l' -> (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) (f16) (f17) (f18) (f19) (f20).
