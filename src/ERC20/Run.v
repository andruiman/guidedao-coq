Require Import ERC20.ERC20.
Require Import UrsusEnvironment.Solidity.current.Environment.

Section Run.

SetUrsusOptions.

Set Dune Build Root "_build/default".
Elpi SetProjectRoot .

Set Coq Root "src".
Set Project Source Path "ERC20". 
Set Functions Path "Functions".
Set Execs Path "Execs".
Set Evals Path "Evals".
Set Tactics Path "Tactics". 
Set Run Script Path "build.sh".
Set Log Path "res.log".

Import ListNotations.
Local Open Scope list_scope.

Definition roots_eval : Datatypes.list string := [ "constructor" ; "transfer" ; "approve" ; "transferFrom" ; "mint" ; "burn" ].
Definition roots_exec : Datatypes.list string := [ "constructor" ; "transfer" ; "approve" ; "transferFrom" ; "mint" ; "burn" ] .

Elpi GenerateFunction ERC20 "Run" "Functions" .

End Run.
