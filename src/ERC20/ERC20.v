Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import UrsusQC.CommonQCEnvironment.
Require Import UrsusContractCreator.UrsusFieldUtils.
Require Import UrsusContractCreator.BaseContracts.EverContract.

Interfaces.
SetUrsusOptions.

MakeInterface Class IERC20 :=
{ 
    #[nonpayable,external]
    transfer : { b & (address) -> (uint256) -> ( UExpression ((bool)) b) };
    #[nonpayable,external]
    approve : { b & (address) -> (uint256) -> ( UExpression ((bool)) b) };
    #[nonpayable,external]
    transferFrom : { b & (address) -> (address) -> (uint256) -> ( UExpression ((bool)) b) }
}.
EndInterfaces.

Set UrsusPrefixTactic "PrefixTestOptimized".

(* Module ERC20. *) 
#[translation = off]
#[quickchick = off]
#[language = solidity]
#[Contract = ERC20Contract]
Contract ERC20 ;
Sends To  ; 
Inherits EverBaseContract ;
Types 
Record SomeRecord := {
    field1 : uint8;
    field2 : uint256
} ;
Constants 
Definition SOME_CONST : uint8 := 5 ;

Record Contract := {
    totalSupply: uint256;
    balanceOf: mapping address uint256 ;
    allowance: mapping address (mapping address uint256);
    name: string;
    symbol: string;
    decimals: uint8;

    (* rrr: _ResolveRecord("SomeRecord") *)
}.

SetUrsusOptions.

UseLocal Definition _ := [
    address;
    uint256;
    bool;
    string;
    uint8
].

Local Open Scope nat_scope.
Local Open Scope Q_scope.
Local Open Scope N_scope.


#[nonpayable, public]
Ursus Definition constructor (name_ : string) (symbol_ : string) (decimals_ : uint8): UExpression PhantomType false.
{
    :://  name := name_.
    :://  symbol := symbol_.
    :://  decimals := decimals_ |.
}
return.
Defined.
Sync.

Print constructor.

#[nonpayable, external, returns=result_]
Ursus Definition transfer (recipient : address) (amount : uint256): UExpression (bool) false.
{
    :://  balanceOf[[msg->sender]] -= amount.
    :://  balanceOf[[recipient]] += amount.
    :://  result_ := {true} |.
}
return.
Defined.
Sync.

#[nonpayable, external, returns=result_]
Ursus Definition transfer' (recipient : address) (amount : uint256): UExpression (bool) true.
{
    ::// require (balanceOf[[msg->sender]] >= amount, {0}).
    ::// balanceOf[[msg->sender]] -= amount.
    ::// balanceOf[[recipient]] += amount.
    ::// result_ := {true} |.
}
return.
Defined.
Sync.


#[nonpayable, external, returns=result_]
Ursus Definition approve (spender : address) (amount : uint256): UExpression (bool) false.
{
    :://  allowance[[msg->sender]][[spender]] := amount.
    :://  result_ := {true} |.
}
return.
Defined.
Sync.


#[nonpayable, external, returns=result_]
Ursus Definition transferFrom (sender : address) (recipient : address) (amount : uint256): UExpression (bool) false.
{
    :://  allowance[[sender]][[msg->sender]] -= amount.
    :://  balanceOf[[sender]] -= amount.
    :://  balanceOf[[recipient]] += amount.
    :://  result_ := {true} |.
}
return.
Defined.
Sync.


#[nonpayable, internal]
Ursus Definition mint_ (to__ : address) (amount : uint256): UExpression PhantomType false.
{
    :://  balanceOf[[to__]] += amount.
    :://  totalSupply += amount |.
}
return.
Defined.
Sync.


#[nonpayable, internal]
Ursus Definition burn_ (from : address) (amount : uint256): UExpression PhantomType false.
{
    :://  balanceOf[[from]] -= amount.
    :://  totalSupply -= amount |.
}
return.
Defined.
Sync.


#[nonpayable, external]
Ursus Definition mint (to__ : address) (amount : uint256): UExpression PhantomType false.
{
    :://  mint_(to__, amount) |.
}
return.
Defined.
Sync.


#[nonpayable, external]
Ursus Definition burn (from : address) (amount : uint256): UExpression PhantomType false.
{
    :://  burn_(from, amount) |.
}
return.
Defined.
Sync.

EndContract Implements IERC20.

GenerateLocalState 0 ERC20.
Fail GenerateLocalState 1 ERC20.

GenerateLocalState ERC20.
