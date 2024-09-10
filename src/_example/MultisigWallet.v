
Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import UrsusQC.CommonQCEnvironment.
Require Import UrsusContractCreator.UrsusFieldUtils.
Require Import UrsusContractCreator.BaseContracts.EverContract.
(* Module MultisigWallet. *) 
#[translation = off]
#[quickchick = off]
#[language = solidity]
#[Contract = MultisigWalletContract]
Contract MultisigWallet ;
Sends To  ; 
Inherits EverBaseContract ;
Types 
Record Transaction := {
    Transaction_ι_id : uint64;
    Transaction_ι_confirmationsMask : uint32;
    Transaction_ι_signsRequired : uint8;
    Transaction_ι_signsReceived : uint8;
    Transaction_ι_creator : uint256;
    Transaction_ι_index : uint8;
    Transaction_ι_dest : address;
    Transaction_ι_value : uint128;
    Transaction_ι_sendFlags : uint16;
    Transaction_ι_payload : TvmCell;
    Transaction_ι_bounce : bool;
    Transaction_ι_stateInit : optional(TvmCell)
},
Record UpdateRequest := {
    UpdateRequest_ι_id : uint64;
    UpdateRequest_ι_index : uint8;
    UpdateRequest_ι_signs : uint8;
    UpdateRequest_ι_confirmationsMask : uint32;
    UpdateRequest_ι_creator : uint256;
    UpdateRequest_ι_codeHash : optional(uint256);
    UpdateRequest_ι_custodians : optional(uint256[]);
    UpdateRequest_ι_reqConfirms : optional(uint8);
    UpdateRequest_ι_lifetime : optional(uint32)
},
Record CustodianInfo := {
    CustodianInfo_ι_index : uint8;
    CustodianInfo_ι_pubkey : uint256
};
Constants 
Definition MAX_QUEUED_REQUESTS : uint8 := 5
Definition DEFAULT_LIFETIME : uint32 := 3600
Definition MIN_LIFETIME : uint32 := 10
Definition MAX_CUSTODIAN_COUNT : uint8 := 32
Definition MAX_CLEANUP_TXNS : uint256 := 40
Definition FLAG_PAY_FWD_FEE_FROM_BALANCE : uint8 := 1
Definition FLAG_IGNORE_ERRORS : uint8 := 2
Definition FLAG_SEND_ALL_REMAINING : uint8 := 128;
Record Contract := {
    m_ownerKey:uint256;
    m_requestsMask:uint256;
    m_transactions:mapping(uint64)((_ResolveRecord("Transaction")));
    m_custodians:mapping(uint256)(uint8);
    m_custodianCount:uint8;
    m_updateRequests:mapping(uint64)((_ResolveRecord("UpdateRequest")));
    m_updateRequestsMask:uint32;
    m_requiredVotes:uint8;
    m_defaultRequiredConfirmations:uint8;
    m_lifetime:uint32
}.
SetUrsusOptions.
Local Close Scope N_scope.
Local Close Scope Q_scope.
Local Close Scope nat_scope.
UseLocal Definition _ := [
    uint64;
    optional(TvmCell);
    optional(uint256);
    optional(uint256[]);
    optional(uint8);
    optional(uint32);
    uint8;
    TvmCell;
    uint256[];
    UpdateRequestLRecord[];
    CustodianInfoLRecord[];
    TransactionLRecord[];
    TransactionLRecord;
    uint32;
    bool;
    address;
    uint128;
    (uint8**uint128);
    uint256;
    optional((uint64**TransactionLRecord));
    optional(TransactionLRecord);
    TvmSlice;
    UpdateRequestLRecord;
    optional((uint64**UpdateRequestLRecord));
    optional(UpdateRequestLRecord);
    TvmBuilder;
   optional(TvmBuilder);
   optional((bool)**TvmSlice);
    (bool);
   optional(TvmBuilder);
   optional(((uint256[]))**TvmSlice);
    ((uint256[]));
   optional(TvmBuilder);
   optional(((mapping(uint256)(uint8))* (uint8* (uint256)))**TvmSlice);
    ((mapping(uint256)(uint8))* (uint8* (uint256)));
   optional(TvmBuilder);
   optional((uint8* (uint32))**TvmSlice);
    (uint8* (uint32))
].
Local Open Scope nat_scope.
Local Open Scope Q_scope.
Local Open Scope N_scope.
Local Open Scope ursus_scope_Transaction.
Local Open Scope ursus_scope_UpdateRequest.
Local Open Scope ursus_scope_CustodianInfo.
#[nonpayable, private]
Ursus Definition initialize_ (ownersOpt : optional(uint256[])) (reqConfirms : uint8) (lifetime : uint32): UExpression PhantomType true.
{
    :://  if (ownersOpt->hasValue()) then { ->/> } .
    {
        :://  var0 ownerCount: uint8 := {0} ;_|.
        :://  var0 owners: uint256[] := ownersOpt->get() ;_|.
        :://  if ((owners->length=={0})) then { ->> } .
        {
            :://  owners->push(tvm->pubkey()) |.
        }
        :://  m_ownerKey := owners[[{0}]].
        :://  var0 len: uint256 := owners->length ;_|.
        :://  m_custodians := {} (* DELETE *) .
        :://  for (var0 i: uint256 := {0} , ((i<len)&&(ownerCount<MAX_CUSTODIAN_COUNT)) , i ++ ) do { ->> }  .
        {
            :://  var0 key: uint256 := owners[[i]] ;_|.
            :://  if (! m_custodians->exists(key)) then { ->> }  |.
            {
                :://  m_custodians[[key]] := (++) (ownerCount) |.
            }
        }
        :://  m_custodianCount := ownerCount |.
    }
    :://  m_defaultRequiredConfirmations := math->min(m_custodianCount,reqConfirms).
    :://  m_requiredVotes := (m_custodianCount<={2}) ? m_custodianCount : (((m_custodianCount*{2})+{1})/{3}).
    :://  var0 minLifetime: uint32 := (uint32(m_custodianCount)*MIN_LIFETIME) ;_|.
    :://  if ((lifetime=={0})) then { ->> } else { ->> }  |.
    {
        :://  m_lifetime := DEFAULT_LIFETIME |.
    }
    {
        :://  m_lifetime := math->max(minLifetime,math->min(lifetime,uint32((block->timestamp&{0xFFFFFFFF})))) |.
    }
}
return.
Defined.
Sync.
#[nonpayable, public]
Ursus Definition constructor (owners : uint256[]) (reqConfirms : uint8) (lifetime : uint32): UExpression PhantomType true.
{
    :://  require(((owners->length>{0})&&(owners->length<=MAX_CUSTODIAN_COUNT)), {(117)}).
    :://  if ((msg->sender->value=={0})) then { ->/> } else { ->/> } .
    {
        :://  require((msg->pubkey()==tvm->pubkey()), {(100)}) |.
    }
    {
        :://  require((owners->length=={1}), {(126)}).
        :://  require((owners[[{0}]]==tvm->pubkey()), {(127)}) |.
    }
    :://  tvm->accept().
    :://  initialize_(some(owners), reqConfirms, lifetime) |.
}
return.
Defined.
Sync.
#[pure, private, returns=result_]
Ursus Definition getMaskValue_ (mask : uint256) (index__ : uint8): UExpression (uint8) true.
{
    :://  result_ := uint8!(((mask>>({8}*uint256(index__)))&{0xFF})) |.
}
return.
Defined.
Sync.
#[pure, private, returns=result_]
Ursus Definition incMaskValue_ (mask : uint256) (index__ : uint8): UExpression (uint256) false.
{
    :://  result_ := (mask+({1}<<({8}*uint256(index__)))) |.
}
return.
Defined.
Sync.
#[pure, private, returns=result_]
Ursus Definition decMaskValue_ (mask : uint256) (index__ : uint8): UExpression (uint256) false.
{
    :://  result_ := (mask-({1}<<({8}*uint256(index__)))) |.
}
return.
Defined.
Sync.
#[pure, private, returns=result_]
Ursus Definition checkBit_ (mask : uint32) (index__ : uint8): UExpression (bool) false.
{
    :://  result_ := ((mask&(uint32({1})<<index__))!={0}) |.
}
return.
Defined.
Sync.
#[pure, private, returns=result_]
Ursus Definition isConfirmed_ (mask : uint32) (custodianIndex : uint8): UExpression (bool) false.
{
    :://  result_ := checkBit_(mask,custodianIndex) |.
}
return.
Defined.
Sync.
#[pure, private, returns=result_]
Ursus Definition isSubmitted_ (mask : uint32) (custodianIndex : uint8): UExpression (bool) false.
{
    :://  result_ := checkBit_(mask,custodianIndex) |.
}
return.
Defined.
Sync.
#[pure, private, write=mask, returns=result_]
Ursus Definition setConfirmed_ (mask : uint32) (custodianIndex : uint8): UExpression (uint32) false.
{
    :://  mask |= (uint32({1})<<custodianIndex).
    :://  result_ := mask |.
}
return.
Defined.
Sync.
#[view, private, returns=result_]
Ursus Definition findCustodian_ (senderKey : uint256): UExpression (uint8) true.
{
    :://  var0 custodianIndex: optional(uint8) := m_custodians->fetch(senderKey) ;_|.
    :://  require(custodianIndex->hasValue(), {(100)}).
    :://  result_ := custodianIndex->get() |.
}
return.
Defined.
Sync.
#[pure, private, returns=result_]
Ursus Definition generateId_ : UExpression (uint64) false.
{
    :://  result_ := (uint64(block->timestamp)<<{32}) |.
}
return.
Defined.
Sync.
#[view, private, returns=result_]
Ursus Definition getExpirationBound_ : UExpression (uint64) false.
{
    :://  result_ := ((uint64(block->timestamp)-uint64(m_lifetime))<<{32}) |.
}
return.
Defined.
Sync.
#[pure, private, write=value__, returns=result_]
Ursus Definition getSendFlags_ (value__ : uint128) (allBalance : bool): UExpression (uint8 ** uint128) false.
{
    :://  var0 flags: uint8 := (FLAG_IGNORE_ERRORS\FLAG_PAY_FWD_FEE_FROM_BALANCE) ;_|.
    :://  if (allBalance) then { ->> } .
    {
        :://  flags := (FLAG_IGNORE_ERRORS\FLAG_SEND_ALL_REMAINING).
        :://  value__ := {0} |.
    }
    :://  result_ := [flags, value__] |.
}
return.
Defined.
Sync.
#[view, public, write=dest]
Ursus Definition sendTransaction (dest : address) (value__ : uint128) (bounce : bool) (flags : uint8) (payload : TvmCell): UExpression PhantomType true.
{
    :://  require((m_custodianCount=={1}), {(108)}).
    :://  require((msg->pubkey()==m_ownerKey), {(100)}).
    :://  tvm->accept().
    :://  tvm->transfer(dest, value__, bounce, (uint16(flags)\FLAG_IGNORE_ERRORS), payload) |.
}
return.
Defined.
Sync.
#[nonpayable, private, write=txn]
Ursus Definition confirmTransaction_ (txn : TransactionLRecord) (custodianIndex : uint8): UExpression PhantomType true.
{
    :://  if (((txn->Transaction_ι_signsReceived+{1})>=txn->Transaction_ι_signsRequired)) then { ->/> } else { ->> }  |.
    {
        :://  if (txn->Transaction_ι_stateInit->hasValue()) then { ->/> } else { ->> } .
        {
            :://  tvm->transfer(txn->Transaction_ι_dest, txn->Transaction_ι_value, txn->Transaction_ι_bounce, txn->Transaction_ι_sendFlags, txn->Transaction_ι_payload, txn->Transaction_ι_stateInit->get()) |.
        }
        {
            :://  tvm->transfer(txn->Transaction_ι_dest, txn->Transaction_ι_value, txn->Transaction_ι_bounce, txn->Transaction_ι_sendFlags, txn->Transaction_ι_payload) |.
        }
        :://  m_requestsMask := decMaskValue_(m_requestsMask,txn->Transaction_ι_index).
        :://  m_transactions[[txn->Transaction_ι_id]] := {} (* DELETE *)  |.
    }
    {
        :://  txn->Transaction_ι_confirmationsMask := setConfirmed_(txn->Transaction_ι_confirmationsMask,custodianIndex).
        :://  txn->Transaction_ι_signsReceived ++.
        :://  m_transactions[[txn->Transaction_ι_id]] := txn |.
    }
}
return.
Defined.
Sync.
#[nonpayable, private]
Ursus Definition removeExpiredTransactions_ : UExpression PhantomType true.
{
    :://  var0 marker: uint64 := getExpirationBound_() ;_|.
    :://  if (m_transactions->empty()) then { ->/> } .
    {
        :://  exit |.
    }
    :://  var0 (trId : uint64, txn : TransactionLRecord) := m_transactions->min()->get() ;_|.
    :://  var0 needCleanup: bool := (trId<=marker) ;_|.
    :://  if (needCleanup) then { ->/> }  |.
    {
        :://  tvm->accept().
        :://  var0 i: uint256 := {0} ;_|.
        :://  while ((needCleanup&&(i<MAX_CLEANUP_TXNS))) do { ->/> }.
        {
            :://  i ++.
            :://  m_requestsMask := decMaskValue_(m_requestsMask,txn->Transaction_ι_index).
            :://  m_transactions[[trId]] := {} (* DELETE *) .
            :://  var0 nextTxn: optional((uint64**TransactionLRecord)) := m_transactions->next(trId) ;_|.
            :://  if (nextTxn->hasValue()) then { ->/> } else { ->> }  |.
            {
                :://  [trId, txn] := nextTxn->get().
                :://  needCleanup := (trId<=marker) |.
            }
            {
                :://  needCleanup := {false} |.
            }
        }
        :://  tvm->commit() |.
    }
}
return.
Defined.
Sync.
#[nonpayable, public, returns=transId]
Ursus Definition submitTransaction (dest : address) (value__ : uint128) (bounce : bool) (allBalance : bool) (payload : TvmCell) (stateInit : optional(TvmCell)): UExpression (uint64) true.
{
    :://  var0 senderKey: uint256 := msg->pubkey() ;_|.
    :://  var0 index__: uint8 := findCustodian_(senderKey) ;_|.
    :://  removeExpiredTransactions_().
    :://  require((getMaskValue_(m_requestsMask,index__)<MAX_QUEUED_REQUESTS), {(113)}).
    :://  tvm->accept().
    :://  var0 (flags : uint8, realValue : uint128) := getSendFlags_(value__,allBalance) ;_|.
    :://  m_requestsMask := incMaskValue_(m_requestsMask,index__).
    :://  var0 trId: uint64 := generateId_() ;_|.
    :://  var0 txn: TransactionLRecord := (* Transaction *) [trId,{0},m_defaultRequiredConfirmations,{0},senderKey,index__,dest,realValue,uint16(flags),payload,bounce,stateInit] ;_|.
    :://  confirmTransaction_(txn, index__).
    :://  transId := trId |.
}
return.
Defined.
Sync.
#[nonpayable, public]
Ursus Definition confirmTransaction (transactionId : uint64): UExpression PhantomType true.
{
    :://  var0 index__: uint8 := findCustodian_(msg->pubkey()) ;_|.
    :://  removeExpiredTransactions_().
    :://  var0 txnOpt: optional(TransactionLRecord) := m_transactions->fetch(transactionId) ;_|.
    :://  require(txnOpt->hasValue(), {(102)}).
    :://  var0 txn: TransactionLRecord := txnOpt->get() ;_|.
    :://  require(! isConfirmed_(txn->Transaction_ι_confirmationsMask,index__), {(103)}).
    :://  tvm->accept().
    :://  confirmTransaction_(txn, index__) |.
}
return.
Defined.
Sync.
#[pure, external, returns=confirmed]
Ursus Definition isConfirmed (mask : uint32) (index__ : uint8): UExpression (bool) false.
{
    :://  confirmed := isConfirmed_(mask,index__) |.
}
return.
Defined.
Sync.
#[view, external, returns=trans]
Ursus Definition getTransaction (transactionId : uint64): UExpression (TransactionLRecord) true.
{
    :://  var0 txnOpt: optional(TransactionLRecord) := m_transactions->fetch(transactionId) ;_|.
    :://  require(txnOpt->hasValue(), {(102)}).
    :://  trans := txnOpt->get() |.
}
return.
Defined.
Sync.
#[view, external, returns=transactions]
Ursus Definition getTransactions : UExpression (TransactionLRecord[]) true.
{
    :://  var0 bound: uint64 := getExpirationBound_() ;_|.
    :://  for ( ['id__, 'txn] in m_transactions) do { ->> }   |.
    {
        :://  if ((id__>bound)) then { ->> }  |.
        {
            :://  transactions->push(txn) |.
        }
    }
}
return.
Defined.
Sync.
#[view, external, returns=custodians]
Ursus Definition getCustodians : UExpression (CustodianInfoLRecord[]) true.
{
    :://  for ( ['key, 'index__] in m_custodians) do { ->> }   |.
    {
        :://  custodians->push((* CustodianInfo *) [index__,key]) |.
    }
}
return.
Defined.
Sync.
#[view, external, returns=updates]
Ursus Definition getUpdateRequests : UExpression (UpdateRequestLRecord[]) true.
{
    :://  var0 bound: uint64 := getExpirationBound_() ;_|.
    :://  for ( ['updateId, 'req] in m_updateRequests) do { ->> }   |.
    {
        :://  if ((updateId>bound)) then { ->> }  |.
        {
            :://  updates->push(req) |.
        }
    }
}
return.
Defined.
Sync.
#[nonpayable, private]
Ursus Definition onCodeUpgrade2 (newOwners : uint256[]) (reqConfirms : uint8): UExpression PhantomType true.
{
    :://  tvm->resetStorage().
    :://  initialize_(some(newOwners), reqConfirms, {0}) |.
}
return.
Defined.
Sync.
#[nonpayable, private]
Ursus Definition onCodeUpgrade1 (data : TvmCell): UExpression PhantomType true.
{
    :://  tvm->resetStorage().
    :://  var0 owners: uint256[] ;_|.
    :://  var0 slice: TvmSlice := data->toSlice() ;_|.
    :://  var0 ownersAsArray: bool := slice->load(bool) ;_|.
    :://  if (ownersAsArray) then { ->/> } else { ->/> } .
    {
        :://  owners := slice->load((uint256[])) |.
    }
    {
        :://  [m_custodians, m_custodianCount, m_ownerKey] := slice->load((mapping(uint256)(uint8)),uint8,uint256) |.
    }
    :://  var0 (reqConfirms : uint8, lifetime : uint32) := slice->load(uint8,uint32) ;_|.
    :://  initialize_(some(owners), reqConfirms, lifetime) |.
}
return.
Defined.
Sync.
#[nonpayable, private]
Ursus Definition confirmUpdate_ (updateId : uint64) (custodianIndex : uint8): UExpression PhantomType false.
{
    :://  var0 request: UpdateRequestLRecord := m_updateRequests[[updateId]] ;_|.
    :://  request->UpdateRequest_ι_signs ++.
    :://  request->UpdateRequest_ι_confirmationsMask := setConfirmed_(request->UpdateRequest_ι_confirmationsMask,custodianIndex).
    :://  m_updateRequests[[updateId]] := request |.
}
return.
Defined.
Sync.
#[nonpayable, private]
Ursus Definition deleteUpdateRequest_ (updateId : uint64) (index__ : uint8): UExpression PhantomType false.
{
    :://  m_updateRequestsMask &= ~ (uint32({1})<<index__).
    :://  m_updateRequests[[updateId]] := {} (* DELETE *)  |.
}
return.
Defined.
Sync.
#[nonpayable, private]
Ursus Definition removeExpiredUpdateRequests_ : UExpression PhantomType true.
{
    :://  var0 marker: uint64 := getExpirationBound_() ;_|.
    :://  if (m_updateRequests->empty()) then { ->/> } .
    {
        :://  exit |.
    }
    :://  var0 (updateId : uint64, req : UpdateRequestLRecord) := m_updateRequests->min()->get() ;_|.
    :://  var0 needCleanup: bool := (updateId<=marker) ;_|.
    :://  if (needCleanup) then { ->/> }  |.
    {
        :://  tvm->accept().
        :://  while (needCleanup) do { ->/> }.
        {
            :://  deleteUpdateRequest_(updateId, req->UpdateRequest_ι_index).
            :://  var0 reqOpt: optional((uint64**UpdateRequestLRecord)) := m_updateRequests->next(updateId) ;_|.
            :://  if (reqOpt->hasValue()) then { ->/> } else { ->> }  |.
            {
                :://  [updateId, req] := reqOpt->get().
                :://  needCleanup := (updateId<=marker) |.
            }
            {
                :://  needCleanup := {false} |.
            }
        }
        :://  tvm->commit() |.
    }
}
return.
Defined.
Sync.
#[nonpayable, public, write=codeHash, returns=updateId]
Ursus Definition submitUpdate (codeHash : optional(uint256)) (owners : optional(uint256[])) (reqConfirms : optional(uint8)) (lifetime : optional(uint32)): UExpression (uint64) true.
{
    :://  var0 sender: uint256 := msg->pubkey() ;_|.
    :://  var0 index__: uint8 := findCustodian_(sender) ;_|.
    :://  if (owners->hasValue()) then { ->/> } .
    {
        :://  var0 newOwnerCount: uint256 := owners->get()->length ;_|.
        :://  require(((newOwnerCount>{0})&&(newOwnerCount<=MAX_CUSTODIAN_COUNT)), {(117)}) |.
    }
    :://  removeExpiredUpdateRequests_().
    :://  require(! isSubmitted_(m_updateRequestsMask,index__), {(113)}).
    :://  tvm->accept().
    :://  if (codeHash->hasValue()) then { ->/> } .
    {
        :://  if ((codeHash->get()==tvm->hash(tvm->code()))) then { ->> }  |.
        {
            :://  codeHash := {} (* DELETE *)  |.
        }
    }
    :://  m_updateRequestsMask := setConfirmed_(m_updateRequestsMask,index__).
    :://  updateId := generateId_().
    :://  m_updateRequests[[updateId]] := (* UpdateRequest *) [updateId,index__,{0},{0},sender,codeHash,owners,reqConfirms,lifetime].
    :://  confirmUpdate_(updateId, index__) |.
}
return.
Defined.
Sync.
#[nonpayable, public]
Ursus Definition confirmUpdate (updateId : uint64): UExpression PhantomType true.
{
    :://  var0 index__: uint8 := findCustodian_(msg->pubkey()) ;_|.
    :://  removeExpiredUpdateRequests_().
    :://  var0 requestOpt: optional(UpdateRequestLRecord) := m_updateRequests->fetch(updateId) ;_|.
    :://  require(requestOpt->hasValue(), {(115)}).
    :://  require(! isConfirmed_(requestOpt->get()->UpdateRequest_ι_confirmationsMask,index__), {(116)}).
    :://  tvm->accept().
    :://  confirmUpdate_(updateId, index__) |.
}
return.
Defined.
Sync.
#[nonpayable, public]
Ursus Definition executeUpdate (updateId : uint64) (code : optional(TvmCell)): UExpression PhantomType true.
{
    :://  require(m_custodians->exists(msg->pubkey()), {(100)}).
    :://  removeExpiredUpdateRequests_().
    :://  var0 requestOpt: optional(UpdateRequestLRecord) := m_updateRequests->fetch(updateId) ;_|.
    :://  require(requestOpt->hasValue(), {(115)}).
    :://  var0 request: UpdateRequestLRecord := requestOpt->get() ;_|.
    :://  if (request->UpdateRequest_ι_codeHash->hasValue()) then { ->/> } else { ->/> } .
    {
        :://  require(code->hasValue(), {(119)}).
        :://  require((tvm->hash(code->get())==request->UpdateRequest_ι_codeHash->get()), {(119)}) |.
    }
    {
        :://  require(! code->hasValue(), {(125)}) |.
    }
    :://  require((request->UpdateRequest_ι_signs>=m_requiredVotes), {(120)}).
    :://  tvm->accept().
    :://  deleteUpdateRequest_(updateId, request->UpdateRequest_ι_index).
    :://  tvm->commit().
    :://  if (request->UpdateRequest_ι_codeHash->hasValue()) then { ->/> } .
    {
        :://  var0 newcode: TvmCell := code->get() ;_|.
        :://  tvm->setcode(newcode).
        :://  tvm->setCurrentCode(newcode) |.
    }
    :://  var0 data: TvmBuilder ;_|.
    :://  if (request->UpdateRequest_ι_custodians->hasValue()) then { ->/> } else { ->/> } .
    {
        :://  data->store({true}, request->UpdateRequest_ι_custodians->get()) |.
    }
    {
        :://  data->store({false}, m_custodians, m_custodianCount, m_ownerKey) |.
    }
    :://  if (request->UpdateRequest_ι_reqConfirms->hasValue()) then { ->/> } else { ->/> } .
    {
        :://  data->store(request->UpdateRequest_ι_reqConfirms->get()) |.
    }
    {
        :://  data->store(m_defaultRequiredConfirmations) |.
    }
    :://  if (request->UpdateRequest_ι_lifetime->hasValue()) then { ->/> } else { ->/> } .
    {
        :://  data->store(request->UpdateRequest_ι_lifetime->get()) |.
    }
    {
        :://  data->store(m_lifetime) |.
    }
    :://  onCodeUpgrade1(data->toCell()) |.
}
return.
Defined.
Sync.
EndContract Implements .
(* End MultisigWallet. *)
GenerateLocalState 0 MultisigWallet.
GenerateLocalState 1 MultisigWallet.
Fail GenerateLocalState 2 MultisigWallet.
GenerateLocalState MultisigWallet.
