(* autogenerated from github.com/mit-pdos/gokv/vrsm/replica *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.goose_dash_lang.std.
From Goose Require github_dot_com.mit_dash_pdos.gokv.grove__ffi.
From Goose Require github_dot_com.mit_dash_pdos.gokv.reconnectclient.
From Goose Require github_dot_com.mit_dash_pdos.gokv.urpc.
From Goose Require github_dot_com.mit_dash_pdos.gokv.vrsm.configservice.
From Goose Require github_dot_com.mit_dash_pdos.gokv.vrsm.e.
From Goose Require github_dot_com.tchajed.goose.machine.
From Goose Require github_dot_com.tchajed.marshal.
From Goose Require sync.

From Perennial.goose_lang Require Import ffi.grove_prelude.

(* 0_marshal.go *)

Definition Op: ty := slice.T byteT.

Definition ApplyAsBackupArgs := struct.decl [
  "epoch" :: uint64T;
  "index" :: uint64T;
  "op" :: slice.T byteT
].

Definition EncodeApplyAsBackupArgs: val :=
  rec: "EncodeApplyAsBackupArgs" "args" :=
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 ((#8 + #8) + (slice.len (struct.loadF ApplyAsBackupArgs "op" (![ptrT] "args"))))) in
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF ApplyAsBackupArgs "epoch" (![ptrT] "args")) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF ApplyAsBackupArgs "index" (![ptrT] "args")) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteBytes (![slice.T byteT] "enc") (struct.loadF ApplyAsBackupArgs "op" (![ptrT] "args")) in
    "enc" <-[slice.T byteT] "$a0";;
    return: (![slice.T byteT] "enc").

Definition DecodeApplyAsBackupArgs: val :=
  rec: "DecodeApplyAsBackupArgs" "enc_args" :=
    let: "enc" := ref_to (slice.T byteT) (![slice.T byteT] "enc_args") in
    let: "args" := ref_zero ptrT in
    let: "$a0" := struct.alloc ApplyAsBackupArgs (zero_val (struct.t ApplyAsBackupArgs)) in
    "args" <-[ptrT] "$a0";;
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc") in
    "enc" <-[slice.T byteT] "$a1";;
    struct.storeF ApplyAsBackupArgs "epoch" (![ptrT] "args") "$a0";;
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc") in
    "enc" <-[slice.T byteT] "$a1";;
    struct.storeF ApplyAsBackupArgs "index" (![ptrT] "args") "$a0";;
    let: "$a0" := ![slice.T byteT] "enc" in
    struct.storeF ApplyAsBackupArgs "op" (![ptrT] "args") "$a0";;
    return: (![ptrT] "args").

Definition SetStateArgs := struct.decl [
  "Epoch" :: uint64T;
  "NextIndex" :: uint64T;
  "CommittedNextIndex" :: uint64T;
  "State" :: slice.T byteT
].

Definition EncodeSetStateArgs: val :=
  rec: "EncodeSetStateArgs" "args" :=
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 (#8 + (slice.len (struct.loadF SetStateArgs "State" (![ptrT] "args"))))) in
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF SetStateArgs "Epoch" (![ptrT] "args")) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF SetStateArgs "NextIndex" (![ptrT] "args")) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF SetStateArgs "CommittedNextIndex" (![ptrT] "args")) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteBytes (![slice.T byteT] "enc") (struct.loadF SetStateArgs "State" (![ptrT] "args")) in
    "enc" <-[slice.T byteT] "$a0";;
    return: (![slice.T byteT] "enc").

Definition DecodeSetStateArgs: val :=
  rec: "DecodeSetStateArgs" "enc_args" :=
    let: "enc" := ref_to (slice.T byteT) (![slice.T byteT] "enc_args") in
    let: "args" := ref_zero ptrT in
    let: "$a0" := struct.alloc SetStateArgs (zero_val (struct.t SetStateArgs)) in
    "args" <-[ptrT] "$a0";;
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc") in
    "enc" <-[slice.T byteT] "$a1";;
    struct.storeF SetStateArgs "Epoch" (![ptrT] "args") "$a0";;
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc") in
    "enc" <-[slice.T byteT] "$a1";;
    struct.storeF SetStateArgs "NextIndex" (![ptrT] "args") "$a0";;
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc") in
    "enc" <-[slice.T byteT] "$a1";;
    struct.storeF SetStateArgs "CommittedNextIndex" (![ptrT] "args") "$a0";;
    let: "$a0" := ![slice.T byteT] "enc" in
    struct.storeF SetStateArgs "State" (![ptrT] "args") "$a0";;
    return: (![ptrT] "args").

Definition GetStateArgs := struct.decl [
  "Epoch" :: uint64T
].

Definition EncodeGetStateArgs: val :=
  rec: "EncodeGetStateArgs" "args" :=
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 #8) in
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF GetStateArgs "Epoch" (![ptrT] "args")) in
    "enc" <-[slice.T byteT] "$a0";;
    return: (![slice.T byteT] "enc").

Definition DecodeGetStateArgs: val :=
  rec: "DecodeGetStateArgs" "enc" :=
    let: "args" := ref_zero ptrT in
    let: "$a0" := struct.alloc GetStateArgs (zero_val (struct.t GetStateArgs)) in
    "args" <-[ptrT] "$a0";;
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc") in
    "$a1";;
    struct.storeF GetStateArgs "Epoch" (![ptrT] "args") "$a0";;
    return: (![ptrT] "args").

Definition GetStateReply := struct.decl [
  "Err" :: uint64T;
  "NextIndex" :: uint64T;
  "CommittedNextIndex" :: uint64T;
  "State" :: slice.T byteT
].

Definition EncodeGetStateReply: val :=
  rec: "EncodeGetStateReply" "reply" :=
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 (#8 + (slice.len (struct.loadF GetStateReply "State" (![ptrT] "reply"))))) in
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF GetStateReply "Err" (![ptrT] "reply")) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF GetStateReply "NextIndex" (![ptrT] "reply")) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF GetStateReply "CommittedNextIndex" (![ptrT] "reply")) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteBytes (![slice.T byteT] "enc") (struct.loadF GetStateReply "State" (![ptrT] "reply")) in
    "enc" <-[slice.T byteT] "$a0";;
    return: (![slice.T byteT] "enc").

Definition DecodeGetStateReply: val :=
  rec: "DecodeGetStateReply" "enc_reply" :=
    let: "enc" := ref_to (slice.T byteT) (![slice.T byteT] "enc_reply") in
    let: "reply" := ref_zero ptrT in
    let: "$a0" := struct.alloc GetStateReply (zero_val (struct.t GetStateReply)) in
    "reply" <-[ptrT] "$a0";;
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc") in
    "enc" <-[slice.T byteT] "$a1";;
    struct.storeF GetStateReply "Err" (![ptrT] "reply") "$a0";;
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc") in
    "enc" <-[slice.T byteT] "$a1";;
    struct.storeF GetStateReply "NextIndex" (![ptrT] "reply") "$a0";;
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc") in
    "enc" <-[slice.T byteT] "$a1";;
    struct.storeF GetStateReply "CommittedNextIndex" (![ptrT] "reply") "$a0";;
    let: "$a0" := ![slice.T byteT] "enc" in
    struct.storeF GetStateReply "State" (![ptrT] "reply") "$a0";;
    return: (![ptrT] "reply").

Definition BecomePrimaryArgs := struct.decl [
  "Epoch" :: uint64T;
  "Replicas" :: slice.T uint64T
].

Definition EncodeBecomePrimaryArgs: val :=
  rec: "EncodeBecomePrimaryArgs" "args" :=
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 ((#8 + #8) + (#8 * (slice.len (struct.loadF BecomePrimaryArgs "Replicas" (![ptrT] "args")))))) in
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF BecomePrimaryArgs "Epoch" (![ptrT] "args")) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (slice.len (struct.loadF BecomePrimaryArgs "Replicas" (![ptrT] "args"))) in
    "enc" <-[slice.T byteT] "$a0";;
    ForSlice uint64T <> "h" (struct.loadF BecomePrimaryArgs "Replicas" (![ptrT] "args"))
      (let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (![uint64T] "h") in
      "enc" <-[slice.T byteT] "$a0";;
      #());;
    return: (![slice.T byteT] "enc").

Definition DecodeBecomePrimaryArgs: val :=
  rec: "DecodeBecomePrimaryArgs" "enc_args" :=
    let: "enc" := ref_to (slice.T byteT) (![slice.T byteT] "enc_args") in
    let: "args" := ref_zero ptrT in
    let: "$a0" := struct.alloc BecomePrimaryArgs (zero_val (struct.t BecomePrimaryArgs)) in
    "args" <-[ptrT] "$a0";;
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc") in
    "enc" <-[slice.T byteT] "$a1";;
    struct.storeF BecomePrimaryArgs "Epoch" (![ptrT] "args") "$a0";;
    let: "replicasLen" := ref (zero_val uint64T) in
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc") in
    "enc" <-[slice.T byteT] "$a1";;
    "replicasLen" <-[uint64T] "$a0";;
    let: "$a0" := NewSlice uint64T (![uint64T] "replicasLen") in
    struct.storeF BecomePrimaryArgs "Replicas" (![ptrT] "args") "$a0";;
    ForSlice uint64T "i" <> (struct.loadF BecomePrimaryArgs "Replicas" (![ptrT] "args"))
      (let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc") in
      "enc" <-[slice.T byteT] "$a1";;
      SliceSet uint64T (struct.loadF BecomePrimaryArgs "Replicas" (![ptrT] "args")) (![intT] "i") "$a0";;
      #());;
    return: (![ptrT] "args").

Definition ApplyReply := struct.decl [
  "Err" :: uint64T;
  "Reply" :: slice.T byteT
].

Definition EncodeApplyReply: val :=
  rec: "EncodeApplyReply" "reply" :=
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 (#8 + (slice.len (struct.loadF ApplyReply "Reply" (![ptrT] "reply"))))) in
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF ApplyReply "Err" (![ptrT] "reply")) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteBytes (![slice.T byteT] "enc") (struct.loadF ApplyReply "Reply" (![ptrT] "reply")) in
    "enc" <-[slice.T byteT] "$a0";;
    return: (![slice.T byteT] "enc").

Definition DecodeApplyReply: val :=
  rec: "DecodeApplyReply" "enc_reply" :=
    let: "enc" := ref_to (slice.T byteT) (![slice.T byteT] "enc_reply") in
    let: "reply" := ref_zero ptrT in
    let: "$a0" := struct.alloc ApplyReply (zero_val (struct.t ApplyReply)) in
    "reply" <-[ptrT] "$a0";;
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc") in
    "enc" <-[slice.T byteT] "$a1";;
    struct.storeF ApplyReply "Err" (![ptrT] "reply") "$a0";;
    let: "$a0" := ![slice.T byteT] "enc" in
    struct.storeF ApplyReply "Reply" (![ptrT] "reply") "$a0";;
    return: (![ptrT] "reply").

Definition IncreaseCommitArgs: ty := uint64T.

Definition EncodeIncreaseCommitArgs: val :=
  rec: "EncodeIncreaseCommitArgs" "args" :=
    return: (marshal.WriteInt slice.nil (![uint64T] "args")).

Definition DecodeIncreaseCommitArgs: val :=
  rec: "DecodeIncreaseCommitArgs" "args" :=
    let: <> := ref_zero (slice.T byteT) in
    let: "a" := ref_zero uint64T in
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "args") in
    "$a1";;
    "a" <-[uint64T] "$a0";;
    return: (![uint64T] "a").

(* 1_statemachine.go *)

Definition StateMachine := struct.decl [
  "StartApply" :: ((slice.T byteT) -> ((slice.T byteT) * (unitT -> unitT)%ht))%ht;
  "ApplyReadonly" :: ((slice.T byteT) -> (uint64T * (slice.T byteT)))%ht;
  "SetStateAndUnseal" :: ((slice.T byteT) -> uint64T -> uint64T -> unitT)%ht;
  "GetStateAndSeal" :: (unitT -> (slice.T byteT))%ht
].

Definition SyncStateMachine := struct.decl [
  "Apply" :: ((slice.T byteT) -> (slice.T byteT))%ht;
  "ApplyReadonly" :: ((slice.T byteT) -> (uint64T * (slice.T byteT)))%ht;
  "SetStateAndUnseal" :: ((slice.T byteT) -> uint64T -> uint64T -> unitT)%ht;
  "GetStateAndSeal" :: (unitT -> (slice.T byteT))%ht
].

(* clerk.go *)

Definition Clerk := struct.decl [
  "cl" :: ptrT
].

Definition RPC_APPLYASBACKUP : expr := #0.

Definition RPC_SETSTATE : expr := #1.

Definition RPC_GETSTATE : expr := #2.

Definition RPC_BECOMEPRIMARY : expr := #3.

Definition RPC_PRIMARYAPPLY : expr := #4.

Definition RPC_ROPRIMARYAPPLY : expr := #6.

Definition RPC_INCREASECOMMIT : expr := #7.

Definition MakeClerk: val :=
  rec: "MakeClerk" "host" :=
    return: (struct.new Clerk [
       "cl" ::= reconnectclient.MakeReconnectingClient (![uint64T] "host")
     ]).

Definition Clerk__ApplyAsBackup: val :=
  rec: "Clerk__ApplyAsBackup" "ck" "args" :=
    let: "reply" := ref_zero ptrT in
    let: "$a0" := ref (zero_val (slice.T byteT)) in
    "reply" <-[ptrT] "$a0";;
    let: "err" := ref_zero uint64T in
    let: "$a0" := reconnectclient.ReconnectingClient__Call (struct.loadF Clerk "cl" (![ptrT] "ck")) RPC_APPLYASBACKUP (EncodeApplyAsBackupArgs (![ptrT] "args")) (![ptrT] "reply") #1000 in
    "err" <-[uint64T] "$a0";;
    (if: (![uint64T] "err") ≠ #0
    then return: (e.Timeout)
    else return: (e.DecodeError (![slice.T byteT] (![ptrT] "reply"))));;
    #().

Definition Clerk__SetState: val :=
  rec: "Clerk__SetState" "ck" "args" :=
    let: "reply" := ref_zero ptrT in
    let: "$a0" := ref (zero_val (slice.T byteT)) in
    "reply" <-[ptrT] "$a0";;
    let: "err" := ref_zero uint64T in
    let: "$a0" := reconnectclient.ReconnectingClient__Call (struct.loadF Clerk "cl" (![ptrT] "ck")) RPC_SETSTATE (EncodeSetStateArgs (![ptrT] "args")) (![ptrT] "reply") #10000 in
    "err" <-[uint64T] "$a0";;
    (if: (![uint64T] "err") ≠ #0
    then return: (e.Timeout)
    else return: (e.DecodeError (![slice.T byteT] (![ptrT] "reply"))));;
    #().

Definition Clerk__GetState: val :=
  rec: "Clerk__GetState" "ck" "args" :=
    let: "reply" := ref_zero ptrT in
    let: "$a0" := ref (zero_val (slice.T byteT)) in
    "reply" <-[ptrT] "$a0";;
    let: "err" := ref_zero uint64T in
    let: "$a0" := reconnectclient.ReconnectingClient__Call (struct.loadF Clerk "cl" (![ptrT] "ck")) RPC_GETSTATE (EncodeGetStateArgs (![ptrT] "args")) (![ptrT] "reply") #10000 in
    "err" <-[uint64T] "$a0";;
    (if: (![uint64T] "err") ≠ #0
    then
      return: (struct.new GetStateReply [
         "Err" ::= e.Timeout
       ])
    else return: (DecodeGetStateReply (![slice.T byteT] (![ptrT] "reply"))));;
    #().

Definition Clerk__BecomePrimary: val :=
  rec: "Clerk__BecomePrimary" "ck" "args" :=
    let: "reply" := ref_zero ptrT in
    let: "$a0" := ref (zero_val (slice.T byteT)) in
    "reply" <-[ptrT] "$a0";;
    let: "err" := ref_zero uint64T in
    let: "$a0" := reconnectclient.ReconnectingClient__Call (struct.loadF Clerk "cl" (![ptrT] "ck")) RPC_BECOMEPRIMARY (EncodeBecomePrimaryArgs (![ptrT] "args")) (![ptrT] "reply") #100 in
    "err" <-[uint64T] "$a0";;
    (if: (![uint64T] "err") ≠ #0
    then return: (e.Timeout)
    else return: (e.DecodeError (![slice.T byteT] (![ptrT] "reply"))));;
    #().

Definition Clerk__Apply: val :=
  rec: "Clerk__Apply" "ck" "op" :=
    let: "reply" := ref_zero ptrT in
    let: "$a0" := ref (zero_val (slice.T byteT)) in
    "reply" <-[ptrT] "$a0";;
    let: "err" := ref_zero uint64T in
    let: "$a0" := reconnectclient.ReconnectingClient__Call (struct.loadF Clerk "cl" (![ptrT] "ck")) RPC_PRIMARYAPPLY (![slice.T byteT] "op") (![ptrT] "reply") #5000 in
    "err" <-[uint64T] "$a0";;
    (if: (![uint64T] "err") = #0
    then
      let: "r" := ref_zero ptrT in
      let: "$a0" := DecodeApplyReply (![slice.T byteT] (![ptrT] "reply")) in
      "r" <-[ptrT] "$a0";;
      return: (struct.loadF ApplyReply "Err" (![ptrT] "r"), struct.loadF ApplyReply "Reply" (![ptrT] "r"))
    else return: (e.Timeout, slice.nil));;
    #().

Definition Clerk__ApplyRo: val :=
  rec: "Clerk__ApplyRo" "ck" "op" :=
    let: "reply" := ref_zero ptrT in
    let: "$a0" := ref (zero_val (slice.T byteT)) in
    "reply" <-[ptrT] "$a0";;
    let: "err" := ref_zero uint64T in
    let: "$a0" := reconnectclient.ReconnectingClient__Call (struct.loadF Clerk "cl" (![ptrT] "ck")) RPC_ROPRIMARYAPPLY (![slice.T byteT] "op") (![ptrT] "reply") #1000 in
    "err" <-[uint64T] "$a0";;
    (if: (![uint64T] "err") = #0
    then
      let: "r" := ref_zero ptrT in
      let: "$a0" := DecodeApplyReply (![slice.T byteT] (![ptrT] "reply")) in
      "r" <-[ptrT] "$a0";;
      return: (struct.loadF ApplyReply "Err" (![ptrT] "r"), struct.loadF ApplyReply "Reply" (![ptrT] "r"))
    else return: (e.Timeout, slice.nil));;
    #().

Definition Clerk__IncreaseCommitIndex: val :=
  rec: "Clerk__IncreaseCommitIndex" "ck" "n" :=
    return: (reconnectclient.ReconnectingClient__Call (struct.loadF Clerk "cl" (![ptrT] "ck")) RPC_INCREASECOMMIT (EncodeIncreaseCommitArgs (![uint64T] "n")) (ref (zero_val (slice.T byteT))) #100).

(* server.go *)

Definition Server := struct.decl [
  "mu" :: ptrT;
  "epoch" :: uint64T;
  "sealed" :: boolT;
  "sm" :: ptrT;
  "nextIndex" :: uint64T;
  "canBecomePrimary" :: boolT;
  "isPrimary" :: boolT;
  "clerks" :: slice.T (slice.T ptrT);
  "isPrimary_cond" :: ptrT;
  "opAppliedConds" :: mapT ptrT;
  "leaseExpiration" :: uint64T;
  "leaseValid" :: boolT;
  "committedNextIndex" :: uint64T;
  "committedNextIndex_cond" :: ptrT;
  "confCk" :: ptrT
].

(* Applies the RO op immediately, but then waits for it to be committed before
   replying to client. *)
Definition Server__ApplyRoWaitForCommit: val :=
  rec: "Server__ApplyRoWaitForCommit" "s" "op" :=
    let: "reply" := ref_zero ptrT in
    let: "$a0" := struct.alloc ApplyReply (zero_val (struct.t ApplyReply)) in
    "reply" <-[ptrT] "$a0";;
    let: "$a0" := slice.nil in
    struct.storeF ApplyReply "Reply" (![ptrT] "reply") "$a0";;
    let: "$a0" := e.None in
    struct.storeF ApplyReply "Err" (![ptrT] "reply") "$a0";;
    sync.Mutex__Lock (struct.loadF Server "mu" (![ptrT] "s"));;
    (if: (~ (struct.loadF Server "leaseValid" (![ptrT] "s")))
    then
      sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "s"));;
      log.Printf #(str"Lease invalid");;
      let: "$a0" := e.LeaseExpired in
      struct.storeF ApplyReply "Err" (![ptrT] "reply") "$a0";;
      return: (![ptrT] "reply")
    else #());;
    (if: ((machine.RandomUint64 #()) `rem` #10000) = #0
    then
      log.Printf #(str"Server nextIndex=%!!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)d(MISSING) commitIndex=%!!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)d(MISSING)") (struct.loadF Server "nextIndex" (![ptrT] "s")) (struct.loadF Server "committedNextIndex" (![ptrT] "s"));;
      #()
    else #());;
    let: "lastModifiedIndex" := ref (zero_val uint64T) in
    let: ("$a0", "$a1") := (struct.loadF StateMachine "ApplyReadonly" (struct.loadF Server "sm" (![ptrT] "s"))) (![slice.T byteT] "op") in
    struct.storeF ApplyReply "Reply" (![ptrT] "reply") "$a1";;
    "lastModifiedIndex" <-[uint64T] "$a0";;
    let: "epoch" := ref_zero uint64T in
    let: "$a0" := struct.loadF Server "epoch" (![ptrT] "s") in
    "epoch" <-[uint64T] "$a0";;
    let: "h" := ref_zero uint64T in
    let: <> := ref_zero uint64T in
    let: ("$a0", "$a1") := grove__ffi.GetTimeRange #() in
    "h" <-[uint64T] "$a1";;
    "$a0";;
    (if: (struct.loadF Server "leaseExpiration" (![ptrT] "s")) ≤ (![uint64T] "h")
    then
      sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "s"));;
      log.Printf #(str"Lease expired because %!!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)d(MISSING) < %!!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)d(MISSING)") (struct.loadF Server "leaseExpiration" (![ptrT] "s")) (![uint64T] "h");;
      let: "$a0" := e.LeaseExpired in
      struct.storeF ApplyReply "Err" (![ptrT] "reply") "$a0";;
      return: (![ptrT] "reply")
    else #());;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: (struct.loadF Server "epoch" (![ptrT] "s")) ≠ (![uint64T] "epoch")
      then
        let: "$a0" := e.Stale in
        struct.storeF ApplyReply "Err" (![ptrT] "reply") "$a0";;
        Break
      else
        (if: (![uint64T] "lastModifiedIndex") ≤ (struct.loadF Server "committedNextIndex" (![ptrT] "s"))
        then
          let: "$a0" := e.None in
          struct.storeF ApplyReply "Err" (![ptrT] "reply") "$a0";;
          Break
        else
          sync.Cond__Wait (struct.loadF Server "committedNextIndex_cond" (![ptrT] "s"));;
          Continue);;
        #());;
      #()).

(* precondition:
   is_epoch_lb epoch ∗ committed_by epoch log ∗ is_pb_log_lb log *)
Definition Server__IncreaseCommitIndex: val :=
  rec: "Server__IncreaseCommitIndex" "s" "newCommittedNextIndex" :=
    sync.Mutex__Lock (struct.loadF Server "mu" (![ptrT] "s"));;
    (if: ((![uint64T] "newCommittedNextIndex") > (struct.loadF Server "committedNextIndex" (![ptrT] "s"))) && ((![uint64T] "newCommittedNextIndex") ≤ (struct.loadF Server "nextIndex" (![ptrT] "s")))
    then
      let: "$a0" := ![uint64T] "newCommittedNextIndex" in
      struct.storeF Server "committedNextIndex" (![ptrT] "s") "$a0";;
      sync.Cond__Broadcast (struct.loadF Server "committedNextIndex_cond" (![ptrT] "s"));;
      #()
    else #());;
    sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "s"));;
    #().

(* called on the primary server to apply a new operation. *)
Definition Server__Apply: val :=
  rec: "Server__Apply" "s" "op" :=
    let: "reply" := ref_zero ptrT in
    let: "$a0" := struct.alloc ApplyReply (zero_val (struct.t ApplyReply)) in
    "reply" <-[ptrT] "$a0";;
    let: "$a0" := slice.nil in
    struct.storeF ApplyReply "Reply" (![ptrT] "reply") "$a0";;
    sync.Mutex__Lock (struct.loadF Server "mu" (![ptrT] "s"));;
    (if: (~ (struct.loadF Server "isPrimary" (![ptrT] "s")))
    then
      sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "s"));;
      let: "$a0" := e.Stale in
      struct.storeF ApplyReply "Err" (![ptrT] "reply") "$a0";;
      return: (![ptrT] "reply")
    else #());;
    (if: struct.loadF Server "sealed" (![ptrT] "s")
    then
      sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "s"));;
      let: "$a0" := e.Stale in
      struct.storeF ApplyReply "Err" (![ptrT] "reply") "$a0";;
      return: (![ptrT] "reply")
    else #());;
    let: "waitForDurable" := ref_zero (arrowT unitT unitT) in
    let: "ret" := ref_zero (slice.T byteT) in
    let: ("$a0", "$a1") := (struct.loadF StateMachine "StartApply" (struct.loadF Server "sm" (![ptrT] "s"))) (![slice.T byteT] "op") in
    "waitForDurable" <-[(arrowT unitT unitT)] "$a1";;
    "ret" <-[slice.T byteT] "$a0";;
    let: "$a0" := ![slice.T byteT] "ret" in
    struct.storeF ApplyReply "Reply" (![ptrT] "reply") "$a0";;
    let: "opIndex" := ref_zero uint64T in
    let: "$a0" := struct.loadF Server "nextIndex" (![ptrT] "s") in
    "opIndex" <-[uint64T] "$a0";;
    let: "$a0" := std.SumAssumeNoOverflow (struct.loadF Server "nextIndex" (![ptrT] "s")) #1 in
    struct.storeF Server "nextIndex" (![ptrT] "s") "$a0";;
    let: "nextIndex" := ref_zero uint64T in
    let: "$a0" := struct.loadF Server "nextIndex" (![ptrT] "s") in
    "nextIndex" <-[uint64T] "$a0";;
    let: "epoch" := ref_zero uint64T in
    let: "$a0" := struct.loadF Server "epoch" (![ptrT] "s") in
    "epoch" <-[uint64T] "$a0";;
    let: "clerks" := ref_zero (slice.T (slice.T ptrT)) in
    let: "$a0" := struct.loadF Server "clerks" (![ptrT] "s") in
    "clerks" <-[slice.T (slice.T ptrT)] "$a0";;
    sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "s"));;
    let: "wg" := ref_zero ptrT in
    let: "$a0" := struct.alloc sync.WaitGroup (zero_val (struct.t sync.WaitGroup)) in
    "wg" <-[ptrT] "$a0";;
    let: "args" := ref_zero ptrT in
    let: "$a0" := struct.new ApplyAsBackupArgs [
      "epoch" ::= ![uint64T] "epoch";
      "index" ::= ![uint64T] "opIndex";
      "op" ::= ![slice.T byteT] "op"
    ] in
    "args" <-[ptrT] "$a0";;
    let: "clerks_inner" := ref_zero (slice.T ptrT) in
    let: "$a0" := SliceGet (slice.T ptrT) (![slice.T (slice.T ptrT)] "clerks") ((machine.RandomUint64 #()) `rem` (slice.len (![slice.T (slice.T ptrT)] "clerks"))) in
    "clerks_inner" <-[slice.T ptrT] "$a0";;
    let: "errs" := ref_zero (slice.T uint64T) in
    let: "$a0" := NewSlice uint64T (slice.len (![slice.T ptrT] "clerks_inner")) in
    "errs" <-[slice.T uint64T] "$a0";;
    ForSlice ptrT "i" "clerk" (![slice.T ptrT] "clerks_inner")
      (let: "clerk" := ref_zero ptrT in
      let: "$a0" := ![ptrT] "clerk" in
      "clerk" <-[ptrT] "$a0";;
      let: "i" := ref_zero intT in
      let: "$a0" := ![intT] "i" in
      "i" <-[intT] "$a0";;
      sync.WaitGroup__Add (![ptrT] "wg") #1;;
      Fork ((for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
              let: "err" := ref_zero uint64T in
              let: "$a0" := Clerk__ApplyAsBackup (![ptrT] "clerk") (![ptrT] "args") in
              "err" <-[uint64T] "$a0";;
              (if: ((![uint64T] "err") = e.OutOfOrder) || ((![uint64T] "err") = e.Timeout)
              then Continue
              else
                let: "$a0" := ![uint64T] "err" in
                SliceSet uint64T (![slice.T uint64T] "errs") (![intT] "i") "$a0";;
                Break);;
              #()));;
      #());;
    sync.WaitGroup__Wait (![ptrT] "wg");;
    (![(arrowT unitT unitT)] "waitForDurable") #();;
    let: "err" := ref_to uint64T e.None in
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, (![uint64T] "i") < (slice.len (![slice.T ptrT] "clerks_inner"))); (λ: <>, Skip) := λ: <>,
      let: "err2" := ref_zero uint64T in
      let: "$a0" := SliceGet uint64T (![slice.T uint64T] "errs") (![uint64T] "i") in
      "err2" <-[uint64T] "$a0";;
      (if: (![uint64T] "err2") ≠ e.None
      then
        let: "$a0" := ![uint64T] "err2" in
        "err" <-[uint64T] "$a0";;
        #()
      else #());;
      "i" <-[uint64T] ((![uint64T] "i") + #1);;
      #()).

Definition Server__leaseRenewalThread: val :=
  rec: "Server__leaseRenewalThread" "s" :=
    let: "latestEpoch" := ref (zero_val uint64T) in
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "leaseExpiration" := ref_zero uint64T in
      let: "leaseErr" := ref_zero uint64T in
      let: ("$a0", "$a1") := configservice.Clerk__GetLease (struct.loadF Server "confCk" (![ptrT] "s")) (![uint64T] "latestEpoch") in
      "leaseExpiration" <-[uint64T] "$a1";;
      "leaseErr" <-[uint64T] "$a0";;
      sync.Mutex__Lock (struct.loadF Server "mu" (![ptrT] "s"));;
      (if: ((struct.loadF Server "epoch" (![ptrT] "s")) = (![uint64T] "latestEpoch")) && ((![uint64T] "leaseErr") = e.None)
      then
        let: "$a0" := ![uint64T] "leaseExpiration" in
        struct.storeF Server "leaseExpiration" (![ptrT] "s") "$a0";;
        let: "$a0" := #true in
        struct.storeF Server "leaseValid" (![ptrT] "s") "$a0";;
        sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "s"));;
        machine.Sleep (#250 * #1000000);;
        #()
      else
        (if: (![uint64T] "latestEpoch") ≠ (struct.loadF Server "epoch" (![ptrT] "s"))
        then
          let: "$a0" := struct.loadF Server "epoch" (![ptrT] "s") in
          "latestEpoch" <-[uint64T] "$a0";;
          sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "s"));;
          #()
        else
          sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "s"));;
          machine.Sleep (#50 * #1000000);;
          #());;
        #());;
      #()).

Definition Server__sendIncreaseCommitThread: val :=
  rec: "Server__sendIncreaseCommitThread" "s" :=
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      sync.Mutex__Lock (struct.loadF Server "mu" (![ptrT] "s"));;
      (for: (λ: <>, (~ (struct.loadF Server "isPrimary" (![ptrT] "s"))) || ((slice.len (SliceGet (slice.T ptrT) (struct.loadF Server "clerks" (![ptrT] "s")) #0)) = #0)); (λ: <>, Skip) := λ: <>,
        sync.Cond__Wait (struct.loadF Server "isPrimary_cond" (![ptrT] "s"));;
        #())).

(* requires that we've already at least entered this epoch
   returns true iff stale *)
Definition Server__isEpochStale: val :=
  rec: "Server__isEpochStale" "s" "epoch" :=
    return: ((struct.loadF Server "epoch" (![ptrT] "s")) ≠ (![uint64T] "epoch")).

(* called on backup servers to apply an operation so it is replicated and
   can be considered committed by primary. *)
Definition Server__ApplyAsBackup: val :=
  rec: "Server__ApplyAsBackup" "s" "args" :=
    sync.Mutex__Lock (struct.loadF Server "mu" (![ptrT] "s"));;
    (for: (λ: <>, (((struct.loadF ApplyAsBackupArgs "index" (![ptrT] "args")) > (struct.loadF Server "nextIndex" (![ptrT] "s"))) && ((struct.loadF Server "epoch" (![ptrT] "s")) = (struct.loadF ApplyAsBackupArgs "epoch" (![ptrT] "args")))) && (~ (struct.loadF Server "sealed" (![ptrT] "s")))); (λ: <>, Skip) := λ: <>,
      let: "ok" := ref_zero boolT in
      let: "cond" := ref_zero ptrT in
      let: ("$a0", "$a1") := Fst (MapGet (struct.loadF Server "opAppliedConds" (![ptrT] "s")) (struct.loadF ApplyAsBackupArgs "index" (![ptrT] "args"))) in
      "ok" <-[boolT] "$a1";;
      "cond" <-[ptrT] "$a0";;
      (if: (~ (![boolT] "ok"))
      then
        let: "cond" := ref_zero ptrT in
        let: "$a0" := sync.NewCond (struct.loadF Server "mu" (![ptrT] "s")) in
        "cond" <-[ptrT] "$a0";;
        let: "$a0" := ![ptrT] "cond" in
        MapInsert (struct.loadF Server "opAppliedConds" (![ptrT] "s")) (struct.loadF ApplyAsBackupArgs "index" (![ptrT] "args")) "$a0";;
        #()
      else
        sync.Cond__Wait (![ptrT] "cond");;
        #());;
      #()).

Definition Server__SetState: val :=
  rec: "Server__SetState" "s" "args" :=
    sync.Mutex__Lock (struct.loadF Server "mu" (![ptrT] "s"));;
    (if: (struct.loadF Server "epoch" (![ptrT] "s")) > (struct.loadF SetStateArgs "Epoch" (![ptrT] "args"))
    then
      sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "s"));;
      return: (e.Stale)
    else
      (if: (struct.loadF Server "epoch" (![ptrT] "s")) = (struct.loadF SetStateArgs "Epoch" (![ptrT] "args"))
      then
        sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "s"));;
        return: (e.None)
      else
        log.Print #(str"Entered new epoch");;
        let: "$a0" := #false in
        struct.storeF Server "isPrimary" (![ptrT] "s") "$a0";;
        let: "$a0" := #true in
        struct.storeF Server "canBecomePrimary" (![ptrT] "s") "$a0";;
        let: "$a0" := struct.loadF SetStateArgs "Epoch" (![ptrT] "args") in
        struct.storeF Server "epoch" (![ptrT] "s") "$a0";;
        let: "$a0" := #false in
        struct.storeF Server "leaseValid" (![ptrT] "s") "$a0";;
        let: "$a0" := #false in
        struct.storeF Server "sealed" (![ptrT] "s") "$a0";;
        let: "$a0" := struct.loadF SetStateArgs "NextIndex" (![ptrT] "args") in
        struct.storeF Server "nextIndex" (![ptrT] "s") "$a0";;
        (struct.loadF StateMachine "SetStateAndUnseal" (struct.loadF Server "sm" (![ptrT] "s"))) (struct.loadF SetStateArgs "State" (![ptrT] "args")) (struct.loadF SetStateArgs "NextIndex" (![ptrT] "args")) (struct.loadF SetStateArgs "Epoch" (![ptrT] "args"));;
        MapIter (struct.loadF Server "opAppliedConds" (![ptrT] "s")) (λ: <> "cond",
          sync.Cond__Signal (![ptrT] "cond");;
          #());;
        sync.Cond__Broadcast (struct.loadF Server "committedNextIndex_cond" (![ptrT] "s"));;
        let: "$a0" := NewMap uint64T ptrT #() in
        struct.storeF Server "opAppliedConds" (![ptrT] "s") "$a0";;
        sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "s"));;
        Server__IncreaseCommitIndex (![ptrT] "s") (struct.loadF SetStateArgs "CommittedNextIndex" (![ptrT] "args"));;
        return: (e.None));;
      #());;
    #().

(* XXX: probably should rename to GetStateAndSeal *)
Definition Server__GetState: val :=
  rec: "Server__GetState" "s" "args" :=
    sync.Mutex__Lock (struct.loadF Server "mu" (![ptrT] "s"));;
    (if: (struct.loadF GetStateArgs "Epoch" (![ptrT] "args")) < (struct.loadF Server "epoch" (![ptrT] "s"))
    then
      sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "s"));;
      return: (struct.new GetStateReply [
         "Err" ::= e.Stale;
         "State" ::= slice.nil
       ])
    else #());;
    let: "$a0" := #true in
    struct.storeF Server "sealed" (![ptrT] "s") "$a0";;
    let: "ret" := ref_zero (slice.T byteT) in
    let: "$a0" := (struct.loadF StateMachine "GetStateAndSeal" (struct.loadF Server "sm" (![ptrT] "s"))) #() in
    "ret" <-[slice.T byteT] "$a0";;
    let: "nextIndex" := ref_zero uint64T in
    let: "$a0" := struct.loadF Server "nextIndex" (![ptrT] "s") in
    "nextIndex" <-[uint64T] "$a0";;
    let: "committedNextIndex" := ref_zero uint64T in
    let: "$a0" := struct.loadF Server "committedNextIndex" (![ptrT] "s") in
    "committedNextIndex" <-[uint64T] "$a0";;
    MapIter (struct.loadF Server "opAppliedConds" (![ptrT] "s")) (λ: <> "cond",
      sync.Cond__Signal (![ptrT] "cond");;
      #());;
    let: "$a0" := NewMap uint64T ptrT #() in
    struct.storeF Server "opAppliedConds" (![ptrT] "s") "$a0";;
    sync.Cond__Broadcast (struct.loadF Server "committedNextIndex_cond" (![ptrT] "s"));;
    sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "s"));;
    return: (struct.new GetStateReply [
       "Err" ::= e.None;
       "State" ::= ![slice.T byteT] "ret";
       "NextIndex" ::= ![uint64T] "nextIndex";
       "CommittedNextIndex" ::= ![uint64T] "committedNextIndex"
     ]).

Definition Server__BecomePrimary: val :=
  rec: "Server__BecomePrimary" "s" "args" :=
    sync.Mutex__Lock (struct.loadF Server "mu" (![ptrT] "s"));;
    (if: ((struct.loadF BecomePrimaryArgs "Epoch" (![ptrT] "args")) ≠ (struct.loadF Server "epoch" (![ptrT] "s"))) || (~ (struct.loadF Server "canBecomePrimary" (![ptrT] "s")))
    then
      log.Printf #(str"Wrong epoch in BecomePrimary request (in %!d(MISSING), got %!d(MISSING))") (struct.loadF Server "epoch" (![ptrT] "s")) (struct.loadF BecomePrimaryArgs "Epoch" (![ptrT] "args"));;
      sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "s"));;
      return: (e.Stale)
    else #());;
    log.Println #(str"Became Primary");;
    let: "$a0" := #true in
    struct.storeF Server "isPrimary" (![ptrT] "s") "$a0";;
    sync.Cond__Signal (struct.loadF Server "isPrimary_cond" (![ptrT] "s"));;
    let: "$a0" := #false in
    struct.storeF Server "canBecomePrimary" (![ptrT] "s") "$a0";;
    let: "numClerks" := ref_zero uint64T in
    let: "$a0" := #32 in
    "numClerks" <-[uint64T] "$a0";;
    let: "$a0" := NewSlice (slice.T ptrT) (![uint64T] "numClerks") in
    struct.storeF Server "clerks" (![ptrT] "s") "$a0";;
    let: "j" := ref_to uint64T #0 in
    (for: (λ: <>, (![uint64T] "j") < (![uint64T] "numClerks")); (λ: <>, Skip) := λ: <>,
      let: "clerks" := ref_zero (slice.T ptrT) in
      let: "$a0" := NewSlice ptrT ((slice.len (struct.loadF BecomePrimaryArgs "Replicas" (![ptrT] "args"))) - #1) in
      "clerks" <-[slice.T ptrT] "$a0";;
      let: "i" := ref_to uint64T #0 in
      (for: (λ: <>, (![uint64T] "i") < (slice.len (![slice.T ptrT] "clerks"))); (λ: <>, Skip) := λ: <>,
        let: "$a0" := MakeClerk (SliceGet uint64T (struct.loadF BecomePrimaryArgs "Replicas" (![ptrT] "args")) ((![uint64T] "i") + #1)) in
        SliceSet ptrT (![slice.T ptrT] "clerks") (![uint64T] "i") "$a0";;
        "i" <-[uint64T] ((![uint64T] "i") + #1);;
        #())).

Definition MakeServer: val :=
  rec: "MakeServer" "sm" "confHosts" "nextIndex" "epoch" "sealed" :=
    let: "s" := ref_zero ptrT in
    let: "$a0" := struct.alloc Server (zero_val (struct.t Server)) in
    "s" <-[ptrT] "$a0";;
    let: "$a0" := struct.alloc sync.Mutex (zero_val (struct.t sync.Mutex)) in
    struct.storeF Server "mu" (![ptrT] "s") "$a0";;
    let: "$a0" := ![uint64T] "epoch" in
    struct.storeF Server "epoch" (![ptrT] "s") "$a0";;
    let: "$a0" := ![boolT] "sealed" in
    struct.storeF Server "sealed" (![ptrT] "s") "$a0";;
    let: "$a0" := ![ptrT] "sm" in
    struct.storeF Server "sm" (![ptrT] "s") "$a0";;
    let: "$a0" := ![uint64T] "nextIndex" in
    struct.storeF Server "nextIndex" (![ptrT] "s") "$a0";;
    let: "$a0" := #false in
    struct.storeF Server "isPrimary" (![ptrT] "s") "$a0";;
    let: "$a0" := #false in
    struct.storeF Server "canBecomePrimary" (![ptrT] "s") "$a0";;
    let: "$a0" := #false in
    struct.storeF Server "leaseValid" (![ptrT] "s") "$a0";;
    let: "$a0" := #false in
    struct.storeF Server "canBecomePrimary" (![ptrT] "s") "$a0";;
    let: "$a0" := NewMap uint64T ptrT #() in
    struct.storeF Server "opAppliedConds" (![ptrT] "s") "$a0";;
    let: "$a0" := configservice.MakeClerk (![slice.T uint64T] "confHosts") in
    struct.storeF Server "confCk" (![ptrT] "s") "$a0";;
    let: "$a0" := sync.NewCond (struct.loadF Server "mu" (![ptrT] "s")) in
    struct.storeF Server "committedNextIndex_cond" (![ptrT] "s") "$a0";;
    let: "$a0" := sync.NewCond (struct.loadF Server "mu" (![ptrT] "s")) in
    struct.storeF Server "isPrimary_cond" (![ptrT] "s") "$a0";;
    return: (![ptrT] "s").

Definition Server__Serve: val :=
  rec: "Server__Serve" "s" "me" :=
    let: "handlers" := ref_zero (mapT (arrowT unitT unitT)) in
    let: "$a0" := NewMap uint64T ((slice.T byteT) -> ptrT -> unitT)%!h(MISSING)t #() in
    "handlers" <-[mapT (arrowT unitT unitT)] "$a0";;
    let: "$a0" := (λ: "args" "reply",
      let: "$a0" := e.EncodeError (Server__ApplyAsBackup (![ptrT] "s") (DecodeApplyAsBackupArgs (![slice.T byteT] "args"))) in
      (![ptrT] "reply") <-[slice.T byteT] "$a0";;
      #()
      ) in
    MapInsert (![mapT (arrowT unitT unitT)] "handlers") RPC_APPLYASBACKUP "$a0";;
    let: "$a0" := (λ: "args" "reply",
      let: "$a0" := e.EncodeError (Server__SetState (![ptrT] "s") (DecodeSetStateArgs (![slice.T byteT] "args"))) in
      (![ptrT] "reply") <-[slice.T byteT] "$a0";;
      #()
      ) in
    MapInsert (![mapT (arrowT unitT unitT)] "handlers") RPC_SETSTATE "$a0";;
    let: "$a0" := (λ: "args" "reply",
      let: "$a0" := EncodeGetStateReply (Server__GetState (![ptrT] "s") (DecodeGetStateArgs (![slice.T byteT] "args"))) in
      (![ptrT] "reply") <-[slice.T byteT] "$a0";;
      #()
      ) in
    MapInsert (![mapT (arrowT unitT unitT)] "handlers") RPC_GETSTATE "$a0";;
    let: "$a0" := (λ: "args" "reply",
      let: "$a0" := e.EncodeError (Server__BecomePrimary (![ptrT] "s") (DecodeBecomePrimaryArgs (![slice.T byteT] "args"))) in
      (![ptrT] "reply") <-[slice.T byteT] "$a0";;
      #()
      ) in
    MapInsert (![mapT (arrowT unitT unitT)] "handlers") RPC_BECOMEPRIMARY "$a0";;
    let: "$a0" := (λ: "args" "reply",
      let: "$a0" := EncodeApplyReply (Server__Apply (![ptrT] "s") (![slice.T byteT] "args")) in
      (![ptrT] "reply") <-[slice.T byteT] "$a0";;
      #()
      ) in
    MapInsert (![mapT (arrowT unitT unitT)] "handlers") RPC_PRIMARYAPPLY "$a0";;
    let: "$a0" := (λ: "args" "reply",
      let: "$a0" := EncodeApplyReply (Server__ApplyRoWaitForCommit (![ptrT] "s") (![slice.T byteT] "args")) in
      (![ptrT] "reply") <-[slice.T byteT] "$a0";;
      #()
      ) in
    MapInsert (![mapT (arrowT unitT unitT)] "handlers") RPC_ROPRIMARYAPPLY "$a0";;
    let: "$a0" := (λ: "args" "reply",
      Server__IncreaseCommitIndex (![ptrT] "s") (DecodeIncreaseCommitArgs (![slice.T byteT] "args"));;
      #()
      ) in
    MapInsert (![mapT (arrowT unitT unitT)] "handlers") RPC_INCREASECOMMIT "$a0";;
    let: "rs" := ref_zero ptrT in
    let: "$a0" := urpc.MakeServer (![mapT (arrowT unitT unitT)] "handlers") in
    "rs" <-[ptrT] "$a0";;
    urpc.Server__Serve (![ptrT] "rs") (![uint64T] "me");;
    Fork (Server__leaseRenewalThread (![ptrT] "s");;
          #());;
    Fork (Server__sendIncreaseCommitThread (![ptrT] "s");;
          #());;
    #().
