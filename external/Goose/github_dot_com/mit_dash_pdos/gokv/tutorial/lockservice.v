(* autogenerated from github.com/mit-pdos/gokv/tutorial/lockservice *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.goose_dash_lang.std.
From Goose Require github_dot_com.mit_dash_pdos.gokv.grove__ffi.
From Goose Require github_dot_com.mit_dash_pdos.gokv.urpc.
From Goose Require github_dot_com.tchajed.goose.machine.
From Goose Require github_dot_com.tchajed.marshal.
From Goose Require sync.

From Perennial.goose_lang Require Import ffi.grove_prelude.

(* 0_lock.gb.go *)

Definition EncodeBool: val :=
  rec: "EncodeBool" "a" :=
    (if: "a"
    then SliceAppend byteT (NewSlice byteT #0) #(U8 1)
    else SliceAppend byteT (NewSlice byteT #0) #(U8 0)).

Definition DecodeBool: val :=
  rec: "DecodeBool" "x" :=
    (SliceGet byteT "x" #0) = #(U8 1).

Definition EncodeUint64: val :=
  rec: "EncodeUint64" "a" :=
    marshal.WriteInt (NewSlice byteT #0) "a".

Definition DecodeUint64: val :=
  rec: "DecodeUint64" "x" :=
    let: ("a", <>) := marshal.ReadInt "x" in
    "a".

(* 1_lock_rpc.gb.go *)

Definition RPC_GET_FRESH_NUM : expr := #0.

Definition RPC_TRY_ACQUIRE : expr := #1.

Definition RPC_RELEASE : expr := #2.

Definition Error: ty := uint64T.

Definition Client := struct.decl [
  "cl" :: ptrT
].

Definition Client__getFreshNum: val :=
  rec: "Client__getFreshNum" "cl" :=
    let: "reply" := ref (zero_val (slice.T byteT)) in
    let: "args" := NewSlice byteT #0 in
    let: "err" := urpc.Client__Call (struct.loadF Client "cl" "cl") RPC_GET_FRESH_NUM "args" "reply" #100 in
    (if: "err" = urpc.ErrNone
    then (DecodeUint64 (![slice.T byteT] "reply"), "err")
    else (#0, "err")).

Definition Client__tryAcquire: val :=
  rec: "Client__tryAcquire" "cl" "id" :=
    let: "reply" := ref (zero_val (slice.T byteT)) in
    let: "args" := EncodeUint64 "id" in
    let: "err" := urpc.Client__Call (struct.loadF Client "cl" "cl") RPC_TRY_ACQUIRE "args" "reply" #100 in
    (if: "err" = urpc.ErrNone
    then (DecodeUint64 (![slice.T byteT] "reply"), "err")
    else (#0, "err")).

Definition Client__release: val :=
  rec: "Client__release" "cl" "id" :=
    let: "reply" := ref (zero_val (slice.T byteT)) in
    let: "args" := EncodeUint64 "id" in
    urpc.Client__Call (struct.loadF Client "cl" "cl") RPC_RELEASE "args" "reply" #100.

Definition makeClient: val :=
  rec: "makeClient" "hostname" :=
    struct.new Client [
      "cl" ::= urpc.MakeClient "hostname"
    ].

(* 2_server.go *)

Definition Server := struct.decl [
  "mu" :: ptrT;
  "nextId" :: uint64T;
  "locked" :: boolT;
  "holder" :: uint64T
].

Definition Server__getFreshNum: val :=
  rec: "Server__getFreshNum" "s" :=
    sync.Mutex__Lock (struct.loadF Server "mu" "s");;
    let: "n" := struct.loadF Server "nextId" "s" in
    struct.storeF Server "nextId" "s" (std.SumAssumeNoOverflow (struct.loadF Server "nextId" "s") #1);;
    sync.Mutex__Unlock (struct.loadF Server "mu" "s");;
    "n".

Definition StatusGranted : expr := #0.

Definition StatusRetry : expr := #2.

Definition StatusStale : expr := #1.

Definition Server__tryAcquire: val :=
  rec: "Server__tryAcquire" "s" "id" :=
    let: "ret" := ref (zero_val uint64T) in
    sync.Mutex__Lock (struct.loadF Server "mu" "s");;
    (if: (struct.loadF Server "holder" "s") > "id"
    then "ret" <-[uint64T] StatusStale
    else
      (if: struct.loadF Server "locked" "s"
      then
        (if: (struct.loadF Server "holder" "s") = "id"
        then "ret" <-[uint64T] StatusGranted
        else "ret" <-[uint64T] StatusRetry)
      else
        struct.storeF Server "holder" "s" "id";;
        struct.storeF Server "locked" "s" #true;;
        (* log.Printf("Lock held by %d", id) *)
        "ret" <-[uint64T] StatusGranted));;
    sync.Mutex__Unlock (struct.loadF Server "mu" "s");;
    ![uint64T] "ret".

Definition Server__release: val :=
  rec: "Server__release" "s" "id" :=
    sync.Mutex__Lock (struct.loadF Server "mu" "s");;
    (if: (struct.loadF Server "holder" "s") = "id"
    then struct.storeF Server "locked" "s" #false
    else #());;
    (* log.Printf("Lock released by %d", id) *)
    sync.Mutex__Unlock (struct.loadF Server "mu" "s");;
    #().

Definition MakeServer: val :=
  rec: "MakeServer" <> :=
    let: "s" := struct.alloc Server (zero_val (struct.t Server)) in
    struct.storeF Server "mu" "s" (struct.alloc sync.Mutex (zero_val (struct.t sync.Mutex)));;
    "s".

(* 3_lock_rpc_server.gb.go *)

Definition Server__Start: val :=
  rec: "Server__Start" "s" "me" :=
    let: "handlers" := NewMap uint64T ((slice.T byteT) -> ptrT -> unitT)%ht #() in
    MapInsert "handlers" RPC_GET_FRESH_NUM (λ: "enc_args" "enc_reply",
      "enc_reply" <-[slice.T byteT] (EncodeUint64 (Server__getFreshNum "s"));;
      #()
      );;
    MapInsert "handlers" RPC_TRY_ACQUIRE (λ: "enc_args" "enc_reply",
      "enc_reply" <-[slice.T byteT] (EncodeUint64 (Server__tryAcquire "s" (DecodeUint64 "enc_args")));;
      #()
      );;
    MapInsert "handlers" RPC_RELEASE (λ: "enc_args" "enc_reply",
      Server__release "s" (DecodeUint64 "enc_args");;
      #()
      );;
    urpc.Server__Serve (urpc.MakeServer "handlers") "me";;
    #().

(* client.go *)

Definition Clerk := struct.decl [
  "rpcCl" :: ptrT
].

Definition Locked := struct.decl [
  "rpcCl" :: ptrT;
  "id" :: uint64T
].

Definition MakeClerk: val :=
  rec: "MakeClerk" "host" :=
    struct.new Clerk [
      "rpcCl" ::= makeClient "host"
    ].

Definition Clerk__Acquire: val :=
  rec: "Clerk__Acquire" "ck" :=
    let: "id" := ref (zero_val uint64T) in
    let: "err" := ref (zero_val uint64T) in
    let: "l" := ref (zero_val ptrT) in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: ("0_ret", "1_ret") := Client__getFreshNum (struct.loadF Clerk "rpcCl" "ck") in
      "id" <-[uint64T] "0_ret";;
      "err" <-[uint64T] "1_ret";;
      (if: (![uint64T] "err") ≠ #0
      then Continue
      else
        Skip;;
        (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
          let: ("lockStatus", "err") := Client__tryAcquire (struct.loadF Clerk "rpcCl" "ck") (![uint64T] "id") in
          (if: ("err" ≠ #0) || ("lockStatus" = StatusRetry)
          then
            machine.Sleep (#100 * #1000000);;
            Continue
          else
            (if: "lockStatus" = StatusGranted
            then
              "l" <-[ptrT] (struct.new Locked [
                "rpcCl" ::= struct.loadF Clerk "rpcCl" "ck";
                "id" ::= ![uint64T] "id"
              ]);;
              Break
            else Break)));;
        (if: (![ptrT] "l") ≠ #null
        then Break
        else Continue)));;
    ![ptrT] "l".

Definition Locked__Release: val :=
  rec: "Locked__Release" "l" :=
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: (Client__release (struct.loadF Locked "rpcCl" "l") (struct.loadF Locked "id" "l")) = #0
      then Break
      else Continue));;
    #().
