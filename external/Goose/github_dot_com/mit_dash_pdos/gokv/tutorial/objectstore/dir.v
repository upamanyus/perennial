(* autogenerated from github.com/mit-pdos/gokv/tutorial/objectstore/dir *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.mit_dash_pdos.gokv.grove__ffi.
From Goose Require github_dot_com.mit_dash_pdos.gokv.reconnectclient.
From Goose Require github_dot_com.mit_dash_pdos.gokv.urpc.
From Goose Require sync.

From Perennial.goose_lang Require Import ffi.grove_prelude.

(* 0data.go *)

(* WriteID from client.go *)

Definition WriteID: ty := uint64T.

Definition PreparedWrite := struct.decl [
  "Id" :: uint64T;
  "ChunkAddrs" :: slice.T uint64T
].

Definition ParsePreparedWrite: val :=
  rec: "ParsePreparedWrite" "data" :=
    Panic "TODO: marshaling";;
    #().

Definition MarshalPreparedWrite: val :=
  rec: "MarshalPreparedWrite" "id" :=
    Panic "TODO: marshaling";;
    #().

Definition RecordChunkArgs := struct.decl [
  "WriteId" :: uint64T;
  "Server" :: uint64T;
  "ContentHash" :: stringT;
  "Index" :: uint64T
].

Definition MarshalRecordChunkArgs: val :=
  rec: "MarshalRecordChunkArgs" "args" :=
    Panic "TODO: marshaling";;
    #().

Definition ParseRecordChunkArgs: val :=
  rec: "ParseRecordChunkArgs" "data" :=
    Panic "TODO: marshaling";;
    #().

Definition FinishWriteArgs := struct.decl [
  "WriteId" :: uint64T;
  "Keyname" :: stringT
].

Definition MarshalFinishWriteArgs: val :=
  rec: "MarshalFinishWriteArgs" "args" :=
    Panic "TODO: marshaling";;
    #().

Definition ParseFinishWriteArgs: val :=
  rec: "ParseFinishWriteArgs" "data" :=
    Panic "TODO: marshaling";;
    #().

Definition ChunkHandle := struct.decl [
  "Addr" :: uint64T;
  "ContentHash" :: stringT
].

Definition PreparedRead := struct.decl [
  "Handles" :: slice.T (struct.t ChunkHandle)
].

Definition MarshalPreparedRead: val :=
  rec: "MarshalPreparedRead" "v" :=
    Panic "TODO: marshaling";;
    #().

Definition ParsePreparedRead: val :=
  rec: "ParsePreparedRead" "data" :=
    Panic "TODO: marshaling";;
    #().

(* client.go *)

Definition PrepareWriteId : expr := #1.

Definition RecordChunkId : expr := #2.

Definition FinishWriteId : expr := #3.

Definition PrepareReadId : expr := #4.

Definition Clerk := struct.decl [
  "client" :: ptrT
].

Definition MakeClerk: val :=
  rec: "MakeClerk" "addr" :=
    let: "client" := reconnectclient.MakeReconnectingClient "addr" in
    struct.new Clerk [
      "client" ::= "client"
    ].

Definition Clerk__PrepareWrite: val :=
  rec: "Clerk__PrepareWrite" "ck" :=
    let: "empty" := NewSlice byteT #0 in
    let: "reply" := ref (zero_val (slice.T byteT)) in
    reconnectclient.ReconnectingClient__Call (struct.loadF Clerk "client" "ck") PrepareWriteId "empty" "reply" #100;;
    ParsePreparedWrite (![slice.T byteT] "reply").

(* From chunk *)
Definition Clerk__RecordChunk: val :=
  rec: "Clerk__RecordChunk" "ck" "args" :=
    let: "req" := MarshalRecordChunkArgs "args" in
    let: "reply" := ref (zero_val (slice.T byteT)) in
    reconnectclient.ReconnectingClient__Call (struct.loadF Clerk "client" "ck") RecordChunkId "req" "reply" #100;;
    #().

(* From chunk *)
Definition Clerk__FinishWrite: val :=
  rec: "Clerk__FinishWrite" "ck" "args" :=
    let: "req" := MarshalFinishWriteArgs "args" in
    let: "reply" := ref (zero_val (slice.T byteT)) in
    reconnectclient.ReconnectingClient__Call (struct.loadF Clerk "client" "ck") FinishWriteId "req" "reply" #100;;
    #().

Definition Clerk__PrepareRead: val :=
  rec: "Clerk__PrepareRead" "ck" "keyname" :=
    let: "req" := StringToBytes "keyname" in
    let: "reply" := ref (zero_val (slice.T byteT)) in
    reconnectclient.ReconnectingClient__Call (struct.loadF Clerk "client" "ck") PrepareReadId "req" "reply" #100;;
    ParsePreparedRead (![slice.T byteT] "reply").

(* server.go *)

Definition PartialValue := struct.decl [
  "servers" :: mapT (struct.t ChunkHandle)
].

Definition Value := struct.decl [
  "servers" :: slice.T (struct.t ChunkHandle)
].

Definition Server := struct.decl [
  "m" :: ptrT;
  "ongoing" :: mapT (struct.t PartialValue);
  "data" :: mapT (struct.t Value);
  "nextWriteId" :: WriteID
].

(* From client *)
Definition Server__PrepareWrite: val :=
  rec: "Server__PrepareWrite" "s" :=
    sync.Mutex__Lock (struct.loadF Server "m" "s");;
    let: "id" := struct.loadF Server "nextWriteId" "s" in
    struct.storeF Server "nextWriteId" "s" ((struct.loadF Server "nextWriteId" "s") + #1);;
    MapInsert (struct.loadF Server "ongoing" "s") "id" (struct.mk PartialValue [
      "servers" ::= NewMap uint64T (struct.t ChunkHandle) #()
    ]);;
    sync.Mutex__Unlock (struct.loadF Server "m" "s");;
    struct.mk PreparedWrite [
      "Id" ::= "id";
      "ChunkAddrs" ::= NewSlice uint64T #0
    ].

(* From chunk *)
Definition Server__RecordChunk: val :=
  rec: "Server__RecordChunk" "s" "args" :=
    sync.Mutex__Lock (struct.loadF Server "m" "s");;
    MapInsert (struct.get PartialValue "servers" (Fst (MapGet (struct.loadF Server "ongoing" "s") (struct.get RecordChunkArgs "WriteId" "args")))) (struct.get RecordChunkArgs "Index" "args") (struct.mk ChunkHandle [
      "Addr" ::= struct.get RecordChunkArgs "Server" "args";
      "ContentHash" ::= struct.get RecordChunkArgs "ContentHash" "args"
    ]);;
    sync.Mutex__Unlock (struct.loadF Server "m" "s");;
    #().

(* From chunk *)
Definition Server__FinishWrite: val :=
  rec: "Server__FinishWrite" "s" "args" :=
    sync.Mutex__Lock (struct.loadF Server "m" "s");;
    let: "v" := struct.get PartialValue "servers" (Fst (MapGet (struct.loadF Server "ongoing" "s") (struct.get FinishWriteArgs "WriteId" "args"))) in
    let: "numChunks" := MapLen "v" in
    let: "servers" := ref_to (slice.T (struct.t ChunkHandle)) (NewSlice (struct.t ChunkHandle) #0) in
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, (![uint64T] "i") < "numChunks"); (λ: <>, "i" <-[uint64T] ((![uint64T] "i") + #1)) := λ: <>,
      "servers" <-[slice.T (struct.t ChunkHandle)] (SliceAppend (struct.t ChunkHandle) (![slice.T (struct.t ChunkHandle)] "servers") (Fst (MapGet "v" (![uint64T] "i"))));;
      Continue);;
    MapInsert (struct.loadF Server "data" "s") (struct.get FinishWriteArgs "Keyname" "args") (struct.mk Value [
      "servers" ::= ![slice.T (struct.t ChunkHandle)] "servers"
    ]);;
    sync.Mutex__Unlock (struct.loadF Server "m" "s");;
    #().

Definition Server__PrepareRead: val :=
  rec: "Server__PrepareRead" "s" "keyname" :=
    sync.Mutex__Lock (struct.loadF Server "m" "s");;
    let: "servers" := struct.get Value "servers" (Fst (MapGet (struct.loadF Server "data" "s") "keyname")) in
    sync.Mutex__Unlock (struct.loadF Server "m" "s");;
    struct.mk PreparedRead [
      "Handles" ::= "servers"
    ].

Definition StartServer: val :=
  rec: "StartServer" "me" :=
    let: "s" := struct.new Server [
      "m" ::= struct.alloc sync.Mutex (zero_val (struct.t sync.Mutex));
      "ongoing" ::= NewMap WriteID (struct.t PartialValue) #();
      "data" ::= NewMap stringT (struct.t Value) #();
      "nextWriteId" ::= #1
    ] in
    let: "handlers" := NewMap uint64T ((slice.T byteT) -> ptrT -> unitT)%ht #() in
    MapInsert "handlers" PrepareWriteId (λ: "_req" "reply",
      let: "ret" := Server__PrepareWrite "s" in
      "reply" <-[slice.T byteT] (MarshalPreparedWrite "ret");;
      #()
      );;
    MapInsert "handlers" RecordChunkId (λ: "req" "reply",
      let: "args" := ParseRecordChunkArgs "req" in
      Server__RecordChunk "s" "args";;
      "reply" <-[slice.T byteT] (NewSlice byteT #0);;
      #()
      );;
    MapInsert "handlers" FinishWriteId (λ: "req" "reply",
      let: "args" := ParseFinishWriteArgs "req" in
      Server__FinishWrite "s" "args";;
      "reply" <-[slice.T byteT] (NewSlice byteT #0);;
      #()
      );;
    MapInsert "handlers" PrepareReadId (λ: "req" "reply",
      let: "args" := StringFromBytes "req" in
      let: "ret" := Server__PrepareRead "s" "args" in
      "reply" <-[slice.T byteT] (MarshalPreparedRead "ret");;
      #()
      );;
    let: "server" := urpc.MakeServer "handlers" in
    urpc.Server__Serve "server" "me";;
    #().
