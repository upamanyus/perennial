(* autogenerated from github.com/mit-pdos/gokv/vrsm/apps/vkv *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.mit_dash_pdos.gokv.grove__ffi.
From Goose Require github_dot_com.mit_dash_pdos.gokv.kv.
From Goose Require github_dot_com.mit_dash_pdos.gokv.map__string__marshal.
From Goose Require github_dot_com.mit_dash_pdos.gokv.vrsm.apps.exactlyonce.
From Goose Require github_dot_com.mit_dash_pdos.gokv.vrsm.storage.
From Goose Require github_dot_com.tchajed.marshal.
From Goose Require sync.

From Perennial.goose_lang Require Import ffi.grove_prelude.

(* clerk.go *)

Definition Clerk := struct.decl [
  "cl" :: ptrT
].

Definition MakeClerk: val :=
  rec: "MakeClerk" "confHosts" :=
    let: "confHosts" := ref_to (slice.T uint64T) "confHosts" in
    return: (struct.new Clerk [
       "cl" ::= exactlyonce.MakeClerk (![slice.T uint64T] "confHosts")
     ]).

(* PutArgs from server.go *)

Definition PutArgs := struct.decl [
  "Key" :: stringT;
  "Val" :: stringT
].

Definition OP_PUT : expr := #(U8 0).

Definition OP_GET : expr := #(U8 1).

Definition OP_COND_PUT : expr := #(U8 2).

Definition encodePutArgs: val :=
  rec: "encodePutArgs" "args" :=
    let: "args" := ref_to ptrT "args" in
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #1 (#1 + #8)) in
    let: "$a0" := OP_PUT in
    SliceSet byteT (![slice.T byteT] "enc") #0 "$a0";;
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (StringLength (struct.loadF PutArgs "Key" (![ptrT] "args"))) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteBytes (![slice.T byteT] "enc") (StringToBytes (struct.loadF PutArgs "Key" (![ptrT] "args"))) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteBytes (![slice.T byteT] "enc") (StringToBytes (struct.loadF PutArgs "Val" (![ptrT] "args"))) in
    "enc" <-[slice.T byteT] "$a0";;
    return: (![slice.T byteT] "enc").

Definition Clerk__Put: val :=
  rec: "Clerk__Put" "ck" "key" "val" :=
    let: "val" := ref_to stringT "val" in
    let: "key" := ref_to stringT "key" in
    let: "ck" := ref_to ptrT "ck" in
    let: "args" := ref_zero ptrT in
    let: "$a0" := struct.new PutArgs [
      "Key" ::= ![stringT] "key";
      "Val" ::= ![stringT] "val"
    ] in
    "args" <-[ptrT] "$a0";;
    exactlyonce.Clerk__ApplyExactlyOnce (struct.loadF Clerk "cl" (![ptrT] "ck")) (encodePutArgs (![ptrT] "args"));;
    #().

Definition encodeGetArgs: val :=
  rec: "encodeGetArgs" "args" :=
    let: "args" := ref_to stringT "args" in
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #1 #1) in
    let: "$a0" := OP_GET in
    SliceSet byteT (![slice.T byteT] "enc") #0 "$a0";;
    let: "$a0" := marshal.WriteBytes (![slice.T byteT] "enc") (StringToBytes (![stringT] "args")) in
    "enc" <-[slice.T byteT] "$a0";;
    return: (![slice.T byteT] "enc").

Definition Clerk__Get: val :=
  rec: "Clerk__Get" "ck" "key" :=
    let: "key" := ref_to stringT "key" in
    let: "ck" := ref_to ptrT "ck" in
    return: (StringFromBytes (exactlyonce.Clerk__ApplyReadonly (struct.loadF Clerk "cl" (![ptrT] "ck")) (encodeGetArgs (![stringT] "key")))).

Definition CondPutArgs := struct.decl [
  "Key" :: stringT;
  "Expect" :: stringT;
  "Val" :: stringT
].

Definition encodeCondPutArgs: val :=
  rec: "encodeCondPutArgs" "args" :=
    let: "args" := ref_to ptrT "args" in
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #1 (#1 + #8)) in
    let: "$a0" := OP_COND_PUT in
    SliceSet byteT (![slice.T byteT] "enc") #0 "$a0";;
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (StringLength (struct.loadF CondPutArgs "Key" (![ptrT] "args"))) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteBytes (![slice.T byteT] "enc") (StringToBytes (struct.loadF CondPutArgs "Key" (![ptrT] "args"))) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (StringLength (struct.loadF CondPutArgs "Expect" (![ptrT] "args"))) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteBytes (![slice.T byteT] "enc") (StringToBytes (struct.loadF CondPutArgs "Expect" (![ptrT] "args"))) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteBytes (![slice.T byteT] "enc") (StringToBytes (struct.loadF CondPutArgs "Val" (![ptrT] "args"))) in
    "enc" <-[slice.T byteT] "$a0";;
    return: (![slice.T byteT] "enc").

Definition Clerk__CondPut: val :=
  rec: "Clerk__CondPut" "ck" "key" "expect" "val" :=
    let: "val" := ref_to stringT "val" in
    let: "expect" := ref_to stringT "expect" in
    let: "key" := ref_to stringT "key" in
    let: "ck" := ref_to ptrT "ck" in
    let: "args" := ref_zero ptrT in
    let: "$a0" := struct.new CondPutArgs [
      "Key" ::= ![stringT] "key";
      "Expect" ::= ![stringT] "expect";
      "Val" ::= ![stringT] "val"
    ] in
    "args" <-[ptrT] "$a0";;
    return: (StringFromBytes (exactlyonce.Clerk__ApplyExactlyOnce (struct.loadF Clerk "cl" (![ptrT] "ck")) (encodeCondPutArgs (![ptrT] "args")))).

(* clerkpool.go *)

Definition ClerkPool := struct.decl [
  "mu" :: ptrT;
  "cls" :: slice.T ptrT;
  "confHosts" :: slice.T uint64T
].

Definition MakeClerkPool: val :=
  rec: "MakeClerkPool" "confHosts" :=
    let: "confHosts" := ref_to (slice.T uint64T) "confHosts" in
    return: (struct.new ClerkPool [
       "mu" ::= struct.alloc sync.Mutex (zero_val (struct.t sync.Mutex));
       "cls" ::= NewSlice ptrT #0;
       "confHosts" ::= ![slice.T uint64T] "confHosts"
     ]).

(* TODO: get rid of stale clerks from the ck.cls list?
   TODO: keep failed clerks out of ck.cls list? Maybe f(cl) can return an
   optional error saying "get rid of cl". *)
Definition ClerkPool__doWithClerk: val :=
  rec: "ClerkPool__doWithClerk" "ck" "f" :=
    let: "f" := ref_to (ptrT -> unitT)%ht "f" in
    let: "ck" := ref_to ptrT "ck" in
    sync.Mutex__Lock (struct.loadF ClerkPool "mu" (![ptrT] "ck"));;
    let: "cl" := ref (zero_val ptrT) in
    (if: (slice.len (struct.loadF ClerkPool "cls" (![ptrT] "ck"))) > #0
    then
      let: "$a0" := SliceGet ptrT (struct.loadF ClerkPool "cls" (![ptrT] "ck")) #0 in
      "cl" <-[ptrT] "$a0";;
      let: "$a0" := SliceSkip ptrT (struct.loadF ClerkPool "cls" (![ptrT] "ck")) #1 in
      struct.storeF ClerkPool "cls" (![ptrT] "ck") "$a0";;
      sync.Mutex__Unlock (struct.loadF ClerkPool "mu" (![ptrT] "ck"));;
      (![(arrowT unitT unitT)] "f") (![ptrT] "cl");;
      sync.Mutex__Lock (struct.loadF ClerkPool "mu" (![ptrT] "ck"));;
      let: "$a0" := SliceAppend ptrT (struct.loadF ClerkPool "cls" (![ptrT] "ck")) (![ptrT] "cl") in
      struct.storeF ClerkPool "cls" (![ptrT] "ck") "$a0";;
      sync.Mutex__Unlock (struct.loadF ClerkPool "mu" (![ptrT] "ck"));;
      #()
    else
      sync.Mutex__Unlock (struct.loadF ClerkPool "mu" (![ptrT] "ck"));;
      let: "$a0" := MakeClerk (struct.loadF ClerkPool "confHosts" (![ptrT] "ck")) in
      "cl" <-[ptrT] "$a0";;
      (![(arrowT unitT unitT)] "f") (![ptrT] "cl");;
      sync.Mutex__Lock (struct.loadF ClerkPool "mu" (![ptrT] "ck"));;
      let: "$a0" := SliceAppend ptrT (struct.loadF ClerkPool "cls" (![ptrT] "ck")) (![ptrT] "cl") in
      struct.storeF ClerkPool "cls" (![ptrT] "ck") "$a0";;
      sync.Mutex__Unlock (struct.loadF ClerkPool "mu" (![ptrT] "ck"));;
      #());;
    #().

Definition ClerkPool__Put: val :=
  rec: "ClerkPool__Put" "ck" "key" "val" :=
    let: "val" := ref_to stringT "val" in
    let: "key" := ref_to stringT "key" in
    let: "ck" := ref_to ptrT "ck" in
    ClerkPool__doWithClerk (![ptrT] "ck") (λ: "ck",
      Clerk__Put (![ptrT] "ck") (![stringT] "key") (![stringT] "val");;
      #()
      );;
    #().

Definition ClerkPool__Get: val :=
  rec: "ClerkPool__Get" "ck" "key" :=
    let: "key" := ref_to stringT "key" in
    let: "ck" := ref_to ptrT "ck" in
    let: "ret" := ref (zero_val stringT) in
    ClerkPool__doWithClerk (![ptrT] "ck") (λ: "ck",
      let: "$a0" := Clerk__Get (![ptrT] "ck") (![stringT] "key") in
      "ret" <-[stringT] "$a0";;
      #()
      );;
    return: (![stringT] "ret").

Definition ClerkPool__CondPut: val :=
  rec: "ClerkPool__CondPut" "ck" "key" "expect" "val" :=
    let: "val" := ref_to stringT "val" in
    let: "expect" := ref_to stringT "expect" in
    let: "key" := ref_to stringT "key" in
    let: "ck" := ref_to ptrT "ck" in
    let: "ret" := ref (zero_val stringT) in
    ClerkPool__doWithClerk (![ptrT] "ck") (λ: "ck",
      let: "$a0" := Clerk__CondPut (![ptrT] "ck") (![stringT] "key") (![stringT] "expect") (![stringT] "val") in
      "ret" <-[stringT] "$a0";;
      #()
      );;
    return: (![stringT] "ret").

Definition MakeKv: val :=
  rec: "MakeKv" "confHosts" :=
    let: "confHosts" := ref_to (slice.T uint64T) "confHosts" in
    let: "ck" := ref_zero ptrT in
    let: "$a0" := MakeClerkPool (![slice.T uint64T] "confHosts") in
    "ck" <-[ptrT] "$a0";;
    return: (struct.new kv.Kv [
       "Put" ::= ClerkPool__Put (![ptrT] "ck");
       "Get" ::= ClerkPool__Get (![ptrT] "ck");
       "ConditionalPut" ::= ClerkPool__CondPut (![ptrT] "ck")
     ]).

(* server.go *)

Definition KVState := struct.decl [
  "kvs" :: mapT stringT;
  "vnums" :: mapT uint64T;
  "minVnum" :: uint64T
].

Definition decodePutArgs: val :=
  rec: "decodePutArgs" "raw_args" :=
    let: "raw_args" := ref_to (slice.T byteT) "raw_args" in
    let: "enc" := ref_to (slice.T byteT) (SliceSkip byteT (![slice.T byteT] "raw_args") #1) in
    let: "args" := ref_zero ptrT in
    let: "$a0" := struct.alloc PutArgs (zero_val (struct.t PutArgs)) in
    "args" <-[ptrT] "$a0";;
    let: "l" := ref (zero_val uint64T) in
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc") in
    "enc" <-[slice.T byteT] "$a1";;
    "l" <-[uint64T] "$a0";;
    let: "$a0" := StringFromBytes (SliceTake (![slice.T byteT] "enc") (![uint64T] "l")) in
    struct.storeF PutArgs "Key" (![ptrT] "args") "$a0";;
    let: "$a0" := StringFromBytes (SliceSkip byteT (![slice.T byteT] "enc") (![uint64T] "l")) in
    struct.storeF PutArgs "Val" (![ptrT] "args") "$a0";;
    return: (![ptrT] "args").

Definition getArgs: ty := stringT.

Definition decodeGetArgs: val :=
  rec: "decodeGetArgs" "raw_args" :=
    let: "raw_args" := ref_to (slice.T byteT) "raw_args" in
    return: (StringFromBytes (SliceSkip byteT (![slice.T byteT] "raw_args") #1)).

Definition decodeCondPutArgs: val :=
  rec: "decodeCondPutArgs" "raw_args" :=
    let: "raw_args" := ref_to (slice.T byteT) "raw_args" in
    let: "enc" := ref_to (slice.T byteT) (SliceSkip byteT (![slice.T byteT] "raw_args") #1) in
    let: "args" := ref_zero ptrT in
    let: "$a0" := struct.alloc CondPutArgs (zero_val (struct.t CondPutArgs)) in
    "args" <-[ptrT] "$a0";;
    let: "l" := ref (zero_val uint64T) in
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc") in
    "enc" <-[slice.T byteT] "$a1";;
    "l" <-[uint64T] "$a0";;
    let: "enc2" := ref_zero (slice.T byteT) in
    let: "keybytes" := ref_zero (slice.T byteT) in
    let: ("$a0", "$a1") := marshal.ReadBytes (![slice.T byteT] "enc") (![uint64T] "l") in
    "enc2" <-[slice.T byteT] "$a1";;
    "keybytes" <-[slice.T byteT] "$a0";;
    let: "$a0" := StringFromBytes (![slice.T byteT] "keybytes") in
    struct.storeF CondPutArgs "Key" (![ptrT] "args") "$a0";;
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc2") in
    "enc" <-[slice.T byteT] "$a1";;
    "l" <-[uint64T] "$a0";;
    let: "$a0" := StringFromBytes (SliceTake (![slice.T byteT] "enc") (![uint64T] "l")) in
    struct.storeF CondPutArgs "Expect" (![ptrT] "args") "$a0";;
    let: "$a0" := StringFromBytes (SliceSkip byteT (![slice.T byteT] "enc") (![uint64T] "l")) in
    struct.storeF CondPutArgs "Val" (![ptrT] "args") "$a0";;
    return: (![ptrT] "args").

(* end of marshalling *)
Definition KVState__put: val :=
  rec: "KVState__put" "s" "args" :=
    let: "args" := ref_to ptrT "args" in
    let: "s" := ref_to ptrT "s" in
    let: "$a0" := struct.loadF PutArgs "Val" (![ptrT] "args") in
    MapInsert (struct.loadF KVState "kvs" (![ptrT] "s")) (struct.loadF PutArgs "Key" (![ptrT] "args")) "$a0";;
    return: (NewSlice byteT #0).

Definition KVState__get: val :=
  rec: "KVState__get" "s" "args" :=
    let: "args" := ref_to stringT "args" in
    let: "s" := ref_to ptrT "s" in
    return: (StringToBytes (Fst (MapGet (struct.loadF KVState "kvs" (![ptrT] "s")) (![stringT] "args")))).

Definition KVState__apply: val :=
  rec: "KVState__apply" "s" "args" "vnum" :=
    let: "vnum" := ref_to uint64T "vnum" in
    let: "args" := ref_to (slice.T byteT) "args" in
    let: "s" := ref_to ptrT "s" in
    (if: (SliceGet byteT (![slice.T byteT] "args") #0) = OP_PUT
    then
      let: "args" := ref_zero ptrT in
      let: "$a0" := decodePutArgs (![slice.T byteT] "args") in
      "args" <-[ptrT] "$a0";;
      let: "$a0" := ![uint64T] "vnum" in
      MapInsert (struct.loadF KVState "vnums" (![ptrT] "s")) (struct.loadF PutArgs "Key" (![ptrT] "args")) "$a0";;
      return: (KVState__put (![ptrT] "s") (![ptrT] "args"))
    else
      (if: (SliceGet byteT (![slice.T byteT] "args") #0) = OP_GET
      then
        let: "key" := ref_zero stringT in
        let: "$a0" := decodeGetArgs (![slice.T byteT] "args") in
        "key" <-[stringT] "$a0";;
        let: "$a0" := ![uint64T] "vnum" in
        MapInsert (struct.loadF KVState "vnums" (![ptrT] "s")) (![stringT] "key") "$a0";;
        return: (KVState__get (![ptrT] "s") (![stringT] "key"))
      else
        (if: (SliceGet byteT (![slice.T byteT] "args") #0) = OP_COND_PUT
        then
          let: "args" := ref_zero ptrT in
          let: "$a0" := decodeCondPutArgs (![slice.T byteT] "args") in
          "args" <-[ptrT] "$a0";;
          (if: (Fst (MapGet (struct.loadF KVState "kvs" (![ptrT] "s")) (struct.loadF CondPutArgs "Key" (![ptrT] "args")))) = (struct.loadF CondPutArgs "Expect" (![ptrT] "args"))
          then
            let: "$a0" := ![uint64T] "vnum" in
            MapInsert (struct.loadF KVState "vnums" (![ptrT] "s")) (struct.loadF CondPutArgs "Key" (![ptrT] "args")) "$a0";;
            let: "$a0" := struct.loadF CondPutArgs "Val" (![ptrT] "args") in
            MapInsert (struct.loadF KVState "kvs" (![ptrT] "s")) (struct.loadF CondPutArgs "Key" (![ptrT] "args")) "$a0";;
            return: (StringToBytes #(str"ok"))
          else #());;
          return: (StringToBytes #(str""))
        else
          Panic "unexpected op type";;
          #());;
        #());;
      #());;
    #().

Definition KVState__applyReadonly: val :=
  rec: "KVState__applyReadonly" "s" "args" :=
    let: "args" := ref_to (slice.T byteT) "args" in
    let: "s" := ref_to ptrT "s" in
    (if: (SliceGet byteT (![slice.T byteT] "args") #0) ≠ OP_GET
    then
      Panic "expected a GET as readonly-operation";;
      #()
    else #());;
    let: "key" := ref_zero stringT in
    let: "$a0" := decodeGetArgs (![slice.T byteT] "args") in
    "key" <-[stringT] "$a0";;
    let: "reply" := ref_zero (slice.T byteT) in
    let: "$a0" := KVState__get (![ptrT] "s") (![stringT] "key") in
    "reply" <-[slice.T byteT] "$a0";;
    let: "ok" := ref_zero boolT in
    let: "vnum" := ref_zero uint64T in
    let: ("$a0", "$a1") := Fst (MapGet (struct.loadF KVState "vnums" (![ptrT] "s")) (![stringT] "key")) in
    "ok" <-[boolT] "$a1";;
    "vnum" <-[uint64T] "$a0";;
    (if: ![boolT] "ok"
    then return: (![uint64T] "vnum", ![slice.T byteT] "reply")
    else return: (struct.loadF KVState "minVnum" (![ptrT] "s"), ![slice.T byteT] "reply"));;
    #().

Definition KVState__getState: val :=
  rec: "KVState__getState" "s" :=
    let: "s" := ref_to ptrT "s" in
    return: (map__string__marshal.EncodeStringMap (struct.loadF KVState "kvs" (![ptrT] "s"))).

Definition KVState__setState: val :=
  rec: "KVState__setState" "s" "snap" "nextIndex" :=
    let: "nextIndex" := ref_to uint64T "nextIndex" in
    let: "snap" := ref_to (slice.T byteT) "snap" in
    let: "s" := ref_to ptrT "s" in
    let: "$a0" := ![uint64T] "nextIndex" in
    struct.storeF KVState "minVnum" (![ptrT] "s") "$a0";;
    let: "$a0" := NewMap stringT uint64T #() in
    struct.storeF KVState "vnums" (![ptrT] "s") "$a0";;
    let: "$a0" := map__string__marshal.DecodeStringMap (![slice.T byteT] "snap") in
    struct.storeF KVState "kvs" (![ptrT] "s") "$a0";;
    #().

Definition makeVersionedStateMachine: val :=
  rec: "makeVersionedStateMachine" <> :=
    let: "s" := ref_zero ptrT in
    let: "$a0" := struct.alloc KVState (zero_val (struct.t KVState)) in
    "s" <-[ptrT] "$a0";;
    let: "$a0" := NewMap stringT stringT #() in
    struct.storeF KVState "kvs" (![ptrT] "s") "$a0";;
    let: "$a0" := NewMap stringT uint64T #() in
    struct.storeF KVState "vnums" (![ptrT] "s") "$a0";;
    return: (struct.new exactlyonce.VersionedStateMachine [
       "ApplyVolatile" ::= KVState__apply (![ptrT] "s");
       "ApplyReadonly" ::= KVState__applyReadonly (![ptrT] "s");
       "GetState" ::= (λ: <>,
         return: (KVState__getState (![ptrT] "s"))
         );
       "SetState" ::= KVState__setState (![ptrT] "s")
     ]).

Definition Start: val :=
  rec: "Start" "fname" "host" "confHosts" :=
    let: "confHosts" := ref_to (slice.T uint64T) "confHosts" in
    let: "host" := ref_to uint64T "host" in
    let: "fname" := ref_to stringT "fname" in
    replica.Server__Serve (storage.MakePbServer (exactlyonce.MakeExactlyOnceStateMachine (makeVersionedStateMachine #())) (![stringT] "fname") (![slice.T uint64T] "confHosts")) (![uint64T] "host");;
    #().
