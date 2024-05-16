(* autogenerated from github.com/mit-pdos/gokv/vrsm/apps/exactlyonce *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.goose_dash_lang.std.
From Goose Require github_dot_com.mit_dash_pdos.gokv.grove__ffi.
From Goose Require github_dot_com.mit_dash_pdos.gokv.map__marshal.
From Goose Require github_dot_com.mit_dash_pdos.gokv.vrsm.clerk.
From Goose Require github_dot_com.mit_dash_pdos.gokv.vrsm.storage.
From Goose Require github_dot_com.tchajed.marshal.

From Perennial.goose_lang Require Import ffi.grove_prelude.

(* sm.go *)

Definition eStateMachine := struct.decl [
  "lastSeq" :: mapT uint64T;
  "lastReply" :: mapT (slice.T byteT);
  "nextCID" :: uint64T;
  "sm" :: ptrT;
  "esmNextIndex" :: uint64T
].

Definition OPTYPE_RW : expr := #(U8 0).

Definition OPTYPE_GETFRESHCID : expr := #(U8 1).

Definition OPTYPE_RO : expr := #(U8 2).

(* VersionedStateMachine from vsm.go *)

Definition VersionedStateMachine := struct.decl [
  "ApplyVolatile" :: ((slice.T byteT) -> uint64T -> (slice.T byteT))%ht;
  "ApplyReadonly" :: ((slice.T byteT) -> (uint64T * (slice.T byteT)))%ht;
  "SetState" :: ((slice.T byteT) -> uint64T -> unitT)%ht;
  "GetState" :: (unitT -> (slice.T byteT))%ht
].

Definition eStateMachine__applyVolatile: val :=
  rec: "eStateMachine__applyVolatile" "s" "op" :=
    let: "op" := ref_to (slice.T byteT) "op" in
    let: "s" := ref_to ptrT "s" in
    let: "ret" := ref (zero_val (slice.T byteT)) in
    let: "$a0" := std.SumAssumeNoOverflow (struct.loadF eStateMachine "esmNextIndex" (![ptrT] "s")) #1 in
    struct.storeF eStateMachine "esmNextIndex" (![ptrT] "s") "$a0";;
    (if: (SliceGet byteT (![slice.T byteT] "op") #0) = OPTYPE_GETFRESHCID
    then
      let: "$a0" := NewSliceWithCap byteT #0 #8 in
      "ret" <-[slice.T byteT] "$a0";;
      let: "$a0" := marshal.WriteInt (![slice.T byteT] "ret") (struct.loadF eStateMachine "nextCID" (![ptrT] "s")) in
      "ret" <-[slice.T byteT] "$a0";;
      let: "$a0" := std.SumAssumeNoOverflow (struct.loadF eStateMachine "nextCID" (![ptrT] "s")) #1 in
      struct.storeF eStateMachine "nextCID" (![ptrT] "s") "$a0";;
      #()
    else
      (if: (SliceGet byteT (![slice.T byteT] "op") #0) = OPTYPE_RW
      then
        let: "n" := ref_zero intT in
        let: "$a0" := slice.len (![slice.T byteT] "op") in
        "n" <-[intT] "$a0";;
        let: "enc" := ref_zero (slice.T byteT) in
        let: "$a0" := SliceSubslice byteT (![slice.T byteT] "op") #1 (![intT] "n") in
        "enc" <-[slice.T byteT] "$a0";;
        let: "enc2" := ref_zero (slice.T byteT) in
        let: "cid" := ref_zero uint64T in
        let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc") in
        "enc2" <-[slice.T byteT] "$a1";;
        "cid" <-[uint64T] "$a0";;
        let: "realOp" := ref_zero (slice.T byteT) in
        let: "seq" := ref_zero uint64T in
        let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc2") in
        "realOp" <-[slice.T byteT] "$a1";;
        "seq" <-[uint64T] "$a0";;
        (if: (Fst (MapGet (struct.loadF eStateMachine "lastSeq" (![ptrT] "s")) (![uint64T] "cid"))) ≥ (![uint64T] "seq")
        then
          let: "$a0" := Fst (MapGet (struct.loadF eStateMachine "lastReply" (![ptrT] "s")) (![uint64T] "cid")) in
          "ret" <-[slice.T byteT] "$a0";;
          #()
        else
          let: "$a0" := (struct.loadF VersionedStateMachine "ApplyVolatile" (struct.loadF eStateMachine "sm" (![ptrT] "s"))) (![slice.T byteT] "realOp") (struct.loadF eStateMachine "esmNextIndex" (![ptrT] "s")) in
          "ret" <-[slice.T byteT] "$a0";;
          let: "$a0" := ![slice.T byteT] "ret" in
          MapInsert (struct.loadF eStateMachine "lastReply" (![ptrT] "s")) (![uint64T] "cid") "$a0";;
          let: "$a0" := ![uint64T] "seq" in
          MapInsert (struct.loadF eStateMachine "lastSeq" (![ptrT] "s")) (![uint64T] "cid") "$a0";;
          #());;
        #()
      else
        (if: (SliceGet byteT (![slice.T byteT] "op") #0) = OPTYPE_RO
        then
          let: "n" := ref_zero intT in
          let: "$a0" := slice.len (![slice.T byteT] "op") in
          "n" <-[intT] "$a0";;
          let: "realOp" := ref_zero (slice.T byteT) in
          let: "$a0" := SliceSubslice byteT (![slice.T byteT] "op") #1 (![intT] "n") in
          "realOp" <-[slice.T byteT] "$a0";;
          let: ("$a0", "$a1") := (struct.loadF VersionedStateMachine "ApplyReadonly" (struct.loadF eStateMachine "sm" (![ptrT] "s"))) (![slice.T byteT] "realOp") in
          "ret" <-[slice.T byteT] "$a1";;
          "$a0";;
          #()
        else
          Panic "unexpected ee op type";;
          #());;
        #());;
      #());;
    return: (![slice.T byteT] "ret").

Definition eStateMachine__applyReadonly: val :=
  rec: "eStateMachine__applyReadonly" "s" "op" :=
    let: "op" := ref_to (slice.T byteT) "op" in
    let: "s" := ref_to ptrT "s" in
    (if: (SliceGet byteT (![slice.T byteT] "op") #0) = OPTYPE_GETFRESHCID
    then
      Panic "Got GETFRESHCID as a read-only op";;
      #()
    else
      (if: (SliceGet byteT (![slice.T byteT] "op") #0) = OPTYPE_RW
      then
        Panic "Got RW as a read-only op";;
        #()
      else
        (if: (SliceGet byteT (![slice.T byteT] "op") #0) ≠ OPTYPE_RO
        then
          Panic "unexpected ee op type";;
          #()
        else #());;
        #());;
      #());;
    let: "n" := ref_zero intT in
    let: "$a0" := slice.len (![slice.T byteT] "op") in
    "n" <-[intT] "$a0";;
    let: "realOp" := ref_zero (slice.T byteT) in
    let: "$a0" := SliceSubslice byteT (![slice.T byteT] "op") #1 (![intT] "n") in
    "realOp" <-[slice.T byteT] "$a0";;
    return: ((struct.loadF VersionedStateMachine "ApplyReadonly" (struct.loadF eStateMachine "sm" (![ptrT] "s"))) (![slice.T byteT] "realOp")).

Definition eStateMachine__getState: val :=
  rec: "eStateMachine__getState" "s" :=
    let: "s" := ref_to ptrT "s" in
    let: "appState" := ref_zero (slice.T byteT) in
    let: "$a0" := (struct.loadF VersionedStateMachine "GetState" (struct.loadF eStateMachine "sm" (![ptrT] "s"))) #() in
    "appState" <-[slice.T byteT] "$a0";;
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 #0) in
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF eStateMachine "nextCID" (![ptrT] "s")) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteBytes (![slice.T byteT] "enc") (map__marshal.EncodeMapU64ToU64 (struct.loadF eStateMachine "lastSeq" (![ptrT] "s"))) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteBytes (![slice.T byteT] "enc") (map__marshal.EncodeMapU64ToBytes (struct.loadF eStateMachine "lastReply" (![ptrT] "s"))) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteBytes (![slice.T byteT] "enc") (![slice.T byteT] "appState") in
    "enc" <-[slice.T byteT] "$a0";;
    return: (![slice.T byteT] "enc").

Definition eStateMachine__setState: val :=
  rec: "eStateMachine__setState" "s" "state" "nextIndex" :=
    let: "nextIndex" := ref_to uint64T "nextIndex" in
    let: "state" := ref_to (slice.T byteT) "state" in
    let: "s" := ref_to ptrT "s" in
    let: "enc" := ref_to (slice.T byteT) (![slice.T byteT] "state") in
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc") in
    "enc" <-[slice.T byteT] "$a1";;
    struct.storeF eStateMachine "nextCID" (![ptrT] "s") "$a0";;
    let: ("$a0", "$a1") := map__marshal.DecodeMapU64ToU64 (![slice.T byteT] "enc") in
    "enc" <-[slice.T byteT] "$a1";;
    struct.storeF eStateMachine "lastSeq" (![ptrT] "s") "$a0";;
    let: ("$a0", "$a1") := map__marshal.DecodeMapU64ToBytes (![slice.T byteT] "enc") in
    "enc" <-[slice.T byteT] "$a1";;
    struct.storeF eStateMachine "lastReply" (![ptrT] "s") "$a0";;
    (struct.loadF VersionedStateMachine "SetState" (struct.loadF eStateMachine "sm" (![ptrT] "s"))) (![slice.T byteT] "enc") (![uint64T] "nextIndex");;
    let: "$a0" := ![uint64T] "nextIndex" in
    struct.storeF eStateMachine "esmNextIndex" (![ptrT] "s") "$a0";;
    #().

Definition MakeExactlyOnceStateMachine: val :=
  rec: "MakeExactlyOnceStateMachine" "sm" :=
    let: "sm" := ref_to ptrT "sm" in
    let: "s" := ref_zero ptrT in
    let: "$a0" := struct.alloc eStateMachine (zero_val (struct.t eStateMachine)) in
    "s" <-[ptrT] "$a0";;
    let: "$a0" := NewMap uint64T uint64T #() in
    struct.storeF eStateMachine "lastSeq" (![ptrT] "s") "$a0";;
    let: "$a0" := NewMap uint64T (slice.T byteT) #() in
    struct.storeF eStateMachine "lastReply" (![ptrT] "s") "$a0";;
    let: "$a0" := #0 in
    struct.storeF eStateMachine "nextCID" (![ptrT] "s") "$a0";;
    let: "$a0" := ![ptrT] "sm" in
    struct.storeF eStateMachine "sm" (![ptrT] "s") "$a0";;
    return: (struct.new storage.InMemoryStateMachine [
       "ApplyReadonly" ::= eStateMachine__applyReadonly (![ptrT] "s");
       "ApplyVolatile" ::= eStateMachine__applyVolatile (![ptrT] "s");
       "GetState" ::= (λ: <>,
         return: (eStateMachine__getState (![ptrT] "s"))
         );
       "SetState" ::= eStateMachine__setState (![ptrT] "s")
     ]).

Definition Clerk := struct.decl [
  "ck" :: ptrT;
  "cid" :: uint64T;
  "seq" :: uint64T
].

Definition MakeClerk: val :=
  rec: "MakeClerk" "confHosts" :=
    let: "confHosts" := ref_to (slice.T uint64T) "confHosts" in
    let: "ck" := ref_zero ptrT in
    let: "$a0" := struct.alloc Clerk (zero_val (struct.t Clerk)) in
    "ck" <-[ptrT] "$a0";;
    let: "$a0" := clerk.Make (![slice.T uint64T] "confHosts") in
    struct.storeF Clerk "ck" (![ptrT] "ck") "$a0";;
    let: "v" := ref_zero (slice.T byteT) in
    let: "$a0" := NewSlice byteT #1 in
    "v" <-[slice.T byteT] "$a0";;
    let: "$a0" := OPTYPE_GETFRESHCID in
    SliceSet byteT (![slice.T byteT] "v") #0 "$a0";;
    let: "cidEnc" := ref_zero (slice.T byteT) in
    let: "$a0" := clerk.Clerk__Apply (struct.loadF Clerk "ck" (![ptrT] "ck")) (![slice.T byteT] "v") in
    "cidEnc" <-[slice.T byteT] "$a0";;
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "cidEnc") in
    "$a1";;
    struct.storeF Clerk "cid" (![ptrT] "ck") "$a0";;
    let: "$a0" := #1 in
    struct.storeF Clerk "seq" (![ptrT] "ck") "$a0";;
    return: (![ptrT] "ck").

Definition Clerk__ApplyExactlyOnce: val :=
  rec: "Clerk__ApplyExactlyOnce" "ck" "req" :=
    let: "req" := ref_to (slice.T byteT) "req" in
    let: "ck" := ref_to ptrT "ck" in
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #1 #1) in
    let: "$a0" := OPTYPE_RW in
    SliceSet byteT (![slice.T byteT] "enc") #0 "$a0";;
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF Clerk "cid" (![ptrT] "ck")) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF Clerk "seq" (![ptrT] "ck")) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteBytes (![slice.T byteT] "enc") (![slice.T byteT] "req") in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := std.SumAssumeNoOverflow (struct.loadF Clerk "seq" (![ptrT] "ck")) #1 in
    struct.storeF Clerk "seq" (![ptrT] "ck") "$a0";;
    return: (clerk.Clerk__Apply (struct.loadF Clerk "ck" (![ptrT] "ck")) (![slice.T byteT] "enc")).

Definition Clerk__ApplyReadonly: val :=
  rec: "Clerk__ApplyReadonly" "ck" "req" :=
    let: "req" := ref_to (slice.T byteT) "req" in
    let: "ck" := ref_to ptrT "ck" in
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #1 #1) in
    let: "$a0" := OPTYPE_RO in
    SliceSet byteT (![slice.T byteT] "enc") #0 "$a0";;
    let: "$a0" := marshal.WriteBytes (![slice.T byteT] "enc") (![slice.T byteT] "req") in
    "enc" <-[slice.T byteT] "$a0";;
    return: (clerk.Clerk__ApplyRo (struct.loadF Clerk "ck" (![ptrT] "ck")) (![slice.T byteT] "enc")).

(* vsm.go *)
