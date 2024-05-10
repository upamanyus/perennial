(* autogenerated from github.com/mit-pdos/gokv/paxi/reconf *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.mit_dash_pdos.gokv.connman.
From Goose Require github_dot_com.mit_dash_pdos.gokv.grove__ffi.
From Goose Require github_dot_com.mit_dash_pdos.gokv.urpc.
From Goose Require github_dot_com.tchajed.goose.machine.
From Goose Require github_dot_com.tchajed.marshal.
From Goose Require log.
From Goose Require sync.

From Perennial.goose_lang Require Import ffi.grove_prelude.

(* 0_quorums.go *)

Definition Config := struct.decl [
  "Members" :: slice.T uint64T;
  "NextMembers" :: slice.T uint64T
].

(* Returns some integer i with the property that
   there exists W such that W contains a majority of members and of nextMembers,
   and every node n in W has indices[n] >= i.
   Even more precisely, it returns the largest such i. *)
Definition GetHighestIndexOfQuorum: val :=
  rec: "GetHighestIndexOfQuorum" "config" "indices" :=
    let: "orderedIndices" := ref_to (slice.T uint64T) (NewSlice uint64T (((slice.len (struct.loadF Config "Members" (![ptrT] "config"))) + #1) `quot` #2)) in
    ForSlice uint64T <> "m" (struct.loadF Config "Members" (![ptrT] "config"))
      (let: "indexToInsert" := ref_zero uint64T in
      let: "$a0" := Fst (MapGet (![mapT uint64T] "indices") (![uint64T] "m")) in
      "indexToInsert" <-[uint64T] "$a0";;
      ForSlice uint64T "i" <> (![slice.T uint64T] "orderedIndices")
        ((if: (SliceGet uint64T (![slice.T uint64T] "orderedIndices") (![intT] "i")) > (![uint64T] "indexToInsert")
        then
          (let: "j" := ref_zero uint64T in
          let: "$a0" := ![intT] "i" in
          "j" <-[uint64T] "$a0";;
          (for: (λ: <>, (![uint64T] "j") < ((slice.len (![slice.T uint64T] "orderedIndices")) - #1)); (λ: <>, "j" <-[uint64T] ((![uint64T] "j") + #1);;
          #()) := λ: <>,
            let: "$a0" := SliceGet uint64T (![slice.T uint64T] "orderedIndices") (![intT] "i") in
            SliceSet uint64T (![slice.T uint64T] "orderedIndices") ((![intT] "i") + #1) "$a0";;
            #()))
        else #());;
        #());;
      #());;
    let: "ret" := ref_zero uint64T in
    let: "$a0" := SliceGet uint64T (![slice.T uint64T] "orderedIndices") ((slice.len (struct.loadF Config "Members" (![ptrT] "config"))) - #1) in
    "ret" <-[uint64T] "$a0";;
    (if: (slice.len (struct.loadF Config "NextMembers" (![ptrT] "config"))) = #0
    then return: (![uint64T] "ret")
    else #());;
    return: (#0).

(* Returns true iff w is a (write) quorum for the config `config`. *)
Definition IsQuorum: val :=
  rec: "IsQuorum" "config" "w" :=
    let: "num" := ref (zero_val uint64T) in
    ForSlice uint64T <> "member" (struct.loadF Config "Members" (![ptrT] "config"))
      ((if: Fst (MapGet (![mapT boolT] "w") (![uint64T] "member"))
      then
        "num" <-[uint64T] ((![uint64T] "num") + #1);;
        #()
      else #());;
      #());;
    (if: (#2 * (![uint64T] "num")) ≤ (slice.len (struct.loadF Config "Members" (![ptrT] "config")))
    then return: (#false)
    else #());;
    (if: (slice.len (struct.loadF Config "NextMembers" (![ptrT] "config"))) = #0
    then return: (#true)
    else #());;
    let: "$a0" := #0 in
    "num" <-[uint64T] "$a0";;
    ForSlice uint64T <> "member" (struct.loadF Config "NextMembers" (![ptrT] "config"))
      ((if: Fst (MapGet (![mapT boolT] "w") (![uint64T] "member"))
      then
        "num" <-[uint64T] ((![uint64T] "num") + #1);;
        #()
      else #());;
      #());;
    (if: (#2 * (![uint64T] "num")) ≤ (slice.len (struct.loadF Config "NextMembers" (![ptrT] "config")))
    then return: (#false)
    else #());;
    return: (#true).

Definition Config__ForEachMember: val :=
  rec: "Config__ForEachMember" "c" "f" :=
    ForSlice uint64T <> "member" (struct.loadF Config "Members" (![ptrT] "c"))
      ((![(arrowT unitT unitT)] "f") (![uint64T] "member");;
      #());;
    ForSlice uint64T <> "member" (struct.loadF Config "NextMembers" (![ptrT] "c"))
      ((![(arrowT unitT unitT)] "f") (![uint64T] "member");;
      #());;
    #().

Definition Config__Contains: val :=
  rec: "Config__Contains" "c" "m" :=
    let: "ret" := ref_to boolT #false in
    ForSlice uint64T <> "member" (struct.loadF Config "Members" (![ptrT] "c"))
      ((if: (![uint64T] "member") = (![uint64T] "m")
      then
        let: "$a0" := #true in
        "ret" <-[boolT] "$a0";;
        #()
      else #());;
      #());;
    ForSlice uint64T <> "member" (struct.loadF Config "NextMembers" (![ptrT] "c"))
      ((if: (![uint64T] "member") = (![uint64T] "m")
      then
        let: "$a0" := #true in
        "ret" <-[boolT] "$a0";;
        #()
      else #());;
      #());;
    return: (![boolT] "ret").

(* 1_marshal.go *)

Definition EncConfig: val :=
  rec: "EncConfig" "pre" "conf" :=
    let: "enc" := ref_to (slice.T byteT) (![slice.T byteT] "pre") in
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (slice.len (struct.loadF Config "Members" (![ptrT] "conf"))) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (slice.len (struct.loadF Config "NextMembers" (![ptrT] "conf"))) in
    "enc" <-[slice.T byteT] "$a0";;
    ForSlice uint64T <> "member" (struct.loadF Config "Members" (![ptrT] "conf"))
      (let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (![uint64T] "member") in
      "enc" <-[slice.T byteT] "$a0";;
      #());;
    ForSlice uint64T <> "member" (struct.loadF Config "NextMembers" (![ptrT] "conf"))
      (let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (![uint64T] "member") in
      "enc" <-[slice.T byteT] "$a0";;
      #());;
    return: (![slice.T byteT] "enc").

Definition DecConfig: val :=
  rec: "DecConfig" "encoded" :=
    let: "dec" := ref_to (slice.T byteT) (![slice.T byteT] "encoded") in
    let: "conf" := ref_zero ptrT in
    let: "$a0" := struct.alloc Config (zero_val (struct.t Config)) in
    "conf" <-[ptrT] "$a0";;
    let: "numMembers" := ref_zero uint64T in
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "dec") in
    "dec" <-[slice.T byteT] "$a1";;
    "numMembers" <-[uint64T] "$a0";;
    let: "numNextMembers" := ref_zero uint64T in
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "dec") in
    "dec" <-[slice.T byteT] "$a1";;
    "numNextMembers" <-[uint64T] "$a0";;
    let: "$a0" := NewSlice uint64T (![uint64T] "numMembers") in
    struct.storeF Config "Members" (![ptrT] "conf") "$a0";;
    let: "$a0" := NewSlice uint64T (![uint64T] "numNextMembers") in
    struct.storeF Config "NextMembers" (![ptrT] "conf") "$a0";;
    ForSlice uint64T "i" <> (struct.loadF Config "Members" (![ptrT] "conf"))
      (let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "dec") in
      "dec" <-[slice.T byteT] "$a1";;
      SliceSet uint64T (struct.loadF Config "Members" (![ptrT] "conf")) (![intT] "i") "$a0";;
      #());;
    ForSlice uint64T "i" <> (struct.loadF Config "NextMembers" (![ptrT] "conf"))
      (let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "dec") in
      "dec" <-[slice.T byteT] "$a1";;
      SliceSet uint64T (struct.loadF Config "Members" (![ptrT] "conf")) (![intT] "i") "$a0";;
      #());;
    return: (![ptrT] "conf", ![slice.T byteT] "dec").

Definition MonotonicValue := struct.decl [
  "version" :: uint64T;
  "val" :: slice.T byteT;
  "conf" :: ptrT
].

Definition EncMonotonicValue: val :=
  rec: "EncMonotonicValue" "pre" "mval" :=
    let: "enc" := ref_to (slice.T byteT) (![slice.T byteT] "pre") in
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF MonotonicValue "version" (![ptrT] "mval")) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (slice.len (struct.loadF MonotonicValue "val" (![ptrT] "mval"))) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteBytes (![slice.T byteT] "enc") (struct.loadF MonotonicValue "val" (![ptrT] "mval")) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := EncConfig (![slice.T byteT] "enc") (struct.loadF MonotonicValue "conf" (![ptrT] "mval")) in
    "enc" <-[slice.T byteT] "$a0";;
    return: (![slice.T byteT] "enc").

Definition DecMonotonicValue: val :=
  rec: "DecMonotonicValue" "encoded" :=
    let: "mval" := ref_zero ptrT in
    let: "$a0" := struct.alloc MonotonicValue (zero_val (struct.t MonotonicValue)) in
    "mval" <-[ptrT] "$a0";;
    let: "dec" := ref_to (slice.T byteT) (![slice.T byteT] "encoded") in
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "dec") in
    "dec" <-[slice.T byteT] "$a1";;
    struct.storeF MonotonicValue "version" (![ptrT] "mval") "$a0";;
    let: "valLen" := ref_zero uint64T in
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "dec") in
    "dec" <-[slice.T byteT] "$a1";;
    "valLen" <-[uint64T] "$a0";;
    let: "$a0" := SliceTake (![slice.T byteT] "dec") (![uint64T] "valLen") in
    struct.storeF MonotonicValue "val" (![ptrT] "mval") "$a0";;
    let: "$a0" := SliceSkip byteT (![slice.T byteT] "dec") (![uint64T] "valLen") in
    "dec" <-[slice.T byteT] "$a0";;
    let: ("$a0", "$a1") := DecConfig (![slice.T byteT] "dec") in
    "dec" <-[slice.T byteT] "$a1";;
    struct.storeF MonotonicValue "conf" (![ptrT] "mval") "$a0";;
    return: (![ptrT] "mval", ![slice.T byteT] "dec").

Definition PrepareReply := struct.decl [
  "Err" :: uint64T;
  "Term" :: uint64T;
  "Val" :: ptrT
].

Definition EncPrepareReply: val :=
  rec: "EncPrepareReply" "pre" "reply" :=
    let: "enc" := ref_to (slice.T byteT) (![slice.T byteT] "pre") in
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF PrepareReply "Err" (![ptrT] "reply")) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF PrepareReply "Term" (![ptrT] "reply")) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := EncMonotonicValue (![slice.T byteT] "enc") (struct.loadF PrepareReply "Val" (![ptrT] "reply")) in
    "enc" <-[slice.T byteT] "$a0";;
    return: (![slice.T byteT] "enc").

Definition DecPrepareReply: val :=
  rec: "DecPrepareReply" "encoded" :=
    let: "dec" := ref_to (slice.T byteT) (![slice.T byteT] "encoded") in
    let: "reply" := ref_zero ptrT in
    let: "$a0" := struct.alloc PrepareReply (zero_val (struct.t PrepareReply)) in
    "reply" <-[ptrT] "$a0";;
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "dec") in
    "dec" <-[slice.T byteT] "$a1";;
    struct.storeF PrepareReply "Err" (![ptrT] "reply") "$a0";;
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "dec") in
    "dec" <-[slice.T byteT] "$a1";;
    struct.storeF PrepareReply "Term" (![ptrT] "reply") "$a0";;
    let: ("$a0", "$a1") := DecMonotonicValue (![slice.T byteT] "dec") in
    "dec" <-[slice.T byteT] "$a1";;
    struct.storeF PrepareReply "Val" (![ptrT] "reply") "$a0";;
    return: (![ptrT] "reply").

Definition ProposeArgs := struct.decl [
  "Term" :: uint64T;
  "Val" :: ptrT
].

Definition EncProposeArgs: val :=
  rec: "EncProposeArgs" "args" :=
    let: "enc" := ref_to (slice.T byteT) (NewSlice byteT #0) in
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF ProposeArgs "Term" (![ptrT] "args")) in
    "enc" <-[slice.T byteT] "$a0";;
    let: "$a0" := EncMonotonicValue (![slice.T byteT] "enc") (struct.loadF ProposeArgs "Val" (![ptrT] "args")) in
    "enc" <-[slice.T byteT] "$a0";;
    return: (![slice.T byteT] "enc").

Definition DecProposeArgs: val :=
  rec: "DecProposeArgs" "encoded" :=
    let: "dec" := ref_to (slice.T byteT) (![slice.T byteT] "encoded") in
    let: "args" := ref_zero ptrT in
    let: "$a0" := struct.alloc ProposeArgs (zero_val (struct.t ProposeArgs)) in
    "args" <-[ptrT] "$a0";;
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "dec") in
    "dec" <-[slice.T byteT] "$a1";;
    struct.storeF ProposeArgs "Term" (![ptrT] "args") "$a0";;
    let: ("$a0", "$a1") := DecMonotonicValue (![slice.T byteT] "dec") in
    "dec" <-[slice.T byteT] "$a1";;
    struct.storeF ProposeArgs "Val" (![ptrT] "args") "$a0";;
    return: (![ptrT] "args", ![slice.T byteT] "dec").

Definition TryCommitReply := struct.decl [
  "err" :: uint64T;
  "version" :: uint64T
].

Definition EncMembers: val :=
  rec: "EncMembers" "members" :=
    let: "enc" := ref_to (slice.T byteT) (NewSlice byteT #0) in
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (slice.len (![slice.T uint64T] "members")) in
    "enc" <-[slice.T byteT] "$a0";;
    ForSlice uint64T <> "member" (![slice.T uint64T] "members")
      (let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (![uint64T] "member") in
      "enc" <-[slice.T byteT] "$a0";;
      #());;
    return: (![slice.T byteT] "enc").

Definition DecMembers: val :=
  rec: "DecMembers" "encoded" :=
    let: "dec" := ref_to (slice.T byteT) (![slice.T byteT] "encoded") in
    let: "numMembers" := ref_zero uint64T in
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "dec") in
    "dec" <-[slice.T byteT] "$a1";;
    "numMembers" <-[uint64T] "$a0";;
    let: "members" := ref_zero (slice.T uint64T) in
    let: "$a0" := NewSlice uint64T (![uint64T] "numMembers") in
    "members" <-[slice.T uint64T] "$a0";;
    ForSlice uint64T "i" <> (![slice.T uint64T] "members")
      (let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "dec") in
      "dec" <-[slice.T byteT] "$a1";;
      SliceSet uint64T (![slice.T uint64T] "members") (![intT] "i") "$a0";;
      #());;
    return: (![slice.T uint64T] "members", ![slice.T byteT] "dec").

(* client.go *)

Definition ClerkPool := struct.decl [
  "cl" :: ptrT
].

Definition RPC_PREPARE : expr := #0.

Definition RPC_PROPOSE : expr := #1.

Definition RPC_TRY_COMMIT_VAL : expr := #2.

Definition RPC_TRY_CONFIG_CHANGE : expr := #3.

Definition MakeClerkPool: val :=
  rec: "MakeClerkPool" <> :=
    return: (struct.new ClerkPool [
       "cl" ::= connman.MakeConnMan #()
     ]).

Definition ClerkPool__PrepareRPC: val :=
  rec: "ClerkPool__PrepareRPC" "ck" "srv" "newTerm" "reply_ptr" :=
    let: "raw_reply" := ref_zero ptrT in
    let: "$a0" := ref (zero_val (slice.T byteT)) in
    "raw_reply" <-[ptrT] "$a0";;
    connman.ConnMan__CallAtLeastOnce (struct.loadF ClerkPool "cl" (![ptrT] "ck")) (![uint64T] "srv") RPC_PREPARE (marshal.WriteInt (NewSlice byteT #0) (![uint64T] "newTerm")) (![ptrT] "raw_reply") #10;;
    let: "$a0" := struct.load PrepareReply (DecPrepareReply (![slice.T byteT] (![ptrT] "raw_reply"))) in
    struct.store PrepareReply (![ptrT] "reply_ptr") "$a0";;
    #().

Definition ClerkPool__ProposeRPC: val :=
  rec: "ClerkPool__ProposeRPC" "ck" "srv" "term" "val" :=
    let: "args" := ref_zero ptrT in
    let: "$a0" := struct.new ProposeArgs [
      "Term" ::= ![uint64T] "term";
      "Val" ::= ![ptrT] "val"
    ] in
    "args" <-[ptrT] "$a0";;
    let: "raw_reply" := ref_zero ptrT in
    let: "$a0" := ref (zero_val (slice.T byteT)) in
    "raw_reply" <-[ptrT] "$a0";;
    connman.ConnMan__CallAtLeastOnce (struct.loadF ClerkPool "cl" (![ptrT] "ck")) (![uint64T] "srv") RPC_PROPOSE (EncProposeArgs (![ptrT] "args")) (![ptrT] "raw_reply") #10;;
    let: <> := ref_zero (slice.T byteT) in
    let: "err" := ref_zero uint64T in
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] (![ptrT] "raw_reply")) in
    "$a1";;
    "err" <-[uint64T] "$a0";;
    return: ((![uint64T] "err") = #0).

Definition ClerkPool__TryCommitVal: val :=
  rec: "ClerkPool__TryCommitVal" "ck" "srv" "v" :=
    let: "raw_reply" := ref_zero ptrT in
    let: "$a0" := ref (zero_val (slice.T byteT)) in
    "raw_reply" <-[ptrT] "$a0";;
    connman.ConnMan__CallAtLeastOnce (struct.loadF ClerkPool "cl" (![ptrT] "ck")) (![uint64T] "srv") RPC_TRY_COMMIT_VAL (![slice.T byteT] "v") (![ptrT] "raw_reply") #1000;;
    let: <> := ref_zero (slice.T byteT) in
    let: "err" := ref_zero uint64T in
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] (![ptrT] "raw_reply")) in
    "$a1";;
    "err" <-[uint64T] "$a0";;
    return: ((![uint64T] "err") = #0).

Definition ClerkPool__TryConfigChange: val :=
  rec: "ClerkPool__TryConfigChange" "ck" "srv" "newMembers" :=
    let: "raw_args" := ref_zero (slice.T byteT) in
    let: "$a0" := EncMembers (![slice.T uint64T] "newMembers") in
    "raw_args" <-[slice.T byteT] "$a0";;
    let: "raw_reply" := ref_zero ptrT in
    let: "$a0" := ref (zero_val (slice.T byteT)) in
    "raw_reply" <-[ptrT] "$a0";;
    connman.ConnMan__CallAtLeastOnce (struct.loadF ClerkPool "cl" (![ptrT] "ck")) (![uint64T] "srv") RPC_TRY_CONFIG_CHANGE (![slice.T byteT] "raw_args") (![ptrT] "raw_reply") #50;;
    let: <> := ref_zero (slice.T byteT) in
    let: "err" := ref_zero uint64T in
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] (![ptrT] "raw_reply")) in
    "$a1";;
    "err" <-[uint64T] "$a0";;
    return: ((![uint64T] "err") = #0).

(* server.go *)

Definition MonotonicValue__GreaterThan: val :=
  rec: "MonotonicValue__GreaterThan" "lhs" "rhs" :=
    return: ((struct.loadF MonotonicValue "version" (![ptrT] "lhs")) > (struct.loadF MonotonicValue "version" (![ptrT] "rhs"))).

Definition Replica := struct.decl [
  "mu" :: ptrT;
  "promisedTerm" :: uint64T;
  "acceptedTerm" :: uint64T;
  "acceptedMVal" :: ptrT;
  "clerkPool" :: ptrT;
  "isLeader" :: boolT
].

Definition ENone : expr := #0.

Definition ETermStale : expr := #1.

Definition ENotLeader : expr := #2.

Definition EQuorumFailed : expr := #3.

Definition Replica__PrepareRPC: val :=
  rec: "Replica__PrepareRPC" "r" "term" "reply" :=
    sync.Mutex__Lock (struct.loadF Replica "mu" (![ptrT] "r"));;
    (if: (![uint64T] "term") > (struct.loadF Replica "promisedTerm" (![ptrT] "r"))
    then
      let: "$a0" := ![uint64T] "term" in
      struct.storeF Replica "promisedTerm" (![ptrT] "r") "$a0";;
      let: "$a0" := struct.loadF Replica "acceptedTerm" (![ptrT] "r") in
      struct.storeF PrepareReply "Term" (![ptrT] "reply") "$a0";;
      let: "$a0" := struct.loadF Replica "acceptedMVal" (![ptrT] "r") in
      struct.storeF PrepareReply "Val" (![ptrT] "reply") "$a0";;
      let: "$a0" := ENone in
      struct.storeF PrepareReply "Err" (![ptrT] "reply") "$a0";;
      #()
    else
      let: "$a0" := ETermStale in
      struct.storeF PrepareReply "Err" (![ptrT] "reply") "$a0";;
      let: "$a0" := struct.alloc MonotonicValue (zero_val (struct.t MonotonicValue)) in
      struct.storeF PrepareReply "Val" (![ptrT] "reply") "$a0";;
      let: "$a0" := struct.alloc Config (zero_val (struct.t Config)) in
      struct.storeF MonotonicValue "conf" (struct.loadF PrepareReply "Val" (![ptrT] "reply")) "$a0";;
      let: "$a0" := struct.loadF Replica "promisedTerm" (![ptrT] "r") in
      struct.storeF PrepareReply "Term" (![ptrT] "reply") "$a0";;
      #());;
    sync.Mutex__Unlock (struct.loadF Replica "mu" (![ptrT] "r"));;
    #().

Definition Replica__ProposeRPC: val :=
  rec: "Replica__ProposeRPC" "r" "term" "v" :=
    sync.Mutex__Lock (struct.loadF Replica "mu" (![ptrT] "r"));;
    (if: (![uint64T] "term") ≥ (struct.loadF Replica "promisedTerm" (![ptrT] "r"))
    then
      let: "$a0" := ![uint64T] "term" in
      struct.storeF Replica "promisedTerm" (![ptrT] "r") "$a0";;
      let: "$a0" := ![uint64T] "term" in
      struct.storeF Replica "acceptedTerm" (![ptrT] "r") "$a0";;
      (if: MonotonicValue__GreaterThan (![ptrT] "v") (struct.loadF Replica "acceptedMVal" (![ptrT] "r"))
      then
        let: "$a0" := ![ptrT] "v" in
        struct.storeF Replica "acceptedMVal" (![ptrT] "r") "$a0";;
        #()
      else #());;
      sync.Mutex__Unlock (struct.loadF Replica "mu" (![ptrT] "r"));;
      return: (ENone)
    else
      sync.Mutex__Unlock (struct.loadF Replica "mu" (![ptrT] "r"));;
      return: (ETermStale));;
    #().

Definition Replica__TryBecomeLeader: val :=
  rec: "Replica__TryBecomeLeader" "r" :=
    sync.Mutex__Lock (struct.loadF Replica "mu" (![ptrT] "r"));;
    let: "newTerm" := ref_zero uint64T in
    let: "$a0" := (struct.loadF Replica "promisedTerm" (![ptrT] "r")) + #1 in
    "newTerm" <-[uint64T] "$a0";;
    let: "$a0" := ![uint64T] "newTerm" in
    struct.storeF Replica "promisedTerm" (![ptrT] "r") "$a0";;
    let: "highestTerm" := ref (zero_val uint64T) in
    let: "$a0" := #0 in
    "highestTerm" <-[uint64T] "$a0";;
    let: "highestVal" := ref (zero_val ptrT) in
    let: "$a0" := struct.loadF Replica "acceptedMVal" (![ptrT] "r") in
    "highestVal" <-[ptrT] "$a0";;
    let: "conf" := ref_zero ptrT in
    let: "$a0" := struct.loadF MonotonicValue "conf" (struct.loadF Replica "acceptedMVal" (![ptrT] "r")) in
    "conf" <-[ptrT] "$a0";;
    sync.Mutex__Unlock (struct.loadF Replica "mu" (![ptrT] "r"));;
    let: "mu" := ref_zero ptrT in
    let: "$a0" := struct.alloc sync.Mutex (zero_val (struct.t sync.Mutex)) in
    "mu" <-[ptrT] "$a0";;
    let: "prepared" := ref_zero (mapT boolT) in
    let: "$a0" := NewMap uint64T boolT #() in
    "prepared" <-[mapT boolT] "$a0";;
    Config__ForEachMember (![ptrT] "conf") (λ: "addr",
      Fork (let: "reply_ptr" := ref_zero ptrT in
            let: "$a0" := struct.alloc PrepareReply (zero_val (struct.t PrepareReply)) in
            "reply_ptr" <-[ptrT] "$a0";;
            ClerkPool__PrepareRPC (struct.loadF Replica "clerkPool" (![ptrT] "r")) (![uint64T] "addr") (![uint64T] "newTerm") (![ptrT] "reply_ptr");;
            (if: (struct.loadF PrepareReply "Err" (![ptrT] "reply_ptr")) = ENone
            then
              sync.Mutex__Lock (![ptrT] "mu");;
              let: "$a0" := #true in
              MapInsert (![mapT boolT] "prepared") (![uint64T] "addr") "$a0";;
              (if: (struct.loadF PrepareReply "Term" (![ptrT] "reply_ptr")) > (![uint64T] "highestTerm")
              then
                let: "$a0" := struct.loadF PrepareReply "Val" (![ptrT] "reply_ptr") in
                "highestVal" <-[ptrT] "$a0";;
                #()
              else
                (if: (struct.loadF PrepareReply "Term" (![ptrT] "reply_ptr")) = (![uint64T] "highestTerm")
                then
                  (if: MonotonicValue__GreaterThan (![ptrT] "highestVal") (struct.loadF PrepareReply "Val" (![ptrT] "reply_ptr"))
                  then
                    let: "$a0" := struct.loadF PrepareReply "Val" (![ptrT] "reply_ptr") in
                    "highestVal" <-[ptrT] "$a0";;
                    #()
                  else #());;
                  #()
                else #());;
                #());;
              sync.Mutex__Unlock (![ptrT] "mu");;
              #()
            else #());;
            #());;
      #()
      );;
    machine.Sleep (#50 * #1000000);;
    sync.Mutex__Lock (![ptrT] "mu");;
    (if: IsQuorum (struct.loadF MonotonicValue "conf" (![ptrT] "highestVal")) (![mapT boolT] "prepared")
    then
      sync.Mutex__Lock (struct.loadF Replica "mu" (![ptrT] "r"));;
      (if: (struct.loadF Replica "promisedTerm" (![ptrT] "r")) = (![uint64T] "newTerm")
      then
        let: "$a0" := ![ptrT] "highestVal" in
        struct.storeF Replica "acceptedMVal" (![ptrT] "r") "$a0";;
        let: "$a0" := #true in
        struct.storeF Replica "isLeader" (![ptrT] "r") "$a0";;
        #()
      else #());;
      sync.Mutex__Unlock (struct.loadF Replica "mu" (![ptrT] "r"));;
      sync.Mutex__Unlock (![ptrT] "mu");;
      return: (#true)
    else #());;
    sync.Mutex__Unlock (![ptrT] "mu");;
    return: (#false).

(* Returns true iff there was an error;
   The error is either that r is not currently a primary, or that r was unable
   to commit the value within one round of commits.

   mvalModifier is not allowed to modify the version number in the given mval. *)
Definition Replica__tryCommit: val :=
  rec: "Replica__tryCommit" "r" "mvalModifier" "reply" :=
    sync.Mutex__Lock (struct.loadF Replica "mu" (![ptrT] "r"));;
    (if: (~ (struct.loadF Replica "isLeader" (![ptrT] "r")))
    then
      sync.Mutex__Unlock (struct.loadF Replica "mu" (![ptrT] "r"));;
      let: "$a0" := ENotLeader in
      struct.storeF TryCommitReply "err" (![ptrT] "reply") "$a0";;
      return: (#())
    else #());;
    (![(arrowT unitT unitT)] "mvalModifier") (struct.loadF Replica "acceptedMVal" (![ptrT] "r"));;
    log.Printf #(str"Trying to commit value; node state: %!!(MISSING)!(MISSING)v(MISSING)
    ") (![ptrT] "r");;
    struct.storeF MonotonicValue "version" (struct.loadF Replica "acceptedMVal" (![ptrT] "r")) ((struct.loadF MonotonicValue "version" (struct.loadF Replica "acceptedMVal" (![ptrT] "r"))) + #1);;
    let: "term" := ref_zero uint64T in
    let: "$a0" := struct.loadF Replica "promisedTerm" (![ptrT] "r") in
    "term" <-[uint64T] "$a0";;
    let: "mval" := ref_zero ptrT in
    let: "$a0" := struct.loadF Replica "acceptedMVal" (![ptrT] "r") in
    "mval" <-[ptrT] "$a0";;
    sync.Mutex__Unlock (struct.loadF Replica "mu" (![ptrT] "r"));;
    let: "mu" := ref_zero ptrT in
    let: "$a0" := struct.alloc sync.Mutex (zero_val (struct.t sync.Mutex)) in
    "mu" <-[ptrT] "$a0";;
    let: "accepted" := ref_zero (mapT boolT) in
    let: "$a0" := NewMap uint64T boolT #() in
    "accepted" <-[mapT boolT] "$a0";;
    Config__ForEachMember (struct.loadF MonotonicValue "conf" (![ptrT] "mval")) (λ: "addr",
      Fork ((if: ClerkPool__ProposeRPC (struct.loadF Replica "clerkPool" (![ptrT] "r")) (![uint64T] "addr") (![uint64T] "term") (![ptrT] "mval")
            then
              sync.Mutex__Lock (![ptrT] "mu");;
              let: "$a0" := #true in
              MapInsert (![mapT boolT] "accepted") (![uint64T] "addr") "$a0";;
              sync.Mutex__Unlock (![ptrT] "mu");;
              #()
            else #());;
            #());;
      #()
      );;
    machine.Sleep (#100 * #1000000);;
    sync.Mutex__Lock (![ptrT] "mu");;
    (if: IsQuorum (struct.loadF MonotonicValue "conf" (![ptrT] "mval")) (![mapT boolT] "accepted")
    then
      let: "$a0" := ENone in
      struct.storeF TryCommitReply "err" (![ptrT] "reply") "$a0";;
      let: "$a0" := struct.loadF MonotonicValue "version" (![ptrT] "mval") in
      struct.storeF TryCommitReply "version" (![ptrT] "reply") "$a0";;
      #()
    else
      let: "$a0" := EQuorumFailed in
      struct.storeF TryCommitReply "err" (![ptrT] "reply") "$a0";;
      #());;
    log.Printf #(str"Result of trying to commit: %!!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)v(MISSING)
    ") (![ptrT] "reply");;
    #().

Definition Replica__TryCommitVal: val :=
  rec: "Replica__TryCommitVal" "r" "v" "reply" :=
    sync.Mutex__Lock (struct.loadF Replica "mu" (![ptrT] "r"));;
    (if: (~ (struct.loadF Replica "isLeader" (![ptrT] "r")))
    then
      sync.Mutex__Unlock (struct.loadF Replica "mu" (![ptrT] "r"));;
      Replica__TryBecomeLeader (![ptrT] "r");;
      #()
    else
      sync.Mutex__Unlock (struct.loadF Replica "mu" (![ptrT] "r"));;
      #());;
    Replica__tryCommit (![ptrT] "r") (λ: "mval",
      let: "$a0" := ![slice.T byteT] "v" in
      struct.storeF MonotonicValue "val" (![ptrT] "mval") "$a0";;
      #()
      ) (![ptrT] "reply");;
    #().

(* requires that newConfig has overlapping quorums with r.config *)
Definition Replica__TryEnterNewConfig: val :=
  rec: "Replica__TryEnterNewConfig" "r" "newMembers" :=
    let: "reply" := ref_zero ptrT in
    let: "$a0" := struct.alloc TryCommitReply (zero_val (struct.t TryCommitReply)) in
    "reply" <-[ptrT] "$a0";;
    Replica__tryCommit (![ptrT] "r") (λ: "mval",
      (if: (slice.len (struct.loadF Config "NextMembers" (struct.loadF MonotonicValue "conf" (![ptrT] "mval")))) = #0
      then
        let: "$a0" := ![slice.T uint64T] "newMembers" in
        struct.storeF Config "NextMembers" (struct.loadF MonotonicValue "conf" (![ptrT] "mval")) "$a0";;
        #()
      else #());;
      #()
      ) (![ptrT] "reply");;
    Replica__tryCommit (![ptrT] "r") (λ: "mval",
      (if: (slice.len (struct.loadF Config "NextMembers" (struct.loadF MonotonicValue "conf" (![ptrT] "mval")))) ≠ #0
      then
        let: "$a0" := struct.loadF Config "NextMembers" (struct.loadF MonotonicValue "conf" (![ptrT] "mval")) in
        struct.storeF Config "Members" (struct.loadF MonotonicValue "conf" (![ptrT] "mval")) "$a0";;
        let: "$a0" := NewSlice uint64T #0 in
        struct.storeF Config "NextMembers" (struct.loadF MonotonicValue "conf" (![ptrT] "mval")) "$a0";;
        #()
      else #());;
      #()
      ) (![ptrT] "reply");;
    #().

Definition StartReplicaServer: val :=
  rec: "StartReplicaServer" "me" "initConfig" :=
    let: "s" := ref_zero ptrT in
    let: "$a0" := struct.alloc Replica (zero_val (struct.t Replica)) in
    "s" <-[ptrT] "$a0";;
    let: "$a0" := struct.alloc sync.Mutex (zero_val (struct.t sync.Mutex)) in
    struct.storeF Replica "mu" (![ptrT] "s") "$a0";;
    let: "$a0" := #0 in
    struct.storeF Replica "promisedTerm" (![ptrT] "s") "$a0";;
    let: "$a0" := #0 in
    struct.storeF Replica "acceptedTerm" (![ptrT] "s") "$a0";;
    let: "$a0" := struct.alloc MonotonicValue (zero_val (struct.t MonotonicValue)) in
    struct.storeF Replica "acceptedMVal" (![ptrT] "s") "$a0";;
    let: "$a0" := ![ptrT] "initConfig" in
    struct.storeF MonotonicValue "conf" (struct.loadF Replica "acceptedMVal" (![ptrT] "s")) "$a0";;
    let: "$a0" := MakeClerkPool #() in
    struct.storeF Replica "clerkPool" (![ptrT] "s") "$a0";;
    let: "$a0" := #false in
    struct.storeF Replica "isLeader" (![ptrT] "s") "$a0";;
    let: "handlers" := ref_zero (mapT (arrowT unitT unitT)) in
    let: "$a0" := NewMap uint64T ((slice.T byteT) -> ptrT -> unitT)%!!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)h(MISSING)t #() in
    "handlers" <-[mapT (arrowT unitT unitT)] "$a0";;
    let: "$a0" := (λ: "args" "raw_reply",
      let: <> := ref_zero (slice.T byteT) in
      let: "term" := ref_zero uint64T in
      let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "args") in
      "$a1";;
      "term" <-[uint64T] "$a0";;
      let: "reply" := ref_zero ptrT in
      let: "$a0" := struct.alloc PrepareReply (zero_val (struct.t PrepareReply)) in
      "reply" <-[ptrT] "$a0";;
      Replica__PrepareRPC (![ptrT] "s") (![uint64T] "term") (![ptrT] "reply");;
      let: "$a0" := EncPrepareReply (NewSlice byteT #0) (![ptrT] "reply") in
      (![ptrT] "raw_reply") <-[slice.T byteT] "$a0";;
      DecPrepareReply (![slice.T byteT] (![ptrT] "raw_reply"));;
      #()
      ) in
    MapInsert (![mapT (arrowT unitT unitT)] "handlers") RPC_PREPARE "$a0";;
    let: "$a0" := (λ: "raw_args" "raw_reply",
      let: <> := ref_zero (slice.T byteT) in
      let: "args" := ref_zero ptrT in
      let: ("$a0", "$a1") := DecProposeArgs (![slice.T byteT] "raw_args") in
      "$a1";;
      "args" <-[ptrT] "$a0";;
      let: "reply" := ref_zero uint64T in
      let: "$a0" := Replica__ProposeRPC (![ptrT] "s") (struct.loadF ProposeArgs "Term" (![ptrT] "args")) (struct.loadF ProposeArgs "Val" (![ptrT] "args")) in
      "reply" <-[uint64T] "$a0";;
      let: "$a0" := marshal.WriteInt (NewSliceWithCap byteT #0 #8) (![uint64T] "reply") in
      (![ptrT] "raw_reply") <-[slice.T byteT] "$a0";;
      #()
      ) in
    MapInsert (![mapT (arrowT unitT unitT)] "handlers") RPC_PROPOSE "$a0";;
    let: "$a0" := (λ: "raw_args" "raw_reply",
      log.Println #(str"RPC_TRY_COMMIT_VAL");;
      let: "val" := ref_zero (slice.T byteT) in
      let: "$a0" := ![slice.T byteT] "raw_args" in
      "val" <-[slice.T byteT] "$a0";;
      let: "reply" := ref_zero ptrT in
      let: "$a0" := struct.alloc TryCommitReply (zero_val (struct.t TryCommitReply)) in
      "reply" <-[ptrT] "$a0";;
      Replica__TryCommitVal (![ptrT] "s") (![slice.T byteT] "val") (![ptrT] "reply");;
      let: "$a0" := marshal.WriteInt (NewSliceWithCap byteT #0 #8) (struct.loadF TryCommitReply "err" (![ptrT] "reply")) in
      (![ptrT] "raw_reply") <-[slice.T byteT] "$a0";;
      #()
      ) in
    MapInsert (![mapT (arrowT unitT unitT)] "handlers") RPC_TRY_COMMIT_VAL "$a0";;
    let: "$a0" := (λ: "raw_args" "raw_reply",
      let: <> := ref_zero (slice.T byteT) in
      let: "args" := ref_zero (slice.T uint64T) in
      let: ("$a0", "$a1") := DecMembers (![slice.T byteT] "raw_args") in
      "$a1";;
      "args" <-[slice.T uint64T] "$a0";;
      Replica__TryEnterNewConfig (![ptrT] "s") (![slice.T uint64T] "args");;
      let: "$a0" := NewSlice byteT #0 in
      (![ptrT] "raw_reply") <-[slice.T byteT] "$a0";;
      #()
      ) in
    MapInsert (![mapT (arrowT unitT unitT)] "handlers") RPC_TRY_CONFIG_CHANGE "$a0";;
    let: "r" := ref_zero ptrT in
    let: "$a0" := urpc.MakeServer (![mapT (arrowT unitT unitT)] "handlers") in
    "r" <-[ptrT] "$a0";;
    urpc.Server__Serve (![ptrT] "r") (![uint64T] "me");;
    #().
