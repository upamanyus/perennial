(* autogenerated from github.com/mit-pdos/gokv/fencing/config *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.mit_dash_pdos.gokv.grove__ffi.
From Goose Require github_dot_com.mit_dash_pdos.gokv.urpc.
From Goose Require github_dot_com.tchajed.goose.machine.
From Goose Require github_dot_com.tchajed.marshal.
From Goose Require log.
From Goose Require sync.

From Perennial.goose_lang Require Import ffi.grove_prelude.

(* client.go *)

Definition RPC_ACQUIRE_EPOCH : expr := #0.

Definition RPC_GET : expr := #1.

Definition RPC_HB : expr := #2.

Definition Clerk := struct.decl [
  "cl" :: ptrT
].

(* TIMEOUT_MS from server.go *)

Definition TIMEOUT_MS : expr := #1000.

Definition MILLION : expr := #1000000.

Definition Clerk__HeartbeatThread: val :=
  rec: "Clerk__HeartbeatThread" "ck" "epoch" :=
    let: "epoch" := ref_to uint64T "epoch" in
    let: "ck" := ref_to ptrT "ck" in
    let: "enc" := ref_zero (struct.t marshal.Enc) in
    let: "$a0" := marshal.NewEnc #8 in
    "enc" <-[struct.t marshal.Enc] "$a0";;
    marshal.Enc__PutInt (![struct.t marshal.Enc] "enc") (![uint64T] "epoch");;
    let: "args" := ref_zero (slice.T byteT) in
    let: "$a0" := marshal.Enc__Finish (![struct.t marshal.Enc] "enc") in
    "args" <-[slice.T byteT] "$a0";;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "reply_ptr" := ref_zero ptrT in
      let: "$a0" := ref (zero_val (slice.T byteT)) in
      "reply_ptr" <-[ptrT] "$a0";;
      machine.Sleep ((TIMEOUT_MS * MILLION) `quot` #3);;
      let: "err" := ref_zero uint64T in
      let: "$a0" := urpc.Client__Call (struct.loadF Clerk "cl" (![ptrT] "ck")) RPC_HB (![slice.T byteT] "args") (![ptrT] "reply_ptr") #100 in
      "err" <-[uint64T] "$a0";;
      (if: ((![uint64T] "err") ≠ #0) || ((slice.len (![slice.T byteT] (![ptrT] "reply_ptr"))) ≠ #0)
      then Break
      else #());;
      #()).

Definition Clerk__AcquireEpoch: val :=
  rec: "Clerk__AcquireEpoch" "ck" "newFrontend" :=
    let: "newFrontend" := ref_to uint64T "newFrontend" in
    let: "ck" := ref_to ptrT "ck" in
    let: "enc" := ref_zero (struct.t marshal.Enc) in
    let: "$a0" := marshal.NewEnc #8 in
    "enc" <-[struct.t marshal.Enc] "$a0";;
    marshal.Enc__PutInt (![struct.t marshal.Enc] "enc") (![uint64T] "newFrontend");;
    let: "reply_ptr" := ref_zero ptrT in
    let: "$a0" := ref (zero_val (slice.T byteT)) in
    "reply_ptr" <-[ptrT] "$a0";;
    let: "err" := ref_zero uint64T in
    let: "$a0" := urpc.Client__Call (struct.loadF Clerk "cl" (![ptrT] "ck")) RPC_ACQUIRE_EPOCH (marshal.Enc__Finish (![struct.t marshal.Enc] "enc")) (![ptrT] "reply_ptr") #100 in
    "err" <-[uint64T] "$a0";;
    (if: (![uint64T] "err") ≠ #0
    then
      log.Println #(str"config: client failed to run RPC on config server");;
      machine.Exit #1;;
      #()
    else #());;
    let: "dec" := ref_zero (struct.t marshal.Dec) in
    let: "$a0" := marshal.NewDec (![slice.T byteT] (![ptrT] "reply_ptr")) in
    "dec" <-[struct.t marshal.Dec] "$a0";;
    return: (marshal.Dec__GetInt (![struct.t marshal.Dec] "dec")).

Definition Clerk__Get: val :=
  rec: "Clerk__Get" "ck" :=
    let: "ck" := ref_to ptrT "ck" in
    let: "reply_ptr" := ref_zero ptrT in
    let: "$a0" := ref (zero_val (slice.T byteT)) in
    "reply_ptr" <-[ptrT] "$a0";;
    let: "err" := ref_zero uint64T in
    let: "$a0" := urpc.Client__Call (struct.loadF Clerk "cl" (![ptrT] "ck")) RPC_GET (NewSlice byteT #0) (![ptrT] "reply_ptr") #100 in
    "err" <-[uint64T] "$a0";;
    (if: (![uint64T] "err") ≠ #0
    then
      log.Println #(str"config: client failed to run RPC on config server");;
      machine.Exit #1;;
      #()
    else #());;
    let: "dec" := ref_zero (struct.t marshal.Dec) in
    let: "$a0" := marshal.NewDec (![slice.T byteT] (![ptrT] "reply_ptr")) in
    "dec" <-[struct.t marshal.Dec] "$a0";;
    return: (marshal.Dec__GetInt (![struct.t marshal.Dec] "dec")).

Definition MakeClerk: val :=
  rec: "MakeClerk" "host" :=
    let: "host" := ref_to uint64T "host" in
    let: "ck" := ref_zero ptrT in
    let: "$a0" := struct.alloc Clerk (zero_val (struct.t Clerk)) in
    "ck" <-[ptrT] "$a0";;
    let: "$a0" := urpc.MakeClient (![uint64T] "host") in
    struct.storeF Clerk "cl" (![ptrT] "ck") "$a0";;
    return: (![ptrT] "ck").

(* server.go *)

Definition Server := struct.decl [
  "mu" :: ptrT;
  "data" :: uint64T;
  "currentEpoch" :: uint64T;
  "epoch_cond" :: ptrT;
  "currHolderActive" :: boolT;
  "currHolderActive_cond" :: ptrT;
  "heartbeatExpiration" :: uint64T
].

Definition Server__AcquireEpoch: val :=
  rec: "Server__AcquireEpoch" "s" "newFrontend" :=
    let: "newFrontend" := ref_to uint64T "newFrontend" in
    let: "s" := ref_to ptrT "s" in
    sync.Mutex__Lock (struct.loadF Server "mu" (![ptrT] "s"));;
    (for: (λ: <>, struct.loadF Server "currHolderActive" (![ptrT] "s")); (λ: <>, Skip) := λ: <>,
      sync.Cond__Wait (struct.loadF Server "currHolderActive_cond" (![ptrT] "s"));;
      #()).

Definition Server__HeartbeatListener: val :=
  rec: "Server__HeartbeatListener" "s" :=
    let: "s" := ref_to ptrT "s" in
    let: "epochToWaitFor" := ref_to uint64T #1 in
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      sync.Mutex__Lock (struct.loadF Server "mu" (![ptrT] "s"));;
      (for: (λ: <>, (struct.loadF Server "currentEpoch" (![ptrT] "s")) < (![uint64T] "epochToWaitFor")); (λ: <>, Skip) := λ: <>,
        sync.Cond__Wait (struct.loadF Server "epoch_cond" (![ptrT] "s"));;
        #())).

(* returns true iff successful *)
Definition Server__Heartbeat: val :=
  rec: "Server__Heartbeat" "s" "epoch" :=
    let: "epoch" := ref_to uint64T "epoch" in
    let: "s" := ref_to ptrT "s" in
    sync.Mutex__Lock (struct.loadF Server "mu" (![ptrT] "s"));;
    let: "ret" := ref_to boolT #false in
    (if: (struct.loadF Server "currentEpoch" (![ptrT] "s")) = (![uint64T] "epoch")
    then
      let: "now" := ref_zero uint64T in
      let: "$a0" := machine.TimeNow #() in
      "now" <-[uint64T] "$a0";;
      let: "$a0" := (![uint64T] "now") + TIMEOUT_MS in
      struct.storeF Server "heartbeatExpiration" (![ptrT] "s") "$a0";;
      let: "$a0" := #true in
      "ret" <-[boolT] "$a0";;
      #()
    else #());;
    sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "s"));;
    return: (![boolT] "ret").

(* XXX: don't need to send fencing token here, because client won't need it *)
Definition Server__Get: val :=
  rec: "Server__Get" "s" :=
    let: "s" := ref_to ptrT "s" in
    sync.Mutex__Lock (struct.loadF Server "mu" (![ptrT] "s"));;
    let: "ret" := ref_zero uint64T in
    let: "$a0" := struct.loadF Server "data" (![ptrT] "s") in
    "ret" <-[uint64T] "$a0";;
    sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "s"));;
    return: (![uint64T] "ret").

Definition StartServer: val :=
  rec: "StartServer" "me" :=
    let: "me" := ref_to uint64T "me" in
    let: "s" := ref_zero ptrT in
    let: "$a0" := struct.alloc Server (zero_val (struct.t Server)) in
    "s" <-[ptrT] "$a0";;
    let: "$a0" := struct.alloc sync.Mutex (zero_val (struct.t sync.Mutex)) in
    struct.storeF Server "mu" (![ptrT] "s") "$a0";;
    let: "$a0" := #0 in
    struct.storeF Server "data" (![ptrT] "s") "$a0";;
    let: "$a0" := #0 in
    struct.storeF Server "currentEpoch" (![ptrT] "s") "$a0";;
    let: "$a0" := sync.NewCond (struct.loadF Server "mu" (![ptrT] "s")) in
    struct.storeF Server "epoch_cond" (![ptrT] "s") "$a0";;
    let: "$a0" := #false in
    struct.storeF Server "currHolderActive" (![ptrT] "s") "$a0";;
    let: "$a0" := sync.NewCond (struct.loadF Server "mu" (![ptrT] "s")) in
    struct.storeF Server "currHolderActive_cond" (![ptrT] "s") "$a0";;
    Fork (Server__HeartbeatListener (![ptrT] "s");;
          #());;
    let: "handlers" := ref_zero (mapT (arrowT unitT unitT)) in
    let: "$a0" := NewMap uint64T (arrowT unitT unitT) #() in
    "handlers" <-[mapT (arrowT unitT unitT)] "$a0";;
    let: "$a0" := (λ: "args" "reply",
      let: "dec" := ref_zero (struct.t marshal.Dec) in
      let: "$a0" := marshal.NewDec (![slice.T byteT] "args") in
      "dec" <-[struct.t marshal.Dec] "$a0";;
      let: "enc" := ref_zero (struct.t marshal.Enc) in
      let: "$a0" := marshal.NewEnc #8 in
      "enc" <-[struct.t marshal.Enc] "$a0";;
      marshal.Enc__PutInt (![struct.t marshal.Enc] "enc") (Server__AcquireEpoch (![ptrT] "s") (marshal.Dec__GetInt (![struct.t marshal.Dec] "dec")));;
      let: "$a0" := marshal.Enc__Finish (![struct.t marshal.Enc] "enc") in
      (![ptrT] "reply") <-[slice.T byteT] "$a0";;
      #()
      ) in
    MapInsert (![mapT (arrowT unitT unitT)] "handlers") RPC_ACQUIRE_EPOCH "$a0";;
    let: "$a0" := (λ: "args" "reply",
      let: "enc" := ref_zero (struct.t marshal.Enc) in
      let: "$a0" := marshal.NewEnc #8 in
      "enc" <-[struct.t marshal.Enc] "$a0";;
      marshal.Enc__PutInt (![struct.t marshal.Enc] "enc") (Server__Get (![ptrT] "s"));;
      let: "$a0" := marshal.Enc__Finish (![struct.t marshal.Enc] "enc") in
      (![ptrT] "reply") <-[slice.T byteT] "$a0";;
      #()
      ) in
    MapInsert (![mapT (arrowT unitT unitT)] "handlers") RPC_GET "$a0";;
    let: "$a0" := (λ: "args" "reply",
      let: "dec" := ref_zero (struct.t marshal.Dec) in
      let: "$a0" := marshal.NewDec (![slice.T byteT] "args") in
      "dec" <-[struct.t marshal.Dec] "$a0";;
      (if: Server__Heartbeat (![ptrT] "s") (marshal.Dec__GetInt (![struct.t marshal.Dec] "dec"))
      then
        let: "$a0" := NewSlice byteT #0 in
        (![ptrT] "reply") <-[slice.T byteT] "$a0";;
        #()
      else
        let: "$a0" := NewSlice byteT #1 in
        (![ptrT] "reply") <-[slice.T byteT] "$a0";;
        #());;
      #()
      ) in
    MapInsert (![mapT (arrowT unitT unitT)] "handlers") RPC_HB "$a0";;
    let: "r" := ref_zero ptrT in
    let: "$a0" := urpc.MakeServer (![mapT (arrowT unitT unitT)] "handlers") in
    "r" <-[ptrT] "$a0";;
    urpc.Server__Serve (![ptrT] "r") (![uint64T] "me");;
    #().
