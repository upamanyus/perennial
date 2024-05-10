(* autogenerated from github.com/mit-pdos/gokv/urpc *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.goose_dash_lang.std.
From Goose Require github_dot_com.mit_dash_pdos.gokv.grove__ffi.
From Goose Require github_dot_com.tchajed.goose.machine.
From Goose Require github_dot_com.tchajed.marshal.
From Goose Require log.
From Goose Require sync.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition Server := struct.decl [
  "handlers" :: mapT ((slice.T byteT) -> ptrT -> unitT)%ht
].

Definition Server__rpcHandle: val :=
  rec: "Server__rpcHandle" "srv" "conn" "rpcid" "seqno" "data" :=
    let: "replyData" := ref_zero ptrT in
    let: "$a0" := ref (zero_val (slice.T byteT)) in
    "replyData" <-[ptrT] "$a0";;
    let: "f" := ref_zero (arrowT unitT unitT) in
    let: "$a0" := Fst (MapGet (struct.loadF Server "handlers" (![ptrT] "srv")) (![uint64T] "rpcid")) in
    "f" <-[(arrowT unitT unitT)] "$a0";;
    (![(arrowT unitT unitT)] "f") (![slice.T byteT] "data") (![ptrT] "replyData");;
    let: "data1" := ref_zero (slice.T byteT) in
    let: "$a0" := NewSliceWithCap byteT #0 (#8 + (slice.len (![slice.T byteT] (![ptrT] "replyData")))) in
    "data1" <-[slice.T byteT] "$a0";;
    let: "data2" := ref_zero (slice.T byteT) in
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "data1") (![uint64T] "seqno") in
    "data2" <-[slice.T byteT] "$a0";;
    let: "data3" := ref_zero (slice.T byteT) in
    let: "$a0" := marshal.WriteBytes (![slice.T byteT] "data2") (![slice.T byteT] (![ptrT] "replyData")) in
    "data3" <-[slice.T byteT] "$a0";;
    grove__ffi.Send (![grove_ffi.Connection] "conn") (![slice.T byteT] "data3");;
    #().

Definition MakeServer: val :=
  rec: "MakeServer" "handlers" :=
    return: (struct.new Server [
       "handlers" ::= ![mapT (arrowT unitT unitT)] "handlers"
     ]).

Definition Server__readThread: val :=
  rec: "Server__readThread" "srv" "conn" :=
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "r" := ref_zero (struct.t grove_ffi.ReceiveRet) in
      let: "$a0" := grove__ffi.Receive (![grove_ffi.Connection] "conn") in
      "r" <-[struct.t grove_ffi.ReceiveRet] "$a0";;
      (if: struct.get grove_ffi.ReceiveRet "Err" (![struct.t grove_ffi.ReceiveRet] "r")
      then Break
      else #());;
      let: "data" := ref_zero (slice.T byteT) in
      let: "$a0" := struct.get grove_ffi.ReceiveRet "Data" (![struct.t grove_ffi.ReceiveRet] "r") in
      "data" <-[slice.T byteT] "$a0";;
      let: "rpcid" := ref_zero uint64T in
      let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "data") in
      "data" <-[slice.T byteT] "$a1";;
      "rpcid" <-[uint64T] "$a0";;
      let: "seqno" := ref_zero uint64T in
      let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "data") in
      "data" <-[slice.T byteT] "$a1";;
      "seqno" <-[uint64T] "$a0";;
      let: "req" := ref_zero (slice.T byteT) in
      let: "$a0" := ![slice.T byteT] "data" in
      "req" <-[slice.T byteT] "$a0";;
      Fork (Server__rpcHandle (![ptrT] "srv") (![grove_ffi.Connection] "conn") (![uint64T] "rpcid") (![uint64T] "seqno") (![slice.T byteT] "req");;
            #());;
      Continue).

Definition Server__Serve: val :=
  rec: "Server__Serve" "srv" "host" :=
    let: "listener" := ref_zero grove_ffi.Listener in
    let: "$a0" := grove__ffi.Listen (![uint64T] "host") in
    "listener" <-[grove_ffi.Listener] "$a0";;
    Fork ((for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
            let: "conn" := ref_zero grove_ffi.Connection in
            let: "$a0" := grove__ffi.Accept (![grove_ffi.Listener] "listener") in
            "conn" <-[grove_ffi.Connection] "$a0";;
            Fork (Server__readThread (![ptrT] "srv") (![grove_ffi.Connection] "conn");;
                  #());;
            #()));;
    #().

Definition callbackStateWaiting : expr := #0.

Definition callbackStateDone : expr := #1.

Definition callbackStateAborted : expr := #2.

Definition Callback := struct.decl [
  "reply" :: ptrT;
  "state" :: ptrT;
  "cond" :: ptrT
].

Definition Client := struct.decl [
  "mu" :: ptrT;
  "conn" :: grove_ffi.Connection;
  "seq" :: uint64T;
  "pending" :: mapT ptrT
].

Definition Client__replyThread: val :=
  rec: "Client__replyThread" "cl" :=
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "r" := ref_zero (struct.t grove_ffi.ReceiveRet) in
      let: "$a0" := grove__ffi.Receive (struct.loadF Client "conn" (![ptrT] "cl")) in
      "r" <-[struct.t grove_ffi.ReceiveRet] "$a0";;
      (if: struct.get grove_ffi.ReceiveRet "Err" (![struct.t grove_ffi.ReceiveRet] "r")
      then
        sync.Mutex__Lock (struct.loadF Client "mu" (![ptrT] "cl"));;
        MapIter (struct.loadF Client "pending" (![ptrT] "cl")) (λ: <> "cb",
          let: "$a0" := callbackStateAborted in
          (struct.loadF Callback "state" (![ptrT] "cb")) <-[uint64T] "$a0";;
          sync.Cond__Signal (struct.loadF Callback "cond" (![ptrT] "cb"));;
          #());;
        sync.Mutex__Unlock (struct.loadF Client "mu" (![ptrT] "cl"));;
        Break
      else #());;
      let: "data" := ref_zero (slice.T byteT) in
      let: "$a0" := struct.get grove_ffi.ReceiveRet "Data" (![struct.t grove_ffi.ReceiveRet] "r") in
      "data" <-[slice.T byteT] "$a0";;
      let: "seqno" := ref_zero uint64T in
      let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "data") in
      "data" <-[slice.T byteT] "$a1";;
      "seqno" <-[uint64T] "$a0";;
      let: "reply" := ref_zero (slice.T byteT) in
      let: "$a0" := ![slice.T byteT] "data" in
      "reply" <-[slice.T byteT] "$a0";;
      sync.Mutex__Lock (struct.loadF Client "mu" (![ptrT] "cl"));;
      let: "ok" := ref_zero boolT in
      let: "cb" := ref_zero ptrT in
      let: ("$a0", "$a1") := Fst (MapGet (struct.loadF Client "pending" (![ptrT] "cl")) (![uint64T] "seqno")) in
      "ok" <-[boolT] "$a1";;
      "cb" <-[ptrT] "$a0";;
      (if: ![boolT] "ok"
      then
        MapDelete (struct.loadF Client "pending" (![ptrT] "cl")) (![uint64T] "seqno");;
        let: "$a0" := ![slice.T byteT] "reply" in
        (struct.loadF Callback "reply" (![ptrT] "cb")) <-[slice.T byteT] "$a0";;
        let: "$a0" := callbackStateDone in
        (struct.loadF Callback "state" (![ptrT] "cb")) <-[uint64T] "$a0";;
        sync.Cond__Signal (struct.loadF Callback "cond" (![ptrT] "cb"));;
        #()
      else #());;
      sync.Mutex__Unlock (struct.loadF Client "mu" (![ptrT] "cl"));;
      Continue).

Definition TryMakeClient: val :=
  rec: "TryMakeClient" "host_name" :=
    let: "host" := ref_zero uint64T in
    let: "$a0" := ![uint64T] "host_name" in
    "host" <-[uint64T] "$a0";;
    let: "a" := ref_zero (struct.t grove_ffi.ConnectRet) in
    let: "$a0" := grove__ffi.Connect (![uint64T] "host") in
    "a" <-[struct.t grove_ffi.ConnectRet] "$a0";;
    let: "nilClient" := ref (zero_val ptrT) in
    (if: struct.get grove_ffi.ConnectRet "Err" (![struct.t grove_ffi.ConnectRet] "a")
    then return: (#1, ![ptrT] "nilClient")
    else #());;
    let: "cl" := ref_zero ptrT in
    let: "$a0" := struct.new Client [
      "conn" ::= struct.get grove_ffi.ConnectRet "Connection" (![struct.t grove_ffi.ConnectRet] "a");
      "mu" ::= struct.alloc sync.Mutex (zero_val (struct.t sync.Mutex));
      "seq" ::= #1;
      "pending" ::= NewMap uint64T ptrT #()
    ] in
    "cl" <-[ptrT] "$a0";;
    Fork (Client__replyThread (![ptrT] "cl");;
          #());;
    return: (#0, ![ptrT] "cl").

Definition MakeClient: val :=
  rec: "MakeClient" "host_name" :=
    let: "cl" := ref_zero ptrT in
    let: "err" := ref_zero uint64T in
    let: ("$a0", "$a1") := TryMakeClient (![uint64T] "host_name") in
    "cl" <-[ptrT] "$a1";;
    "err" <-[uint64T] "$a0";;
    (if: (![uint64T] "err") ≠ #0
    then
      log.Printf #(str"Unable to connect to %!!(MISSING)!(MISSING)!(MISSING)!(MISSING)s(MISSING)") (grove__ffi.AddressToStr (![uint64T] "host_name"));;
      #()
    else #());;
    machine.Assume ((![uint64T] "err") = #0);;
    return: (![ptrT] "cl").

Definition Error: ty := uint64T.

Definition ErrNone : expr := #0.

Definition ErrTimeout : expr := #1.

Definition ErrDisconnect : expr := #2.

Definition Client__CallStart: val :=
  rec: "Client__CallStart" "cl" "rpcid" "args" :=
    let: "reply_buf" := ref_zero ptrT in
    let: "$a0" := ref (zero_val (slice.T byteT)) in
    "reply_buf" <-[ptrT] "$a0";;
    let: "cb" := ref_zero ptrT in
    let: "$a0" := struct.new Callback [
      "reply" ::= ![ptrT] "reply_buf";
      "state" ::= ref (zero_val uint64T);
      "cond" ::= sync.NewCond (struct.loadF Client "mu" (![ptrT] "cl"))
    ] in
    "cb" <-[ptrT] "$a0";;
    let: "$a0" := callbackStateWaiting in
    (struct.loadF Callback "state" (![ptrT] "cb")) <-[uint64T] "$a0";;
    sync.Mutex__Lock (struct.loadF Client "mu" (![ptrT] "cl"));;
    let: "seqno" := ref_zero uint64T in
    let: "$a0" := struct.loadF Client "seq" (![ptrT] "cl") in
    "seqno" <-[uint64T] "$a0";;
    let: "$a0" := std.SumAssumeNoOverflow (struct.loadF Client "seq" (![ptrT] "cl")) #1 in
    struct.storeF Client "seq" (![ptrT] "cl") "$a0";;
    let: "$a0" := ![ptrT] "cb" in
    MapInsert (struct.loadF Client "pending" (![ptrT] "cl")) (![uint64T] "seqno") "$a0";;
    sync.Mutex__Unlock (struct.loadF Client "mu" (![ptrT] "cl"));;
    let: "data1" := ref_zero (slice.T byteT) in
    let: "$a0" := NewSliceWithCap byteT #0 ((#8 + #8) + (slice.len (![slice.T byteT] "args"))) in
    "data1" <-[slice.T byteT] "$a0";;
    let: "data2" := ref_zero (slice.T byteT) in
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "data1") (![uint64T] "rpcid") in
    "data2" <-[slice.T byteT] "$a0";;
    let: "data3" := ref_zero (slice.T byteT) in
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "data2") (![uint64T] "seqno") in
    "data3" <-[slice.T byteT] "$a0";;
    let: "reqData" := ref_zero (slice.T byteT) in
    let: "$a0" := marshal.WriteBytes (![slice.T byteT] "data3") (![slice.T byteT] "args") in
    "reqData" <-[slice.T byteT] "$a0";;
    (if: grove__ffi.Send (struct.loadF Client "conn" (![ptrT] "cl")) (![slice.T byteT] "reqData")
    then
      return: (struct.new Callback [
       ], ErrDisconnect)
    else #());;
    return: (![ptrT] "cb", ErrNone).

Definition Client__CallComplete: val :=
  rec: "Client__CallComplete" "cl" "cb" "reply" "timeout_ms" :=
    sync.Mutex__Lock (struct.loadF Client "mu" (![ptrT] "cl"));;
    (if: (![uint64T] (struct.loadF Callback "state" (![ptrT] "cb"))) = callbackStateWaiting
    then
      machine.WaitTimeout (struct.loadF Callback "cond" (![ptrT] "cb")) (![uint64T] "timeout_ms");;
      #()
    else #());;
    let: "state" := ref_zero uint64T in
    let: "$a0" := ![uint64T] (struct.loadF Callback "state" (![ptrT] "cb")) in
    "state" <-[uint64T] "$a0";;
    (if: (![uint64T] "state") = callbackStateDone
    then
      let: "$a0" := ![slice.T byteT] (struct.loadF Callback "reply" (![ptrT] "cb")) in
      (![ptrT] "reply") <-[slice.T byteT] "$a0";;
      sync.Mutex__Unlock (struct.loadF Client "mu" (![ptrT] "cl"));;
      return: (#0)
    else
      sync.Mutex__Unlock (struct.loadF Client "mu" (![ptrT] "cl"));;
      (if: (![uint64T] "state") = callbackStateAborted
      then return: (ErrDisconnect)
      else return: (ErrTimeout));;
      #());;
    #().

Definition Client__Call: val :=
  rec: "Client__Call" "cl" "rpcid" "args" "reply" "timeout_ms" :=
    let: "err" := ref_zero uint64T in
    let: "cb" := ref_zero ptrT in
    let: ("$a0", "$a1") := Client__CallStart (![ptrT] "cl") (![uint64T] "rpcid") (![slice.T byteT] "args") in
    "err" <-[uint64T] "$a1";;
    "cb" <-[ptrT] "$a0";;
    (if: (![uint64T] "err") ≠ #0
    then return: (![uint64T] "err")
    else #());;
    return: (Client__CallComplete (![ptrT] "cl") (![ptrT] "cb") (![ptrT] "reply") (![uint64T] "timeout_ms")).
