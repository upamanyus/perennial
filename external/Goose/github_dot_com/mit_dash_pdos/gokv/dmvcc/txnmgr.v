(* autogenerated from github.com/mit-pdos/gokv/dmvcc/txnmgr *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.tchajed.goose.machine.
From Goose Require sync.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

(* clerk.go *)

Definition Clerk := struct.decl [
].

(* server.go *)

Definition Server := struct.decl [
  "mu" :: ptrT;
  "p" :: ProphIdT;
  "nextTid" :: uint64T
].

Definition MakeServer: val :=
  rec: "MakeServer" <> :=
    let: "p" := ref_zero ProphIdT in
    let: "$a0" := machine.NewProph #() in
    "p" <-[ProphIdT] "$a0";;
    let: "txnMgr" := ref_zero ptrT in
    let: "$a0" := struct.new Server [
      "p" ::= ![ProphIdT] "p";
      "nextTid" ::= #1
    ] in
    "txnMgr" <-[ptrT] "$a0";;
    let: "$a0" := struct.alloc sync.Mutex (zero_val (struct.t sync.Mutex)) in
    struct.storeF Server "mu" (![ptrT] "txnMgr") "$a0";;
    return: (![ptrT] "txnMgr").

Definition Server__New: val :=
  rec: "Server__New" "txnMgr" :=
    sync.Mutex__Lock (struct.loadF Server "mu" (![ptrT] "txnMgr"));;
    let: "tid" := ref_zero uint64T in
    let: "$a0" := struct.loadF Server "nextTid" (![ptrT] "txnMgr") in
    "tid" <-[uint64T] "$a0";;
    struct.storeF Server "nextTid" (![ptrT] "txnMgr") ((struct.loadF Server "nextTid" (![ptrT] "txnMgr")) + #1);;
    sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "txnMgr"));;
    return: (![uint64T] "tid").

End code.
