(* autogenerated from github.com/mit-pdos/gokv/dmvcc/txn *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.mit_dash_pdos.gokv.dmvcc.index.
From Goose Require github_dot_com.mit_dash_pdos.gokv.dmvcc.prophname.
From Goose Require github_dot_com.mit_dash_pdos.gokv.dmvcc.txncoordinator.
From Goose Require github_dot_com.mit_dash_pdos.gokv.dmvcc.txnmgr.
From Goose Require github_dot_com.mit_dash_pdos.vmvcc.trusted__proph.
From Goose Require github_dot_com.tchajed.goose.machine.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

Definition Clerk := struct.decl [
  "p" :: ProphIdT;
  "tid" :: uint64T;
  "writes" :: mapT stringT;
  "indexCk" :: ptrT;
  "txnMgrHost" :: ptrT;
  "txnCoordCk" :: ptrT
].

Definition Begin: val :=
  rec: "Begin" "txnMgrHost" "txnCoordHost" "indexHost" :=
    return: (struct.new Clerk [
       "p" ::= prophname.Get #();
       "tid" ::= txnmgr.Server__New (![ptrT] "txnMgrHost");
       "writes" ::= NewMap uint64T stringT #();
       "indexCk" ::= index.MakeClerk (![ptrT] "indexHost");
       "txnMgrHost" ::= ![ptrT] "txnMgrHost";
       "txnCoordCk" ::= txncoordinator.MakeClerk (![ptrT] "txnCoordHost")
     ]).

Definition Clerk__Put: val :=
  rec: "Clerk__Put" "txnCk" "key" "val" :=
    let: "$a0" := ![stringT] "val" in
    MapInsert (struct.loadF Clerk "writes" (![ptrT] "txnCk")) (![uint64T] "key") "$a0";;
    #().

Definition Clerk__Get: val :=
  rec: "Clerk__Get" "txnCk" "key" :=
    let: "ok" := ref_zero boolT in
    let: "val1" := ref_zero stringT in
    let: ("$a0", "$a1") := Fst (MapGet (struct.loadF Clerk "writes" (![ptrT] "txnCk")) (![uint64T] "key")) in
    "ok" <-[boolT] "$a1";;
    "val1" <-[stringT] "$a0";;
    (if: ![boolT] "ok"
    then return: (![stringT] "val1")
    else #());;
    let: "val2" := ref_zero stringT in
    let: "$a0" := index.Clerk__Read (struct.loadF Clerk "indexCk" (![ptrT] "txnCk")) (![uint64T] "key") (struct.loadF Clerk "tid" (![ptrT] "txnCk")) in
    "val2" <-[stringT] "$a0";;
    trusted__proph.ResolveRead (struct.loadF Clerk "p" (![ptrT] "txnCk")) (struct.loadF Clerk "tid" (![ptrT] "txnCk")) (![uint64T] "key");;
    return: (![stringT] "val2").

Definition Clerk__abort: val :=
  rec: "Clerk__abort" "txnCk" :=
    trusted__proph.ResolveAbort (struct.loadF Clerk "p" (![ptrT] "txnCk")) (struct.loadF Clerk "tid" (![ptrT] "txnCk"));;
    #().

Definition Clerk__begin: val :=
  rec: "Clerk__begin" "txn" :=
    let: "tid" := ref_zero uint64T in
    let: "$a0" := txnmgr.Server__New (struct.loadF Clerk "txnMgrHost" (![ptrT] "txn")) in
    "tid" <-[uint64T] "$a0";;
    let: "$a0" := ![uint64T] "tid" in
    struct.storeF Clerk "tid" (![ptrT] "txn") "$a0";;
    #().

Definition Clerk__DoTxn: val :=
  rec: "Clerk__DoTxn" "txn" "body" :=
    Clerk__begin (![ptrT] "txn");;
    let: "wantToCommit" := ref_zero boolT in
    let: "$a0" := (![(arrowT unitT unitT)] "body") (![ptrT] "txn") in
    "wantToCommit" <-[boolT] "$a0";;
    (if: (~ (![boolT] "wantToCommit"))
    then
      Clerk__abort (![ptrT] "txn");;
      return: (#false)
    else #());;
    return: (txncoordinator.Clerk__TryCommit (struct.loadF Clerk "txnCoordCk" (![ptrT] "txn")) (struct.loadF Clerk "tid" (![ptrT] "txn")) (struct.loadF Clerk "writes" (![ptrT] "txn"))).

End code.
