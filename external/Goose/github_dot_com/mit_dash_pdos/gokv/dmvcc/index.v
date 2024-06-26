(* autogenerated from github.com/mit-pdos/gokv/dmvcc/index *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.mit_dash_pdos.vmvcc.index.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

(* 0_server.go *)

Definition Server := struct.decl [
  "index" :: ptrT
].

Definition Server__AcquireTuple: val :=
  rec: "Server__AcquireTuple" "s" "key" "tid" :=
    let: "tid" := ref_to uint64T "tid" in
    let: "key" := ref_to uint64T "key" in
    let: "s" := ref_to ptrT "s" in
    return: (tuple.Tuple__Own (index.Index__GetTuple (struct.loadF Server "index" (![ptrT] "s")) (![uint64T] "key")) (![uint64T] "tid")).

Definition Server__Read: val :=
  rec: "Server__Read" "s" "key" "tid" :=
    let: "tid" := ref_to uint64T "tid" in
    let: "key" := ref_to uint64T "key" in
    let: "s" := ref_to ptrT "s" in
    let: "t" := ref_zero ptrT in
    let: "$a0" := index.Index__GetTuple (struct.loadF Server "index" (![ptrT] "s")) (![uint64T] "key") in
    "t" <-[ptrT] "$a0";;
    tuple.Tuple__ReadWait (![ptrT] "t") (![uint64T] "tid");;
    let: <> := ref_zero boolT in
    let: "val" := ref_zero stringT in
    let: ("$a0", "$a1") := tuple.Tuple__ReadVersion (index.Index__GetTuple (struct.loadF Server "index" (![ptrT] "s")) (![uint64T] "key")) (![uint64T] "tid") in
    "$a1";;
    "val" <-[stringT] "$a0";;
    return: (![stringT] "val").

Definition Server__UpdateAndRelease: val :=
  rec: "Server__UpdateAndRelease" "s" "tid" "writes" :=
    let: "writes" := ref_to (mapT stringT) "writes" in
    let: "tid" := ref_to uint64T "tid" in
    let: "s" := ref_to ptrT "s" in
    MapIter (![mapT stringT] "writes") (λ: "key" "val",
      let: "t" := ref_zero ptrT in
      let: "$a0" := index.Index__GetTuple (struct.loadF Server "index" (![ptrT] "s")) (![uint64T] "key") in
      "t" <-[ptrT] "$a0";;
      tuple.Tuple__WriteOpen (![ptrT] "t");;
      tuple.Tuple__AppendVersion (![ptrT] "t") (![uint64T] "tid") (![stringT] "val");;
      #());;
    #().

Definition MakeServer: val :=
  rec: "MakeServer" <> :=
    return: (struct.new Server [
       "index" ::= index.MkIndex #()
     ]).

(* clerk.go *)

Definition Clerk := struct.decl [
  "s" :: ptrT
].

Definition Clerk__AcquireTuple: val :=
  rec: "Clerk__AcquireTuple" "ck" "key" "tid" :=
    let: "tid" := ref_to uint64T "tid" in
    let: "key" := ref_to uint64T "key" in
    let: "ck" := ref_to ptrT "ck" in
    return: (Server__AcquireTuple (struct.loadF Clerk "s" (![ptrT] "ck")) (![uint64T] "key") (![uint64T] "tid")).

Definition Clerk__Read: val :=
  rec: "Clerk__Read" "ck" "key" "tid" :=
    let: "tid" := ref_to uint64T "tid" in
    let: "key" := ref_to uint64T "key" in
    let: "ck" := ref_to ptrT "ck" in
    return: (Server__Read (struct.loadF Clerk "s" (![ptrT] "ck")) (![uint64T] "key") (![uint64T] "tid")).

Definition Clerk__UpdateAndRelease: val :=
  rec: "Clerk__UpdateAndRelease" "ck" "tid" "writes" :=
    let: "writes" := ref_to (mapT stringT) "writes" in
    let: "tid" := ref_to uint64T "tid" in
    let: "ck" := ref_to ptrT "ck" in
    Server__UpdateAndRelease (struct.loadF Clerk "s" (![ptrT] "ck")) (![uint64T] "tid") (![mapT stringT] "writes");;
    #().

Definition MakeClerk: val :=
  rec: "MakeClerk" "hostname" :=
    let: "hostname" := ref_to ptrT "hostname" in
    return: (struct.new Clerk [
       "s" ::= ![ptrT] "hostname"
     ]).

End code.
