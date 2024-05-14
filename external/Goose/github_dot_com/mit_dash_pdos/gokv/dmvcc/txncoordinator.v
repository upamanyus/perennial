(* autogenerated from github.com/mit-pdos/gokv/dmvcc/txncoordinator *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.mit_dash_pdos.gokv.dmvcc.index.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

(* 0_server.go *)

Definition Server := struct.decl [
  "indexCk" :: ptrT
].

Definition Server__TryCommit: val :=
  rec: "Server__TryCommit" "s" "tid" "writes" :=
    let: "err" := ref_to uint64T #0 in
    MapIter (![mapT stringT] "writes") (λ: "key" <>,
      (if: (![uint64T] "err") = #0
      then
        let: "$a0" := index.Clerk__AcquireTuple (struct.loadF Server "indexCk" (![ptrT] "s")) (![uint64T] "key") (![uint64T] "tid") in
        "err" <-[uint64T] "$a0";;
        #()
      else #());;
      #());;
    (if: (![uint64T] "err") ≠ #0
    then return: (#false)
    else #());;
    index.Clerk__UpdateAndRelease (struct.loadF Server "indexCk" (![ptrT] "s")) (![uint64T] "tid") (![mapT stringT] "writes");;
    return: (#true).

Definition MakeServer: val :=
  rec: "MakeServer" "indexHost" :=
    return: (struct.new Server [
       "indexCk" ::= index.MakeClerk (![ptrT] "indexHost")
     ]).

(* clerk.go *)

Definition Clerk := struct.decl [
  "s" :: ptrT
].

Definition Clerk__TryCommit: val :=
  rec: "Clerk__TryCommit" "ck" "tid" "writes" :=
    return: (Server__TryCommit (struct.loadF Clerk "s" (![ptrT] "ck")) (![uint64T] "tid") (![mapT stringT] "writes")).

Definition MakeClerk: val :=
  rec: "MakeClerk" "host" :=
    return: (struct.new Clerk [
       "s" ::= ![ptrT] "host"
     ]).

End code.