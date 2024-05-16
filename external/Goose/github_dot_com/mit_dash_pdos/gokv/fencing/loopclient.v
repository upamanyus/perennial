(* autogenerated from github.com/mit-pdos/gokv/fencing/loopclient *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.mit_dash_pdos.gokv.fencing.client.
From Goose Require github_dot_com.mit_dash_pdos.gokv.grove__ffi.
From Goose Require github_dot_com.tchajed.goose.machine.
From Goose Require log.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition LoopOnKey: val :=
  rec: "LoopOnKey" "key" "config" :=
    let: "config" := ref_to uint64T "config" in
    let: "key" := ref_to uint64T "key" in
    let: "ck" := ref_zero ptrT in
    let: "$a0" := client.MakeClerk (![uint64T] "config") in
    "ck" <-[ptrT] "$a0";;
    let: "lowerBound" := ref_to uint64T (client.Clerk__FetchAndIncrement (![ptrT] "ck") (![uint64T] "key")) in
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "v" := ref_zero uint64T in
      let: "$a0" := client.Clerk__FetchAndIncrement (![ptrT] "ck") (![uint64T] "key") in
      "v" <-[uint64T] "$a0";;
      machine.Assert ((![uint64T] "v") > (![uint64T] "lowerBound"));;
      (if: ((![uint64T] "v") `rem` #1000) = #0
      then
        log.Printf #(str"reached %!!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)d(MISSING) >= %!!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)d(MISSING)") (![uint64T] "key") (![uint64T] "v");;
        #()
      else #());;
      let: "$a0" := ![uint64T] "v" in
      "lowerBound" <-[uint64T] "$a0";;
      #()).
