(* autogenerated from github.com/mit-pdos/gokv/fencing/loopclient *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.mit_dash_pdos.gokv.fencing.client.
From Goose Require github_dot_com.mit_dash_pdos.gokv.grove__ffi.
From Goose Require github_dot_com.tchajed.goose.machine.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition LoopOnKey: val :=
  rec: "LoopOnKey" "key" "config" :=
    let: "ck" := client.MakeClerk "config" in
    let: "lowerBound" := ref_to uint64T (client.Clerk__FetchAndIncrement "ck" "key") in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "v" := client.Clerk__FetchAndIncrement "ck" "key" in
      machine.Assert ("v" > (![uint64T] "lowerBound"));;
      (if: ("v" `rem` #1000) = #0
      then
        (* log.Printf("reached %d >= %d", key, v) *)
        #()
      else #());;
      "lowerBound" <-[uint64T] "v";;
      Continue);;
    #().
