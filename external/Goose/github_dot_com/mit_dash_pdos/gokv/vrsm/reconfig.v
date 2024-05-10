(* autogenerated from github.com/mit-pdos/gokv/vrsm/reconfig *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.mit_dash_pdos.gokv.grove__ffi.
From Goose Require github_dot_com.mit_dash_pdos.gokv.vrsm.configservice.
From Goose Require github_dot_com.mit_dash_pdos.gokv.vrsm.e.
From Goose Require github_dot_com.mit_dash_pdos.gokv.vrsm.replica.
From Goose Require github_dot_com.tchajed.goose.machine.
From Goose Require log.
From Goose Require sync.

From Perennial.goose_lang Require Import ffi.grove_prelude.

(* admin.go *)

Definition EnterNewConfig: val :=
  rec: "EnterNewConfig" "configHosts" "servers" :=
    (if: (slice.len (![slice.T uint64T] "servers")) = #0
    then
      log.Println #(str"Tried creating empty config");;
      return: (e.EmptyConfig)
    else #());;
    let: "configCk" := ref_zero ptrT in
    let: "$a0" := configservice.MakeClerk (![slice.T uint64T] "configHosts") in
    "configCk" <-[ptrT] "$a0";;
    let: "oldServers" := ref_zero (slice.T uint64T) in
    let: "epoch" := ref_zero uint64T in
    let: ("$a0", "$a1") := configservice.Clerk__ReserveEpochAndGetConfig (![ptrT] "configCk") in
    "oldServers" <-[slice.T uint64T] "$a1";;
    "epoch" <-[uint64T] "$a0";;
    log.Printf #(str"Reserved %!!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)d(MISSING)") (![uint64T] "epoch");;
    let: "id" := ref_zero uint64T in
    let: "$a0" := ((machine.RandomUint64 #()) + #1) `rem` (slice.len (![slice.T uint64T] "oldServers")) in
    "id" <-[uint64T] "$a0";;
    let: "oldClerk" := ref_zero ptrT in
    let: "$a0" := replica.MakeClerk (SliceGet uint64T (![slice.T uint64T] "oldServers") (![uint64T] "id")) in
    "oldClerk" <-[ptrT] "$a0";;
    let: "reply" := ref_zero ptrT in
    let: "$a0" := replica.Clerk__GetState (![ptrT] "oldClerk") (struct.new replica.GetStateArgs [
      "Epoch" ::= ![uint64T] "epoch"
    ]) in
    "reply" <-[ptrT] "$a0";;
    (if: (struct.loadF replica.GetStateReply "Err" (![ptrT] "reply")) ≠ e.None
    then
      log.Printf #(str"Error while getting state and sealing in epoch %!!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)d(MISSING)") (![uint64T] "epoch");;
      return: (struct.loadF replica.GetStateReply "Err" (![ptrT] "reply"))
    else #());;
    let: "clerks" := ref_zero (slice.T ptrT) in
    let: "$a0" := NewSlice ptrT (slice.len (![slice.T uint64T] "servers")) in
    "clerks" <-[slice.T ptrT] "$a0";;
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, (![uint64T] "i") < (slice.len (![slice.T ptrT] "clerks"))); (λ: <>, Skip) := λ: <>,
      let: "$a0" := replica.MakeClerk (SliceGet uint64T (![slice.T uint64T] "servers") (![uint64T] "i")) in
      SliceSet ptrT (![slice.T ptrT] "clerks") (![uint64T] "i") "$a0";;
      "i" <-[uint64T] ((![uint64T] "i") + #1);;
      #()).

(* init.go *)

Definition InitializeSystem: val :=
  rec: "InitializeSystem" "configHosts" "servers" :=
    let: "configCk" := ref_zero ptrT in
    let: "$a0" := configservice.MakeClerk (![slice.T uint64T] "configHosts") in
    "configCk" <-[ptrT] "$a0";;
    configservice.Clerk__TryWriteConfig (![ptrT] "configCk") #0 (![slice.T uint64T] "servers");;
    return: (EnterNewConfig (![slice.T uint64T] "configHosts") (![slice.T uint64T] "servers")).
