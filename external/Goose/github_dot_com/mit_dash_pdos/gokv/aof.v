(* autogenerated from github.com/mit-pdos/gokv/aof *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.goose_dash_lang.std.
From Goose Require github_dot_com.mit_dash_pdos.gokv.grove__ffi.
From Goose Require github_dot_com.tchajed.marshal.
From Goose Require sync.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition AppendOnlyFile := struct.decl [
  "mu" :: ptrT;
  "oldDurableCond" :: ptrT;
  "durableCond" :: ptrT;
  "lengthCond" :: ptrT;
  "membuf" :: slice.T byteT;
  "length" :: uint64T;
  "durableLength" :: uint64T;
  "closeRequested" :: boolT;
  "closed" :: boolT;
  "closedCond" :: ptrT
].

Definition CreateAppendOnlyFile: val :=
  rec: "CreateAppendOnlyFile" "fname" :=
    let: "a" := ref_zero ptrT in
    let: "$a0" := struct.alloc AppendOnlyFile (zero_val (struct.t AppendOnlyFile)) in
    "a" <-[ptrT] "$a0";;
    let: "$a0" := struct.alloc sync.Mutex (zero_val (struct.t sync.Mutex)) in
    struct.storeF AppendOnlyFile "mu" (![ptrT] "a") "$a0";;
    let: "$a0" := sync.NewCond (struct.loadF AppendOnlyFile "mu" (![ptrT] "a")) in
    struct.storeF AppendOnlyFile "lengthCond" (![ptrT] "a") "$a0";;
    let: "$a0" := sync.NewCond (struct.loadF AppendOnlyFile "mu" (![ptrT] "a")) in
    struct.storeF AppendOnlyFile "oldDurableCond" (![ptrT] "a") "$a0";;
    let: "$a0" := sync.NewCond (struct.loadF AppendOnlyFile "mu" (![ptrT] "a")) in
    struct.storeF AppendOnlyFile "durableCond" (![ptrT] "a") "$a0";;
    let: "$a0" := sync.NewCond (struct.loadF AppendOnlyFile "mu" (![ptrT] "a")) in
    struct.storeF AppendOnlyFile "closedCond" (![ptrT] "a") "$a0";;
    Fork (sync.Mutex__Lock (struct.loadF AppendOnlyFile "mu" (![ptrT] "a"));;
          (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
            (if: ((slice.len (struct.loadF AppendOnlyFile "membuf" (![ptrT] "a"))) = #0) && (~ (struct.loadF AppendOnlyFile "closeRequested" (![ptrT] "a")))
            then
              sync.Cond__Wait (struct.loadF AppendOnlyFile "lengthCond" (![ptrT] "a"));;
              Continue
            else #());;
            (if: struct.loadF AppendOnlyFile "closeRequested" (![ptrT] "a")
            then
              grove__ffi.FileAppend (![stringT] "fname") (struct.loadF AppendOnlyFile "membuf" (![ptrT] "a"));;
              let: "$a0" := NewSlice byteT #0 in
              struct.storeF AppendOnlyFile "membuf" (![ptrT] "a") "$a0";;
              let: "$a0" := struct.loadF AppendOnlyFile "length" (![ptrT] "a") in
              struct.storeF AppendOnlyFile "durableLength" (![ptrT] "a") "$a0";;
              sync.Cond__Broadcast (struct.loadF AppendOnlyFile "durableCond" (![ptrT] "a"));;
              let: "$a0" := #true in
              struct.storeF AppendOnlyFile "closed" (![ptrT] "a") "$a0";;
              sync.Cond__Broadcast (struct.loadF AppendOnlyFile "closedCond" (![ptrT] "a"));;
              sync.Mutex__Unlock (struct.loadF AppendOnlyFile "mu" (![ptrT] "a"));;
              Break
            else #());;
            let: "l" := ref_zero (slice.T byteT) in
            let: "$a0" := struct.loadF AppendOnlyFile "membuf" (![ptrT] "a") in
            "l" <-[slice.T byteT] "$a0";;
            let: "newLength" := ref_zero uint64T in
            let: "$a0" := struct.loadF AppendOnlyFile "length" (![ptrT] "a") in
            "newLength" <-[uint64T] "$a0";;
            let: "$a0" := NewSlice byteT #0 in
            struct.storeF AppendOnlyFile "membuf" (![ptrT] "a") "$a0";;
            let: "cond" := ref_zero ptrT in
            let: "$a0" := struct.loadF AppendOnlyFile "durableCond" (![ptrT] "a") in
            "cond" <-[ptrT] "$a0";;
            let: "$a0" := struct.loadF AppendOnlyFile "oldDurableCond" (![ptrT] "a") in
            struct.storeF AppendOnlyFile "durableCond" (![ptrT] "a") "$a0";;
            let: "$a0" := ![ptrT] "cond" in
            struct.storeF AppendOnlyFile "oldDurableCond" (![ptrT] "a") "$a0";;
            sync.Mutex__Unlock (struct.loadF AppendOnlyFile "mu" (![ptrT] "a"));;
            grove__ffi.FileAppend (![stringT] "fname") (![slice.T byteT] "l");;
            sync.Mutex__Lock (struct.loadF AppendOnlyFile "mu" (![ptrT] "a"));;
            let: "$a0" := ![uint64T] "newLength" in
            struct.storeF AppendOnlyFile "durableLength" (![ptrT] "a") "$a0";;
            sync.Cond__Broadcast (![ptrT] "cond");;
            Continue));;
    return: (![ptrT] "a").

(* NOTE: cannot be called concurrently with Append() *)
Definition AppendOnlyFile__Close: val :=
  rec: "AppendOnlyFile__Close" "a" :=
    sync.Mutex__Lock (struct.loadF AppendOnlyFile "mu" (![ptrT] "a"));;
    let: "$a0" := #true in
    struct.storeF AppendOnlyFile "closeRequested" (![ptrT] "a") "$a0";;
    sync.Cond__Signal (struct.loadF AppendOnlyFile "lengthCond" (![ptrT] "a"));;
    (for: (λ: <>, (~ (struct.loadF AppendOnlyFile "closed" (![ptrT] "a")))); (λ: <>, Skip) := λ: <>,
      sync.Cond__Wait (struct.loadF AppendOnlyFile "closedCond" (![ptrT] "a"));;
      #()).

(* NOTE: cannot be called concurrently with Close() *)
Definition AppendOnlyFile__Append: val :=
  rec: "AppendOnlyFile__Append" "a" "data" :=
    sync.Mutex__Lock (struct.loadF AppendOnlyFile "mu" (![ptrT] "a"));;
    let: "$a0" := marshal.WriteBytes (struct.loadF AppendOnlyFile "membuf" (![ptrT] "a")) (![slice.T byteT] "data") in
    struct.storeF AppendOnlyFile "membuf" (![ptrT] "a") "$a0";;
    let: "$a0" := std.SumAssumeNoOverflow (struct.loadF AppendOnlyFile "length" (![ptrT] "a")) (slice.len (![slice.T byteT] "data")) in
    struct.storeF AppendOnlyFile "length" (![ptrT] "a") "$a0";;
    let: "r" := ref_zero uint64T in
    let: "$a0" := struct.loadF AppendOnlyFile "length" (![ptrT] "a") in
    "r" <-[uint64T] "$a0";;
    sync.Cond__Signal (struct.loadF AppendOnlyFile "lengthCond" (![ptrT] "a"));;
    sync.Mutex__Unlock (struct.loadF AppendOnlyFile "mu" (![ptrT] "a"));;
    return: (![uint64T] "r").

Definition AppendOnlyFile__WaitAppend: val :=
  rec: "AppendOnlyFile__WaitAppend" "a" "length" :=
    sync.Mutex__Lock (struct.loadF AppendOnlyFile "mu" (![ptrT] "a"));;
    let: "cond" := ref (zero_val ptrT) in
    (if: ((![uint64T] "length") + (slice.len (struct.loadF AppendOnlyFile "membuf" (![ptrT] "a")))) ≤ (struct.loadF AppendOnlyFile "length" (![ptrT] "a"))
    then
      let: "$a0" := struct.loadF AppendOnlyFile "oldDurableCond" (![ptrT] "a") in
      "cond" <-[ptrT] "$a0";;
      #()
    else
      let: "$a0" := struct.loadF AppendOnlyFile "durableCond" (![ptrT] "a") in
      "cond" <-[ptrT] "$a0";;
      #());;
    (for: (λ: <>, (struct.loadF AppendOnlyFile "durableLength" (![ptrT] "a")) < (![uint64T] "length")); (λ: <>, Skip) := λ: <>,
      sync.Cond__Wait (![ptrT] "cond");;
      #()).