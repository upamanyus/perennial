(* autogenerated from github.com/mit-pdos/gokv/asyncfile *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.goose_dash_lang.std.
From Goose Require github_dot_com.mit_dash_pdos.gokv.grove__ffi.
From Goose Require sync.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition AsyncFile := struct.decl [
  "mu" :: ptrT;
  "data" :: slice.T byteT;
  "filename" :: stringT;
  "index" :: uint64T;
  "indexCond" :: ptrT;
  "durableIndex" :: uint64T;
  "durableIndexCond" :: ptrT;
  "closeRequested" :: boolT;
  "closed" :: boolT;
  "closedCond" :: ptrT
].

Definition AsyncFile__wait: val :=
  rec: "AsyncFile__wait" "s" "index" :=
    sync.Mutex__Lock (struct.loadF AsyncFile "mu" (![ptrT] "s"));;
    (for: (λ: <>, (struct.loadF AsyncFile "durableIndex" (![ptrT] "s")) < (![uint64T] "index")); (λ: <>, Skip) := λ: <>,
      sync.Cond__Wait (struct.loadF AsyncFile "durableIndexCond" (![ptrT] "s"));;
      #()).

Definition AsyncFile__Write: val :=
  rec: "AsyncFile__Write" "s" "data" :=
    sync.Mutex__Lock (struct.loadF AsyncFile "mu" (![ptrT] "s"));;
    let: "$a0" := ![slice.T byteT] "data" in
    struct.storeF AsyncFile "data" (![ptrT] "s") "$a0";;
    let: "$a0" := std.SumAssumeNoOverflow (struct.loadF AsyncFile "index" (![ptrT] "s")) #1 in
    struct.storeF AsyncFile "index" (![ptrT] "s") "$a0";;
    let: "index" := ref_zero uint64T in
    let: "$a0" := struct.loadF AsyncFile "index" (![ptrT] "s") in
    "index" <-[uint64T] "$a0";;
    sync.Cond__Signal (struct.loadF AsyncFile "indexCond" (![ptrT] "s"));;
    sync.Mutex__Unlock (struct.loadF AsyncFile "mu" (![ptrT] "s"));;
    return: ((λ: <>,
       AsyncFile__wait (![ptrT] "s") (![uint64T] "index");;
       #()
       )).

Definition AsyncFile__flushThread: val :=
  rec: "AsyncFile__flushThread" "s" :=
    sync.Mutex__Lock (struct.loadF AsyncFile "mu" (![ptrT] "s"));;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: struct.loadF AsyncFile "closeRequested" (![ptrT] "s")
      then
        grove__ffi.FileWrite (struct.loadF AsyncFile "filename" (![ptrT] "s")) (struct.loadF AsyncFile "data" (![ptrT] "s"));;
        let: "$a0" := struct.loadF AsyncFile "index" (![ptrT] "s") in
        struct.storeF AsyncFile "durableIndex" (![ptrT] "s") "$a0";;
        sync.Cond__Broadcast (struct.loadF AsyncFile "durableIndexCond" (![ptrT] "s"));;
        let: "$a0" := #true in
        struct.storeF AsyncFile "closed" (![ptrT] "s") "$a0";;
        sync.Mutex__Unlock (struct.loadF AsyncFile "mu" (![ptrT] "s"));;
        sync.Cond__Signal (struct.loadF AsyncFile "closedCond" (![ptrT] "s"));;
        Break
      else #());;
      (if: (struct.loadF AsyncFile "durableIndex" (![ptrT] "s")) ≥ (struct.loadF AsyncFile "index" (![ptrT] "s"))
      then
        sync.Cond__Wait (struct.loadF AsyncFile "indexCond" (![ptrT] "s"));;
        Continue
      else #());;
      let: "index" := ref_zero uint64T in
      let: "$a0" := struct.loadF AsyncFile "index" (![ptrT] "s") in
      "index" <-[uint64T] "$a0";;
      let: "data" := ref_zero (slice.T byteT) in
      let: "$a0" := struct.loadF AsyncFile "data" (![ptrT] "s") in
      "data" <-[slice.T byteT] "$a0";;
      sync.Mutex__Unlock (struct.loadF AsyncFile "mu" (![ptrT] "s"));;
      grove__ffi.FileWrite (struct.loadF AsyncFile "filename" (![ptrT] "s")) (![slice.T byteT] "data");;
      sync.Mutex__Lock (struct.loadF AsyncFile "mu" (![ptrT] "s"));;
      let: "$a0" := ![uint64T] "index" in
      struct.storeF AsyncFile "durableIndex" (![ptrT] "s") "$a0";;
      sync.Cond__Broadcast (struct.loadF AsyncFile "durableIndexCond" (![ptrT] "s"));;
      #()).

Definition AsyncFile__Close: val :=
  rec: "AsyncFile__Close" "s" :=
    sync.Mutex__Lock (struct.loadF AsyncFile "mu" (![ptrT] "s"));;
    let: "$a0" := #true in
    struct.storeF AsyncFile "closeRequested" (![ptrT] "s") "$a0";;
    sync.Cond__Signal (struct.loadF AsyncFile "indexCond" (![ptrT] "s"));;
    (for: (λ: <>, (~ (struct.loadF AsyncFile "closed" (![ptrT] "s")))); (λ: <>, Skip) := λ: <>,
      sync.Cond__Wait (struct.loadF AsyncFile "closedCond" (![ptrT] "s"));;
      #()).

(* returns the state, then the File object *)
Definition MakeAsyncFile: val :=
  rec: "MakeAsyncFile" "filename" :=
    let: "s" := ref_zero ptrT in
    let: "$a0" := struct.alloc AsyncFile (zero_val (struct.t AsyncFile)) in
    "s" <-[ptrT] "$a0";;
    let: "$a0" := struct.alloc sync.Mutex (zero_val (struct.t sync.Mutex)) in
    struct.storeF AsyncFile "mu" (![ptrT] "s") "$a0";;
    let: "$a0" := sync.NewCond (struct.loadF AsyncFile "mu" (![ptrT] "s")) in
    struct.storeF AsyncFile "indexCond" (![ptrT] "s") "$a0";;
    let: "$a0" := sync.NewCond (struct.loadF AsyncFile "mu" (![ptrT] "s")) in
    struct.storeF AsyncFile "durableIndexCond" (![ptrT] "s") "$a0";;
    let: "$a0" := sync.NewCond (struct.loadF AsyncFile "mu" (![ptrT] "s")) in
    struct.storeF AsyncFile "closedCond" (![ptrT] "s") "$a0";;
    let: "$a0" := ![stringT] "filename" in
    struct.storeF AsyncFile "filename" (![ptrT] "s") "$a0";;
    let: "$a0" := grove__ffi.FileRead (![stringT] "filename") in
    struct.storeF AsyncFile "data" (![ptrT] "s") "$a0";;
    let: "$a0" := #0 in
    struct.storeF AsyncFile "index" (![ptrT] "s") "$a0";;
    let: "$a0" := #0 in
    struct.storeF AsyncFile "durableIndex" (![ptrT] "s") "$a0";;
    let: "$a0" := #false in
    struct.storeF AsyncFile "closed" (![ptrT] "s") "$a0";;
    let: "$a0" := #false in
    struct.storeF AsyncFile "closeRequested" (![ptrT] "s") "$a0";;
    let: "data" := ref_zero (slice.T byteT) in
    let: "$a0" := struct.loadF AsyncFile "data" (![ptrT] "s") in
    "data" <-[slice.T byteT] "$a0";;
    Fork (AsyncFile__flushThread (![ptrT] "s");;
          #());;
    return: (![slice.T byteT] "data", ![ptrT] "s").