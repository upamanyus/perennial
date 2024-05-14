(* autogenerated from github.com/mit-pdos/gokv/tutorial/queue *)
From Perennial.goose_lang Require Import prelude.
From Goose Require sync.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

Definition Queue := struct.decl [
  "queue" :: slice.T uint64T;
  "cond" :: ptrT;
  "lock" :: ptrT;
  "first" :: uint64T;
  "count" :: uint64T
].

Definition NewQueue: val :=
  rec: "NewQueue" "queue_size" :=
    let: "lock" := ref_zero ptrT in
    let: "$a0" := struct.alloc sync.Mutex (zero_val (struct.t sync.Mutex)) in
    "lock" <-[ptrT] "$a0";;
    return: (struct.mk Queue [
       "queue" ::= NewSliceWithCap uint64T (![uint64T] "queue_size") (![uint64T] "queue_size");
       "cond" ::= sync.NewCond (![ptrT] "lock");
       "lock" ::= ![ptrT] "lock";
       "first" ::= #0;
       "count" ::= #0
     ]).

Definition Queue__Enqueue: val :=
  rec: "Queue__Enqueue" "q" "a" :=
    sync.Mutex__Lock (struct.loadF Queue "lock" (![ptrT] "q"));;
    let: "queue_size" := ref_to uint64T (slice.len (struct.loadF Queue "queue" (![ptrT] "q"))) in
    (for: (λ: <>, (struct.loadF Queue "count" (![ptrT] "q")) ≥ (![uint64T] "queue_size")); (λ: <>, Skip) := λ: <>,
      sync.Cond__Wait (struct.loadF Queue "cond" (![ptrT] "q"));;
      #()).

Definition Queue__Dequeue: val :=
  rec: "Queue__Dequeue" "q" :=
    sync.Mutex__Lock (struct.loadF Queue "lock" (![ptrT] "q"));;
    let: "queue_size" := ref_to uint64T (slice.len (struct.loadF Queue "queue" (![ptrT] "q"))) in
    (for: (λ: <>, (struct.loadF Queue "count" (![ptrT] "q")) = #0); (λ: <>, Skip) := λ: <>,
      sync.Cond__Wait (struct.loadF Queue "cond" (![ptrT] "q"));;
      #()).

Definition Queue__Peek: val :=
  rec: "Queue__Peek" "q" :=
    sync.Mutex__Lock (struct.loadF Queue "lock" (![ptrT] "q"));;
    (if: (struct.loadF Queue "count" (![ptrT] "q")) > #0
    then
      let: "first" := ref_zero uint64T in
      let: "$a0" := SliceGet uint64T (struct.loadF Queue "queue" (![ptrT] "q")) (struct.loadF Queue "first" (![ptrT] "q")) in
      "first" <-[uint64T] "$a0";;
      sync.Mutex__Unlock (struct.loadF Queue "lock" (![ptrT] "q"));;
      return: (![uint64T] "first", #true)
    else #());;
    sync.Mutex__Unlock (struct.loadF Queue "lock" (![ptrT] "q"));;
    return: (#0, #false).

End code.