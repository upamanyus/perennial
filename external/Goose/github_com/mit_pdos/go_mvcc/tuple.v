(* autogenerated from github.com/mit-pdos/go-mvcc/tuple *)
From Perennial.goose_lang Require Import prelude.
Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

From Goose Require github_com.mit_pdos.go_mvcc.common.

(* *
    * The lifetime of a version starts from `begin` of itself to the `begin` of
    * next version; it's a half-open interval (]. *)
Definition Version := struct.decl [
  "begin" :: uint64T;
  "deleted" :: boolT;
  "val" :: uint64T
].

(* *
    * `tidown`
    *		An TID specifying which txn owns the permission to write this tuple.
    * `tidlast`
    *		An TID specifying the last txn (in the sense of the largest TID, not
    *		actual physical time) that reads or writes this tuple. *)
Definition Tuple := struct.decl [
  "latch" :: ptrT;
  "rcond" :: ptrT;
  "tidown" :: uint64T;
  "tidlast" :: uint64T;
  "vers" :: slice.T (struct.t Version)
].

(* *
    * TODO: Maybe start from the end (i.e., the newest version).
    * TODO: Can simply return a value rather than a version. *)
Definition findRightVer: val :=
  rec: "findRightVer" "tid" "vers" :=
    let: "ver" := ref (zero_val (struct.t Version)) in
    let: "found" := ref_to boolT #false in
    let: "length" := slice.len "vers" in
    let: "idx" := ref_to uint64T #0 in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: ![uint64T] "idx" ≥ "length"
      then Break
      else
        "ver" <-[struct.t Version] SliceGet (struct.t Version) "vers" ("length" - ![uint64T] "idx" - #1);;
        (if: "tid" > struct.get Version "begin" (![struct.t Version] "ver")
        then
          "found" <-[boolT] #true;;
          Break
        else
          "idx" <-[uint64T] ![uint64T] "idx" + #1;;
          Continue)));;
    (struct.get Version "val" (![struct.t Version] "ver"), ![boolT] "found").

(* *
    * Preconditions:
    *
    * Postconditions:
    * 1. On a successful return, the txn `tid` get the permission to update this
    * tuple (when we also acquire the latch of this tuple). *)
Definition Tuple__Own: val :=
  rec: "Tuple__Own" "tuple" "tid" :=
    lock.acquire (struct.loadF Tuple "latch" "tuple");;
    (if: "tid" < struct.loadF Tuple "tidlast" "tuple"
    then
      lock.release (struct.loadF Tuple "latch" "tuple");;
      common.RET_UNSERIALIZABLE
    else
      (if: struct.loadF Tuple "tidown" "tuple" ≠ #0
      then
        lock.release (struct.loadF Tuple "latch" "tuple");;
        common.RET_RETRY
      else
        struct.storeF Tuple "tidown" "tuple" "tid";;
        lock.release (struct.loadF Tuple "latch" "tuple");;
        common.RET_SUCCESS)).

Definition Tuple__appendVersion: val :=
  rec: "Tuple__appendVersion" "tuple" "tid" "val" :=
    let: "verNew" := struct.mk Version [
      "begin" ::= "tid";
      "val" ::= "val";
      "deleted" ::= #false
    ] in
    struct.storeF Tuple "vers" "tuple" (SliceAppend (struct.t Version) (struct.loadF Tuple "vers" "tuple") "verNew");;
    struct.storeF Tuple "tidown" "tuple" #0;;
    struct.storeF Tuple "tidlast" "tuple" "tid";;
    #().

(* *
    * Preconditions:
    * 1. The txn `tid` has the permission to update this tuple. *)
Definition Tuple__AppendVersion: val :=
  rec: "Tuple__AppendVersion" "tuple" "tid" "val" :=
    lock.acquire (struct.loadF Tuple "latch" "tuple");;
    Tuple__appendVersion "tuple" "tid" "val";;
    lock.condBroadcast (struct.loadF Tuple "rcond" "tuple");;
    lock.release (struct.loadF Tuple "latch" "tuple");;
    #().

Definition Tuple__killVersion: val :=
  rec: "Tuple__killVersion" "tuple" "tid" :=
    let: "verNew" := struct.mk Version [
      "begin" ::= "tid";
      "deleted" ::= #true
    ] in
    struct.storeF Tuple "vers" "tuple" (SliceAppend (struct.t Version) (struct.loadF Tuple "vers" "tuple") "verNew");;
    struct.storeF Tuple "tidown" "tuple" #0;;
    struct.storeF Tuple "tidlast" "tuple" "tid";;
    #true.

(* *
    * Preconditions:
    * 1. The txn `tid` has the permission to update this tuple. *)
Definition Tuple__KillVersion: val :=
  rec: "Tuple__KillVersion" "tuple" "tid" :=
    lock.acquire (struct.loadF Tuple "latch" "tuple");;
    let: "ok" := Tuple__killVersion "tuple" "tid" in
    let: "ret" := ref (zero_val uint64T) in
    (if: "ok"
    then "ret" <-[uint64T] common.RET_SUCCESS
    else "ret" <-[uint64T] common.RET_NONEXIST);;
    lock.condBroadcast (struct.loadF Tuple "rcond" "tuple");;
    lock.release (struct.loadF Tuple "latch" "tuple");;
    ![uint64T] "ret".

(* *
    * Preconditions: *)
Definition Tuple__Free: val :=
  rec: "Tuple__Free" "tuple" "tid" :=
    lock.acquire (struct.loadF Tuple "latch" "tuple");;
    struct.storeF Tuple "tidown" "tuple" #0;;
    lock.condBroadcast (struct.loadF Tuple "rcond" "tuple");;
    lock.release (struct.loadF Tuple "latch" "tuple");;
    #().

(* *
    * Preconditions: *)
Definition Tuple__ReadVersion: val :=
  rec: "Tuple__ReadVersion" "tuple" "tid" :=
    lock.acquire (struct.loadF Tuple "latch" "tuple");;
    Skip;;
    (for: (λ: <>, ("tid" > struct.loadF Tuple "tidlast" "tuple") && (struct.loadF Tuple "tidown" "tuple" ≠ #0)); (λ: <>, Skip) := λ: <>,
      lock.condWait (struct.loadF Tuple "rcond" "tuple");;
      Continue);;
    let: ("val", "found") := findRightVer "tid" (struct.loadF Tuple "vers" "tuple") in
    let: "ret" := ref (zero_val uint64T) in
    (if: "found"
    then "ret" <-[uint64T] common.RET_SUCCESS
    else "ret" <-[uint64T] common.RET_NONEXIST);;
    (if: struct.loadF Tuple "tidlast" "tuple" < "tid"
    then struct.storeF Tuple "tidlast" "tuple" "tid"
    else #());;
    lock.release (struct.loadF Tuple "latch" "tuple");;
    ("val", ![uint64T] "ret").

Definition Tuple__removeVersions: val :=
  rec: "Tuple__removeVersions" "tuple" "tid" :=
    let: "idx" := ref_to uint64T #0 in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: ![uint64T] "idx" ≥ slice.len (struct.loadF Tuple "vers" "tuple")
      then Break
      else
        let: "ver" := SliceGet (struct.t Version) (struct.loadF Tuple "vers" "tuple") (![uint64T] "idx") in
        (if: struct.get Version "begin" "ver" > "tid"
        then Break
        else
          "idx" <-[uint64T] ![uint64T] "idx" + #1;;
          Continue)));;
    struct.storeF Tuple "vers" "tuple" (SliceSkip (struct.t Version) (struct.loadF Tuple "vers" "tuple") (![uint64T] "idx"));;
    #().

(* *
    * Remove all versions whose `end` timestamp is less than or equal to `tid`.
    * Preconditions: *)
Definition Tuple__RemoveVersions: val :=
  rec: "Tuple__RemoveVersions" "tuple" "tid" :=
    lock.acquire (struct.loadF Tuple "latch" "tuple");;
    Tuple__removeVersions "tuple" "tid";;
    lock.release (struct.loadF Tuple "latch" "tuple");;
    #().

Definition MkTuple: val :=
  rec: "MkTuple" <> :=
    let: "tuple" := struct.alloc Tuple (zero_val (struct.t Tuple)) in
    struct.storeF Tuple "latch" "tuple" (lock.new #());;
    struct.storeF Tuple "rcond" "tuple" (lock.newCond (struct.loadF Tuple "latch" "tuple"));;
    struct.storeF Tuple "tidown" "tuple" #0;;
    struct.storeF Tuple "tidlast" "tuple" #0;;
    struct.storeF Tuple "vers" "tuple" (NewSlice (struct.t Version) #0);;
    "tuple".

End code.
