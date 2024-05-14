(* autogenerated from github.com/mit-pdos/perennial-examples/replicated_block *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.tchajed.goose.machine.disk.
From Goose Require sync.

From Perennial.goose_lang Require Import ffi.disk_prelude.

Definition RepBlock := struct.decl [
  "d" :: disk.Disk;
  "addr" :: uint64T;
  "m" :: ptrT
].

(* Open initializes a replicated block,
   either after a crash or from two disk blocks.

   Takes ownership of addr and addr+1 on disk. *)
Definition Open: val :=
  rec: "Open" "d" "addr" :=
    let: "b" := disk.Read "addr" in
    disk.Write ("addr" + #1) "b";;
    struct.new RepBlock [
      "d" ::= "d";
      "addr" ::= "addr";
      "m" ::= struct.alloc sync.Mutex (zero_val (struct.t sync.Mutex))
    ].

(* readAddr returns the address to read from

   gives ownership of a disk block, so requires the lock to be held *)
Definition RepBlock__readAddr: val :=
  rec: "RepBlock__readAddr" "rb" "primary" :=
    (if: "primary"
    then struct.loadF RepBlock "addr" "rb"
    else (struct.loadF RepBlock "addr" "rb") + #1).

Definition RepBlock__Read: val :=
  rec: "RepBlock__Read" "rb" "primary" :=
    sync.Mutex__Lock (struct.loadF RepBlock "m" "rb");;
    let: "b" := disk.Read (RepBlock__readAddr "rb" "primary") in
    sync.Mutex__Unlock (struct.loadF RepBlock "m" "rb");;
    "b".

Definition RepBlock__write: val :=
  rec: "RepBlock__write" "rb" "b" :=
    disk.Write (struct.loadF RepBlock "addr" "rb") "b";;
    disk.Write ((struct.loadF RepBlock "addr" "rb") + #1) "b";;
    #().

Definition RepBlock__Write: val :=
  rec: "RepBlock__Write" "rb" "b" :=
    sync.Mutex__Lock (struct.loadF RepBlock "m" "rb");;
    RepBlock__write "rb" "b";;
    sync.Mutex__Unlock (struct.loadF RepBlock "m" "rb");;
    #().