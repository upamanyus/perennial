(* autogenerated from github.com/mit-pdos/perennial-examples/async_inode *)
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.

From Goose Require github_com.mit_pdos.perennial_examples.alloc.
From Goose Require github_com.tchajed.marshal.

Definition MaxBlocks : expr := #511.

Definition Inode := struct.decl [
  "d" :: disk.Disk;
  "m" :: lockRefT;
  "addr" :: uint64T;
  "addrs" :: slice.T uint64T;
  "buffered" :: slice.T disk.blockT
].

Definition Open: val :=
  rec: "Open" "d" "addr" :=
    let: "b" := disk.Read "addr" in
    let: "dec" := marshal.NewDec "b" in
    let: "numAddrs" := marshal.Dec__GetInt "dec" in
    let: "addrs" := marshal.Dec__GetInts "dec" "numAddrs" in
    struct.new Inode [
      "d" ::= "d";
      "m" ::= lock.new #();
      "addr" ::= "addr";
      "addrs" ::= "addrs";
      "buffered" ::= slice.nil
    ].

(* UsedBlocks returns the addresses allocated to the inode for the purposes
   of recovery. Assumes full ownership of the inode, so does not lock,
   and expects the caller to need only temporary access to the returned slice. *)
Definition Inode__UsedBlocks: val :=
  rec: "Inode__UsedBlocks" "i" :=
    struct.loadF Inode "addrs" "i".

Definition Inode__read: val :=
  rec: "Inode__read" "i" "off" :=
    (if: "off" ≥ slice.len (struct.loadF Inode "addrs" "i") + slice.len (struct.loadF Inode "buffered" "i")
    then slice.nil
    else
      (if: "off" < slice.len (struct.loadF Inode "addrs" "i")
      then
        let: "a" := SliceGet uint64T (struct.loadF Inode "addrs" "i") "off" in
        disk.Read "a"
      else SliceGet (slice.T byteT) (struct.loadF Inode "buffered" "i") ("off" - slice.len (struct.loadF Inode "addrs" "i")))).

Definition Inode__Read: val :=
  rec: "Inode__Read" "i" "off" :=
    lock.acquire (struct.loadF Inode "m" "i");;
    let: "b" := Inode__read "i" "off" in
    lock.release (struct.loadF Inode "m" "i");;
    "b".

Definition Inode__Size: val :=
  rec: "Inode__Size" "i" :=
    lock.acquire (struct.loadF Inode "m" "i");;
    let: "sz" := slice.len (struct.loadF Inode "addrs" "i") + slice.len (struct.loadF Inode "buffered" "i") in
    lock.release (struct.loadF Inode "m" "i");;
    "sz".

Definition Inode__mkHdr: val :=
  rec: "Inode__mkHdr" "i" :=
    let: "enc" := marshal.NewEnc disk.BlockSize in
    marshal.Enc__PutInt "enc" (slice.len (struct.loadF Inode "addrs" "i"));;
    marshal.Enc__PutInts "enc" (struct.loadF Inode "addrs" "i");;
    let: "hdr" := marshal.Enc__Finish "enc" in
    "hdr".

(* appendOne durably extends the inode with the data in some address *)
Definition Inode__appendOne: val :=
  rec: "Inode__appendOne" "i" "a" :=
    struct.storeF Inode "addrs" "i" (SliceAppend uint64T (struct.loadF Inode "addrs" "i") "a");;
    let: "hdr" := Inode__mkHdr "i" in
    disk.Write (struct.loadF Inode "addr" "i") "hdr".

(* flushOne extends the on-disk inode with the next buffered write

   assumes lock is held and that there is at least one buffered write *)
Definition Inode__flushOne: val :=
  rec: "Inode__flushOne" "i" "allocator" :=
    let: ("a", "ok") := alloc.Allocator__Reserve "allocator" in
    (if: ~ "ok"
    then #false
    else
      let: "b" := SliceGet (slice.T byteT) (struct.loadF Inode "buffered" "i") #0 in
      struct.storeF Inode "buffered" "i" (SliceSkip (slice.T byteT) (struct.loadF Inode "buffered" "i") #1);;
      disk.Write "a" "b";;
      Inode__appendOne "i" "a";;
      #true).

(* critical section for Flush

   assumes lock is held *)
Definition Inode__flush: val :=
  rec: "Inode__flush" "i" "allocator" :=
    Skip;;
    (for: (λ: <>, slice.len (struct.loadF Inode "buffered" "i") > #0); (λ: <>, Skip) := λ: <>,
      let: "ok" := Inode__flushOne "i" "allocator" in
      (if: ~ "ok"
      then Break
      else Continue));;
    (if: slice.len (struct.loadF Inode "buffered" "i") > #0
    then #false
    else #true).

(* Flush persists all allocated data atomically

   returns false on allocator failure *)
Definition Inode__Flush: val :=
  rec: "Inode__Flush" "i" "allocator" :=
    lock.acquire (struct.loadF Inode "m" "i");;
    let: "ok" := Inode__flush "i" "allocator" in
    lock.release (struct.loadF Inode "m" "i");;
    "ok".

(* assumes lock is held *)
Definition Inode__append: val :=
  rec: "Inode__append" "i" "b" :=
    (if: slice.len (struct.loadF Inode "addrs" "i") + slice.len (struct.loadF Inode "buffered" "i") ≥ MaxBlocks
    then #false
    else
      struct.storeF Inode "buffered" "i" (SliceAppend (slice.T byteT) (struct.loadF Inode "buffered" "i") "b");;
      #true).

(* Append adds a block to the inode, without making it persistent.

   Returns false on failure (if the allocator or inode are out of space) *)
Definition Inode__Append: val :=
  rec: "Inode__Append" "i" "b" :=
    lock.acquire (struct.loadF Inode "m" "i");;
    let: "ok" := Inode__append "i" "b" in
    lock.release (struct.loadF Inode "m" "i");;
    "ok".
