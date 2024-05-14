(* autogenerated from github.com/mit-pdos/perennial-examples/indirect_inode *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.mit_dash_pdos.perennial_dash_examples.alloc.
From Goose Require github_dot_com.tchajed.goose.machine.disk.
From Goose Require github_dot_com.tchajed.marshal.
From Goose Require sync.

From Perennial.goose_lang Require Import ffi.disk_prelude.

Definition MaxBlocks : expr := #500 + (#10 * #512).

Definition maxDirect : expr := #500.

Definition maxIndirect : expr := #10.

Definition indirectNumBlocks : expr := #512.

Definition Inode := struct.decl [
  "d" :: disk.Disk;
  "m" :: ptrT;
  "addr" :: uint64T;
  "size" :: uint64T;
  "direct" :: slice.T uint64T;
  "indirect" :: slice.T uint64T
].

Definition min: val :=
  rec: "min" "a" "b" :=
    (if: "a" ≤ "b"
    then "a"
    else "b").

Definition Open: val :=
  rec: "Open" "d" "addr" :=
    let: "b" := disk.Read "addr" in
    let: "dec" := marshal.NewDec "b" in
    let: "size" := marshal.Dec__GetInt "dec" in
    let: "direct" := marshal.Dec__GetInts "dec" maxDirect in
    let: "indirect" := marshal.Dec__GetInts "dec" maxIndirect in
    let: "numIndirect" := marshal.Dec__GetInt "dec" in
    let: "numDirect" := min "size" maxDirect in
    struct.new Inode [
      "d" ::= "d";
      "m" ::= struct.alloc sync.Mutex (zero_val (struct.t sync.Mutex));
      "size" ::= "size";
      "addr" ::= "addr";
      "direct" ::= SliceTake "direct" "numDirect";
      "indirect" ::= SliceTake "indirect" "numIndirect"
    ].

Definition readIndirect: val :=
  rec: "readIndirect" "d" "a" :=
    let: "b" := disk.Read "a" in
    let: "dec" := marshal.NewDec "b" in
    marshal.Dec__GetInts "dec" indirectNumBlocks.

Definition prepIndirect: val :=
  rec: "prepIndirect" "addrs" :=
    let: "enc" := marshal.NewEnc disk.BlockSize in
    marshal.Enc__PutInts "enc" "addrs";;
    marshal.Enc__Finish "enc".

Definition Inode__UsedBlocks: val :=
  rec: "Inode__UsedBlocks" "i" :=
    let: "addrs" := ref (zero_val (slice.T uint64T)) in
    "addrs" <-[slice.T uint64T] (NewSlice uint64T #0);;
    let: "direct" := struct.loadF Inode "direct" "i" in
    let: "indirect" := struct.loadF Inode "indirect" "i" in
    ForSlice uint64T <> "a" "direct"
      ("addrs" <-[slice.T uint64T] (SliceAppend uint64T (![slice.T uint64T] "addrs") "a"));;
    ForSlice uint64T <> "blkAddr" "indirect"
      ("addrs" <-[slice.T uint64T] (SliceAppend uint64T (![slice.T uint64T] "addrs") "blkAddr"));;
    ForSlice uint64T <> "blkAddr" "indirect"
      ("addrs" <-[slice.T uint64T] (SliceAppendSlice uint64T (![slice.T uint64T] "addrs") (readIndirect (struct.loadF Inode "d" "i") "blkAddr")));;
    ![slice.T uint64T] "addrs".

Definition indNum: val :=
  rec: "indNum" "off" :=
    ("off" - maxDirect) `quot` indirectNumBlocks.

Definition indOff: val :=
  rec: "indOff" "off" :=
    ("off" - maxDirect) `rem` indirectNumBlocks.

Definition Inode__Read: val :=
  rec: "Inode__Read" "i" "off" :=
    sync.Mutex__Lock (struct.loadF Inode "m" "i");;
    (if: "off" ≥ (struct.loadF Inode "size" "i")
    then
      sync.Mutex__Unlock (struct.loadF Inode "m" "i");;
      slice.nil
    else
      (if: "off" < maxDirect
      then
        let: "a" := SliceGet uint64T (struct.loadF Inode "direct" "i") "off" in
        let: "b" := disk.Read "a" in
        sync.Mutex__Unlock (struct.loadF Inode "m" "i");;
        "b"
      else
        let: "addrs" := readIndirect (struct.loadF Inode "d" "i") (SliceGet uint64T (struct.loadF Inode "indirect" "i") (indNum "off")) in
        let: "b" := disk.Read (SliceGet uint64T "addrs" (indOff "off")) in
        sync.Mutex__Unlock (struct.loadF Inode "m" "i");;
        "b")).

Definition Inode__Size: val :=
  rec: "Inode__Size" "i" :=
    sync.Mutex__Lock (struct.loadF Inode "m" "i");;
    let: "sz" := struct.loadF Inode "size" "i" in
    sync.Mutex__Unlock (struct.loadF Inode "m" "i");;
    "sz".

Definition padInts: val :=
  rec: "padInts" "enc" "num" :=
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, (![uint64T] "i") < "num"); (λ: <>, "i" <-[uint64T] ((![uint64T] "i") + #1)) := λ: <>,
      marshal.Enc__PutInt "enc" #0;;
      Continue);;
    #().

Definition Inode__mkHdr: val :=
  rec: "Inode__mkHdr" "i" :=
    let: "enc" := marshal.NewEnc disk.BlockSize in
    marshal.Enc__PutInt "enc" (struct.loadF Inode "size" "i");;
    marshal.Enc__PutInts "enc" (struct.loadF Inode "direct" "i");;
    padInts "enc" (maxDirect - (slice.len (struct.loadF Inode "direct" "i")));;
    marshal.Enc__PutInts "enc" (struct.loadF Inode "indirect" "i");;
    padInts "enc" (maxIndirect - (slice.len (struct.loadF Inode "indirect" "i")));;
    marshal.Enc__PutInt "enc" (slice.len (struct.loadF Inode "indirect" "i"));;
    let: "hdr" := marshal.Enc__Finish "enc" in
    "hdr".

Definition Inode__inSize: val :=
  rec: "Inode__inSize" "i" :=
    let: "hdr" := Inode__mkHdr "i" in
    disk.Write (struct.loadF Inode "addr" "i") "hdr";;
    #().

(* checkTotalSize determines that the inode is not already at maximum size

   Requires the lock to be held. *)
Definition Inode__checkTotalSize: val :=
  rec: "Inode__checkTotalSize" "i" :=
    (if: (struct.loadF Inode "size" "i") ≥ MaxBlocks
    then #false
    else #true).

(* appendDirect attempts to append the block stored at a without allocating new metadata blocks.

   Requires the lock to be held.

   Fails when the inode does not have direct block space. *)
Definition Inode__appendDirect: val :=
  rec: "Inode__appendDirect" "i" "a" :=
    (if: (struct.loadF Inode "size" "i") < maxDirect
    then
      struct.storeF Inode "direct" "i" (SliceAppend uint64T (struct.loadF Inode "direct" "i") "a");;
      struct.storeF Inode "size" "i" ((struct.loadF Inode "size" "i") + #1);;
      let: "hdr" := Inode__mkHdr "i" in
      disk.Write (struct.loadF Inode "addr" "i") "hdr";;
      #true
    else #false).

(* writeIndirect preps the block of addrs and
   adds the new indirect block to the inode on disk

   Requires the lock to be held. *)
Definition Inode__writeIndirect: val :=
  rec: "Inode__writeIndirect" "i" "indAddr" "addrs" :=
    let: "diskBlk" := prepIndirect "addrs" in
    disk.Write "indAddr" "diskBlk";;
    struct.storeF Inode "size" "i" ((struct.loadF Inode "size" "i") + #1);;
    let: "hdr" := Inode__mkHdr "i" in
    disk.Write (struct.loadF Inode "addr" "i") "hdr";;
    #().

(* appendIndirect adds address a (and whatever data is stored there) to the
   inode using space in an existing indirect block, without allocation

   Requires the lock to be held.

   Assumes there is no direct block space left, but can fail if the last
   indirect block is full. *)
Definition Inode__appendIndirect: val :=
  rec: "Inode__appendIndirect" "i" "a" :=
    (if: (indNum (struct.loadF Inode "size" "i")) ≥ (slice.len (struct.loadF Inode "indirect" "i"))
    then #false
    else
      let: "indAddr" := SliceGet uint64T (struct.loadF Inode "indirect" "i") (indNum (struct.loadF Inode "size" "i")) in
      let: "addrs" := readIndirect (struct.loadF Inode "d" "i") "indAddr" in
      SliceSet uint64T "addrs" (indOff (struct.loadF Inode "size" "i")) "a";;
      Inode__writeIndirect "i" "indAddr" "addrs";;
      #true).

(* Append adds a block to the inode.

   Returns false on failure (if the allocator or inode are out of space) *)
Definition Inode__Append: val :=
  rec: "Inode__Append" "i" "b" "allocator" :=
    sync.Mutex__Lock (struct.loadF Inode "m" "i");;
    let: "ok" := Inode__checkTotalSize "i" in
    (if: (~ "ok")
    then
      sync.Mutex__Unlock (struct.loadF Inode "m" "i");;
      #false
    else
      let: ("a", "ok2") := alloc.Allocator__Reserve "allocator" in
      (if: (~ "ok2")
      then
        sync.Mutex__Unlock (struct.loadF Inode "m" "i");;
        #false
      else
        disk.Write "a" "b";;
        let: "ok3" := Inode__appendDirect "i" "a" in
        (if: "ok3"
        then
          sync.Mutex__Unlock (struct.loadF Inode "m" "i");;
          #true
        else
          let: "ok4" := Inode__appendIndirect "i" "a" in
          (if: "ok4"
          then
            sync.Mutex__Unlock (struct.loadF Inode "m" "i");;
            #true
          else
            let: ("indAddr", "ok") := alloc.Allocator__Reserve "allocator" in
            (if: (~ "ok")
            then
              sync.Mutex__Unlock (struct.loadF Inode "m" "i");;
              alloc.Allocator__Free "allocator" "a";;
              #false
            else
              struct.storeF Inode "indirect" "i" (SliceAppend uint64T (struct.loadF Inode "indirect" "i") "indAddr");;
              Inode__writeIndirect "i" "indAddr" (SliceSingleton "a");;
              sync.Mutex__Unlock (struct.loadF Inode "m" "i");;
              #true))))).