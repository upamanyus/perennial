(* autogenerated from github.com/mit-pdos/go-nfsd/simple *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.mit_dash_pdos.go_dash_journal.addr.
From Goose Require github_dot_com.mit_dash_pdos.go_dash_journal.buf.
From Goose Require github_dot_com.mit_dash_pdos.go_dash_journal.common.
From Goose Require github_dot_com.mit_dash_pdos.go_dash_journal.jrnl.
From Goose Require github_dot_com.mit_dash_pdos.go_dash_journal.lockmap.
From Goose Require github_dot_com.mit_dash_pdos.go_dash_journal.obj.
From Goose Require github_dot_com.mit_dash_pdos.go_dash_journal.util.
From Goose Require github_dot_com.mit_dash_pdos.go_dash_nfsd.nfstypes.
From Goose Require github_dot_com.tchajed.goose.machine.disk.
From Goose Require github_dot_com.tchajed.marshal.

From Perennial.goose_lang Require Import ffi.disk_prelude.

(* 0super.go *)

Definition block2addr: val :=
  rec: "block2addr" "blkno" :=
    addr.MkAddr "blkno" #0.

Definition nInode: val :=
  rec: "nInode" <> :=
    common.INODEBLK.

Definition inum2Addr: val :=
  rec: "inum2Addr" "inum" :=
    addr.MkAddr common.LOGSIZE (("inum" * common.INODESZ) * #8).

(* fh.go *)

Definition Fh := struct.decl [
  "Ino" :: uint64T
].

Definition MakeFh: val :=
  rec: "MakeFh" "fh3" :=
    let: "dec" := marshal.NewDec (struct.get nfstypes.Nfs_fh3 "Data" "fh3") in
    let: "i" := marshal.Dec__GetInt "dec" in
    struct.mk Fh [
      "Ino" ::= "i"
    ].

Definition Fh__MakeFh3: val :=
  rec: "Fh__MakeFh3" "fh" :=
    let: "enc" := marshal.NewEnc #16 in
    marshal.Enc__PutInt "enc" (struct.get Fh "Ino" "fh");;
    let: "fh3" := struct.mk nfstypes.Nfs_fh3 [
      "Data" ::= marshal.Enc__Finish "enc"
    ] in
    "fh3".

Definition MkRootFh3: val :=
  rec: "MkRootFh3" <> :=
    let: "enc" := marshal.NewEnc #16 in
    marshal.Enc__PutInt "enc" common.ROOTINUM;;
    struct.mk nfstypes.Nfs_fh3 [
      "Data" ::= marshal.Enc__Finish "enc"
    ].

(* inode.go *)

Definition Inode := struct.decl [
  "Inum" :: uint64T;
  "Size" :: uint64T;
  "Data" :: uint64T
].

Definition Inode__Encode: val :=
  rec: "Inode__Encode" "ip" :=
    let: "enc" := marshal.NewEnc common.INODESZ in
    marshal.Enc__PutInt "enc" (struct.loadF Inode "Size" "ip");;
    marshal.Enc__PutInt "enc" (struct.loadF Inode "Data" "ip");;
    marshal.Enc__Finish "enc".

Definition Decode: val :=
  rec: "Decode" "buf" "inum" :=
    let: "ip" := struct.alloc Inode (zero_val (struct.t Inode)) in
    let: "dec" := marshal.NewDec (struct.loadF buf.Buf "Data" "buf") in
    struct.storeF Inode "Inum" "ip" "inum";;
    struct.storeF Inode "Size" "ip" (marshal.Dec__GetInt "dec");;
    struct.storeF Inode "Data" "ip" (marshal.Dec__GetInt "dec");;
    "ip".

(* Returns number of bytes read and eof *)
Definition Inode__Read: val :=
  rec: "Inode__Read" "ip" "op" "offset" "bytesToRead" :=
    (if: "offset" ≥ (struct.loadF Inode "Size" "ip")
    then (slice.nil, #true)
    else
      let: "count" := ref_to uint64T "bytesToRead" in
      (if: (![uint64T] "count") > ((struct.loadF Inode "Size" "ip") - "offset")
      then "count" <-[uint64T] ((struct.loadF Inode "Size" "ip") - "offset")
      else #());;
      util.DPrintf #5 #(str"Read: off %d cnt %d
      ") #();;
      let: "data" := ref_to (slice.T byteT) (NewSlice byteT #0) in
      let: "buf" := jrnl.Op__ReadBuf "op" (block2addr (struct.loadF Inode "Data" "ip")) common.NBITBLOCK in
      let: "countCopy" := ![uint64T] "count" in
      let: "b" := ref_to uint64T #0 in
      (for: (λ: <>, (![uint64T] "b") < "countCopy"); (λ: <>, "b" <-[uint64T] ((![uint64T] "b") + #1)) := λ: <>,
        "data" <-[slice.T byteT] (SliceAppend byteT (![slice.T byteT] "data") (SliceGet byteT (struct.loadF buf.Buf "Data" "buf") ("offset" + (![uint64T] "b"))));;
        Continue);;
      let: "eof" := ("offset" + (![uint64T] "count")) ≥ (struct.loadF Inode "Size" "ip") in
      util.DPrintf #10 #(str"Read: off %d cnt %d -> %v, %v
      ") #();;
      (![slice.T byteT] "data", "eof")).

Definition Inode__WriteInode: val :=
  rec: "Inode__WriteInode" "ip" "op" :=
    let: "d" := Inode__Encode "ip" in
    jrnl.Op__OverWrite "op" (inum2Addr (struct.loadF Inode "Inum" "ip")) (common.INODESZ * #8) "d";;
    util.DPrintf #1 #(str"WriteInode %v
    ") #();;
    #().

(* Returns number of bytes written and error *)
Definition Inode__Write: val :=
  rec: "Inode__Write" "ip" "op" "offset" "count" "dataBuf" :=
    util.DPrintf #5 #(str"Write: off %d cnt %d
    ") #();;
    (if: "count" ≠ (slice.len "dataBuf")
    then (#0, #false)
    else
      (if: util.SumOverflows "offset" "count"
      then (#0, #false)
      else
        (if: ("offset" + "count") > disk.BlockSize
        then (#0, #false)
        else
          (if: "offset" > (struct.loadF Inode "Size" "ip")
          then (#0, #false)
          else
            let: "buffer" := jrnl.Op__ReadBuf "op" (block2addr (struct.loadF Inode "Data" "ip")) common.NBITBLOCK in
            let: "b" := ref_to uint64T #0 in
            (for: (λ: <>, (![uint64T] "b") < "count"); (λ: <>, "b" <-[uint64T] ((![uint64T] "b") + #1)) := λ: <>,
              SliceSet byteT (struct.loadF buf.Buf "Data" "buffer") ("offset" + (![uint64T] "b")) (SliceGet byteT "dataBuf" (![uint64T] "b"));;
              Continue);;
            buf.Buf__SetDirty "buffer";;
            util.DPrintf #1 #(str"Write: off %d cnt %d size %d
            ") #();;
            (if: ("offset" + "count") > (struct.loadF Inode "Size" "ip")
            then
              struct.storeF Inode "Size" "ip" ("offset" + "count");;
              Inode__WriteInode "ip" "op"
            else #());;
            ("count", #true))))).

Definition ReadInode: val :=
  rec: "ReadInode" "op" "inum" :=
    let: "buffer" := jrnl.Op__ReadBuf "op" (inum2Addr "inum") (common.INODESZ * #8) in
    let: "ip" := Decode "buffer" "inum" in
    "ip".

Definition Inode__MkFattr: val :=
  rec: "Inode__MkFattr" "ip" :=
    struct.mk nfstypes.Fattr3 [
      "Ftype" ::= nfstypes.NF3REG;
      "Mode" ::= #(U32 511);
      "Nlink" ::= #(U32 1);
      "Uid" ::= #(U32 0);
      "Gid" ::= #(U32 0);
      "Size" ::= struct.loadF Inode "Size" "ip";
      "Used" ::= struct.loadF Inode "Size" "ip";
      "Rdev" ::= struct.mk nfstypes.Specdata3 [
        "Specdata1" ::= #(U32 0);
        "Specdata2" ::= #(U32 0)
      ];
      "Fsid" ::= #0;
      "Fileid" ::= struct.loadF Inode "Inum" "ip";
      "Atime" ::= struct.mk nfstypes.Nfstime3 [
        "Seconds" ::= #(U32 0);
        "Nseconds" ::= #(U32 0)
      ];
      "Mtime" ::= struct.mk nfstypes.Nfstime3 [
        "Seconds" ::= #(U32 0);
        "Nseconds" ::= #(U32 0)
      ];
      "Ctime" ::= struct.mk nfstypes.Nfstime3 [
        "Seconds" ::= #(U32 0);
        "Nseconds" ::= #(U32 0)
      ]
    ].

Definition inodeInit: val :=
  rec: "inodeInit" "op" :=
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, (![uint64T] "i") < (nInode #())); (λ: <>, "i" <-[uint64T] ((![uint64T] "i") + #1)) := λ: <>,
      let: "ip" := ReadInode "op" (![uint64T] "i") in
      struct.storeF Inode "Data" "ip" ((common.LOGSIZE + #1) + (![uint64T] "i"));;
      Inode__WriteInode "ip" "op";;
      Continue);;
    #().

(* mkfs.go *)

Definition Nfs := struct.decl [
  "t" :: ptrT;
  "l" :: ptrT
].

Definition Mkfs: val :=
  rec: "Mkfs" "d" :=
    let: "log" := obj.MkLog "d" in
    let: "op" := jrnl.Begin "log" in
    inodeInit "op";;
    let: "ok" := jrnl.Op__CommitWait "op" #true in
    (if: (~ "ok")
    then slice.nil
    else "log").

Definition Recover: val :=
  rec: "Recover" "d" :=
    let: "log" := obj.MkLog "d" in
    let: "lockmap" := lockmap.MkLockMap #() in
    let: "nfs" := struct.new Nfs [
      "t" ::= "log";
      "l" ::= "lockmap"
    ] in
    "nfs".

Definition MakeNfs: val :=
  rec: "MakeNfs" "d" :=
    let: "log" := obj.MkLog "d" in
    let: "op" := jrnl.Begin "log" in
    inodeInit "op";;
    let: "ok" := jrnl.Op__CommitWait "op" #true in
    (if: (~ "ok")
    then slice.nil
    else
      let: "lockmap" := lockmap.MkLockMap #() in
      let: "nfs" := struct.new Nfs [
        "t" ::= "log";
        "l" ::= "lockmap"
      ] in
      "nfs").

(* mount.go *)

Definition Nfs__MOUNTPROC3_NULL: val :=
  rec: "Nfs__MOUNTPROC3_NULL" "nfs" :=
    #().

Definition Nfs__MOUNTPROC3_MNT: val :=
  rec: "Nfs__MOUNTPROC3_MNT" "nfs" "args" :=
    let: "reply" := struct.alloc nfstypes.Mountres3 (zero_val (struct.t nfstypes.Mountres3)) in
    (* log.Printf("Mount %v\n", args) *)
    struct.storeF nfstypes.Mountres3 "Fhs_status" "reply" nfstypes.MNT3_OK;;
    struct.storeF nfstypes.Mountres3_ok "Fhandle" (struct.fieldRef nfstypes.Mountres3 "Mountinfo" "reply") (struct.get nfstypes.Nfs_fh3 "Data" (MkRootFh3 #()));;
    struct.load nfstypes.Mountres3 "reply".

Definition Nfs__MOUNTPROC3_UMNT: val :=
  rec: "Nfs__MOUNTPROC3_UMNT" "nfs" "args" :=
    (* log.Printf("Unmount %v\n", args) *)
    #().

Definition Nfs__MOUNTPROC3_UMNTALL: val :=
  rec: "Nfs__MOUNTPROC3_UMNTALL" "nfs" :=
    (* log.Printf("Unmountall\n") *)
    #().

Definition Nfs__MOUNTPROC3_DUMP: val :=
  rec: "Nfs__MOUNTPROC3_DUMP" "nfs" :=
    (* log.Printf("Dump\n") *)
    struct.mk nfstypes.Mountopt3 [
      "P" ::= slice.nil
    ].

Definition Nfs__MOUNTPROC3_EXPORT: val :=
  rec: "Nfs__MOUNTPROC3_EXPORT" "nfs" :=
    let: "res" := struct.mk nfstypes.Exports3 [
      "Ex_dir" ::= #(str"");
      "Ex_groups" ::= slice.nil;
      "Ex_next" ::= slice.nil
    ] in
    struct.storeF nfstypes.Exports3 "Ex_dir" "res" #(str"/");;
    struct.mk nfstypes.Exportsopt3 [
      "P" ::= "res"
    ].

(* ops.go *)

Definition fh2ino: val :=
  rec: "fh2ino" "fh3" :=
    let: "fh" := MakeFh "fh3" in
    struct.get Fh "Ino" "fh".

Definition rootFattr: val :=
  rec: "rootFattr" <> :=
    struct.mk nfstypes.Fattr3 [
      "Ftype" ::= nfstypes.NF3DIR;
      "Mode" ::= #(U32 511);
      "Nlink" ::= #(U32 1);
      "Uid" ::= #(U32 0);
      "Gid" ::= #(U32 0);
      "Size" ::= #0;
      "Used" ::= #0;
      "Rdev" ::= struct.mk nfstypes.Specdata3 [
        "Specdata1" ::= #(U32 0);
        "Specdata2" ::= #(U32 0)
      ];
      "Fsid" ::= #0;
      "Fileid" ::= common.ROOTINUM;
      "Atime" ::= struct.mk nfstypes.Nfstime3 [
        "Seconds" ::= #(U32 0);
        "Nseconds" ::= #(U32 0)
      ];
      "Mtime" ::= struct.mk nfstypes.Nfstime3 [
        "Seconds" ::= #(U32 0);
        "Nseconds" ::= #(U32 0)
      ];
      "Ctime" ::= struct.mk nfstypes.Nfstime3 [
        "Seconds" ::= #(U32 0);
        "Nseconds" ::= #(U32 0)
      ]
    ].

Definition Nfs__NFSPROC3_NULL: val :=
  rec: "Nfs__NFSPROC3_NULL" "nfs" :=
    util.DPrintf #0 #(str"NFS Null
    ") #();;
    #().

Definition validInum: val :=
  rec: "validInum" "inum" :=
    (if: "inum" = #0
    then #false
    else
      (if: "inum" = common.ROOTINUM
      then #false
      else
        (if: "inum" ≥ (nInode #())
        then #false
        else #true))).

Definition NFSPROC3_GETATTR_wp: val :=
  rec: "NFSPROC3_GETATTR_wp" "args" "reply" "inum" "op" :=
    let: "ip" := ReadInode "op" "inum" in
    struct.storeF nfstypes.GETATTR3resok "Obj_attributes" (struct.fieldRef nfstypes.GETATTR3res "Resok" "reply") (Inode__MkFattr "ip");;
    #().

Definition NFSPROC3_GETATTR_internal: val :=
  rec: "NFSPROC3_GETATTR_internal" "args" "reply" "inum" "op" :=
    NFSPROC3_GETATTR_wp "args" "reply" "inum" "op";;
    let: "ok" := jrnl.Op__CommitWait "op" #true in
    (if: "ok"
    then
      struct.storeF nfstypes.GETATTR3res "Status" "reply" nfstypes.NFS3_OK;;
      #()
    else
      struct.storeF nfstypes.GETATTR3res "Status" "reply" nfstypes.NFS3ERR_SERVERFAULT;;
      #()).

Definition Nfs__NFSPROC3_GETATTR: val :=
  rec: "Nfs__NFSPROC3_GETATTR" "nfs" "args" :=
    let: "reply" := ref (zero_val (struct.t nfstypes.GETATTR3res)) in
    util.DPrintf #1 #(str"NFS GetAttr %v
    ") #();;
    let: "txn" := jrnl.Begin (struct.loadF Nfs "t" "nfs") in
    let: "inum" := fh2ino (struct.get nfstypes.GETATTR3args "Object" "args") in
    (if: "inum" = common.ROOTINUM
    then
      struct.storeF nfstypes.GETATTR3res "Status" "reply" nfstypes.NFS3_OK;;
      struct.storeF nfstypes.GETATTR3resok "Obj_attributes" (struct.fieldRef nfstypes.GETATTR3res "Resok" "reply") (rootFattr #());;
      ![struct.t nfstypes.GETATTR3res] "reply"
    else
      (if: (~ (validInum "inum"))
      then
        struct.storeF nfstypes.GETATTR3res "Status" "reply" nfstypes.NFS3ERR_INVAL;;
        ![struct.t nfstypes.GETATTR3res] "reply"
      else
        lockmap.LockMap__Acquire (struct.loadF Nfs "l" "nfs") "inum";;
        NFSPROC3_GETATTR_internal "args" "reply" "inum" "txn";;
        lockmap.LockMap__Release (struct.loadF Nfs "l" "nfs") "inum";;
        ![struct.t nfstypes.GETATTR3res] "reply")).

Definition NFSPROC3_SETATTR_wp: val :=
  rec: "NFSPROC3_SETATTR_wp" "args" "reply" "inum" "op" :=
    let: "ip" := ReadInode "op" "inum" in
    let: "ok" := ref (zero_val boolT) in
    (if: struct.get nfstypes.Set_size3 "Set_it" (struct.get nfstypes.Sattr3 "Size" (struct.get nfstypes.SETATTR3args "New_attributes" "args"))
    then
      let: "newsize" := struct.get nfstypes.Set_size3 "Size" (struct.get nfstypes.Sattr3 "Size" (struct.get nfstypes.SETATTR3args "New_attributes" "args")) in
      (if: (struct.loadF Inode "Size" "ip") < "newsize"
      then
        let: "data" := NewSlice byteT ("newsize" - (struct.loadF Inode "Size" "ip")) in
        Inode__Write "ip" "op" (struct.loadF Inode "Size" "ip") ("newsize" - (struct.loadF Inode "Size" "ip")) "data";;
        (if: (struct.loadF Inode "Size" "ip") ≠ "newsize"
        then struct.storeF nfstypes.SETATTR3res "Status" "reply" nfstypes.NFS3ERR_NOSPC
        else "ok" <-[boolT] #true)
      else
        struct.storeF Inode "Size" "ip" "newsize";;
        Inode__WriteInode "ip" "op";;
        "ok" <-[boolT] #true)
    else "ok" <-[boolT] #true);;
    ![boolT] "ok".

Definition NFSPROC3_SETATTR_internal: val :=
  rec: "NFSPROC3_SETATTR_internal" "args" "reply" "inum" "op" :=
    let: "ok1" := NFSPROC3_SETATTR_wp "args" "reply" "inum" "op" in
    (if: (~ "ok1")
    then #()
    else
      let: "ok2" := jrnl.Op__CommitWait "op" #true in
      (if: "ok2"
      then
        struct.storeF nfstypes.SETATTR3res "Status" "reply" nfstypes.NFS3_OK;;
        #()
      else
        struct.storeF nfstypes.SETATTR3res "Status" "reply" nfstypes.NFS3ERR_SERVERFAULT;;
        #())).

Definition Nfs__NFSPROC3_SETATTR: val :=
  rec: "Nfs__NFSPROC3_SETATTR" "nfs" "args" :=
    let: "reply" := ref (zero_val (struct.t nfstypes.SETATTR3res)) in
    util.DPrintf #1 #(str"NFS SetAttr %v
    ") #();;
    let: "txn" := jrnl.Begin (struct.loadF Nfs "t" "nfs") in
    let: "inum" := fh2ino (struct.get nfstypes.SETATTR3args "Object" "args") in
    util.DPrintf #1 #(str"inum %d %d
    ") #();;
    (if: (~ (validInum "inum"))
    then
      struct.storeF nfstypes.SETATTR3res "Status" "reply" nfstypes.NFS3ERR_INVAL;;
      ![struct.t nfstypes.SETATTR3res] "reply"
    else
      lockmap.LockMap__Acquire (struct.loadF Nfs "l" "nfs") "inum";;
      NFSPROC3_SETATTR_internal "args" "reply" "inum" "txn";;
      lockmap.LockMap__Release (struct.loadF Nfs "l" "nfs") "inum";;
      ![struct.t nfstypes.SETATTR3res] "reply").

(* Lookup must lock child inode to find gen number *)
Definition Nfs__NFSPROC3_LOOKUP: val :=
  rec: "Nfs__NFSPROC3_LOOKUP" "nfs" "args" :=
    util.DPrintf #1 #(str"NFS Lookup %v
    ") #();;
    let: "reply" := ref (zero_val (struct.t nfstypes.LOOKUP3res)) in
    let: "fn" := struct.get nfstypes.Diropargs3 "Name" (struct.get nfstypes.LOOKUP3args "What" "args") in
    let: "inum" := ref (zero_val uint64T) in
    (if: "fn" = #(str"a")
    then "inum" <-[uint64T] #2
    else #());;
    (if: "fn" = #(str"b")
    then "inum" <-[uint64T] #3
    else #());;
    (if: (~ (validInum (![uint64T] "inum")))
    then
      struct.storeF nfstypes.LOOKUP3res "Status" "reply" nfstypes.NFS3ERR_NOENT;;
      ![struct.t nfstypes.LOOKUP3res] "reply"
    else
      let: "fh" := struct.mk Fh [
        "Ino" ::= ![uint64T] "inum"
      ] in
      struct.storeF nfstypes.LOOKUP3resok "Object" (struct.fieldRef nfstypes.LOOKUP3res "Resok" "reply") (Fh__MakeFh3 "fh");;
      struct.storeF nfstypes.LOOKUP3res "Status" "reply" nfstypes.NFS3_OK;;
      ![struct.t nfstypes.LOOKUP3res] "reply").

Definition Nfs__NFSPROC3_ACCESS: val :=
  rec: "Nfs__NFSPROC3_ACCESS" "nfs" "args" :=
    util.DPrintf #1 #(str"NFS Access %v
    ") #();;
    let: "reply" := ref (zero_val (struct.t nfstypes.ACCESS3res)) in
    struct.storeF nfstypes.ACCESS3res "Status" "reply" nfstypes.NFS3_OK;;
    struct.storeF nfstypes.ACCESS3resok "Access" (struct.fieldRef nfstypes.ACCESS3res "Resok" "reply") (((((nfstypes.ACCESS3_READ `or` nfstypes.ACCESS3_LOOKUP) `or` nfstypes.ACCESS3_MODIFY) `or` nfstypes.ACCESS3_EXTEND) `or` nfstypes.ACCESS3_DELETE) `or` nfstypes.ACCESS3_EXECUTE);;
    ![struct.t nfstypes.ACCESS3res] "reply".

Definition NFSPROC3_READ_wp: val :=
  rec: "NFSPROC3_READ_wp" "args" "reply" "inum" "op" :=
    let: "ip" := ReadInode "op" "inum" in
    let: ("data", "eof") := Inode__Read "ip" "op" (struct.get nfstypes.READ3args "Offset" "args") (to_u64 (struct.get nfstypes.READ3args "Count" "args")) in
    struct.storeF nfstypes.READ3resok "Count" (struct.fieldRef nfstypes.READ3res "Resok" "reply") (to_u32 (slice.len "data"));;
    struct.storeF nfstypes.READ3resok "Data" (struct.fieldRef nfstypes.READ3res "Resok" "reply") "data";;
    struct.storeF nfstypes.READ3resok "Eof" (struct.fieldRef nfstypes.READ3res "Resok" "reply") "eof";;
    #().

Definition NFSPROC3_READ_internal: val :=
  rec: "NFSPROC3_READ_internal" "args" "reply" "inum" "op" :=
    NFSPROC3_READ_wp "args" "reply" "inum" "op";;
    let: "ok" := jrnl.Op__CommitWait "op" #true in
    (if: "ok"
    then
      struct.storeF nfstypes.READ3res "Status" "reply" nfstypes.NFS3_OK;;
      #()
    else
      struct.storeF nfstypes.READ3res "Status" "reply" nfstypes.NFS3ERR_SERVERFAULT;;
      #()).

Definition Nfs__NFSPROC3_READ: val :=
  rec: "Nfs__NFSPROC3_READ" "nfs" "args" :=
    let: "reply" := ref (zero_val (struct.t nfstypes.READ3res)) in
    util.DPrintf #1 #(str"NFS Read %v %d %d
    ") #();;
    let: "txn" := jrnl.Begin (struct.loadF Nfs "t" "nfs") in
    let: "inum" := fh2ino (struct.get nfstypes.READ3args "File" "args") in
    (if: (~ (validInum "inum"))
    then
      struct.storeF nfstypes.READ3res "Status" "reply" nfstypes.NFS3ERR_INVAL;;
      ![struct.t nfstypes.READ3res] "reply"
    else
      lockmap.LockMap__Acquire (struct.loadF Nfs "l" "nfs") "inum";;
      NFSPROC3_READ_internal "args" "reply" "inum" "txn";;
      lockmap.LockMap__Release (struct.loadF Nfs "l" "nfs") "inum";;
      ![struct.t nfstypes.READ3res] "reply").

Definition NFSPROC3_WRITE_wp: val :=
  rec: "NFSPROC3_WRITE_wp" "args" "reply" "inum" "op" :=
    let: "ip" := ReadInode "op" "inum" in
    let: ("count", "writeok") := Inode__Write "ip" "op" (struct.get nfstypes.WRITE3args "Offset" "args") (to_u64 (struct.get nfstypes.WRITE3args "Count" "args")) (struct.get nfstypes.WRITE3args "Data" "args") in
    (if: (~ "writeok")
    then
      struct.storeF nfstypes.WRITE3res "Status" "reply" nfstypes.NFS3ERR_SERVERFAULT;;
      #false
    else
      struct.storeF nfstypes.WRITE3resok "Count" (struct.fieldRef nfstypes.WRITE3res "Resok" "reply") (to_u32 "count");;
      struct.storeF nfstypes.WRITE3resok "Committed" (struct.fieldRef nfstypes.WRITE3res "Resok" "reply") nfstypes.FILE_SYNC;;
      #true).

Definition NFSPROC3_WRITE_internal: val :=
  rec: "NFSPROC3_WRITE_internal" "args" "reply" "inum" "op" :=
    let: "ok1" := NFSPROC3_WRITE_wp "args" "reply" "inum" "op" in
    (if: (~ "ok1")
    then #()
    else
      let: "ok2" := jrnl.Op__CommitWait "op" #true in
      (if: "ok2"
      then
        struct.storeF nfstypes.WRITE3res "Status" "reply" nfstypes.NFS3_OK;;
        #()
      else
        struct.storeF nfstypes.WRITE3res "Status" "reply" nfstypes.NFS3ERR_SERVERFAULT;;
        #())).

Definition Nfs__NFSPROC3_WRITE: val :=
  rec: "Nfs__NFSPROC3_WRITE" "nfs" "args" :=
    let: "reply" := ref (zero_val (struct.t nfstypes.WRITE3res)) in
    util.DPrintf #1 #(str"NFS Write %v off %d cnt %d how %d
    ") #();;
    let: "txn" := jrnl.Begin (struct.loadF Nfs "t" "nfs") in
    let: "inum" := fh2ino (struct.get nfstypes.WRITE3args "File" "args") in
    util.DPrintf #1 #(str"inum %d %d
    ") #();;
    (if: (~ (validInum "inum"))
    then
      struct.storeF nfstypes.WRITE3res "Status" "reply" nfstypes.NFS3ERR_INVAL;;
      ![struct.t nfstypes.WRITE3res] "reply"
    else
      lockmap.LockMap__Acquire (struct.loadF Nfs "l" "nfs") "inum";;
      NFSPROC3_WRITE_internal "args" "reply" "inum" "txn";;
      lockmap.LockMap__Release (struct.loadF Nfs "l" "nfs") "inum";;
      ![struct.t nfstypes.WRITE3res] "reply").

Definition Nfs__NFSPROC3_CREATE: val :=
  rec: "Nfs__NFSPROC3_CREATE" "nfs" "args" :=
    util.DPrintf #1 #(str"NFS Create %v
    ") #();;
    let: "reply" := ref (zero_val (struct.t nfstypes.CREATE3res)) in
    struct.storeF nfstypes.CREATE3res "Status" "reply" nfstypes.NFS3ERR_NOTSUPP;;
    ![struct.t nfstypes.CREATE3res] "reply".

Definition Nfs__NFSPROC3_MKDIR: val :=
  rec: "Nfs__NFSPROC3_MKDIR" "nfs" "args" :=
    util.DPrintf #1 #(str"NFS Mkdir %v
    ") #();;
    let: "reply" := ref (zero_val (struct.t nfstypes.MKDIR3res)) in
    struct.storeF nfstypes.MKDIR3res "Status" "reply" nfstypes.NFS3ERR_NOTSUPP;;
    ![struct.t nfstypes.MKDIR3res] "reply".

Definition Nfs__NFSPROC3_SYMLINK: val :=
  rec: "Nfs__NFSPROC3_SYMLINK" "nfs" "args" :=
    util.DPrintf #1 #(str"NFS Symlink %v
    ") #();;
    let: "reply" := ref (zero_val (struct.t nfstypes.SYMLINK3res)) in
    struct.storeF nfstypes.SYMLINK3res "Status" "reply" nfstypes.NFS3ERR_NOTSUPP;;
    ![struct.t nfstypes.SYMLINK3res] "reply".

Definition Nfs__NFSPROC3_READLINK: val :=
  rec: "Nfs__NFSPROC3_READLINK" "nfs" "args" :=
    util.DPrintf #1 #(str"NFS Readlink %v
    ") #();;
    let: "reply" := ref (zero_val (struct.t nfstypes.READLINK3res)) in
    struct.storeF nfstypes.READLINK3res "Status" "reply" nfstypes.NFS3ERR_NOTSUPP;;
    ![struct.t nfstypes.READLINK3res] "reply".

Definition Nfs__NFSPROC3_MKNOD: val :=
  rec: "Nfs__NFSPROC3_MKNOD" "nfs" "args" :=
    util.DPrintf #1 #(str"NFS Mknod %v
    ") #();;
    let: "reply" := ref (zero_val (struct.t nfstypes.MKNOD3res)) in
    struct.storeF nfstypes.MKNOD3res "Status" "reply" nfstypes.NFS3ERR_NOTSUPP;;
    ![struct.t nfstypes.MKNOD3res] "reply".

Definition Nfs__NFSPROC3_REMOVE: val :=
  rec: "Nfs__NFSPROC3_REMOVE" "nfs" "args" :=
    util.DPrintf #1 #(str"NFS Remove %v
    ") #();;
    let: "reply" := ref (zero_val (struct.t nfstypes.REMOVE3res)) in
    struct.storeF nfstypes.REMOVE3res "Status" "reply" nfstypes.NFS3ERR_NOTSUPP;;
    ![struct.t nfstypes.REMOVE3res] "reply".

Definition Nfs__NFSPROC3_RMDIR: val :=
  rec: "Nfs__NFSPROC3_RMDIR" "nfs" "args" :=
    util.DPrintf #1 #(str"NFS Rmdir %v
    ") #();;
    let: "reply" := ref (zero_val (struct.t nfstypes.RMDIR3res)) in
    struct.storeF nfstypes.RMDIR3res "Status" "reply" nfstypes.NFS3ERR_NOTSUPP;;
    ![struct.t nfstypes.RMDIR3res] "reply".

Definition Nfs__NFSPROC3_RENAME: val :=
  rec: "Nfs__NFSPROC3_RENAME" "nfs" "args" :=
    util.DPrintf #1 #(str"NFS Rename %v
    ") #();;
    let: "reply" := ref (zero_val (struct.t nfstypes.RENAME3res)) in
    struct.storeF nfstypes.RENAME3res "Status" "reply" nfstypes.NFS3ERR_NOTSUPP;;
    ![struct.t nfstypes.RENAME3res] "reply".

Definition Nfs__NFSPROC3_LINK: val :=
  rec: "Nfs__NFSPROC3_LINK" "nfs" "args" :=
    util.DPrintf #1 #(str"NFS Link %v
    ") #();;
    let: "reply" := ref (zero_val (struct.t nfstypes.LINK3res)) in
    struct.storeF nfstypes.LINK3res "Status" "reply" nfstypes.NFS3ERR_NOTSUPP;;
    ![struct.t nfstypes.LINK3res] "reply".

Definition Nfs__NFSPROC3_READDIR: val :=
  rec: "Nfs__NFSPROC3_READDIR" "nfs" "args" :=
    util.DPrintf #1 #(str"NFS Readdir %v
    ") #();;
    let: "reply" := ref (zero_val (struct.t nfstypes.READDIR3res)) in
    let: "e2" := struct.new nfstypes.Entry3 [
      "Fileid" ::= #3;
      "Name" ::= #(str"b");
      "Cookie" ::= #1;
      "Nextentry" ::= slice.nil
    ] in
    let: "e1" := struct.new nfstypes.Entry3 [
      "Fileid" ::= #2;
      "Name" ::= #(str"a");
      "Cookie" ::= #0;
      "Nextentry" ::= "e2"
    ] in
    struct.storeF nfstypes.READDIR3res "Status" "reply" nfstypes.NFS3_OK;;
    struct.storeF nfstypes.READDIR3resok "Reply" (struct.fieldRef nfstypes.READDIR3res "Resok" "reply") (struct.mk nfstypes.Dirlist3 [
      "Entries" ::= "e1";
      "Eof" ::= #true
    ]);;
    ![struct.t nfstypes.READDIR3res] "reply".

Definition Nfs__NFSPROC3_READDIRPLUS: val :=
  rec: "Nfs__NFSPROC3_READDIRPLUS" "nfs" "args" :=
    util.DPrintf #1 #(str"NFS Readdirplus %v
    ") #();;
    let: "reply" := ref (zero_val (struct.t nfstypes.READDIRPLUS3res)) in
    struct.storeF nfstypes.READDIRPLUS3res "Status" "reply" nfstypes.NFS3ERR_NOTSUPP;;
    ![struct.t nfstypes.READDIRPLUS3res] "reply".

Definition Nfs__NFSPROC3_FSSTAT: val :=
  rec: "Nfs__NFSPROC3_FSSTAT" "nfs" "args" :=
    util.DPrintf #1 #(str"NFS Fsstat %v
    ") #();;
    let: "reply" := ref (zero_val (struct.t nfstypes.FSSTAT3res)) in
    struct.storeF nfstypes.FSSTAT3res "Status" "reply" nfstypes.NFS3ERR_NOTSUPP;;
    ![struct.t nfstypes.FSSTAT3res] "reply".

Definition Nfs__NFSPROC3_FSINFO: val :=
  rec: "Nfs__NFSPROC3_FSINFO" "nfs" "args" :=
    util.DPrintf #1 #(str"NFS Fsinfo %v
    ") #();;
    let: "reply" := ref (zero_val (struct.t nfstypes.FSINFO3res)) in
    struct.storeF nfstypes.FSINFO3res "Status" "reply" nfstypes.NFS3_OK;;
    struct.storeF nfstypes.FSINFO3resok "Wtmax" (struct.fieldRef nfstypes.FSINFO3res "Resok" "reply") #(U32 4096);;
    struct.storeF nfstypes.FSINFO3resok "Maxfilesize" (struct.fieldRef nfstypes.FSINFO3res "Resok" "reply") #4096;;
    ![struct.t nfstypes.FSINFO3res] "reply".

Definition Nfs__NFSPROC3_PATHCONF: val :=
  rec: "Nfs__NFSPROC3_PATHCONF" "nfs" "args" :=
    util.DPrintf #1 #(str"NFS Pathconf %v
    ") #();;
    let: "reply" := ref (zero_val (struct.t nfstypes.PATHCONF3res)) in
    struct.storeF nfstypes.PATHCONF3res "Status" "reply" nfstypes.NFS3ERR_NOTSUPP;;
    ![struct.t nfstypes.PATHCONF3res] "reply".

Definition Nfs__NFSPROC3_COMMIT: val :=
  rec: "Nfs__NFSPROC3_COMMIT" "nfs" "args" :=
    util.DPrintf #1 #(str"NFS Commit %v
    ") #();;
    let: "reply" := ref (zero_val (struct.t nfstypes.COMMIT3res)) in
    let: "op" := jrnl.Begin (struct.loadF Nfs "t" "nfs") in
    let: "inum" := fh2ino (struct.get nfstypes.COMMIT3args "File" "args") in
    (if: (~ (validInum "inum"))
    then
      struct.storeF nfstypes.COMMIT3res "Status" "reply" nfstypes.NFS3ERR_INVAL;;
      ![struct.t nfstypes.COMMIT3res] "reply"
    else
      lockmap.LockMap__Acquire (struct.loadF Nfs "l" "nfs") "inum";;
      let: "ok" := jrnl.Op__CommitWait "op" #true in
      (if: "ok"
      then struct.storeF nfstypes.COMMIT3res "Status" "reply" nfstypes.NFS3_OK
      else struct.storeF nfstypes.COMMIT3res "Status" "reply" nfstypes.NFS3ERR_IO);;
      lockmap.LockMap__Release (struct.loadF Nfs "l" "nfs") "inum";;
      ![struct.t nfstypes.COMMIT3res] "reply").

(* recover_example.go *)

Definition exampleWorker: val :=
  rec: "exampleWorker" "nfs" "ino" :=
    let: "fh" := struct.mk Fh [
      "Ino" ::= "ino"
    ] in
    let: "buf" := NewSlice byteT #1024 in
    Nfs__NFSPROC3_GETATTR "nfs" (struct.mk nfstypes.GETATTR3args [
      "Object" ::= Fh__MakeFh3 "fh"
    ]);;
    Nfs__NFSPROC3_READ "nfs" (struct.mk nfstypes.READ3args [
      "File" ::= Fh__MakeFh3 "fh";
      "Offset" ::= #0;
      "Count" ::= #(U32 1024)
    ]);;
    Nfs__NFSPROC3_WRITE "nfs" (struct.mk nfstypes.WRITE3args [
      "File" ::= Fh__MakeFh3 "fh";
      "Offset" ::= #0;
      "Count" ::= #(U32 1024);
      "Data" ::= "buf"
    ]);;
    #().

Definition RecoverExample: val :=
  rec: "RecoverExample" "d" :=
    let: "nfs" := Recover "d" in
    Fork (exampleWorker "nfs" #3);;
    Fork (exampleWorker "nfs" #3);;
    Fork (exampleWorker "nfs" #4);;
    #().
