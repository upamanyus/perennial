(* autogenerated from mailboat *)
From Perennial.go_lang Require Import prelude.

(* disk FFI *)
From Perennial.go_lang Require Import ffi.disk_prelude.

Module partialFile.
  Definition S := struct.decl [
    "off" :: uint64T;
    "data" :: slice.T byteT
  ].
  Definition T: ty := struct.t S.
  Definition Ptr: ty := struct.ptrT S.
  Section fields.
    Context `{ext_ty: ext_types}.
    Definition get := struct.get S.
  End fields.
End partialFile.

Definition GetUserDir: val :=
  λ: "user",
    #(str"user") + uint64_to_string "user".

Definition SpoolDir : expr := #(str"spool").

Definition NumUsers : expr := #100.

Definition readMessage: val :=
  λ: "userDir" "name",
    let: "f" := FS.open "userDir" "name" in
    let: "fileContents" := ref (zero_val (slice.T byteT)) in
    let: "initData" := NewSlice byteT #0 in
    let: "pf" := ref (struct.mk partialFile.S [
      "off" ::= #0;
      "data" ::= "initData"
    ]) in
    (for: (#true); (Skip) :=
      let: "buf" := FS.readAt "f" (partialFile.get "off" !"pf") #512 in
      let: "newData" := SliceAppendSlice (partialFile.get "data" !"pf") "buf" in
      (if: slice.len "buf" < #512
      then
        "fileContents" <- "newData";;
        Break
      else
        "pf" <- struct.mk partialFile.S [
          "off" ::= partialFile.get "off" !"pf" + slice.len "buf";
          "data" ::= "newData"
        ];;
        Continue));;
    let: "fileData" := !"fileContents" in
    let: "fileStr" := Data.bytesToString "fileData" in
    FS.close "f";;
    "fileStr".

Module Message.
  Definition S := struct.decl [
    "Id" :: stringT;
    "Contents" :: stringT
  ].
  Definition T: ty := struct.t S.
  Definition Ptr: ty := struct.ptrT S.
  Section fields.
    Context `{ext_ty: ext_types}.
    Definition get := struct.get S.
  End fields.
End Message.

(* Pickup reads all stored messages and acquires a per-user lock. *)
Definition Pickup: val :=
  λ: "user",
    let: "ls" := Globals.getX #() in
    let: "l" := SliceGet "ls" "user" in
    Data.lockAcquire Writer "l";;
    let: "userDir" := GetUserDir "user" in
    let: "names" := FS.list "userDir" in
    let: "messages" := ref (zero_val (slice.T Message.T)) in
    let: "initMessages" := NewSlice Message.T #0 in
    "messages" <- "initMessages";;
    let: "i" := ref #0 in
    (for: (#true); (Skip) :=
      (if: !"i" = slice.len "names"
      then Break
      else
        let: "name" := SliceGet "names" !"i" in
        let: "msg" := readMessage "userDir" "name" in
        let: "oldMessages" := !"messages" in
        let: "newMessages" := SliceAppend "oldMessages" (struct.mk Message.S [
          "Id" ::= "name";
          "Contents" ::= "msg"
        ]) in
        "messages" <- "newMessages";;
        "i" <- !"i" + #1;;
        Continue));;
    let: "msgs" := !"messages" in
    "msgs".

Definition createTmp: val :=
  λ: <>,
    let: "initID" := Data.randomUint64 #() in
    let: "finalFile" := ref (zero_val fileT) in
    let: "finalName" := ref (zero_val stringT) in
    let: "id" := ref "initID" in
    (for: (#true); (Skip) :=
      let: "fname" := uint64_to_string !"id" in
      let: ("f", "ok") := FS.create SpoolDir "fname" in
      (if: "ok"
      then
        "finalFile" <- "f";;
        "finalName" <- "fname";;
        Break
      else
        let: "newID" := Data.randomUint64 #() in
        "id" <- "newID";;
        Continue);;
      Continue);;
    let: "f" := !"finalFile" in
    let: "name" := !"finalName" in
    ("f", "name").

Definition writeTmp: val :=
  λ: "data",
    let: ("f", "name") := createTmp #() in
    let: "buf" := ref "data" in
    (for: (#true); (Skip) :=
      (if: slice.len !"buf" < #4096
      then
        FS.append "f" !"buf";;
        Break
      else
        FS.append "f" (SliceTake !"buf" #4096);;
        "buf" <- SliceSkip !"buf" #4096;;
        Continue));;
    FS.close "f";;
    "name".

(* Deliver stores a new message.
   Does not require holding the per-user pickup/delete lock. *)
Definition Deliver: val :=
  λ: "user" "msg",
    let: "userDir" := GetUserDir "user" in
    let: "tmpName" := writeTmp "msg" in
    let: "initID" := Data.randomUint64 #() in
    let: "id" := ref "initID" in
    (for: (#true); (Skip) :=
      let: "ok" := FS.link SpoolDir "tmpName" "userDir" (#(str"msg") + uint64_to_string !"id") in
      (if: "ok"
      then Break
      else
        let: "newID" := Data.randomUint64 #() in
        "id" <- "newID";;
        Continue);;
      Continue);;
    FS.delete SpoolDir "tmpName".

(* Delete deletes a message for the current user.
   Requires the per-user lock, acquired with pickup. *)
Definition Delete: val :=
  λ: "user" "msgID",
    let: "userDir" := GetUserDir "user" in
    FS.delete "userDir" "msgID".

(* Lock acquires the lock for the current user *)
Definition Lock: val :=
  λ: "user",
    let: "locks" := Globals.getX #() in
    let: "l" := SliceGet "locks" "user" in
    Data.lockAcquire Writer "l".

(* Unlock releases the lock for the current user. *)
Definition Unlock: val :=
  λ: "user",
    let: "locks" := Globals.getX #() in
    let: "l" := SliceGet "locks" "user" in
    Data.lockRelease Writer "l".

Definition open: val :=
  λ: <>,
    let: "locks" := ref (zero_val (slice.T lockRefT)) in
    let: "initLocks" := NewSlice lockRefT #0 in
    "locks" <- "initLocks";;
    let: "i" := ref #0 in
    (for: (#true); (Skip) :=
      (if: !"i" = NumUsers
      then Break
      else
        let: "oldLocks" := !"locks" in
        let: "l" := Data.newLock #() in
        let: "newLocks" := SliceAppend "oldLocks" "l" in
        "locks" <- "newLocks";;
        "i" <- !"i" + #1;;
        Continue));;
    let: "finalLocks" := !"locks" in
    Globals.setX "finalLocks".

Definition init: val :=
  λ: <>,
    open #().

Definition Recover: val :=
  λ: <>,
    let: "spooled" := FS.list SpoolDir in
    let: "i" := ref #0 in
    (for: (#true); (Skip) :=
      (if: !"i" = slice.len "spooled"
      then Break
      else
        let: "name" := SliceGet "spooled" !"i" in
        FS.delete SpoolDir "name";;
        "i" <- !"i" + #1;;
        Continue)).
