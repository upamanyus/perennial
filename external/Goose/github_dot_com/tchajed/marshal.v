(* autogenerated from github.com/tchajed/marshal *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.goose_dash_lang.std.
From Goose Require github_dot_com.tchajed.goose.machine.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

(* marshal.go *)

(* Enc is a stateful encoder for a statically-allocated array. *)
Definition Enc := struct.decl [
  "b" :: slice.T byteT;
  "off" :: ptrT
].

Definition NewEncFromSlice: val :=
  rec: "NewEncFromSlice" "b" :=
    struct.mk Enc [
      "b" ::= "b";
      "off" ::= ref (zero_val uint64T)
    ].

Definition NewEnc: val :=
  rec: "NewEnc" "sz" :=
    let: "b" := NewSlice byteT "sz" in
    NewEncFromSlice "b".

Definition Enc__PutInt: val :=
  rec: "Enc__PutInt" "enc" "x" :=
    let: "off" := ![uint64T] (struct.get Enc "off" "enc") in
    machine.UInt64Put (SliceSkip byteT (struct.get Enc "b" "enc") "off") "x";;
    (struct.get Enc "off" "enc") <-[uint64T] ((![uint64T] (struct.get Enc "off" "enc")) + #8);;
    #().

Definition Enc__PutInt32: val :=
  rec: "Enc__PutInt32" "enc" "x" :=
    let: "off" := ![uint64T] (struct.get Enc "off" "enc") in
    machine.UInt32Put (SliceSkip byteT (struct.get Enc "b" "enc") "off") "x";;
    (struct.get Enc "off" "enc") <-[uint64T] ((![uint64T] (struct.get Enc "off" "enc")) + #4);;
    #().

Definition Enc__PutInts: val :=
  rec: "Enc__PutInts" "enc" "xs" :=
    ForSlice uint64T <> "x" "xs"
      (Enc__PutInt "enc" "x");;
    #().

Definition Enc__PutBytes: val :=
  rec: "Enc__PutBytes" "enc" "b" :=
    let: "off" := ![uint64T] (struct.get Enc "off" "enc") in
    let: "n" := SliceCopy byteT (SliceSkip byteT (struct.get Enc "b" "enc") "off") "b" in
    (struct.get Enc "off" "enc") <-[uint64T] ((![uint64T] (struct.get Enc "off" "enc")) + "n");;
    #().

Definition bool2byte: val :=
  rec: "bool2byte" "b" :=
    (if: "b"
    then #(U8 1)
    else #(U8 0)).

Definition Enc__PutBool: val :=
  rec: "Enc__PutBool" "enc" "b" :=
    let: "off" := ![uint64T] (struct.get Enc "off" "enc") in
    SliceSet byteT (struct.get Enc "b" "enc") "off" (bool2byte "b");;
    (struct.get Enc "off" "enc") <-[uint64T] ((![uint64T] (struct.get Enc "off" "enc")) + #1);;
    #().

Definition Enc__Finish: val :=
  rec: "Enc__Finish" "enc" :=
    struct.get Enc "b" "enc".

(* Dec is a stateful decoder that returns values encoded
   sequentially in a single slice. *)
Definition Dec := struct.decl [
  "b" :: slice.T byteT;
  "off" :: ptrT
].

Definition NewDec: val :=
  rec: "NewDec" "b" :=
    struct.mk Dec [
      "b" ::= "b";
      "off" ::= ref (zero_val uint64T)
    ].

Definition Dec__GetInt: val :=
  rec: "Dec__GetInt" "dec" :=
    let: "off" := ![uint64T] (struct.get Dec "off" "dec") in
    (struct.get Dec "off" "dec") <-[uint64T] ((![uint64T] (struct.get Dec "off" "dec")) + #8);;
    machine.UInt64Get (SliceSkip byteT (struct.get Dec "b" "dec") "off").

Definition Dec__GetInt32: val :=
  rec: "Dec__GetInt32" "dec" :=
    let: "off" := ![uint64T] (struct.get Dec "off" "dec") in
    (struct.get Dec "off" "dec") <-[uint64T] ((![uint64T] (struct.get Dec "off" "dec")) + #4);;
    machine.UInt32Get (SliceSkip byteT (struct.get Dec "b" "dec") "off").

Definition Dec__GetInts: val :=
  rec: "Dec__GetInts" "dec" "num" :=
    let: "xs" := ref (zero_val (slice.T uint64T)) in
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, (![uint64T] "i") < "num"); (λ: <>, "i" <-[uint64T] ((![uint64T] "i") + #1)) := λ: <>,
      "xs" <-[slice.T uint64T] (SliceAppend uint64T (![slice.T uint64T] "xs") (Dec__GetInt "dec"));;
      Continue);;
    ![slice.T uint64T] "xs".

Definition Dec__GetBytes: val :=
  rec: "Dec__GetBytes" "dec" "num" :=
    let: "off" := ![uint64T] (struct.get Dec "off" "dec") in
    let: "b" := SliceSubslice byteT (struct.get Dec "b" "dec") "off" ("off" + "num") in
    (struct.get Dec "off" "dec") <-[uint64T] ((![uint64T] (struct.get Dec "off" "dec")) + "num");;
    "b".

Definition Dec__GetBool: val :=
  rec: "Dec__GetBool" "dec" :=
    let: "off" := ![uint64T] (struct.get Dec "off" "dec") in
    (struct.get Dec "off" "dec") <-[uint64T] ((![uint64T] (struct.get Dec "off" "dec")) + #1);;
    (if: (SliceGet byteT (struct.get Dec "b" "dec") "off") = #(U8 0)
    then #false
    else #true).

(* stateless.go *)

Definition compute_new_cap: val :=
  rec: "compute_new_cap" "old_cap" "min_cap" :=
    let: "new_cap" := ref_to uint64T ("old_cap" * #2) in
    (if: (![uint64T] "new_cap") < "min_cap"
    then "new_cap" <-[uint64T] "min_cap"
    else #());;
    ![uint64T] "new_cap".

(* Grow a slice to have at least `additional` unused bytes in the capacity.
   Runtime-check against overflow. *)
Definition reserve: val :=
  rec: "reserve" "b" "additional" :=
    let: "min_cap" := std.SumAssumeNoOverflow (slice.len "b") "additional" in
    (if: (slice.cap "b") < "min_cap"
    then
      let: "new_cap" := compute_new_cap (slice.cap "b") "min_cap" in
      let: "dest" := NewSliceWithCap byteT (slice.len "b") "new_cap" in
      SliceCopy byteT "dest" "b";;
      "dest"
    else "b").

(* Functions for the stateless decoder API *)
Definition ReadInt: val :=
  rec: "ReadInt" "b" :=
    let: "i" := machine.UInt64Get "b" in
    ("i", SliceSkip byteT "b" #8).

Definition ReadBytes: val :=
  rec: "ReadBytes" "b" "l" :=
    let: "s" := SliceTake "b" "l" in
    ("s", SliceSkip byteT "b" "l").

(* Like ReadBytes, but avoids keeping the source slice [b] alive. *)
Definition ReadBytesCopy: val :=
  rec: "ReadBytesCopy" "b" "l" :=
    let: "s" := NewSlice byteT "l" in
    SliceCopy byteT "s" (SliceTake "b" "l");;
    ("s", SliceSkip byteT "b" "l").

(* Functions for the stateless encoder API *)
Definition WriteInt: val :=
  rec: "WriteInt" "b" "i" :=
    let: "b2" := reserve "b" #8 in
    let: "off" := slice.len "b2" in
    let: "b3" := SliceTake "b2" ("off" + #8) in
    machine.UInt64Put (SliceSkip byteT "b3" "off") "i";;
    "b3".

Definition WriteBytes: val :=
  rec: "WriteBytes" "b" "data" :=
    let: "b2" := reserve "b" (slice.len "data") in
    let: "off" := slice.len "b2" in
    let: "b3" := SliceTake "b2" ("off" + (slice.len "data")) in
    SliceCopy byteT (SliceSkip byteT "b3" "off") "data";;
    "b3".

End code.
