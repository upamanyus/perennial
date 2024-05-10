(* autogenerated from github.com/mit-pdos/gokv/ctrexample/client *)
From Perennial.goose_lang Require Import prelude.
From Goose Require fmt.
From Goose Require github_dot_com.mit_dash_pdos.gokv.urpc.
From Goose Require github_dot_com.tchajed.goose.machine.
From Goose Require github_dot_com.tchajed.marshal.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition FAI_OP : expr := #0.

(* the boot/main() function for the server *)
Definition main: val :=
  rec: "main" <> :=
    let: "cl" := ref_zero ptrT in
    let: "$a0" := urpc.MakeClient #53021371269120 in
    "cl" <-[ptrT] "$a0";;
    let: "localBound" := ref_to uint64T #0 in
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "rep" := ref_zero ptrT in
      let: "$a0" := ref (zero_val (slice.T byteT)) in
      "rep" <-[ptrT] "$a0";;
      let: "err" := ref_zero uint64T in
      let: "$a0" := urpc.Client__Call (![ptrT] "cl") FAI_OP (NewSlice byteT #0) (![ptrT] "rep") #100 in
      "err" <-[uint64T] "$a0";;
      (if: (![uint64T] "err") ≠ #0
      then Continue
      else #());;
      let: "dec" := ref_zero (struct.t marshal.Dec) in
      let: "$a0" := marshal.NewDec (![slice.T byteT] (![ptrT] "rep")) in
      "dec" <-[struct.t marshal.Dec] "$a0";;
      let: "v" := ref_zero uint64T in
      let: "$a0" := marshal.Dec__GetInt (![struct.t marshal.Dec] "dec") in
      "v" <-[uint64T] "$a0";;
      machine.Assert ((![uint64T] "v") ≥ (![uint64T] "localBound"));;
      let: "$a0" := ![uint64T] "v" in
      "localBound" <-[uint64T] "$a0";;
      fmt.Println #(str"One");;
      #()).
