From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

(* FIXME: make everything in here opaque. *)

(* FIXME: want to expose a type, not descriptor *)
Definition Mutex : descriptor :=
  ["state" :: boolT]
.
Axiom WaitGroup: descriptor.

Definition Mutex__Lock : val :=
  rec: "f" "m" :=
    if: CmpXchg (struct.fieldRef Mutex "state" "m") #false #true then
      #()
    else
      "f" #()
.
Definition Mutex__Unlock : val :=
  λ: "f" "m", CmpXchg (struct.fieldRef Mutex "state" "m") #true #false
.

Axiom NewCond: val.
Axiom Cond__Wait: val.
Axiom Cond__Broadcast: val.
Axiom Cond__Signal: val.
Axiom WaitGroup__Add : val.
Axiom WaitGroup__Done : val.
Axiom WaitGroup__Wait : val.

End code.
