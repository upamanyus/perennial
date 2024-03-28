From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

(* FIXME: want to expose a type, not descriptor *)
Axiom Mutex : descriptor.
Axiom WaitGroup: descriptor.

Axiom Mutex__Lock : val.
Axiom Mutex__Unlock : val.
Axiom NewCond: val.
Axiom Cond__Wait: val.
Axiom Cond__Broadcast: val.
Axiom Cond__Signal: val.
Axiom WaitGroup__Add : val.
Axiom WaitGroup__Done : val.
Axiom WaitGroup__Wait : val.

End code.
