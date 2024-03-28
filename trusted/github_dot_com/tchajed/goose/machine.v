From Goose Require Import sync.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang.lib Require control encoding time rand.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

Definition Assume: val := control.impl.Assume.
Definition Assert: val := control.impl.Assert.
Definition Exit: val := control.impl.Exit.

Definition EncodeUInt32: val := encoding.impl.EncodeUInt32.
Definition DecodeUInt32: val := encoding.impl.DecodeUInt32.
Definition EncodeUInt64: val := encoding.impl.EncodeUInt64.
Definition DecodeUInt64: val := encoding.impl.DecodeUInt64.

Definition UInt64Put: val := encoding.impl.UInt64Put.
Definition UInt64Get: val := encoding.impl.UInt64Get.
Definition UInt32Put: val := encoding.impl.UInt32Put.
Definition UInt32Get: val := encoding.impl.UInt32Get.

Definition WaitTimeout: val := λ: "l" "timeout", sync.Cond__Wait "l".
Definition Millisecond: val := time.impl.time.Millisecond.
Definition Second: val := time.impl.time.Second.
Definition Sleep: val := time.impl.time.Sleep.
Definition TimeNow: val := time.impl.time.TimeNow.

Definition RandomUint64: val := rand.impl.rand.RandomUint64.

End code.
