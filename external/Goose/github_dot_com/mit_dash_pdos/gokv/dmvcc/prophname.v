(* autogenerated from github.com/mit-pdos/gokv/dmvcc/prophname *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.tchajed.goose.machine.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

Definition Get: val :=
  rec: "Get" <> :=
    machine.NewProph #().

End code.
