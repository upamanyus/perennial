(* autogenerated from github.com/mit-pdos/secure-chat/kt/kt_shim *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.mit_dash_pdos.secure_dash_chat.kt.shared.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

Definition SignerT := struct.decl [
].

Definition VerifierT := struct.decl [
].

Definition MakeKeys: val :=
  rec: "MakeKeys" <> :=
    Panic "ffi";;
    #().

Definition SignerT__Sign: val :=
  rec: "SignerT__Sign" "s" "data" :=
    Panic "ffi";;
    #().

Definition VerifierT__Verify: val :=
  rec: "VerifierT__Verify" "v" "signature" "data" :=
    Panic "ffi";;
    #().

End code.