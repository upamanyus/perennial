From Perennial.goose_lang Require Import notation typing.

Module trusted_example.
  Section goose_lang.
    Context {ext:ffi_syntax}.
    Context {ext_tys: ext_types ext}.

    Local Coercion Var' (s:string): expr := Var s.

    Definition Foo: val := λ: <>, #().
  End goose_lang.
End trusted_example.
