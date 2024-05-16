From Perennial.goose_lang Require Export notation.

Section defn.

Context `{ext_ty: ext_types}.
Context `{!ffi_syntax}.
Local Coercion Var' s: expr := Var s.

(* "Exception" monad *)
Definition do_return : val :=
  λ: "v", (#(str "return"), Var "v")
.

Definition do_execute : val :=
  λ: "v", (#(str "noreturn"), Var "v")
.

Definition exception_seq : val :=
  λ: "s1" "s2",
    if: (Fst "s1") = #(str "return") then
      do_return (Snd "s1")
    else
      "s2" #()
.

Definition exception_do : val :=
  λ: "v", Snd "v"
.

End defn.

Global Notation "e1 ;;; e2" := (exception_seq e1%E (Lam BAnon e2%E)%E)
  (at level 90, e2 at level 200,
      format "'[' e1  ;;;  '//' e2 ']'") : expr_scope.

Global Notation "e1 ;;; e2" := (exception_seq e1%E (Lam BAnon e2%E)%V)
  (at level 90, e2 at level 200,
      format "'[' e1  ;;;  '//' e2 ']'") : expr_scope.

Global Notation "do: e" := (do_execute e%E)
  (at level 90, e at level 85,
      format "do:  '[' e ']'") : expr_scope.

Global Notation "return: e" := (do_return e%E)
  (at level 90, e at level 85, format "return:  '[' e ']'") : expr_scope.
