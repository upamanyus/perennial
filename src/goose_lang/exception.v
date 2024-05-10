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
  λ: "s1",
    if: ((Fst (Fst $ Var "s1")) = #(str "return")) then
      do_return (Snd (Fst $ Var "s1"))
    else
      (Snd $ Var "s1") #()
.

Definition exception_do : val :=
  λ: "v", Snd "v"
.

End defn.

Notation "e1 ;;; e2" := (exception_seq (e1%E, (Lam BAnon e2%E))%E)
  (at level 100, e2 at level 200,
      format "'[' '[hv' '[' e1 ']' ;;;  ']' '/' e2 ']'") : expr_scope.

Notation "do: e" := (do_return e%E)
  (at level 90, e at level 200,
      format "'do:' e") : expr_scope.

Notation "return: e" := (do_return e%E)
  (at level 90, e at level 200, format "'return:' e") : expr_scope.
