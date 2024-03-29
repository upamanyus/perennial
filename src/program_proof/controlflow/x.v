From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition do_return : expr.
Admitted.

Definition test : val :=
  λ: <>,
     (if: (#0 = #0) then
       do_return #3
      else #()) ;;
    do_return #2
.

Definition returnV: val := #str "return".
Definition noreturnV: val := #str "noreturn".

Definition code_block (s:expr) (n:expr) : expr :=
     let: "0ret" := s in
     if: ((Fst "0ret") = Val returnV) then
       Snd "0ret"
     else
       s
.

Definition test2 : val :=
  λ: <>,
     code_block

     (if: (#0 = #0) then
        (returnV, #3)
      else (noreturnV, #()))

     (returnV, #2)
.

From Perennial.program_proof Require Import grove_prelude.
Section proof.
Context `{!heapGS Σ}.
Lemma wp_test2:
  {{{ True }}}
    test2 #()
  {{{ RET #(); True }}}.
Proof.
  iIntros (?) "Hpre HΦ".
  wp_lam.
  unfold code_block.
  wp_pures.
Abort.

End proof.
