From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.grove_prelude.
From Goose Require sync. Module mysync := sync.

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

Axiom eval_exprs_unordered : list (expr) → expr.

Definition f : val :=
  λ: <>, #3.

Definition g : val :=
  λ: <>, #5.

Definition h : val :=
  λ: <>, #7.

(* y[f()] = g(z || h(), i()+x[j()], <-c) *)
Definition order_of_eval_test : val :=
  λ: <>,
  let: "x" := (eval_exprs_unordered [f #(); g #(); h#()]) in
  Fst "x"
.

Definition sp e P : val → iProp Σ :=
  λ v, (∀ Φ, (P -∗ WP e {{ Φ }}) -∗ Φ v)%I.

Axiom wp_eval_exprs_unordered3 :
  ∀ e1 e2 e3 Φ1 Φ2 Φ3 (Φ:_ → iProp Σ),
  (WP e1 {{ Φ1 }} ∗
  WP e3 {{ Φ2 }} ∗
  WP e3 {{ Φ3 }} ∗
  (∀ v1 v2 v3, Φ1 v1 ∗ Φ2 v2 ∗ Φ3 v3 -∗ (Φ (v1, (v2, v3))%V))) -∗
  WP (eval_exprs_unordered [e1 ; e2 ; e3]) {{ Φ }}
.

(*
Axiom wp_sp_eval_exprs_unordered3 :
  ∀ e1 e2 e3 (Φ:_ → iProp Σ),
  (sp e1 Φ1∗
  sp e3 Φ2 ∗
  WP e3 {{ Φ3 }} ∗
  (∀ v  -∗ (Φ (v1, (v2, v3))%V))) -∗
  WP (eval_exprs_unordered [e1 ; e2 ; e3]) {{ Φ }}
. *)

Lemma wp_value (v:val) :
  ⊢ WP of_val v {{ v', ⌜ v' = v ⌝ }}.
Proof. by iApply wp_value. Qed.

Lemma wp_order_of_eval_test :
  ∀ Φ,
  Φ #3 -∗
  WP order_of_eval_test #() {{ Φ }}
.
Proof.
  iIntros (?) "HΦ".
  wp_lam.
  wp_apply wp_eval_exprs_unordered3.
  iSplitR.
  (* FIXME: is there a setup where it is not necessary to have this explicit
     intermediate predicate? *)
  {
    unfold f.
    (* wp_pures without wp_finish *)
    lazymatch goal with
    | |- envs_entails ?envs (wp ?s ?E ?e ?Q) =>
        let e := eval simpl in e in
          reshape_expr e ltac:(fun K e' =>
                                 wp_pure_filter e';
                                 eapply (tac_wp_pure_no_later _ _ _ K e')
                              ) || fail "wp_pure: cannot find redex pattern"
    | _ => fail "wp_pure: not a 'wp'"
    end.
    { apply _. }
    { done. }
    simpl.
    iApply wp_value.
  }
  iSplitR.
  { wp_lam. instantiate (1:=(λ v, ⌜v = #_⌝)%I). done. }
  iSplitR.
  { wp_lam. instantiate (1:=(λ v, ⌜v = #_⌝)%I). done. }
  iIntros "* (%&%&%)".
  subst.
  wp_pures.
  by iApply "HΦ".
Qed.

End proof.
