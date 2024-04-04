From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.grove_prelude.
From Goose Require sync. Module mysync := sync.

(* "Exception" monad *)
Definition go_return : val :=
  λ: "v", (#(str "return"), Var "v")
.

Definition do : val :=
  λ: <>, (#(str "noreturn"), #())
.

(* Takes in the return value of the first block and a lambda for the next block
   as a pair. Taking it as a pair (instead of via currying) results in the
   notation working better during printing. With currying, the notation looks
   for (App (App exception_seq ....)). Here, it just needs (App exception_seq ...)
 *)
Definition exception_seq : val :=
  λ: "s1",
    if: ((Fst (Fst "s1")) = #(str "return")) then
      go_return (Snd (Fst "s1"))
    else
      (Snd "s1") #()
.

Definition exception_do : val :=
  λ: "v", Snd "v"
.

Local Notation "e1 ;;; e2" := (exception_seq (e1%E, (Lam BAnon e2%E))%E)
  (at level 100, e2 at level 200,
      format "'[' '[hv' '[' e1 ']' ;;;  ']' '/' e2 ']'") : expr_scope.

Definition test2 : val :=
  λ: <>,
     exception_do (
     let: "x" := ref_zero uint64T #() in
     (if: (#0 = #0) then
        (do ("x" <-[uint64T] #37)) ;;;
        (do ("x" <-[uint64T] ![uint64T] "x" * ![uint64T] "x"))
      else
        go_return #3
     ) ;;;
     (if: ![uint64T] "x" > #13 then
        go_return ![uint64T] "x" ;;;
        do #1 + #(str "unreachable")
      else
       do #()) ;;;
     go_return #3
     )
.

From Perennial.program_proof Require Import grove_prelude.
Section proof.
Context `{!heapGS Σ}.
Lemma wp_test2:
  {{{ True }}}
    test2 #()
  {{{ RET #(LitInt (word.mul (U64 37) (U64 37))); True }}}.
Proof.
  iIntros (?) "Hpre HΦ".
  wp_lam.
  wp_pures.
  wp_apply wp_ref_zero.
  { done. }
  iIntros (x) "Hx".
  wp_pures.
  wp_store.

  (* This should be abstracted away *)
  wp_lam; wp_pures; wp_lam; wp_pures.

  wp_load.
  wp_load.
  wp_store.

  (* This should be abstracted away *)
  wp_lam; wp_pures; wp_lam; wp_pures.

  wp_load.
  wp_pures.
  wp_load.

  (* This should be abstracted away *)
  wp_lam; wp_pures; wp_lam; wp_pures.
  wp_lam; wp_pures; wp_lam; wp_pures.
  wp_lam; wp_pures; wp_lam; wp_pures.

  by iApply "HΦ".
Qed.

(* TODO: look at https://robbertkrebbers.nl/research/articles/iris_c.pdf *)
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


* Translation looks weird compared to Go code
*
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
