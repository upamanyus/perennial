From Perennial.goose_lang.examples Require Import append_log.
From Perennial.goose_lang.lib Require Import encoding crash_lock.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import append_log_hocap.
From Perennial.goose_lang.ffi Require Import append_log_ffi.
From Perennial.goose_lang Require Import logical_reln spec_assert.
From Perennial.program_logic Require Import ghost_var.

Existing Instances log_spec_ext log_spec_ffi_model log_spec_ext_semantics log_spec_ffi_interp log_spec_interp_adequacy.

Section refinement.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Context `{!refinement_heapG Σ}.
Context `{!lockG Σ, stagedG Σ}.
Existing Instance logG0.
Context `{Hin: inG Σ (authR (optionUR (exclR log_stateO)))}.
Context `{Hin_nat_ctx: inG Σ (authR (optionUR (exclR (leibnizO (nat * (spec_lang.(language.expr) →
                                                                       spec_lang.(language.expr)))))))}.
Context (SIZE: nat).
Context (SIZE_nonzero: 0 < SIZE).
Context (SIZE_bounds: int.nat SIZE = SIZE).
Existing Instances spec_ffi_model_field spec_ext_op_field spec_ext_semantics_field (* spec_ffi_interp_field  *) spec_ffi_interp_adequacy_field.

Notation sstate := (@state (@spec_ext_op_field log_spec_ext) (spec_ffi_model_field)).
Notation sexpr := (@expr (@spec_ext_op_field log_spec_ext)).
Notation sval := (@val (@spec_ext_op_field log_spec_ext)).

Definition Nlog := nroot.@"log".

Definition thread_tok_frag γ j K :=
  own γ (◯ Excl' ((j, K) : leibnizO (nat * (sexpr → sexpr)))).
Definition thread_tok_auth γ j K :=
  own γ (● Excl' ((j, K) : leibnizO (nat * (sexpr → sexpr)))).
Definition thread_tok_full γ j K :=
 (thread_tok_auth γ j K ∗ thread_tok_frag γ j K)%I.

Definition P (γ: gname) (s: log_state) :=
  match s with
  | UnInit => log_uninit_frag ∗ log_frag [] ∗ thread_tok_full γ 0 id
  | Initing  => log_uninit_frag ∗ log_frag []
  | Closed vs => log_closed_frag ∗ log_frag vs ∗ thread_tok_full γ 0 id
  | Opening vs => log_closed_frag ∗ log_frag vs
  | Opened vs l => (∃ l', log_open l' ∗ log_frag vs)
  end%I.

Definition POpened := (∃ l, log_open l)%I.
Definition PStartedOpening γ :=
  (∃ j (K: spec_lang.(language.expr) → spec_lang.(language.expr)) (Hctx: LanguageCtx K),
      j ⤇ K (ExternalOp (ext := spec_ext_op_field) OpenOp #())
      ∗ thread_tok_auth γ j K)%I.
Definition PStartedIniting γ :=
  (∃ j (K: spec_lang.(language.expr) → spec_lang.(language.expr)) (Hctx: LanguageCtx K),
      j ⤇ K (ExternalOp (ext := spec_ext_op_field) InitOp #())
      ∗ thread_tok_auth γ j K)%I.

Lemma PStartedOpening_Timeless γ : Timeless (PStartedOpening γ).
Proof. apply _. Qed.
Lemma PStartedIniting_Timeless γ : Timeless (PStartedIniting γ).
Proof. apply _. Qed.

Definition log_inv γ : nat → iProp Σ :=
  log_inv Nlog (P γ) (POpened) (PStartedOpening γ) (PStartedIniting γ) SIZE.
Definition is_log γ : nat → loc → iProp Σ :=
  is_log Nlog (P γ) (POpened) (PStartedOpening γ) (PStartedIniting γ) SIZE.

Theorem wpc_Init j γ K `{LanguageCtx _ K} k k' E2:
  (S k < k')%nat →
  {{{ spec_ctx ∗ log_inv γ k' ∗ j ⤇ K (ExternalOp (ext := spec_ext_op_field) InitOp #()) }}}
    Init #SIZE @ NotStuck; LVL (S (S (S k))); ⊤; E2
  {{{ l, RET (#l, #true);  is_log γ k' l ∗ (∃ (l': loc), j ⤇ K (of_val (#l', #true) : sexpr) ∗ log_open l')}}}
  {{{ True }}}.
Proof using SIZE_nonzero SIZE_bounds.
  iIntros (? Φ Φc) "(#Hspec&#Hinv&Hj) HΦ".
  unshelve
    wpc_apply (wpc_Init _ _ _ _ _ _ _ _ _ _ _ _ (True%I)
                        (λ l, (∃ (l': loc), j ⤇ K (of_val (#l', #true)) ∗ log_open l'))%I
               with "[Hj]"); try iFrame "Hinv"; eauto.
  { apply _. }
  iSplit; [| iSplit].
  - iIntros (vs); simpl P.
    iIntros "(Hclosed&Hlist&Htok)".
    iMod (log_closed_init_false with "[$] [$] [$] Hj") as %[].
    { solve_ndisj. }
  - iIntros "[Hiniting|[Hopening|Hopened]]".
    * iDestruct "Hiniting" as (j' K' Hctx') "(Hj'&_)".
      iMod (log_init_init_false with "[$] [$] [$]") as %[].
      { solve_ndisj. }
    * iDestruct "Hopening" as (j' K' Hctx') "(Hj'&_)".
      iMod (log_init_open_false with "[$] [$] [$]") as %[].
      { solve_ndisj. }
    * iDestruct "Hopened" as (l) "Hopen".
      iMod (log_opened_init_false with "[$] [$] [$]") as %[].
      { solve_ndisj. }
  - iSplit; last done. simpl.
    iIntros "(Huninit_frag&Hvals_frag&(Hthread_auth&Hthread_frag))".
    iMod (ghost_var_update _ ((j, K) : leibnizO (nat * (sexpr → sexpr))) with "[$] [$]")
         as "(Hthread_auth&Hthread_frag)".
    iModIntro.
    iSplitL "Hthread_auth Hj".
    { unshelve (iExists _, _, _; iFrame); eauto. }
    iFrame. iSplit; first done.
    iIntros (l) "(Huninit&Hvals) Hthread".
    iDestruct "Hthread" as (j' K' ?) "(Hj&Hthread_auth)".
    rewrite /thread_tok_auth.
    unify_ghost.
    iMod (ghost_step_log_init with "[$] [$] [$] [$]") as (l') "(Hj&#Hopen&Hvals)".
    { solve_ndisj. }
    iModIntro. iSplitR "Hvals".
    * iExists _. iFrame. iFrame "Hopen".
    * iFrame. iSplitL ""; iExists _; iFrame "Hopen".
Qed.

Theorem wpc_Open j γ K `{LanguageCtx _ K} k k' E2:
  (S k < k')%nat →
  {{{ spec_ctx ∗ log_inv γ k' ∗ j ⤇ K (ExternalOp (ext := spec_ext_op_field) OpenOp #()) }}}
    Open #() @ NotStuck; LVL (S (S (S k))); ⊤; E2
  {{{ l, RET #l;  is_log γ k' l ∗ (∃ (l': loc), j ⤇ K (of_val #l': sexpr) ∗ log_open l')}}}
  {{{ True }}}.
Proof using SIZE_bounds.
  iIntros (? Φ Φc) "(#Hspec&#Hinv&Hj) HΦ".
  unshelve
  wpc_apply (wpc_Open _ _ _ _ _ _ _ _ _ _ (True%I) (λ l, (∃ (l': loc), j ⤇ K (of_val #l') ∗ log_open l'))%I
               with "[Hj]"); try iFrame "Hinv"; eauto.
  { apply _. }
  iSplit; [| iSplit].
  - iIntros "(Huninit&Hlist&Htok)".
    iMod (log_uninit_open_false with "[$] [$] [$] Hj") as %[].
    { solve_ndisj. }
  - iIntros "[Hiniting|[Hopening|Hopened]]".
    * iDestruct "Hiniting" as (j' K' Hctx') "(Hj'&_)".
      iMod (log_init_open_false with "[$] [$] [$]") as %[].
      { solve_ndisj. }
    * iDestruct "Hopening" as (j' K' Hctx') "(Hj'&_)".
      iMod (log_open_open_false with "[$] [$] [$]") as %[].
      { solve_ndisj. }
    * iDestruct "Hopened" as (l) "Hopen".
      iMod (log_opened_open_false with "[$] [$] [$]") as %[].
      { solve_ndisj. }
  - iSplit; last done. simpl.
    iIntros (vs) "(Hclosed_frag&Hvals_frag&(Hthread_auth&Hthread_frag))".
    iMod (ghost_var_update _ ((j, K) : leibnizO (nat * (sexpr → sexpr))) with "[$] [$]")
         as "(Hthread_auth&Hthread_frag)".
    iModIntro.
    iSplitL "Hthread_auth Hj".
    { unshelve (iExists _, _, _; iFrame); eauto. }
    iFrame. iSplit; first done.
    iIntros (l) "(Huninit&Hvals) Hthread".
    iDestruct "Hthread" as (j' K' ?) "(Hj&Hthread_auth)".
    rewrite /thread_tok_auth.
    unify_ghost.
    iMod (ghost_step_log_open with "[$] [$] [$] [$]") as (l') "(Hj&#Hopen&Hvals)".
    { solve_ndisj. }
    iModIntro. iSplitR "Hvals".
    * iExists _. iFrame. iFrame "Hopen".
    * iFrame. iSplitL ""; iExists _; iFrame "Hopen".
Qed.

Theorem wpc_Log__Reset j γ K `{LanguageCtx _ K} k k' E2 (l l': loc):
  (S (S k) < k')%nat →
  {{{ spec_ctx ∗ log_inv γ k' ∗ j ⤇ K (ExternalOp (ext := spec_ext_op_field) (ResetOp) #l') ∗
               is_log γ k' l ∗ log_open l'
  }}}
    Log__Reset #l @ NotStuck; (LVL (S (S (S k)))); ⊤; E2
  {{{ RET #(); j ⤇ K (of_val #(): sexpr)}}}
  {{{ True }}}.
Proof using SIZE_bounds.
  iIntros (? Φ Φc) "(#Hspec&#Hinv&Hj&His_log&#Hopen) HΦ".
  wpc_apply (wpc_Log__Reset _ _ _ _ _ _ _ _ _ _ (j ⤇ K (of_val #()))%I True%I
               with "[Hj His_log Hopen]"); try iFrame "His_log"; eauto.
  iSplit; last done.
  iIntros (bs).
  iIntros "Hopened". iDestruct "Hopened" as (?) "(_&Hfrag)".
  iMod (ghost_step_log_reset with "[$] [$] [$] [$]") as "(Hj&Hvals)".
  { solve_ndisj. }
  iModIntro. iFrame. iExists _. eauto.
Qed.


End refinement.

Section refinement.
Context (SIZE: nat).
Context (SIZE_nonzero: 0 < SIZE).
Context (SIZE_bounds: int.nat SIZE = SIZE).
Class appendG (Σ: gFunctors) :=
  { append_lockG :> lockG Σ;
    append_stagedG :> stagedG Σ;
    append_stateG :> inG Σ (authR (optionUR (exclR log_stateO)));
    append_nat_ctx :> inG Σ (authR (optionUR (exclR (leibnizO (nat * (spec_lang.(language.expr) →
                                                                       spec_lang.(language.expr)))))))
  }.

Definition append_names := unit.
Definition append_get_names (Σ: gFunctors) (hG: appendG Σ) := tt.
Definition append_update (Σ: gFunctors) (hG: appendG Σ) (n: append_names) := hG.

Definition LVL_INIT : nat := 100.
Definition LVL_INV : nat := 75.
Definition LVL_OPS : nat := 50.
Existing Instance logG0.

Definition append_inv {Σ: gFunctors} {hG: heapG Σ} {rG: refinement_heapG Σ} {cG: crashG Σ} {aG : appendG Σ} :=
  (∃ γ, log_inv SIZE γ LVL_INV%nat)%I.
Definition append_init {Σ: gFunctors} {hG: heapG Σ} {rG: refinement_heapG Σ} {cG: crashG Σ} {aG : appendG Σ}
  : iProp Σ := (∃ γ, log_init (P γ) SIZE).
Definition append_crash_cond {Σ: gFunctors} {hG: heapG Σ} {rG: refinement_heapG Σ} {cG: crashG Σ} {aG : appendG Σ}
  : iProp Σ := (∃ γ, log_crash_cond (P γ) SIZE).
Definition appendN : coPset := (∅ : coPset).
Definition append_val_interp {Σ: gFunctors} {hG: heapG Σ} {rG: refinement_heapG Σ} {cG: crashG Σ} {aG : appendG Σ}
           (ty: @ext_tys (@val_tys _ log_ty)) : val_semTy :=
  λ vspec vimpl, (∃ (lspec: loc) (limpl: loc) γ,
            ⌜ vspec = #lspec ∧ vimpl = #limpl ⌝ ∗ is_log SIZE γ LVL_INV limpl ∗ log_open lspec)%I.

Instance appendTy_model : specTy_model log_ty.
Proof using SIZE.
 refine
  {| styG := appendG;
     sty_names := append_names;
     sty_get_names := append_get_names;
     sty_update := append_update;
     sty_inv := @append_inv;
     sty_init := @append_init;
     sty_crash_cond := @append_crash_cond;
     styN := appendN;
     sty_val_interp := @append_val_interp |}.
 - intros ? [] [] => //=.
 - intros ? [] => //=.
 - intros ?? [] [] => //=.
 - rewrite /sN/appendN. apply disjoint_empty_r.
Defined.
(* XXX: some of the fields should be opaque/abstract here, because they're enormous proof terms.
  perhaps specTy_model should be split into two typeclasses? *)

Existing Instances subG_stagedG subG_lockΣ.

Definition appendΣ := #[lockΣ; stagedΣ;
                          GFunctor (authR (optionUR (exclR log_stateO)));
                          GFunctor ((authR (optionUR (exclR (leibnizO (nat * (spec_lang.(language.expr) →
                                                                       spec_lang.(language.expr))))))))].

Instance subG_appendPreG: ∀ Σ, subG appendΣ Σ → appendG Σ.
Proof. solve_inG. Qed.
Definition append_initP (σimpl: @state disk_op disk_model) (σspec : @state log_op log_model) : Prop :=
  (σimpl.(world) = init_disk ∅ SIZE) ∧
  (σspec.(world) = UnInit).
Definition append_update_pre (Σ: gFunctors) (hG: appendG Σ) (n: append_names) : appendG Σ := hG.

Program Instance appendTy_update_model : specTy_update _ appendTy_model :=
  {| sty_preG := appendG;
            styΣ := appendΣ;
            subG_styPreG := subG_appendPreG;
            sty_update_pre := @append_update_pre |}.
Next Obligation. rewrite //=. Qed.
Next Obligation. rewrite //=. intros ?? [] => //=. Qed.

Notation append_nat_K :=
(leibnizO (nat * ((@spec_lang log_spec_ext log_spec_ffi_model log_spec_ext_semantics).(language.expr)
                           → (@spec_lang log_spec_ext log_spec_ffi_model log_spec_ext_semantics).(language.expr)))).

Lemma append_init_obligation1: sty_init_obligation1 _ appendTy_update_model append_initP.
Proof.
  rewrite /sty_init_obligation1//=.
  iIntros (? hG hRG hC hAppend σs σi Hinit) "Hdisk".
  rewrite /log_start /append_init/log_init.
  inversion Hinit as [Heqi Heqs]. rewrite Heqs Heqi.
  iIntros "(Huninit_frag&Hlog_frag)". rewrite /P//=.
  rewrite /thread_tok_full.
  iMod (ghost_var_alloc ((O, id) : append_nat_K)) as (γ) "Hown".
  iModIntro. iExists tt, γ. iLeft. iFrame.
  rewrite /append_log_proof.uninit_log.
  iExists _.
  iSplitL "Hdisk".
  - by iApply disk_array_init_disk.
  - rewrite replicate_length //=.
Qed.

Lemma append_crash_inv_obligation:
  @sty_crash_inv_obligation _ _ disk_semantics _ _ _ _ _ _ (LVL (LVL_INIT)) (LVL (LVL_OPS)) appendTy_model.
Proof using SIZE SIZE_bounds.
  rewrite /sty_crash_inv_obligation//=.
  iIntros (? hG hC hRG hAppend e Φ) "Hinit Hspec Hwand".
  rewrite /append_inv/append_init/log_inv.
  iDestruct ("Hinit") as (γ) "Hinit".
  rewrite /append_crash_cond.
  iPoseProof (append_log_na_crash_inv_obligation Nlog _ POpened (PStartedOpening _)
                                                 _ _ _ _ _ _ LVL_INIT
                                                 LVL_INV LVL_OPS with "Hinit [Hwand]") as ">(Hinv&Hwp)".
  { rewrite /LVL_INIT/LVL_INV. lia. }
  { rewrite /LVL_INIT/LVL_OPS. lia. }
  { iIntros "Hinv". iApply "Hwand". iExists _. eauto. }
  iModIntro. iSplitL "Hinv".
  { iExists _. iApply "Hinv". }
  iApply (wpc_mono with "Hwp"); eauto.
  iIntros "(_&H)". iExists _. iFrame.
Qed.

Lemma append_crash_obligation:
  @sty_crash_obligation _ _ disk_semantics _ _ _ _ _ _ _ _ appendTy_model.
Proof.
  rewrite /sty_crash_obligation//=.
  iIntros (? hG hC hRG hAppend) "Hinv Hcrash_cond".
  iMod (ghost_var_alloc ((O, id) : append_nat_K)) as (γtok) "Hown".
  iDestruct "Hinv" as (γ1) "#Hlog_inv".
  rewrite /append_crash_cond.
  iDestruct "Hcrash_cond" as (γ2 ls) "(Hstate_to_crash&HP)".
  rewrite/ log_state_to_crash.
  iModIntro. iNext. iIntros (hG').
  iModIntro. iIntros (hC' σs Hrel).
  destruct Hrel as (?&?&_&Heq&_).
  iIntros "Hctx".
  rewrite /append_init/log_init.
  destruct (σs.(world)) eqn:Hworld_case; try iDestruct "Hctx" as %[].
  - iAssert (⌜ ls = UnInit ⌝ ∗ log_ctx UnInit ∗ log_frag [])%I with "[HP Hctx]" as (Heqls) "(Hctx&Hfrag)".
    { admit. }
    iExists _. unshelve (iExists _).
    { econstructor.
      { symmetry; eauto. }
      repeat econstructor.
    }
    iFrame. iIntros (hRG' (Heq1&Heq2)) "Hrestart".
    iModIntro.
    iExists tt, γtok. iLeft.
    rewrite /logG0//=/log_frag//=. rewrite Heq2. rewrite Heq1.
    iFrame. subst.
    rewrite /append_log_proof.uninit_log.
    rewrite /disk_array. rewrite /diskG0.
    rewrite Heq.
    iFrame.
  - rewrite /P/log_ctx.
    iAssert (⌜ ls = Closed s ∨ ls = Opening s  ⌝ ∗ log_ctx (Closed s) ∗ log_frag s)%I with "[HP Hctx]" as (Heqls) "(Hctx&Hfrag)".
    { admit. }
    iExists _. unshelve (iExists _).
    { econstructor.
      { symmetry; eauto. }
      simpl.
      repeat econstructor.
    }
    iFrame. iIntros (hRG' (Heq1&Heq2)) "Hrestart".
    iModIntro.
    iExists tt, γtok. iRight.
    rewrite /logG0//=/log_frag//=. rewrite Heq2. rewrite Heq1.
    iFrame. subst.
    rewrite /append_log_proof.uninit_log.
    rewrite /disk_array. rewrite /diskG0.
    destruct Heqls as [-> | ->];
      iExists _; iFrame;
      iFrame; subst;
      (* XXX: need a typeclass? or lemma? to say that these kinds of
         disk assertions are "stable" when we go from hG to hG' because
         disk ffi generation number doesn't change *)
      rewrite /append_log_proof.uninit_log;
      rewrite /append_log_proof.crashed_log;
      rewrite /append_log_proof.is_log';
      rewrite /append_log_proof.is_hdr;
      rewrite /disk_array; rewrite /diskG0;
      rewrite Heq;
      iFrame.
  - rewrite /P/log_ctx.
    iAssert (⌜ ls = Opened s l  ⌝ ∗ log_ctx (Opened s l) ∗ log_frag s)%I with "[HP Hctx]" as (Heqls) "(Hctx&Hfrag)".
    { admit. }
    iExists _. unshelve (iExists _).
    { econstructor.
      { symmetry; eauto. }
      simpl.
      repeat econstructor.
    }
    iFrame. iIntros (hRG' (Heq1&Heq2)) "Hrestart".
    iModIntro.
    iExists tt, γtok. iRight.
    rewrite /logG0//=/log_frag//=. rewrite Heq2. rewrite Heq1.
    iFrame. subst.
    rewrite /append_log_proof.uninit_log.
    rewrite /disk_array. rewrite /diskG0.
      iExists _; iFrame;
      iFrame; subst;
      (* XXX: need a typeclass? or lemma? to say that these kinds of
         disk assertions are "stable" when we go from hG to hG' because
         disk ffi generation number doesn't change *)
      rewrite /append_log_proof.uninit_log;
      rewrite /append_log_proof.crashed_log;
      rewrite /append_log_proof.is_log';
      rewrite /append_log_proof.is_hdr;
      rewrite /disk_array; rewrite /diskG0;
      rewrite Heq;
      iFrame.
Admitted.

End refinement.
