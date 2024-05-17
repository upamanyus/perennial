From Perennial.goose_lang Require Import notation typing exception.
From Perennial.goose_lang Require Import proofmode wpc_proofmode.
From Perennial.goose_lang.lib Require Export typed_mem loop.impl.

Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context {ext_ty: ext_types ext}.

Theorem wp_for P stk E (cond body post: val) Φ :
  P -∗
  □ (P -∗
     WP cond #() @ stk ; E {{ v, ⌜ v = #true ⌝ ∗
                                 WP body #() @ stk ; E {{ bv,
                                              ⌜ bv = continue_val ⌝ ∗ WP post #() @ stk; E {{ _, P }} ∨
                                              ⌜ bv = execute_val ⌝ ∗ WP post #() @ stk; E {{ _, P }} ∨
                                              ⌜ bv = break_val ⌝ ∗ WP do: #() @ stk ; E {{ Φ }} ∨
                                              ∃ v, ⌜ bv = return_val v ⌝ ∗ Φ bv
                                                       }} ∨
                                 ⌜ v = #false ⌝ ∗ Φ #() }}) -∗
  WP (for: cond; post := body) @ stk ; E {{ Φ }}.
Proof.
  iIntros "HP #Hloop".
  wp_rec.
  wp_let. wp_let.
  wp_pure (Rec _ _ _).
  match goal with
  | |- context[RecV (BNamed "loop") _ ?body] => set (loop:=body)
  end.
  iLöb as "IH".
  wp_pures.
  iDestruct ("Hloop" with "HP") as "Hloop1".
  wp_bind (cond #()).
  wp_apply (wp_wand with "Hloop1").
  iIntros (c) "Hbody".
  iDestruct "Hbody" as "[[% Hbody]|[% HΦ]]"; subst.
  - wp_pures.
    wp_apply (wp_wand with "Hbody").
    iIntros (bc) "Hb". (*[[% HP] | [[% HP] | [[% HΦ] | HΦ]]]". *)
    iDestruct "Hb" as "[[% HP]|Hb]".
    { (* body terminates with "continue" *)
      subst. wp_pures. (* FIXME: don't unfold [do:] here *)
      wp_lam; wp_pures; wp_lam; wp_pures.
      wp_apply (wp_wand with "HP").
      iIntros (?) "HP".
      wp_lam; wp_pures.
      wp_lam. do 6 wp_pure1.
      wp_bind (App (RecV "loop" _ _) _).
      iSpecialize ("IH" with "HP").
      iApply (wp_wand with "IH").
      iIntros (?) "HΦ".
      wp_lam; wp_pures; wp_lam; wp_pures.
      done.
    }
    iDestruct "Hb" as "[[% HP]|Hb]".
    { (* body terminates with "execute" *)
      subst. wp_pures. (* FIXME: don't unfold [do:] here *)
      wp_lam; wp_pures; wp_lam; wp_pures.
      wp_apply (wp_wand with "HP").
      iIntros (?) "HP".
      wp_lam; wp_pures.
      wp_lam. do 6 wp_pure1.
      wp_bind (App (RecV "loop" _ _) _).
      iSpecialize ("IH" with "HP").
      iApply (wp_wand with "IH").
      iIntros (?) "HΦ".
      wp_lam; wp_pures; wp_lam; wp_pures.
      done.
    }
    iDestruct "Hb" as "[[% HP]|Hb]".
    { (* body terminates with "break" *)
      subst. wp_pures.
      wp_apply (wp_wand with "HP").
      iIntros (?) "HΦ".
      (* FIXME: don't unfold [return:] here *)
      wp_lam; wp_pures; wp_lam; wp_pures.
      done.
    }
    iDestruct "Hb" as (?) "[% HΦ]".
    { (* body terminates with other error code *)
      wp_pures.
      subst.
      wp_pures.
      wp_lam; wp_pures; wp_lam; wp_pures.
      wp_lam; wp_pures; wp_lam; wp_pures.
      wp_lam; wp_pures; wp_lam; wp_pures.
      done.
    }
  -
    wp_pures.
    wp_lam; wp_pures; wp_lam; wp_pures.
    done.
Qed.

Local Opaque load_ty store_ty.

(* FIXME: change requirement on return of [body] *)
Theorem wp_forUpto (I: u64 -> iProp Σ) stk E (start max:u64) (l:loc) (body: val) :
  int.Z start <= int.Z max ->
  (∀ (i:u64),
      {{{ I i ∗ l ↦[uint64T] #i ∗ ⌜int.Z i < int.Z max⌝ }}}
        body #() @ stk; E
      {{{ RET #true; I (word.add i (U64 1)) ∗ l ↦[uint64T] #i }}}) -∗
  {{{ I start ∗ l ↦[uint64T] #start }}}
    (for: (λ:<>, #max > ![uint64T] #l)%V ; (λ:<>, #l <-[uint64T] ![uint64T] #l + #1)%V :=
       body) @ stk; E
  {{{ RET #(); I max ∗ l ↦[uint64T] #max }}}.
Proof.
  iIntros (Hstart_max) "#Hbody".
  iIntros (Φ) "!> (H0 & Hl) HΦ".
  iAssert (∃ i, "HI" ∷ I i ∗
                "Hl" ∷ l ↦[uint64T] #i ∗
                "%Hineq" ∷ ⌜ int.Z i <= int.Z max ⌝)%I with "[H0 Hl]" as "HH".
  { iExists _; iFrame. done. }
  wp_apply (wp_for with "[-]"); [ by iNamedAccu | iIntros "!# __CTX"; iNamed "__CTX" ].
  iNamed "HH".
  wp_load.
  wp_pures.
Admitted.

(* Example specification for the usual for i := 0; i < max; i++ loop in Go.

In practice it is easier to use wp_forUpto, which is just after the loop
variable is allocated (it is a pointer since the loop must mutate it), since it
applies to just the For combinator rather than the sequence of allocation +
For. *)
Theorem wp_simpleFor (I: u64 -> iProp Σ) (max:u64) (body: val) :
  (∀ (l:loc) (i:u64),
      {{{ I i ∗ l ↦[uint64T] #i ∗ ⌜int.Z i < int.Z max⌝ }}}
        body #l
      {{{ RET #true; I (word.add i (U64 1)) ∗ l ↦[uint64T] #i }}}) -∗
  {{{ I (U64 0) }}}
    (let: "i" := ref_to uint64T #0 in
     (for: (λ:<>, ![uint64T] (Var "i") < #max)%E;
           (λ:<>, (Var "i") <-[uint64T] ![uint64T] (Var "i") + #1)%E :=
       (λ:<>, body (Var "i"))))
  {{{ RET #(); I max }}}.
Proof.
  iIntros "#Hbody".
  iIntros (Φ) "!> HI0 HΦ".
  wp_apply wp_ref_to; [ val_ty | ].
  iIntros (l) "Hl".
  wp_pures.
  wp_apply (wp_forUpto I with "[] [$HI0 $Hl]").
  { word. }
  { clear.
    iIntros (i).
    iIntros (Φ) "!> (Hi & Hl & %Hbound) HΦ".
    wp_pures.
    wp_apply ("Hbody" with "[$Hi $Hl] [$]").
    iPureIntro; done. }
  iIntros "[HI _]".
  iApply ("HΦ" with "[$]").
Qed.

Local Hint Extern 2 (envs_entails _ (∃ i, ?I i ∗ ⌜_⌝)%I) =>
iExists _; iFrame; iPureIntro; word : core.

Theorem wpc_forBreak_cond' (I: bool -> iProp Σ) Ic Φ Φc stk E1 (cond body: val) :
  (∀ b, I b -∗ Ic) -∗
  (Ic -∗ Φc) ∧ ▷ (I false -∗ Φ #()) -∗
  □ (I true -∗
     WPC if: cond #() then body #() else #false @ stk; E1
     {{ v, ∃ b : bool, ⌜ v = #b ⌝ ∧ I b }}
     {{ Ic }}) -∗
  I true -∗
  WPC (for: cond; (λ: <>, (λ: <>, #())%V #())%V := body) @ stk; E1
  {{ Φ }}
  {{ Φc }}.
Proof.
  iIntros "HIc HΦ #Hbody I".
  rewrite /For.
  iCache with "HIc I HΦ".
  { iLeft in "HΦ". iDestruct ("HIc" with "[$]") as "HI". by iApply "HΦ". }
  wpc_pures.
  wpc_pures.
  { iLeft in "HΦ". iDestruct ("HIc" with "[$]") as "HI". by iApply "HΦ". }
  iLöb as "IH".
  wpc_bind_seq.
  iDestruct ("Hbody" with "I") as "Hbody1".
  iApply (wpc_strong_mono with "Hbody1"); try auto.
  iSplit; last first.
  { iLeft in "HΦ". iIntros "H". iModIntro.
    by iApply "HΦ". }
  iIntros (v) "H".
  iModIntro.
  iDestruct "H" as (b Heq) "I".
  iCache with "HIc I HΦ".
  { iLeft in "HΦ". iDestruct ("HIc" with "[$]") as "HI". by iApply "HΦ". }
  wpc_pures. wpc_pures.
  subst.
  destruct b.
  - wpc_pures.
    iApply ("IH" with "[$] [$] [$]").
  - wpc_pures.
    { iRight in "HΦ". by iApply "HΦ". }
Qed.

Theorem wpc_forBreak_cond (I: bool -> iProp Σ) Ic stk E1 (cond body: val) :
  (∀ b, I b -∗ Ic) →
  {{{ I true }}}
    if: cond #() then body #() else #false @ stk; E1
  {{{ r, RET #r; I r }}}
  {{{ Ic }}} -∗
  {{{ I true }}}
    (for: cond; (λ: <>, (λ: <>, #())%V #())%V :=
       body) @ stk; E1
  {{{ RET #(); I false }}}
  {{{ Ic }}}.
Proof.
  iIntros (Hcrash) "#Hbody".
  iIntros (Φ Φc) "!> I HΦ".
  iApply (wpc_forBreak_cond' I Ic with "[] [$] [] [$]").
  { iIntros. by iApply Hcrash. }
  iModIntro. iIntros "HI".
  iApply ("Hbody" with "[$]").
  iSplit; eauto.
Qed.

Theorem wpc_forBreak_cond_2 (P: iProp Σ) stk E (cond body: goose_lang.val) (Φ : goose_lang.val → iProp Σ) (Φc: iProp Σ) :
  P -∗
  (P -∗ Φc) -∗
  □ (P -∗
      WPC if: cond #() then body #() else #false @ stk; E
      {{ v, ⌜v = #true⌝ ∗ P ∨ ⌜v = #false⌝ ∗ (Φ #() ∧ Φc) }} {{ Φc }} ) -∗
  WPC (for: cond; (λ: <>, Skip)%V := body) @ stk; E {{ Φ }} {{ Φc }}.
Proof.
  iIntros "HP HΦc #Hbody".
  rewrite /For.
  iCache with "HP HΦc".
  { by iApply "HΦc". }
  wpc_pures.
  iLöb as "IH".
  wpc_bind_seq.
  iDestruct ("Hbody" with "HP") as "Hbody1".
  iApply (wpc_strong_mono with "Hbody1"); try auto.
  iSplit; last first.
  { iIntros. by iModIntro. }
  iIntros (v) "H".
  iModIntro.
  iDestruct "H" as "[[% H]|[% H]]"; subst.
  - iCache with "HΦc H".
    { iSpecialize ("HΦc" with "H"). done. }
    wpc_pures.
    wpc_pures.
    iApply ("IH" with "[$] [$]").
  - iCache with "H".
    { by iRight in "H". }
    wpc_pures.
    wpc_pures.
    by iLeft in "H".
Qed.

Theorem wpc_forUpto (I I': u64 -> iProp Σ) stk E1 (start max:u64) (l:loc) (body: val) :
  int.Z start <= int.Z max ->
  (∀ (i:u64), ⌜int.Z start ≤ int.Z i ≤ int.Z max⌝ -∗ I i -∗ I' i) →
  (∀ (i:u64),
      {{{ I i ∗ l ↦[uint64T] #i ∗ ⌜int.Z i < int.Z max⌝ }}}
        body #() @ stk; E1
      {{{ RET #true; I (word.add i (U64 1)) ∗ l ↦[uint64T] #i }}}
      {{{ I' i ∨ I' (word.add i (U64 1)) }}}) -∗
  {{{ I start ∗ l ↦[uint64T] #start }}}
    (for: (λ:<>, #max > ![uint64T] #l)%V ; (λ:<>, #l <-[uint64T] ![uint64T] #l + #1)%V :=
       body) @ stk; E1
  {{{ RET #(); I max ∗ l ↦[uint64T] #max }}}
  {{{ ∃ (i:u64), I' i ∗ ⌜int.Z start <= int.Z i <= int.Z max⌝ }}}.
Proof.
  iIntros (Hstart_max Himpl) "#Hbody".
  iIntros (Φ Φc) "!> (H0 & Hl) HΦ".
  rewrite /For /Continue.
  wpc_rec Hcrash.
  {
    iDestruct (Himpl with "[%] H0") as "H0".
    { lia. }
    crash_case.
    iExists _; iFrame.
    auto.
  }
  clear Hcrash.
  wpc_pure1 Hcrash; auto.
  {
    iDestruct (Himpl with "[%] H0") as "H0".
    { lia. }
    crash_case.
    iExists _; iFrame.
    auto.
  }
  wpc_pure1 _; auto.
  wpc_pure1 _; auto.
  wpc_pure1 _; auto.
  wpc_pure (Rec _ _ _) Hcrash.
  match goal with
  | |- context[RecV (BNamed "loop") _ ?body] => set (loop:=body)
  end.
  remember start as x.
  assert (int.Z start <= int.Z x <= int.Z max) as Hbounds by (subst; word).
  clear Heqx Hstart_max.
  iDestruct "H0" as "HIx".
  clear Hcrash.
  (iLöb as "IH" forall (x Himpl Hbounds)).
  iCache with "HΦ HIx".
  {
    iDestruct (Himpl with "[] [$]") as "?"; eauto.
    { iPureIntro; lia. }
    crash_case.
    iExists _; iFrame.
    iPureIntro. lia.
  }
  wpc_pures.
  wpc_pures.
  wpc_bind (load_ty _ _).
  wpc_frame.
  wp_load.
  iIntros "!> H". iNamed "H".
  wpc_pures.
  wpc_bind (If _ _ _).
  wpc_if_destruct; wpc_pures; auto; try (by (iDestruct (Himpl with "[$]") as "?"; eauto)).
  - wpc_apply ("Hbody" with "[$HIx $Hl]").
    { iPureIntro; lia. }
    iSplit.
    { iDestruct "HΦ" as "(HΦ&_)".  iIntros "[IH1 | IH2]"; iApply "HΦ"; auto. }
    iIntros "!> [HIx Hl]".
    iCache with "HΦ HIx".
    {
      iDestruct (Himpl with "[] [$]") as "?"; eauto.
      {iPureIntro; word. }
      crash_case.
      eauto.
    }
    wpc_pures.
    wpc_frame_seq.
    wp_load.
    wp_store.
    iModIntro. iNamed 1.
    wpc_pure1 Hcrash.
    { iFromCache. }
    wpc_pure1 Hcrash.
    iApply ("IH" with "[%] [] HIx Hl").
    { iIntros (i Hbound) "HIx".
      iDestruct (Himpl with "[%] HIx") as "$".
      revert Hbound; word. }
    { iPureIntro; word. }
    iSplit.
    + iLeft in "HΦ".
      iIntros "HIx".
      iApply "HΦ".
      iDestruct "HIx" as (x') "[HI %]".
      iExists _; iFrame.
      iPureIntro; revert H; word.
    + iRight in "HΦ".
      iFrame.
  - assert (int.Z x = int.Z max) by word.
    apply word.unsigned_inj in H; subst.
    iApply ("HΦ" with "[$]").
Qed.

End goose_lang.

(** Tactics for convenient loop reasoning *)
Ltac wp_forBreak_cond :=
  wp_bind (For _ _ _); iApply (wp_forBreak_cond' with "[-]");
  [ by iNamedAccu
  | iIntros "!# __CTX"; iNamed "__CTX" ].
Ltac wp_forBreak :=
  wp_bind (For _ _ _); iApply (wp_forBreak' with "[-]");
  [ by iNamedAccu
  | iIntros "!# __CTX"; iNamed "__CTX" ].
