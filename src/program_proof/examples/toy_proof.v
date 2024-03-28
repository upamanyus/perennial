From RecordUpdate Require Import RecordSet.

From Perennial.Helpers Require Import ModArith.
From Perennial.goose_lang Require Import crash_modality recovery_lifting.

From Goose.github_dot_com.mit_dash_pdos.perennial_dash_examples Require Import toy.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import disk_prelude.

Section goose.
  Context `{!heapGS Σ}.
  Context `{!stagedG Σ}.

  Definition EBlk (addr: u64) :=
   (∃ v n, "Ha" ∷ int.Z addr d↦ v ∗ "%H0iseven" ∷ ⌜ Block_to_vals v !! O = Some #(U8 n) ∧ Z.even n ⌝)%I.

  Definition written_slice : list val :=
    <[int.nat 0:=#(U8 4)]> (replicate (int.nat 4096) (zero_val byteT)).

  Definition written_block : Block := list_to_vec (U8 4 :: replicate (int.nat 4095) (U8 0)).

  Lemma written_slice_to_written_block:
    written_slice = Block_to_vals written_block.
  Proof.
    rewrite /written_slice.
    change (zero_val byteT) with #(U8 0).
    change (int.nat 4095) with (Z.to_nat 4095).
    rewrite /Block_to_vals /written_block //=.
  Qed.

  Theorem wpc_consumeEvenBlock_seq {E1} (d_ref: loc) (addr: u64) :
    {{{ EBlk addr }}}
      consumeEvenBlock #d_ref #addr @ E1
    {{{ RET #(); EBlk addr }}}
    {{{ EBlk addr }}}.
  Proof.
    iIntros (Φ Φc) "HE HΦ"; iNamed "HE".
    wpc_call.
    { iExists _, _; eauto. }
    { iExists _, _; eauto. }
    rewrite /BlockSize.
    iCache Φc with "HΦ Ha".
    { crash_case. iExists _, _; eauto. }
    wpc_pures.
    wpc_frame_seq.
    wp_apply (wp_new_slice).
    { apply to_val_has_zero. }
    iIntros (s) "Hslice". iNamed 1.
    wpc_pures.
    wpc_frame_seq.
    iDestruct (own_slice_small_acc with "Hslice") as "(H1&H2)".
    wp_apply (wp_SliceSet with "[$H1]").
    { eauto. }
    iIntros "Hslice"; iNamed 1.
    wpc_pures.
    wpc_bind (Write _ _).
    iApply (wpc_Write_fupd E1 with "[ Hslice]").
    { rewrite /is_block. iExactEq "Hslice". f_equal.
      erewrite <-written_slice_to_written_block. eauto.
    }
    iSplit; first iFromCache.
    iModIntro.
    iExists _. iFrame. iNext.
    iIntros "Hwritten".
    iModIntro.
    iCache Φc with "Hwritten HΦ".
    { crash_case. iExists _, 4. iFrame. iPureIntro. rewrite //=. }
    iSplit; first iFromCache.
    iIntros "Hblock".
    wpc_pures.

    wpc_bind (Read _).
    iApply (wpc_Read with "Hwritten").
    iSplit.
    { iLeft in "HΦ". iIntros "Hwritten". iApply "HΦ".
      iExists _, 4. iFrame. iPureIntro. rewrite //=. }
    iNext. iIntros (s') "(Hwritten&Hslice)".
    wpc_pures.

    wpc_frame.
    wp_bind (SliceGet _ _ _).
    iDestruct (own_slice_small_acc with "Hslice") as "(H1&H2')".
    iApply (wp_SliceGet with "[$H1]").
    { iPureIntro. rewrite //=. }
    iNext. iIntros "(H1&%Hval)".
    wp_pures.
    iModIntro. iNamed 1.
    iApply "HΦ". iExists _, _. iFrame. eauto.
  Qed.

  Theorem wpc_consumeEvenBlock (d_ref: loc) (addr: u64):
    {{{ crash_borrow (EBlk addr) (EBlk addr) }}}
      consumeEvenBlock #d_ref #addr @ ⊤
    {{{ RET #() ; True }}}
    {{{ True }}}.
  Proof.
    iIntros (Φ Φc) "Hncinv HΦ".
    iApply (wpc_step_strong_mono' _ _ _ _ _
           (λ v, ⌜ v = #() ⌝ ∗ True)%I _ True with "[-HΦ] [HΦ]"); auto.
    2: { iSplit.
         * iNext. iIntros (?) "H". iDestruct "H" as (?) "%". subst.
           iModIntro. iRight in "HΦ". by iApply "HΦ".
         * iLeft in "HΦ". iIntros. by iApply "HΦ". }
    iApply (wpc_crash_borrow_open with "Hncinv").
    { eauto. }
    iSplit; first eauto.
    iIntros "Hblk".
    wpc_apply (wpc_consumeEvenBlock_seq with "[$]").
    iSplit.
    { iIntros; iFrame. }
    iNext. iIntros "$ _".
    iSplit; eauto.
    Unshelve. exact ⊤.
  Qed.

  Theorem wpc_TransferEvenBlock (d_ref: loc) (addr: u64) :
    {{{ EBlk addr }}}
      TransferEvenBlock #d_ref #addr @ ⊤
    {{{ RET #() ; True }}}
    {{{ EBlk addr }}}.
  Proof using stagedG0.
    iIntros (Φ Φc) "HEblk HΦ".
    rewrite /TransferEvenBlock.
    iApply (wpc_crash_borrow_init_ctx _ _ _ _ (EBlk addr)%I (EBlk addr)%I id with "HEblk"); auto.
    iSplit.
    { by iLeft in "HΦ". }
    iIntros "Hborrow".
    wpc_pures.
    { iLeft in "HΦ". eauto. }
    wpc_pures.
    { iLeft in "HΦ". eauto. }
    wpc_apply (wpc_fork with "[Hborrow]").
    { iNext. iApply (wpc_consumeEvenBlock with "Hborrow"); eauto. }
    iSplit.
    { iLeft in "HΦ". eauto. }
    { iNext. simpl. wpc_pures; first by iLeft in "HΦ".
      iModIntro. iApply wpc_value. iSplit.
      * iRight in "HΦ". by iApply "HΦ".
      * iLeft in "HΦ". iModIntro. by iApply "HΦ".
    }
  Qed.

End goose.
