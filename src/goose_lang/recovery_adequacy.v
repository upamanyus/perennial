From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From Perennial.base_logic.lib Require Import proph_map.
From Perennial.program_logic Require Export weakestpre adequacy.
From Perennial.algebra Require Import proph_map.
From Perennial.goose_lang Require Import proofmode notation.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy.
From Perennial.goose_lang Require Export wpr_lifting.
From Perennial.goose_lang Require Import typing adequacy lang.
Set Default Proof Using "Type".

Theorem heap_recv_adequacy `{ffi_sem: ext_semantics} `{!ffi_interp ffi} {Hffi_adequacy:ffi_interp_adequacy} Σ `{hPre: !heapPreG Σ} s k e r σ φ φr φinv Φinv (HINIT: ffi_initP σ.(world)) :
  (∀ `{Hheap : !heapG Σ},
     ⊢ (ffi_start (heapG_ffiG) σ.(world) -∗ trace_frag σ.(trace) -∗ oracle_frag σ.(oracle) ={⊤}=∗
       □ (∀ n ns σ κ, state_interp σ ns κ n -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝) ∗
       □ (∀ hG (Hpf: @heapG_invG _ _ _ _ Hheap = @heapG_invG _ _ _ _ hG),
                     Φinv hG -∗ □ ∀ σ ns κ n, state_interp σ ns κ n -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝) ∗
        wpr s k ⊤ e r (λ v, ⌜φ v⌝) Φinv (λ _ v, ⌜φr v⌝))) →
  recv_adequate (CS := goose_crash_lang) s e r σ (λ v _, φ v) (λ v _, φr v) φinv.
Proof.
  intros Hwp.
  eapply (wp_recv_adequacy_inv _ _ _ heap_namesO _ _ _ _ _ _ _ _ (λ Hinv Hc names, Φinv (heap_update_pre _ _ Hinv Hc (@pbundleT _ _ names))) (λ n, n)).
  iIntros (???) "".
  iMod (na_heap_name_init tls σ.(heap)) as (name_na_heap) "Hh".
  iMod (proph_map_name_init _ κs σ.(used_proph_id)) as (name_proph_map) "Hp".
  iMod (ffi_name_init _ _ σ.(world)) as (ffi_names) "(Hw&Hstart)"; first auto.
  iMod (trace_name_init σ.(trace) σ.(oracle)) as (name_trace) "(Htr&Htrfrag&Hor&Hofrag)".
  set (hnames := {| heap_heap_names := name_na_heap;
                      heap_proph_name := name_proph_map;
                      heap_ffi_names := ffi_names;
                      heap_trace_names := name_trace |}).
  set (hG := heap_update_pre _ hPre Hinv Hc hnames).
  iExists ({| pbundleT := hnames |}).
  iExists
    (λ t σ ns κs nt, let _ := heap_update Σ hG Hinv Hc (@pbundleT _ _ t) in
               state_interp σ ns κs nt)%I,
    (λ t _, True%I).
  iExists _. (* (λ Hc t, λ (σ0 : state) (_ : nat) (κs0 : list observation) (_ : nat),
                                              lifting.heapG_irisG_obligation_1 Σ
                                                (heap_update Σ (heap_update_pre Σ hPre Hinv Hc hnames) Hinv Hc
                                                   pbundleT) σ0 κs0). *)
  iExists _.
  iExists _.
  iMod (Hwp hG with "[$] [$] [$]") as "(#H1&#H2&Hwp)".
  iModIntro.
  iSplitR.
  { iModIntro. iIntros (????) "H". rewrite heap_update_pre_update.
    by iApply "H1".
  }
  iSplitR.
  {
    iModIntro. iIntros (Hc' names') "H". rewrite ?heap_update_pre_update.
    iDestruct ("H2" $! _ _ with "H") as "#H3".
    iModIntro. iIntros (????) "H". iSpecialize ("H3" with "H").
    eauto.
  }
  iFrame. rewrite /hG//=.
  rewrite ffi_update_pre_update //=. iFrame.
  rewrite /wpr. rewrite /hG//=.
  rewrite heap_update_pre_get.
  rewrite //=.
  iApply (recovery_weakestpre.wpr_strong_mono with "Hwp").
  repeat iSplit; [| iModIntro; iSplit]; eauto.
  iIntros. rewrite heap_update_pre_update. eauto.
  Unshelve.
  - eauto.
  - (* TODO: where is this coming from? *)
    exact O.
  - (* TODO: where is this coming from? *)
    exact O.
Qed.
