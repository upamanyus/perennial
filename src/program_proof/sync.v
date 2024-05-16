From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.program_logic Require Import weakestpre.

From Perennial.goose_lang Require Import lang typing.
From Perennial.goose_lang Require Import proofmode notation.
From Perennial.goose_lang Require Import persistent_readonly.
From Perennial.goose_lang.lib Require Import typed_mem.
From Goose Require Export sync.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang Require Import exception.

Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.
Context {ext_tys: ext_types ext}.

Local Coercion Var' (s:string): expr := Var s.

Section proof.
  Context `{!heapGS Σ} (N : namespace).

  (** This means [m] is a valid mutex with invariant R. *)
  Definition is_Mutex (m: loc) (R : iProp Σ) : iProp Σ :=
    inv N (
          ∃ b : bool, m ↦[Mutex :: "state"]{1/4} #b ∗
                   if b then True else m ↦[Mutex :: "state"]{3/4} #b ∗ R
          ).

  (** This resource denotes ownership of the lock (i.e. the lock is currently
      held). *)
  Definition own_Mutex (m: loc) : iProp Σ := m ↦[Mutex :: "state"]{3/4} #true.

  Lemma own_Mutex_exclusive (m : loc) : own_Mutex m -∗ own_Mutex m -∗ False.
  Proof.
    iIntros "H1 H2".
    iCombine "H1 H2" as "H".
    (* FIXME: need
    iDestruct (struct_field_pointsto_frac_valid with "H") as %Hval. *)
    admit.
  Admitted.

  Global Instance is_Mutex_ne m : NonExpansive (is_Mutex m).
  Proof. solve_proper. Qed.

  (** The main proofs. *)
  Global Instance is_Mutex_persistent m R : Persistent (is_Mutex m R).
  Proof. apply _. Qed.
  Global Instance locked_timeless m : Timeless (own_Mutex m).
  Proof. apply _. Qed.

  (** Denotes ownership of a mutex for which the lock invariant is not yet
      decided *)
  Definition own_uninit_Mutex (m: loc): iProp Σ := m ↦[Mutex :: "state"] #false.

  Theorem init_Mutex_inv R E m : own_uninit_Mutex m -∗ ▷ R ={E}=∗ is_Mutex m R.
  Proof.
    iIntros "Hl HR".
    iMod (inv_alloc N _ (_) with "[Hl HR]") as "#?".
    2:{ by iFrame "#". }
    { iIntros "!>". iExists false. iFrame.
      rewrite /own_uninit_Mutex.
      iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
      iDestruct "Hl" as "[Hl1 Hl2]".
      iFrame.
    }
  Qed.

  (* FIXME: lemma for (zero_val Mutex) *)
  (*
  Lemma wp_new_free_lock E:
    {{{ True }}} lock.new #() @ E {{{ m, RET #lk; own_uninit_Mutex m }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_call.
    wp_apply wp_alloc_untyped; auto.
  Qed. *)

  (*
  Lemma newlock_spec E (R : iProp Σ):
    {{{ ▷ R }}} lock.new #() @ E {{{ (lk:loc), RET #lk; own_lock #lk R }}}.
  Proof.
    iIntros (Φ) "HR HΦ". rewrite -wp_fupd /lock.new /=.
    wp_lam. wp_apply wp_alloc_untyped; first by auto.
    iIntros (l) "Hl".
    iMod (alloc_lock with "[$] HR") as "Hlock".
    iModIntro.
    iApply "HΦ". iFrame.
  Qed. *)

  Lemma wp_Mutex__Lock m R :
    {{{ is_Mutex m R }}}
      Mutex__Lock #m
    {{{ RET #(); own_Mutex m ∗ R }}}.
  Proof.
    iIntros (Φ) "#Hinv HΦ".
    wp_rec.
    wp_apply wp_struct_fieldRef; first done.
    wp_bind (CmpXchg _ _ _).
    wp_pures.
    iInv N as ([]) "[Hl HR]".
    -
      (* FIXME: struct fieldRef_f should match up with struct field points-tos. *)
      (*
      wp_cmpxchg_fail. iModIntro. iSplitL "Hl"; first (iNext; iExists true; eauto).
      wp_pures. iApply ("HΦ" $! false). done.
    - iDestruct "HR" as "[Hl2 HR]".
      iCombine "Hl Hl2" as "Hl".
      rewrite Qp.quarter_three_quarter.
      wp_cmpxchg_suc.
      iModIntro.
      iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
      iDestruct "Hl" as "[Hl1 Hl2]".
      iSplitL "Hl1"; first (iNext; iExists true; eauto).
      rewrite /locked. wp_pures.
      iApply "HΦ".
      eauto with iFrame. *)
  Admitted.

  Lemma wp_Mutex__Unlock m R :
    {{{ is_Mutex m R ∗ own_Mutex m ∗ ▷ R }}} Mutex__Unlock #m {{{ RET #(); True }}}.
  Proof.
    (*
    iIntros (? Φ) "(Hlock & Hlocked & HR) HΦ".
    iDestruct "Hlock" as (l ->) "#Hinv".
    rewrite /lock.release /=. wp_lam.
    wp_bind (CmpXchg _ _ _).
    iInv N as (b) "[>Hl _]".

    iDestruct (locked_loc with "Hlocked") as "Hl2".
    iDestruct (heap_pointsto_agree with "[$Hl $Hl2]") as %->.
    iCombine "Hl Hl2" as "Hl".
    rewrite Qp.quarter_three_quarter.
    wp_cmpxchg_suc.
    iModIntro.
    iSplitR "HΦ"; last by wp_seq; iApply "HΦ".
    iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
    iDestruct "Hl" as "[Hl1 Hl2]".
    iNext. iExists false. iFrame. *)
  Admitted.

  (** Cond proofs *)

  Definition is_Cond (c : loc) (m : loc) : iProp Σ :=
    readonly (c ↦ #m).

  Global Instance is_cond_persistent c m :
    Persistent (is_Cond c m) := _.

  Theorem wp_NewCond (m : loc) :
    {{{ True }}}
      NewCond #m
    {{{ (c: loc), RET #c; is_Cond c m }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    wp_call. wp_apply wp_fupd.
    wp_apply wp_alloc_untyped; [ auto | ].
    iIntros (c) "Hc".
    iMod (readonly_alloc_1 with "Hc") as "Hcond".
    wp_pures.
    iApply "HΦ". by iFrame.
  Qed.

  Theorem wp_Cond__Signal c m :
    {{{ is_Cond c m }}}
      Cond__Signal #c
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    wp_call.
    iApply ("HΦ" with "[//]").
  Qed.

  Theorem wp_Cond__Broadcast c lk :
    {{{ is_Cond c lk }}}
      Cond__Broadcast #c
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    wp_call.
    iApply ("HΦ" with "[//]").
  Qed.

  (* FIXME: notation *)
  Notation "e1 ;;;; e2" := (exception_seq e1 (λ: <>, e2)%V) (at level 90).
  Definition x := (Skip ;;;; Skip)%E.
  Print x. (* why doesn't printing use the same notation that was used in parsing x? *)
  Notation "e1 ~~~ e2" := (App (App (Val exception_seq) e1%E) (Val (RecV BAnon BAnon e2))) (at level 90).
  Print x.
  (* confirm that the two ways of invoking exception_seq are actually the same *)
  Definition f e1 e2 := (exception_seq e1%E (λ: <>, e2%E)%V)%E.
  Definition g e1 e2 := (App (App (Val exception_seq) e1%E) (Val (RecV BAnon BAnon e2))).
  Set Printing All. Print f. Print g. Unset Printing All.


  Instance pure_exception_seq (v:val) e : PureExec True 2 ((do: v) ;;; e) (e).
  Admitted.

  Theorem wp_Cond__Wait c m R :
    {{{ is_Cond c m ∗ is_Mutex m R ∗ own_Mutex m ∗ R }}}
      Cond__Wait #c
    {{{ RET #(); own_Mutex m ∗ R }}}.
  Proof.
    iIntros (Φ) "(#Hcond&#Hlock&Hlocked&HR) HΦ".
    unfold Cond__Wait.
    wp_pures.

    iMod (readonly_load with "Hcond") as (q) "Hc".
    wp_untyped_load.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $HR]").
    wp_bind (exception_seq _).
    wp_bind (Pair _ _).
    wp_lam. wp_pures.
    Search PureExec.
    wp_pure1.
    wp_pures.
    wp_untyped_load.
    wp_apply (acquire_spec with "[$Hlock]").
    iIntros "(Hlocked&HR)".
    iApply "HΦ".
    iFrame.
  Qed.

  Theorem wp_condWaitTimeout c (t : u64) lk R :
    {{{ is_cond c lk ∗ is_lock lk R ∗ locked lk ∗ R }}}
      lock.condWaitTimeout #c #t
    {{{ RET #(); locked lk ∗ R }}}.
  Proof.
    iIntros (Φ) "Hpre HΦ".
    wp_lam. wp_pures.
    wp_apply (wp_condWait with "Hpre").
    done.
  Qed.

End proof.
End goose_lang.

(* Typeclasses Opaque is_lock is_cond locked. *)
