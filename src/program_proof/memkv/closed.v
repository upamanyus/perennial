From Perennial.algebra Require Import gen_heap_names.
From Perennial.goose_lang Require Import lang notation typing lifting.
From Perennial.goose_lang.lib Require Import map.impl list.impl list_slice.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang.ffi Require Import dist_ffi.
From Perennial.goose_lang Require Import ffi.dist_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.


From Perennial.program_proof Require Import dist_prelude.
From Perennial.program_proof.lockservice Require Export rpc.
From Perennial.program_proof.memkv Require Export
     memkv_shard_definitions memkv_shard_start_proof memkv_shard_make_proof memkv_shard_ghost_init.

Definition shard_boot (host : u64) : expr :=
  let: "s" := MakeMemKVShardServer #true in
  MemKVShardServer__Start "s" #host.

From Perennial.goose_lang Require Import adequacy recovery_adequacy dist_adequacy.

Definition shardΣ := #[heapΣ; kvMapΣ; rpcΣ ShardReplyC; rpcregΣ].

(* TODO: move *)
Lemma heapG_heap_globalG_roundtrip {Σ} Hheap Hcrash local_names :
  Hheap =
  @heapG_heap_globalG Σ
    (@heap_globalG_heapG grove_op grove_model grove_semantics grove_interp grove_interp_adequacy Σ Hheap
       Hcrash local_names).
Proof.
  rewrite /heapG_heap_globalG. rewrite /heap_globalG_heapG //=.
  destruct Hheap => //=. f_equal.
  * destruct heap_globalG_preG => //= . f_equal.
    { destruct heap_preG_iris => //=. }
    { destruct heap_preG_crash => //=. }
    { destruct heap_preG_heap => //=. }
    { destruct heap_preG_ffi => //=. }
    { destruct heap_preG_trace => //=. }
  * rewrite gen_heapG_update_pre_get //=.
  * rewrite /inv_get_names //=.
    destruct heap_globalG_inv_names => //=.
Qed.

Lemma shard_boot1 (host : chan) σ (g : ffi_global_state) :
  ffi_initgP g →
  ffi_initP σ.(world) g →
  (g : gmap chan (gset message)) !! host = Some (∅ : gset message) →
  dist_adequate_failstop [(shard_boot host, σ)] g (λ _, True).
Proof.
  intros Hinit1 Hinit2 Hlookup.
  eapply (heap_dist_adequacy_failstop (shardΣ)).
  { assumption. }
  { auto. }
  intros Hheap. rewrite /=.
  iIntros "(Hchan&_)".

  (* Get out the channel for the server *)
  iDestruct (big_sepM_lookup_acc with "Hchan") as "(Hg&_)"; first eassumption.
  remember (uNSHARD) as uNSHARD' eqn:Heq_unSHARD'.
  iMod (kvptsto_init uNSHARD') as (γkv) "(Hserver_shards&Hclients_ptstos)"; first done.
  iMod (shard_server_ghost_init host γkv with "[$Hg]") as (γ Heq_kv) "(#Hdom&#Hsrv&Hsrv_rpc_ghost&Hsrv_cid)".

  iModIntro.
  iSplitR ""; last first.
  { iMod (fupd_mask_subseteq ∅); eauto. }
  iSplitR ""; last eauto.

  iIntros (Hcrash Heq local_names) "(_&?&?)".

  iModIntro. iExists (λ _, True%I).
  rewrite /shard_boot.
  wp_bind (MakeMemKVShardServer #true).
  wp_apply (wp_MakeMemKVShardServer with "[Hsrv_cid Hserver_shards Hsrv_rpc_ghost]").
  { iSplitL "".
    { rewrite is_shard_server_unfold. iNamed "Hsrv". iFrame "#". }
    iClear "Hsrv". iFrame "Hsrv_rpc_ghost".
    rewrite -Heq_unSHARD' Heq_kv. iFrame "Hserver_shards".
    eauto. }
  iIntros (s) "His_server".
  wp_pures.
  wp_apply (wp_MemKVShardServer__Start with "[] [] [$His_server]").
  { iExactEq "Hdom". rewrite //=. f_equal. set_solver. }
  { iExactEq "Hsrv". f_equal. apply heapG_heap_globalG_roundtrip. }
  eauto.
Qed.