From Perennial.algebra Require Import gen_heap_names.
From Perennial.goose_lang Require Import lang notation typing lifting.
From Perennial.goose_lang.lib Require Import map.impl list.impl list_slice.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv connman.


From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.lockservice Require Export rpc.
From Perennial.program_proof.memkv Require Export
     memkv_shard_definitions memkv_shard_start_proof memkv_shard_make_proof memkv_shard_ghost_init.
From Perennial.program_proof.memkv Require Export
     memkv_coord_definitions memkv_coord_start_proof memkv_coord_make_proof memkv_coord_ghost_init.
From Perennial.program_proof.memkv Require Export memkv_clerk_proof.

Definition shard_boot (host : u64) : expr :=
  let: "s" := MakeKVShardServer #true in
  KVShardServer__Start "s" #host.

Definition coord_boot (host : u64) (init : u64) : expr :=
  let: "s" := MakeKVCoordServer #init in
  KVCoord__Start "s" #host.

Definition client_boot (coord : u64) : expr :=
  let: "cm" := MakeConnMan #() in
  MakeKVClerk #coord "cm".

From Perennial.goose_lang Require Import adequacy dist_adequacy grove_ffi_adequacy.
From Perennial.goose_lang.ffi Require Import grove_ffi_adequacy.

Definition shardΣ := #[heapΣ; kvMapΣ; rpcΣ ShardReplyC; rpcregΣ].

(* TODO: move *)
Lemma heapG_heap_globalG_roundtrip {Σ} Hheap Hcrash local_names :
  Hheap =
  @heapG_heap_globalG Σ
    (@dist_heapGS_heapGS grove_op grove_model grove_semantics grove_interp grove_interp_adequacy Σ Hheap
       Hcrash local_names).
Proof.
  rewrite /heapG_heap_globalG. rewrite /dist_heapGS_heapGS //=.
  destruct Hheap => //=. f_equal.
  * destruct dist_heapGpreS => //= . f_equal.
    { destruct heap_preG_iris => //=. }
    { destruct heap_preG_crash => //=. }
    { destruct heap_preG_heap => //=. }
    { destruct heap_preG_ffi => //=. }
    { destruct heap_preG_trace => //=. }
    { destruct heap_preG_credit => //=. }
  * rewrite gen_heapG_update_pre_get //=.
  * rewrite /inv_get_names //=.
    destruct dist_heapGS_inv_names => //=.
Qed.

Lemma shard_coord_boot (shardId coordId : chan) σshard σcoord σclient (g : ffi_global_state) :
  shardId ≠ coordId →
  ffi_initgP g →
  ffi_initP σshard.(world) g →
  ffi_initP σcoord.(world) g →
  ffi_initP σclient.(world) g →
  (g : gmap chan (gset message)) !! shardId = Some (∅ : gset message) →
  (g : gmap chan (gset message)) !! coordId = Some (∅ : gset message) →
  dist_adequate_failstop [(shard_boot shardId, σshard);
                          (coord_boot coordId shardId, σcoord);
                          (client_boot coordId, σclient)] g (λ _, True).
Proof.
  intros Hneq Hinitg Hinitshard Hinitcoord Hinitclient Hlookup1 Hlookup2.
  eapply (grove_ffi_dist_adequacy_failstop (shardΣ)).
  { assumption. }
  intros Hheap.
  iIntros "Hchan".

  (* Init the channel inv for the shard server *)
  iDestruct (big_sepM_delete with "Hchan") as "(Hshard_chan&Hrest)"; first eapply Hlookup1.
  remember (uNSHARD) as uNSHARD' eqn:Heq_unSHARD'.
  iMod (kvptsto_init uNSHARD') as (γkv) "(Hserver_shards&Hclients_ptstos)"; first done.
  iMod (shard_server_ghost_init shardId γkv with "[$Hshard_chan]")
    as (γ Heq_kv) "(#Hdom&#Hsrv&Hsrv_rpc_ghost&Hsrv_cid)".

  (* Init the channel inv for the shard server *)
  iDestruct (big_sepM_delete with "Hrest") as "(Hcoord_chan&_)".
  { rewrite lookup_delete_ne; first eapply Hlookup2; eauto. }
  iMod (coord_server_ghost_init coordId γkv with "[$Hcoord_chan]")
    as (γ' Heq_kv') "(#Hdom'&#Hsrv')".

  iModIntro.
  iSplitR ""; last first.
  { iMod (fupd_mask_subseteq ∅); eauto. }
  iSplitL "Hserver_shards Hsrv_rpc_ghost Hsrv_cid".
  {
    iIntros (Hcrash local_names).
    iModIntro. iExists (λ _, True%I).
    rewrite /shard_boot. simpl.
    wp_bind (MakeKVShardServer #true).
    wp_apply (wp_MakeKVShardServer with "[Hsrv_cid Hserver_shards Hsrv_rpc_ghost]").
    { iSplitL "".
      { rewrite is_shard_server_unfold. iNamed "Hsrv". iFrame "#". }
      iClear "Hsrv". iFrame "Hsrv_rpc_ghost".
      rewrite -Heq_unSHARD' Heq_kv. iFrame "Hserver_shards".
      eauto. }
    iIntros (s) "His_server".
    wp_pures.
    wp_apply (wp_KVShardServer__Start with "[] [] [$His_server]").
    { iExactEq "Hdom". rewrite //=. f_equal. set_solver. }
    { iExactEq "Hsrv". f_equal. apply heapG_heap_globalG_roundtrip. }
    eauto.
  }
  iSplitR "Hclients_ptstos".
  {
    iIntros (Hcrash local_names).
    iModIntro. iExists (λ _, True%I).
    rewrite /coord_boot. simpl.
    wp_bind (MakeKVCoordServer #(shardId : u64)).
    wp_apply (wp_MakeKVCoordServer with "[]").
    { iSplitL ""; last first.
      { rewrite /named. iExactEq "Hsrv".
        f_equal. apply heapG_heap_globalG_roundtrip. }
      { iPureIntro. rewrite Heq_kv; symmetry; eauto. }
    }
    iIntros (s) "His_server".
    wp_pures.
    wp_apply (wp_KVCoordServer__Start with "[] [] [His_server]").
    { iExactEq "Hdom'". rewrite //=. f_equal. set_solver. }
    { iExactEq "Hsrv'". rewrite -heapG_heap_globalG_roundtrip. eauto. }
    { iFrame "His_server". }
    eauto.
  }
  iSplitR ""; last eauto.
  {
    iIntros (Hcrash local_names).
    iModIntro. iExists (λ _, True%I).
    rewrite /client_boot. iEval simpl.
    wp_apply wp_MakeConnMan.
    iIntros (cm) "Hcm".
    wp_apply (wp_MakeKVClerk with "[] Hcm").
    {
      iExactEq "Hsrv'". rewrite -heapG_heap_globalG_roundtrip. f_equal.
    }
    eauto.
  }
Qed.
