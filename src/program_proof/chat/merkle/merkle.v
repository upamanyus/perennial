From Perennial.program_proof Require Import grove_prelude.
From Goose.github_dot_com.mit_dash_pdos.secure_dash_chat.merkle Require Import merkle__shim.
From Goose.github_dot_com.mit_dash_pdos.secure_dash_chat Require Import merkle.

From Perennial.program_proof.chat.merkle Require Import shim.
From Perennial.program_proof Require Import std_proof.

Section defs.
Context `{!heapGS Σ}.

Inductive tree : Type :=
  (* Cut only exists for proof checking trees. *)
  | Cut : list u8 → tree
  | Empty : tree
  | Leaf : list u8 → tree
  | Interior : list tree → tree.

Fixpoint containsNodeAtEnd (tr : tree) (id : list u8) (node : tree) : Prop :=
  match tr with
  | Cut _ => False
  | Empty => id = [] ∧ tr = node
  | Leaf val => id = [] ∧ tr = node
  | Interior children =>
    match id with
    | [] => False
    | pos :: rest =>
      ∃ child, children !! int.nat pos = Some child ∧ containsNodeAtEnd child rest node
    end
  end.

Fixpoint is_tree_hash (tr: tree) (hash: list u8) : iProp Σ :=
  match tr with
  | Cut hash' => ⌜hash = hash' ∧ length hash' = 32%nat⌝
  | Empty => is_hash [U8 0] hash
  | Leaf val => is_hash (val ++ [U8 1]) hash
  | Interior children =>
    ∃ (child_hashes : list (list u8)),
    let map_fn := (λ c h, is_tree_hash c h) in
    ([∗ list] child_fn;hash' ∈ (map_fn <$> children);child_hashes,
      child_fn hash') ∗
    is_hash (concat child_hashes ++ [U8 2]) hash
  end%I.

(*
(* Note: don't currently need this, but it'd be nice to have. *)
#[global]
Instance is_tree_hash_persistent tr hash : Persistent (is_tree_hash tr hash).
Proof.
  rewrite /Persistent.
  iStartProof.
  iLöb as "IH" forall (tr hash).
  iIntros "Htr_hash".
  destruct tr.
  1-3: iDestruct "Htr_hash" as "#Htr_hash"; done.
  simpl.
  iDestruct "Htr_hash" as (?) "[Htr_hash #Hhash]".
  iFrame "#"; iClear (hash) "Hhash".
  iApply big_sepL2_persistently.
  iDestruct (big_sepL2_fmap_l (λ c h, is_tree_hash c h) with "Htr_hash") as "Htr_hash".
  iApply (big_sepL2_fmap_l (λ c h, is_tree_hash c h)).
  iApply (big_sepL2_impl with "Htr_hash").
  iIntros "!> %k %tr' %hash' % % Htr_hash".
  iSpecialize ("IH" $! tr' hash' with "[Htr_hash]"); [iFrame|].
  iDestruct (later_persistently_1 with "IH") as "#IH2".
  iIntros "!>".
  (* Problem: don't have later in goal to iMod IH2. *)
Admitted.
 *)

Lemma tree_hash_len tr hash :
  is_tree_hash tr hash -∗ ⌜length hash = 32%nat⌝.
Proof.
  iIntros "Htree".
  destruct tr.
  { iDestruct "Htree" as "[%Heq %Hlen]". naive_solver. }
  1-2: iDestruct (hash_len with "Htree") as "%Hlen"; naive_solver.
  {
    iDestruct "Htree" as (ch) "[_ Htree]".
    by iDestruct (hash_len with "Htree") as "%Hlen".
  }
Qed.

Definition is_path_node id node digest : iProp Σ :=
  ∃ tr,
  is_tree_hash tr digest ∧
  ⌜containsNodeAtEnd tr id node⌝.

Definition is_path_val id val digest : iProp Σ :=
  ∃ tr,
  is_tree_hash tr digest ∧
  ⌜containsNodeAtEnd tr id
    match val with
    | None => Empty
    | Some val' => Leaf val'
    end⌝.

Lemma concat_eq_dim1_eq {A : Type} sz (l1 l2 : list (list A)) :
  concat l1 = concat l2 →
  (Forall (λ l, length l = sz) l1) →
  (Forall (λ l, length l = sz) l2) →
  0 < sz →
  l1 = l2.
Proof.
  intros Heq_concat Hlen_l1 Hlen_l2 Hsz.
  apply (f_equal length) in Heq_concat as Heq_concat_len.
  do 2 rewrite concat_length in Heq_concat_len.
  generalize dependent l2.
  induction l1 as [|a1]; destruct l2 as [|a2]; simpl;
    intros Heq_concat Hlen_l2 Heq_concat_len;
    decompose_Forall; eauto with lia.
  apply (f_equal (take (length a1))) in Heq_concat as Htake_concat.
  apply (f_equal (drop (length a1))) in Heq_concat as Hdrop_concat.
  rewrite <-H in Htake_concat at 2.
  rewrite <-H in Hdrop_concat at 2.
  do 2 rewrite take_app_length in Htake_concat.
  do 2 rewrite drop_app_length in Hdrop_concat.
  rewrite Htake_concat.
  apply (app_inv_head_iff [a2]).
  apply IHl1; eauto with lia.
Qed.

Lemma sep_tree_hash_impl_forall_len ct ch :
  ([∗ list] t;h ∈ ct;ch, is_tree_hash t h) -∗
  ⌜Forall (λ l, length l = 32%nat) ch⌝.
Proof.
  iIntros "Htree".
  iDestruct (big_sepL2_impl _ (λ _ _ h, ⌜length h = 32%nat⌝%I) with "Htree []") as "Hlen_sepL2".
  {
    iIntros "!>" (???) "_ _ Hhash".
    by iDestruct (tree_hash_len with "Hhash") as "Hlen".
  }
  iDestruct (big_sepL2_const_sepL_r with "Hlen_sepL2") as "[_ %Hlen_sepL1]".
  iPureIntro.
  by apply Forall_lookup.
Qed.

Lemma is_path_val_inj' pos rest val1 val2 digest :
  is_path_val (pos :: rest) val1 digest -∗
  is_path_val (pos :: rest) val2 digest -∗
  ∃ digest',
  is_path_val rest val1 digest' ∗
  is_path_val rest val2 digest'.
Proof.
  iIntros "Hval1 Hval2".
  rewrite /is_path_val.
  iDestruct "Hval1" as (tr1) "[Htree1 %Hcont1]".
  iDestruct "Hval2" as (tr2) "[Htree2 %Hcont2]".
  destruct tr1 as [| | |ct1], tr2 as [| | |ct2]; try naive_solver.

  (* Get contains pred and is_tree_hash for children. *)
  destruct Hcont1 as [child1 [Hlist1 Hcont1]].
  destruct Hcont2 as [child2 [Hlist2 Hcont2]].
  iDestruct "Htree1" as (ch1) "[Htree1 Hdig1]".
  iDestruct "Htree2" as (ch2) "[Htree2 Hdig2]".
  iDestruct (big_sepL2_fmap_l (λ c h, is_tree_hash c h) with "Htree1") as "Htree1".
  iDestruct (big_sepL2_fmap_l (λ c h, is_tree_hash c h) with "Htree2") as "Htree2".

  (* Use is_hash ch1/ch2 digest to prove that child hashes are same. *)
  iDestruct (sep_tree_hash_impl_forall_len with "Htree1") as "%Hlen_ch1".
  iDestruct (sep_tree_hash_impl_forall_len with "Htree2") as "%Hlen_ch2".

  iDestruct (hash_inj with "Hdig1 Hdig2") as "%Heq".
  apply app_inv_tail in Heq.
  assert (ch1 = ch2) as Hch.
  { apply (concat_eq_dim1_eq 32); eauto with lia. }
  subst ch1.

  (* Finish up. *)
  iDestruct (big_sepL2_lookup_1_some with "Htree1") as (h1) "%Hlook1"; [done|].
  iDestruct (big_sepL2_lookup_1_some with "Htree2") as (h2) "%Hlook2"; [done|].
  iDestruct (big_sepL2_lookup with "Htree1") as "Hhash1"; [done..|].
  iDestruct (big_sepL2_lookup with "Htree2") as "Hhash2"; [done..|].
  clear Hlook1 Hlook2.

  iFrame "%∗".
Qed.

Lemma empty_leaf_hash_disjoint digest v :
  is_tree_hash Empty digest -∗
  is_tree_hash (Leaf v) digest -∗
  False.
Proof.
  iIntros "Hempty Hleaf".
  iDestruct (hash_inj with "Hempty Hleaf") as "%Heq".
  iPureIntro.
  destruct v as [|a]; [naive_solver|].
  (* TODO: why doesn't list_simplifier or solve_length take care of this? *)
  apply (f_equal length) in Heq.
  rewrite app_length in Heq.
  simpl in *.
  lia.
Qed.

Lemma is_path_val_inj id val1 val2 digest :
  is_path_val id val1 digest -∗
  is_path_val id val2 digest -∗
  ⌜val1 = val2⌝.
Proof.
  iInduction (id) as [|a] "IH" forall (digest);
    iIntros "Hpath1 Hpath2".
  {
    rewrite /is_path_val.
    iDestruct "Hpath1" as (tr1) "[Htree1 %Hcont1]".
    iDestruct "Hpath2" as (tr2) "[Htree2 %Hcont2]".
    destruct tr1 as [| | |ct1], tr2 as [| | |ct2], val1, val2; try naive_solver.
    { iExFalso. iApply (empty_leaf_hash_disjoint with "[$] [$]"). }
    { iExFalso. iApply (empty_leaf_hash_disjoint with "[$] [$]"). }
    destruct Hcont1 as [_ Hleaf1].
    destruct Hcont2 as [_ Hleaf2].
    inversion Hleaf1; subst l; clear Hleaf1.
    inversion Hleaf2; subst l0; clear Hleaf2.
    iDestruct (hash_inj with "[$Htree1] [$Htree2]") as "%Heq".
    by list_simplifier.
  }
  {
    iDestruct (is_path_val_inj' with "[$Hpath1] [$Hpath2]") as (digest') "[Hval1 Hval2]".
    by iSpecialize ("IH" $! digest' with "[$Hval1] [$Hval2]").
  }
Qed.

Definition own_Node' (recur : loc -d> tree -d> iPropO Σ) : loc -d> tree -d> iPropO Σ :=
  (λ ptr_tr tr,
    match tr with
    (* We should never have cuts in in-memory trees. *)
    | Cut _ => False
    | Empty =>
      ∃ hash,
      "#His_hash" ∷ is_tree_hash tr hash ∗
      "%Hnil" ∷ ⌜ptr_tr = null⌝
    | Leaf val =>
      ∃ sl_val hash sl_hash,
      "Hval" ∷ own_slice_small sl_val byteT 1 val ∗
      "Hptr_val" ∷ ptr_tr ↦[Node :: "Val"] (slice_val sl_val) ∗
      "#His_hash" ∷ is_tree_hash tr hash ∗
      "Hhash" ∷ own_slice_small sl_hash byteT 1 hash ∗
      "Hsl_hash" ∷ ptr_tr ↦[Node :: "hash"] (slice_val sl_hash)
    | Interior children =>
      ∃ hash sl_hash sl_children ptr_children,
      "#His_hash" ∷ is_tree_hash tr hash ∗
      "Hhash" ∷ own_slice_small sl_hash byteT 1 hash ∗
      "Hsl_children" ∷ own_slice_small sl_children ptrT 1 ptr_children ∗
      "Hptr_children" ∷ ptr_tr ↦[Node :: "Children"] (slice_val sl_children) ∗
      "Hchildren" ∷
        ([∗ list] child;ptr_child ∈ children;ptr_children,
          ▷ recur ptr_child child)
    end)%I.

Local Instance own_Node'_contractive : Contractive own_Node'.
Proof. solve_contractive. Qed.

Definition own_Node : loc → tree → iProp Σ := fixpoint own_Node'.

Lemma own_Node_unfold ptr obj :
  own_Node ptr obj ⊣⊢ (own_Node' own_Node) ptr obj.
Proof.
  apply (fixpoint_unfold own_Node').
Qed.

Definition tree_to_map (tr : tree) : gmap (list u8) (list u8) :=
  let fix traverse (tr : tree) (acc : gmap (list u8) (list u8)) (path : list u8) :=
    match tr with
    | Cut _ => acc
    | Empty => acc
    | Leaf val => <[path:=val]>acc
    | Interior children =>
      (* Grab all entries from the children, storing the ongoing path. *)
      (foldr
        (λ child (pIdxAcc:(Z * gmap (list u8) (list u8))),
          let acc' := traverse child pIdxAcc.2 (path ++ [U8 pIdxAcc.1])
          in (pIdxAcc.1 + 1, acc'))
        (0, acc) children
      ).2
    end
  in traverse tr ∅ [].

Definition own_Tree ptr_tr entry_map : iProp Σ :=
  ∃ tr root,
  "Hnode" ∷ own_Node root tr ∗
  "%Htree_map" ∷ ⌜tree_to_map tr = entry_map⌝ ∗
  "Hptr_root" ∷ ptr_tr ↦[Tree :: "Root"] #root.

Definition is_Slice3D (sl : Slice.t) (obj0 : list (list (list u8))) : iProp Σ :=
  ∃ list_sl0,
  readonly (own_slice_small sl (slice.T (slice.T byteT)) 1 list_sl0) ∗
  ([∗ list] obj1;sl_1 ∈ obj0;list_sl0,
    ∃ list_sl1,
    readonly (own_slice_small sl_1 (slice.T byteT) 1 list_sl1) ∗
    ([∗ list] obj2;sl_2 ∈ obj1;list_sl1,
      readonly (own_slice_small sl_2 byteT 1 obj2))).

End defs.

(*
Module PathProof.
Record t :=
  mk {
    Id: list u8;
    NodeHash: list u8;
    Digest: list u8;
    ChildHashes: list (list (list u8));
  }.

Section local_defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ sl_Id sl_NodeHash sl_Digest sl_ChildHashes,
  "HId" ∷ own_slice_small sl_Id byteT 1 obj.(Id) ∗
  "Hptr_Id" ∷ ptr ↦[PathProof :: "Id"] (slice_val sl_Id) ∗
  "HNodeHash" ∷ own_slice_small sl_NodeHash byteT 1 obj.(NodeHash) ∗
  "Hptr_NodeHash" ∷ ptr ↦[PathProof :: "NodeHash"] (slice_val sl_NodeHash) ∗
  "HDigest" ∷ own_slice_small sl_Digest byteT 1 obj.(Digest) ∗
  "Hptr_Digest" ∷ ptr ↦[PathProof :: "Digest"] (slice_val sl_Digest) ∗
  "#HChildHashes" ∷ is_Slice3D sl_ChildHashes obj.(ChildHashes) ∗
  "Hptr_ChildHashes" ∷ ptr ↦[PathProof :: "ChildHashes"] (slice_val sl_ChildHashes).
End local_defs.
End PathProof.

Section proofs.
Context `{!heapGS Σ}.

Lemma wp_Put ptr_tr entry_map sl_id id sl_val val :
  {{{
    "Htree" ∷ own_Tree ptr_tr entry_map ∗
    "Hid" ∷ own_slice_small sl_id byteT 1 id ∗
    "Hval" ∷ own_slice_small sl_val byteT 1 val
  }}}
  Tree__Put #ptr_tr (slice_val sl_id) (slice_val sl_val)
  {{{
    sl_digest ptr_proof (err:u64),
    RET ((slice_val sl_digest), #ptr_proof, #err);
    if bool_decide (err = 0) then
      "Htree" ∷ own_Tree ptr_tr (<[id:=val]>entry_map)
    else True%I
  }}}.
Proof. Admitted.

Lemma wp_NodeHashNull :
  {{{ True }}}
  Node__Hash #null
  {{{
    sl_hash hash, RET (slice_val sl_hash);
    "Hhash" ∷ own_slice_small sl_hash byteT 1 hash ∗
    "#His_hash" ∷ is_tree_hash Empty hash
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  rewrite /Node__Hash.
  wp_apply wp_SliceSingleton; [val_ty|];
    iIntros (sl_data) "Hdata".
  (* SliceSingleton gives untyped slice. Need typed slice. *)
  wp_apply (wp_Hash with "[Hdata]").
  {
    iDestruct (slice.own_slice_to_small with "Hdata") as "Hdata".
    rewrite /own_slice_small.
    instantiate (1:=[_]).
    iFrame.
  }
  iIntros (??) "H"; iNamed "H".
  iApply "HΦ".
  iFrame.
  iApply is_tree_hash_unfold.
  rewrite /is_tree_hash'.
  iFrame "#".
Qed.

Lemma wp_PathProofCheck ptr_proof proof node :
  {{{
    "Hproof" ∷ PathProof.own ptr_proof proof ∗
    "#Hvalid_NodeHash" ∷ is_tree_hash node proof.(PathProof.NodeHash) ∗
    "%Hproof_len_eq" ∷ ⌜length proof.(PathProof.Id) = length proof.(PathProof.ChildHashes)⌝ ∗
    "%Hproof_len_ub" ∷ ⌜length proof.(PathProof.Id) ≤ 32⌝
  }}}
  PathProof__Check #ptr_proof
  {{{
    (err:u64), RET #err;
    if bool_decide (err = 0) then
      "#Hpath" ∷ is_path_node proof.(PathProof.Id) node proof.(PathProof.Digest)
    else True%I
  }}}.
Proof.
  iIntros (Φ) "H HΦ"; iNamed "H".
  rewrite /PathProof__Check.
  iNamed "Hproof".
  wp_loadField.
  wp_apply wp_slice_len.
  iDestruct (own_slice_small_sz with "HId") as "%Hid_sz".
  wp_if_destruct.
  {
    (* Case: empty tree. *)
    wp_apply wp_ref_of_zero; [done|].
    iIntros (ptr_empty) "Hempty".
    wp_loadField.
    wp_loadField.
    wp_apply (wp_BytesEqual with "[$HNodeHash $HDigest]");
      iIntros "[HNodeHash HDigest]".
    wp_if_destruct; [|by iApply "HΦ"].
    wp_load.
    wp_apply (wp_NodeHashNull); iIntros (??) "H"; iNamed "H".
    wp_loadField.
    wp_apply (wp_BytesEqual with "[$HNodeHash $Hhash]");
      iIntros "[HNodeHash Hhash]".
    wp_if_destruct; [|by iApply "HΦ"].
    iApply "HΦ".
    iIntros "!>".
    rewrite /is_path_node.
    iExists Empty.
    subst hash.
    rewrite Heqb0.
    iSplit; [iFrame "#"|].
    rewrite Heqb in Hid_sz.
    apply length_zero_iff_nil in Hid_sz.
    rewrite Hid_sz.
    iDestruct (is_tree_hash_inj with "Hvalid_NodeHash His_hash") as %Hnode.
    rewrite Hnode.
    naive_solver.
  }

  (* By the end of this next block, we should have is_tree_hash holding
     on the bottom-most node of the tree. *)
  wp_loadField.
  admit.
Admitted.

Lemma wp_MembProofCheck sl_proof proof sl_id sl_val sl_digest (id val digest : list u8) :
  {{{
    "#Hproof" ∷ is_Slice3D sl_proof proof ∗
    "Hid" ∷ own_slice_small sl_id byteT 1 id ∗
    "Hval" ∷ own_slice_small sl_val byteT 1 val ∗
    "Hdigest" ∷ own_slice_small sl_digest byteT 1 digest
  }}}
  MembProofCheck (slice_val sl_proof) (slice_val sl_id) (slice_val sl_val) (slice_val sl_digest)
  {{{
    (err:u64), RET #err;
    if bool_decide (err = 0) then
      "#Hpath" ∷ is_path_val id (Some val) digest
    else True%I
  }}}.
Proof.
  iIntros (Φ) "H HΦ"; iNamed "H".
  rewrite /MembProofCheck.
  admit.
Admitted.

Lemma wp_NonmembCheck sl_proof proof sl_id sl_digest (id digest : list u8) :
  {{{
    "#Hproof" ∷ is_Slice3D sl_proof proof ∗
    "Hid" ∷ own_slice_small sl_id byteT 1 id ∗
    "Hdigest" ∷ own_slice_small sl_digest byteT 1 digest
  }}}
  NonmembProofCheck (slice_val sl_proof) (slice_val sl_id) (slice_val sl_digest)
  {{{
    (err:u64), RET #err;
    if bool_decide (err = 0) then
      "#Hpath" ∷ is_path_val id None digest
    else True%I
  }}}.
Proof. Admitted.

End proofs.
*)
