From iris.algebra Require Import auth gset.
From iris.heap_lang Require Import notation.

From SkipList.lib Require Import zrange.
From SkipList.atomic Require Import weakestpre proofmode lock.
From SkipList.lazy_list Require Import code inv.
From SkipList.lazy_list.spec Require Import find.


Module LASpec (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module Invariant := FindSpec Params.
  Export Invariant.

  Section proofs.
    Context `{!heapGS Σ, !lazyG Σ}.
    Local Open Scope Z.

    Theorem new_spec :
      {{{ emp }}}
        new #()
      {{{ p Γ, RET #p; set p ∅ Γ }}}.
    Proof.
      iIntros (Φ) "_ HΦ"; wp_lam. 

      wp_alloc t as "(Ht & Ht')"; wp_let.
      wp_alloc l as "Hl"; wp_let.

      set (head := (INT_MIN, t, l)).
      wp_pures; rewrite (fold_rep_to_node head).
      wp_alloc h as "Hh"; iMod (mapsto_persist with "Hh") as "#Hh".

      iMod (own_alloc (● ∅ ⋅ ◯ ∅))
        as (γauth) "[Hauth _]"; 
        first by apply auth_both_valid.
      iMod (own_alloc (GSet ∅ ⋅ ZRange INT_MIN INT_MAX))
        as (γdisj) "[Hdisj Hkeys]";
        first by (pose HMIN_MAX; rewrite ZRange_disj).
      set (Γ := mk_lazy_gname γauth γdisj).

      iModIntro; iApply ("HΦ" $! h Γ).
      iFrame; iExists head, ∅. 
      rewrite /lazy_list set_map_empty right_id_L ?big_sepS_singleton.
      iFrame "# ∗"; do 2 (iSplit; first done).
      iSplitL "Ht Hkeys"; first (iExists tail; iFrame; by iLeft).
      iExists Free. iSplitR "Ht'"; last by iExists tail. 
      iExists l. by iFrame.
    Qed.

    Theorem contains_spec (p: loc) (Γ: lazy_gname)
      (k: Z) (Hrange: INT_MIN < k < INT_MAX) :
      ⊢ <<<
        ∀∀ (s: gset Z), set p s Γ =>
        ∃∃ (b: bool), set p s Γ ∗ ⌜ if b then k ∈ s else k ∉ s ⌝;
        RET #b
      >>> @ ∅
      {{{ emp }}} contains #p #k {{{ emp }}}.
    Proof.
      iIntros "!> %Φ _ AU".
      rewrite difference_empty_L.
      wp_lam. wp_let. 
      
      wp_bind (Load _). iMod "AU" as (s) "[Hset [Hclose _]]".
      iDestruct "Hset" as (head S) "(#Hhead & %Hmin & %Hkeys & Hlazy)".
      wp_load. iDestruct ("Hclose" with "[Hlazy]") as ">AU".
      { iExists head, S; by iFrame "# ∗". }
      iModIntro; clear dependent s S.

      awp_apply (find_spec with "[]"); first lia; first by iLeft.
      iApply (aacc_aupd_sub with "[] AU"); try done.
      { iIntros "!> %s". by iApply set_has_lazy. }
      iIntros (s) "Hset"; iDestruct "Hset" as (? S) "(H & _ & -> & Hlazy)".
      iDestruct (mapsto_agree with "Hhead H") as %<-%rep_to_node_inj; iClear "H".
      iAaccIntro with "Hlazy".
      { iIntros; iModIntro; iSplitR ""; last by iIntros. iExists head, S; by iFrame "# ∗". }
      iIntros (pred succ) "[Hlazy %Hkin]".

      iModIntro. iExists S. iFrame "Hlazy". iIntros "Hlazy".
      iRight. iExists (bool_decide (k = node_key succ)).
      iSplitR "".
      + iSplit; first (iExists head, S; by iFrame "# ∗").
        case_bool_decide; rewrite -Hkin //.
      + clear dependent S. iIntros "AP".
        iMod (atomic_post_commit with "AP") as "HΦ".
        iModIntro. iIntros "_".
        iModIntro. wp_pures; wp_lam; wp_pures.
        do 2 case_bool_decide; try congruence; by iApply "HΦ".
    Qed.

    Theorem add_spec (p: loc) (Γ: lazy_gname)
      (k: Z) (Hrange: INT_MIN < k < INT_MAX) :
      ⊢ <<< ∀∀ (s: gset Z), set p s Γ => set p (s ∪ {[ k ]}) Γ; RET #() >>> @ ∅
      {{{ emp }}} add #p #k {{{ emp }}}.
    Proof.
      iIntros "!> %Φ _ AU".
      rewrite difference_empty_L.
      wp_lam. wp_let. 
      
      wp_bind (Load _). iMod "AU" as (s) "[Hset [Hclose _]]".
      iDestruct "Hset" as (head S) "(#Hhead & %Hmin & %Hkeys & Hlazy)".
      wp_load. iDestruct ("Hclose" with "[Hlazy]") as ">AU".
      { iExists head, S; by iFrame "# ∗". }
      iModIntro; clear dependent s S.

      awp_apply (findLock_spec with "[]"); first lia; first by iLeft.
      iApply (aacc_aupd_sub with "[] AU"); try done.
      { iIntros "!> %s". by iApply set_has_lazy. }
      iIntros (s) "Hset"; iDestruct "Hset" as (? S) "(H & _ & -> & Hlazy)".
      iDestruct (mapsto_agree with "Hhead H") as %<-%rep_to_node_inj; iClear "H".
      iAaccIntro with "Hlazy".
      { iIntros; iModIntro; iSplitR ""; last by iIntros. iExists head, S; by iFrame "# ∗". }
      iIntros (pred succ) "[Hlazy %Hkin]".

      iModIntro. iExists S. iFrame "Hlazy". iIntros "Hlazy".
      destruct (decide (k = node_key succ)) as [->|Hneq].
      + iRight. iSplitL "Hlazy".
        { iExists head, S; iFrame "# ∗"; iSplit; first done. iPureIntro; set_solver. }
        clear dependent S. iIntros "AP".
        iModIntro. iIntros "(#Hpred & _ & _ & Hnext' & Hacq)".
        iModIntro. wp_pures; wp_lam; wp_pures; wp_lam; wp_pures.
        case_bool_decide; last congruence; wp_if.

        iAssert (in_lock pred)%I with "[Hnext']" as "Hin"; first by iExists succ.
        awp_apply (release_spec with "Hacq").
        iApply (aacc_apst_sub with "[] AP"); try done.
        { 
          iIntros "!> %s H". iDestruct (set_node_has_lock with "Hhead Hpred H") as "[Hlock Hset]".
          iDestruct "Hlock" as (st) "[Hlock Hin]". iExists st. iFrame. iIntros "Hlock".
          iApply "Hset". iExists st. iFrame. 
        }
        iIntros (s) "Hset".
        iDestruct (set_node_has_lock with "Hhead Hpred Hset") as "[Hlock Hset]".
        iDestruct "Hlock" as (st) "[Hlock Hin']"; iAaccIntro with "Hlock".
        { 
          iIntros "H"; iDestruct ("Hset" with "[H Hin']") as "Hset";
            first (iExists st; iFrame). iModIntro; iFrame; by iIntros.
        }
        iIntros "Hlock"; iModIntro; iExists Free; iFrame "Hlock".
        iIntros "H"; iDestruct ("Hset" with "[H Hin]") as "Hset";
          first (iExists Free; iFrame); iClear "Hin'".
        iFrame "Hset". iIntros "AP". rewrite difference_empty_L.
        by iMod (atomic_post_commit with "AP").
      + iLeft. iSplitL "Hlazy"; first (iExists head, S; by iFrame "# ∗").
        clear dependent S; iIntros "AU".
        iModIntro. iIntros "(#Hpred & #Hsucc & %Hk & Hnext' & Hacq)".
        iModIntro. wp_pures; wp_lam; wp_pures; wp_lam; wp_pures.
        case_bool_decide; first congruence; wp_if.
        wp_lam; wp_pures; wp_load.

        wp_alloc n as "(Hn & Hn')"; wp_let.
        wp_alloc l as "Hl"; wp_let.
        wp_pures; set (new := (k, n, l)); rewrite (fold_rep_to_node new).

        wp_bind (Store _ _).
        iMod "AU" as (s) "[Hset [_ HAP]]".
        iDestruct "Hset" as (h' S) "(H & _ & %Hkeys & Hlazy)".
        iDestruct (mapsto_agree with "Hhead H") as %<-%rep_to_node_inj; iClear "H".
        iDestruct (singleton_frag_in with "Hpred Hlazy") as %Hpred.
        iDestruct "Hlazy" as "(Hauth & Hdisj & Hnexts & Hlocks)".

        rewrite (big_sepS_delete (has_next _) _ pred) //.
        iDestruct "Hnexts" as "[Hnext Hnexts]".
        iDestruct "Hnext" as (succ') "(Hnext & _ & Hkeys)".
        iDestruct (mapsto_agree with "Hnext Hnext'") as %->%rep_to_node_inj.
        iCombine "Hnext Hnext'" as "Hnext"; wp_store.
        iDestruct "Hnext" as "[Hnext Hnext']".

        iMod (own_update with "Hauth") as "[Hauth Hfrag]".
        { by apply auth_update_alloc, (op_local_update_discrete _ _ {[new]}). }
        rewrite right_id (comm _ {[new]} S).

        rewrite (ZRange_split k); last lia.
        iDestruct "Hkeys" as "((Hkeys & Hkey) & Hkeys')".
        iDestruct (own_valid_2 with "Hdisj Hkey") as %Hdisj%gset_disj_valid_op.
        iCombine "Hdisj Hkey" as "Hdisj"; rewrite gset_disj_union //.

        iAssert (has_next _ pred) with "[Hnext Hfrag Hkeys]" as "Hnext".
        { iExists new; iFrame. }
        iCombine "Hnext Hnexts" as "Hnexts".
        rewrite -big_sepS_delete //.

        iAssert (has_lock new) with "[Hn' Hl]" as "Hlock".
        { iExists Free. iSplitR "Hn'"; last by iExists succ. iExists l. by iFrame. }
        iAssert (has_next _ new) with "[Hn Hkeys']" as "Hnext".
        { iExists succ; iFrame "# ∗". }
        iCombine "Hlock Hlocks" as "Hlocks"; iCombine "Hnext Hnexts" as "Hnexts".
        assert (node_key new ≠ node_key head) by (rewrite Hmin /node_key/=; lia).
        assert (new ∉ {[head]} ∪ S) by set_solver.
        do 2 rewrite -big_sepS_insert // (comm_L _ _ ({[head]} ∪ S)) -assoc_L.

        iMod ("HAP" with "[Hauth Hdisj Hlocks Hnexts]") as "AP".
        { 
          iExists head, (S ∪ {[new]}).
          rewrite /lazy_list set_map_union_L set_map_singleton_L.
          iFrame "# ∗". iPureIntro. set_solver. 
        }
        clear dependent s S; iModIntro; wp_pures.

        iAssert (in_lock pred)%I with "[Hnext']" as "Hin"; first by iExists new.
        awp_apply (release_spec with "Hacq").
        iApply (aacc_apst_sub with "[] AP"); try done.
        { 
          iIntros "!> %s H". iDestruct (set_node_has_lock with "Hhead Hpred H") as "[Hlock Hset]".
          iDestruct "Hlock" as (st) "[Hlock Hin]". iExists st. iFrame. iIntros "Hlock".
          iApply "Hset". iExists st. iFrame. 
        }
        iIntros (s) "Hset".
        iDestruct (set_node_has_lock with "Hhead Hpred Hset") as "[Hlock Hset]".
        iDestruct "Hlock" as (st) "[Hlock Hin']"; iAaccIntro with "Hlock".
        { 
          iIntros "H"; iDestruct ("Hset" with "[H Hin']") as "Hset";
            first (iExists st; iFrame). iModIntro; iFrame; by iIntros.
        }
        iIntros "Hlock"; iModIntro; iExists Free; iFrame "Hlock".
        iIntros "H"; iDestruct ("Hset" with "[H Hin]") as "Hset";
          first (iExists Free; iFrame).
        iFrame "Hset". iIntros "AP". rewrite difference_empty_L.
        by iMod (atomic_post_commit with "AP").
    Qed.
  End proofs.
End LASpec.