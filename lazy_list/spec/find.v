From SkipList.atomic Require Import proofmode lock weakestpre.
From SkipList.lib Require Import zrange.
From SkipList.lazy_list Require Import code inv.

From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation.


Module FindSpec (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module Invariant := LazyListInv Params.
  Export Invariant.

  Section proofs.
    Context `{!heapGS Σ, !lazyG Σ}.
    Local Open Scope Z.

    Theorem find_spec (k: Z) (head curr: node_rep) (Γ: lazy_gname) :
      node_key curr < k < INT_MAX →
      (⌜ curr = head ⌝ ∨ own Γ.(auth_gname) (◯ {[curr]})) -∗
      <<< ∀∀ (S: gset node_rep), lazy_list head S Γ >>>
        find (rep_to_node curr) #k @ ∅
      <<< ∃∃ pred succ, 
        lazy_list head S Γ
        ∗
        ⌜ k = node_key succ ↔ k ∈ (set_map node_key S : gset Z) ⌝, 
      RET ((rep_to_node pred), (rep_to_node succ)) >>>
      {{{ 
        (⌜ pred = head ⌝ ∨ own Γ.(auth_gname) (◯ {[pred]}))
        ∗
        (⌜ succ = tail ⌝ ∨ own Γ.(auth_gname) (◯ {[succ]}))
        ∗
        ⌜ node_key pred < k ≤ node_key succ ⌝
      }}}.
    Proof.
      iIntros "%Hk Hcurr %Φ"; iRevert (curr Hk) "Hcurr".
      iLöb as "IH"; iIntros (curr Hk) "#Hcurr AU".
      rewrite difference_empty_L.
      wp_lam. wp_let. wp_lam. wp_pures.

      wp_bind (Load _). iMod "AU" as (S) "[Hlazy Hclose]".
      iDestruct (singleton_frag_in with "Hcurr Hlazy") as %Hcurr.
      iDestruct (node_has_next with "Hcurr Hlazy")
        as (succ) "(Hnext & #Hsucc & %Hdisj & Hlazy)".
      destruct (decide (k ≤ node_key succ)) as [|Hcase].
      + wp_load. iDestruct ("Hlazy" with "Hnext") as "Hlazy".
        iDestruct "Hclose" as "[_ Hclose]".
        iDestruct ("Hclose" $! curr succ with "[-]") as ">AP".
        {
          iDestruct (singleton_frag_in with "Hsucc Hlazy") as %Hsucc.
          rewrite elem_of_union elem_of_singleton in Hsucc.
          iFrame "Hlazy"; iPureIntro. split.
          + intros ->; destruct Hsucc as [->|Hsucc]; last set_solver.
            exfalso. rewrite /node_key/= in Hk. lia.
          + intros Hin. destruct (decide (node_key succ = k)); first done.
            exfalso. by apply (Hdisj k); last (rewrite zrange_spec; lia).
        }
        iMod (atomic_post_commit with "AP") as "HΦ".
        iModIntro; wp_let; wp_lam; wp_pures.
        case_bool_decide; last lia; wp_if.
        wp_pure. iApply "HΦ".
        iFrame "#". iPureIntro; lia.
      + wp_load. iDestruct ("Hlazy" with "Hnext") as "Hlazy".
        iDestruct "Hclose" as "[Hclose _]"; iDestruct ("Hclose" with "Hlazy") as ">AU".
        iModIntro; wp_let; wp_lam; wp_pures.
        case_bool_decide; first lia; wp_if.

        iDestruct "Hsucc" as "[->|Hsucc]"; first (rewrite /node_key/= in Hcase; lia).
        iApply ("IH" with "[%] [$] AU"); lia.
    Qed.

    Theorem findLock_spec (k: Z) (head curr: node_rep) (Γ: lazy_gname) :
      node_key curr < k < INT_MAX →
      (⌜ curr = head ⌝ ∨ own Γ.(auth_gname) (◯ {[curr]})) -∗
      <<< ∀∀ (S: gset node_rep), lazy_list head S Γ >>>
        findLock (rep_to_node curr) #k @ ∅
      <<< ∃∃ pred succ,
        lazy_list head S Γ
        ∗
        ⌜ k = node_key succ ↔ k ∈ (set_map node_key S : gset Z) ⌝,
      RET ((rep_to_node pred), (rep_to_node succ)) >>>
      {{{
        (⌜ pred = head ⌝ ∨ own Γ.(auth_gname) (◯ {[pred]}))
        ∗
        (⌜ succ = tail ⌝ ∨ own Γ.(auth_gname) (◯ {[succ]}))
        ∗
        ⌜ node_key pred < k ≤ node_key succ ⌝
        ∗
        node_next pred ↦{#1 / 2} rep_to_node succ
        ∗
        lock.locked #(node_lock pred)
      }}}.
    Proof.
      iIntros "%Hk Hcurr %Φ"; iRevert (curr Hk) "Hcurr".
      iLöb as "IH"; iIntros (curr Hk) "#Hcurr AU".
      rewrite difference_empty_L.
      wp_lam. wp_let.

      awp_apply (find_spec with "Hcurr"); first done.
      iApply (aacc_aupd_eq with "AU"); try done.
      iIntros (S) "Hlazy"; iAaccIntro with "Hlazy".
      { do 2 (iIntros; iModIntro; iFrame). }
      iIntros (pred succ') "[Hlazy _]".
      iModIntro. iExists S. iFrame "Hlazy". iIntros "Hlazy".
      iLeft. iFrame "Hlazy". clear dependent S. iIntros "AU".
      iModIntro. iIntros "(#Hpred & _ & [%Hk' _])".
      iModIntro. wp_pures; wp_lam; wp_pures.

      awp_apply acquire_spec.
      iApply (aacc_aupd_sub with "[] AU"); try done.
      { iIntros "!> %S H"; iDestruct (lazy_node_has_lock with "Hpred H") as "$". }
      iIntros (S) "Hlazy".
      iDestruct (lazy_node_has_lock with "Hpred Hlazy") as "[Hlock Hlazy]".
      iAaccIntro with "Hlock".
      { iIntros "H"; iDestruct ("Hlazy" with "H") as "Hlazy"; iModIntro; iFrame; by iIntros. }
      iIntros "Hlock". iModIntro. iFrame "Hlock".
      iIntros "H"; iDestruct ("Hlazy" with "H") as "Hlazy".
      iLeft. iFrame "Hlazy". clear dependent S. iIntros "AU".
      iModIntro. iIntros "[Hlocked Hin_lock]".
      iModIntro. wp_pures; wp_lam; wp_pures.

      wp_bind (Load _). iMod "AU" as (S) "[Hlazy Hclose]".
      iDestruct (singleton_frag_in with "Hpred Hlazy") as %Hpred.
      iDestruct (node_has_next with "Hpred Hlazy")
        as (succ) "(Hnext & #Hsucc & %Hdisj & Hlazy)".
      destruct (decide (k ≤ node_key succ)) as [|Hcase].
      + iDestruct "Hin_lock" as (?) "Hnext'".
        iDestruct (mapsto_agree with "Hnext Hnext'") as %<-.

        wp_load. iDestruct ("Hlazy" with "Hnext") as "Hlazy".
        iDestruct "Hclose" as "[_ Hclose]".
        iDestruct ("Hclose" $! pred succ with "[Hlazy]") as ">AP".
        {
          iDestruct (singleton_frag_in with "Hsucc Hlazy") as %Hsucc.
          rewrite elem_of_union elem_of_singleton in Hsucc.
          iFrame "Hlazy"; iPureIntro. split.
          + intros ->; destruct Hsucc as [->|Hsucc]; last set_solver.
            exfalso. rewrite /node_key/= in Hk; lia.
          + intros Hin. destruct (decide (node_key succ = k)); first done.
            exfalso. by apply (Hdisj k); last (rewrite zrange_spec; lia).
        }
        iMod (atomic_post_commit with "AP") as "HΦ".
        iModIntro. wp_let; wp_lam; wp_pures.
        case_bool_decide; last lia; wp_if.
        wp_pure. iApply "HΦ".
        iFrame "# ∗". iPureIntro; lia.
      + wp_load. iDestruct ("Hlazy" with "Hnext") as "Hlazy".
        iDestruct "Hclose" as "[Hclose _]"; iDestruct ("Hclose" with "Hlazy") as ">AU".
        iModIntro. wp_let; wp_lam; wp_pures.
        case_bool_decide; first lia; wp_if.

        clear dependent S.
        awp_apply (release_spec with "Hlocked Hin_lock").
        iApply (aacc_aupd_sub with "[] AU"); try done.
        { iIntros "!> %S H"; iDestruct (lazy_node_has_lock with "Hpred H") as "$". }
        iIntros (S) "Hlazy". 
        iDestruct (lazy_node_has_lock with "Hpred Hlazy") as "(Hlock & Hlazy)".
        iAaccIntro with "Hlock".
        { iIntros "H"; iDestruct ("Hlazy" with "H") as "Hlazy"; iModIntro; iFrame; by iIntros. }
        iIntros "Hlock". iModIntro. iFrame "Hlock".
        iIntros "Hlock"; iDestruct ("Hlazy" with "Hlock") as "Hlazy".
        iLeft. iFrame "Hlazy". clear dependent S. iIntros "AU".
        iModIntro. iIntros "_".
        iModIntro. wp_pures.

        iDestruct "Hsucc" as "[->|Hsucc]"; first (rewrite /node_key/= in Hcase; lia).
        iApply ("IH" with "[%] [$] AU"); lia.
    Qed.
  End proofs.
End FindSpec.