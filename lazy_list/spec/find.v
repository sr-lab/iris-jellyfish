From AtomicInvariant.lib Require Import zrange.
From iris.heap_lang Require Import proofmode notation.
From AtomicInvariant.atomic Require Import triple lock.
From AtomicInvariant.lazy_list Require Import code inv.


Module FindSpec (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module Invariant := LazyListInv Params.
  Export Invariant.

  Section proofs.
    Context `{!heapGS Σ, !lazyG Σ}.
    Local Open Scope Z.

    Theorem find_spec (k: Z) (head curr: node_rep) (Γ: lazy_gname) :
      node_key curr < k < INT_MAX →
      ⊢ ⌜ curr = head ⌝ ∨ own Γ.(auth_gname) (◯ {[curr]}) -∗
      <<{ ∀∀ (S: gset node_rep), lazy_list head S Γ }>>
        find (rep_to_node curr) #k @ ∅
      <<{
        ∃∃ pred succ, lazy_list head S Γ ∗ 
          ⌜ k = node_key succ ↔ k ∈ (set_map node_key S : gset Z) ⌝ |
        RET ((rep_to_node pred), (rep_to_node succ));
        (⌜ pred = head ⌝ ∨ own Γ.(auth_gname) (◯ {[pred]}))
        ∗
        (⌜ succ = tail ⌝ ∨ own Γ.(auth_gname) (◯ {[succ]}))
        ∗
        ⌜ node_key pred < k ≤ node_key succ ⌝
      }>>.
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
        iMod ("Hclose" $! curr succ with "[-]") as "AR".
        {
          iDestruct (singleton_frag_in with "Hsucc Hlazy") as %Hsucc.
          rewrite elem_of_union elem_of_singleton in Hsucc.
          iFrame "Hlazy"; iPureIntro. split.
          + intros ->; destruct Hsucc as [->|Hsucc]; last set_solver.
            exfalso. rewrite /node_key/= in Hk. lia.
          + intros Hin. destruct (decide (node_key succ = k)); first done.
            exfalso. by apply (Hdisj k); last (rewrite zrange_spec; lia).
        }
        iMod (ares_commit with "AR") as "HΦ".
        iModIntro; wp_let; wp_lam; wp_pures.
        case_bool_decide; last lia; wp_if.
        wp_pure. iApply "HΦ".
        iFrame "#". iPureIntro; lia.
      + wp_load. iDestruct ("Hlazy" with "Hnext") as "Hlazy".
        iDestruct "Hclose" as "[Hclose _]"; iMod ("Hclose" with "Hlazy") as "AU".
        iModIntro; wp_let; wp_lam; wp_pures.
        case_bool_decide; first lia; wp_if.

        iDestruct "Hsucc" as "[->|Hsucc]"; first (rewrite /node_key/= in Hcase; lia).
        iApply ("IH" with "[%] [$] AU"); lia.
    Qed.

    Theorem findLock_spec (k: Z) (head curr: node_rep) (Γ: lazy_gname) :
      node_key curr < k < INT_MAX →
      ⊢ ⌜ curr = head ⌝ ∨ own Γ.(auth_gname) (◯ {[curr]}) -∗ 
      <<{ ∀∀ (S: gset node_rep), lazy_list head S Γ }>>
        findLock (rep_to_node curr) #k @ ∅
      <<{
        ∃∃ pred succ, lazy_list head S Γ ∗ 
          ⌜ k = node_key succ ↔ k ∈ (set_map node_key S : gset Z) ⌝ |
        RET ((rep_to_node pred), (rep_to_node succ));
        (⌜ pred = head ⌝ ∨ own Γ.(auth_gname) (◯ {[pred]}))
        ∗
        (⌜ succ = tail ⌝ ∨ own Γ.(auth_gname) (◯ {[succ]}))
        ∗
        ⌜ node_key pred < k ≤ node_key succ ⌝
        ∗
        node_next pred ↦{#1 / 2} rep_to_node succ
        ∗
        acquired #(node_lock pred)
      }>>.
    Proof.
      iIntros "%Hk Hcurr %Φ"; iRevert (curr Hk) "Hcurr".
      iLöb as "IH"; iIntros (curr Hk) "#Hcurr AI".
      rewrite difference_empty_L.
      wp_lam. wp_let.

      wp_apply (find_spec with "Hcurr"); first done.
      iApply (ainv_ainv with "AI"); try done.
      iIntros "!>" (S) "Hlazy !>". iExists S. iFrame.
      iSplit; first by iIntros. iIntros (pred succ') "[Hlazy _]".
      iLeft. iFrame. clear dependent S.
      iIntros "!> AI !> (#Hpred & _ & [%Hk' _])".
      wp_pures; wp_lam; wp_pures. clear dependent succ'.

      wp_apply acquire_spec.
      iApply (ainv_ainv with "AI"); try done.
      iIntros "!>" (S) "Hlazy !>".
      iDestruct (lazy_node_has_lock with "Hpred Hlazy") as "[Hlock Hlazy]".
      iDestruct "Hlock" as (st) "[Hlock Hin]". iExists st. iFrame.
      iSplit. { iIntros "Hlock". iApply "Hlazy". iExists st. iFrame. }
      iIntros "[Hlock ->] !>". iDestruct "Hin" as (succ) "Hnext".
      iLeft. iSplitR "Hnext". { iApply "Hlazy". iExists Locked. iFrame. } clear dependent S.
      iIntros "AI !> Hacq". wp_pures; wp_lam; wp_pures.

      wp_bind (Load _). iMod "AI" as (S) "[Hlazy Hclose]".
      iDestruct (singleton_frag_in with "Hpred Hlazy") as %Hpred.
      iDestruct (node_has_next with "Hpred Hlazy")
        as (succ') "(Hnext' & #Hsucc & %Hdisj & Hlazy)".
      iDestruct (pointsto_agree with "Hnext' Hnext") as %->%rep_to_node_inj.
      destruct (decide (k ≤ node_key succ)) as [|Hcase].
      + wp_load. iDestruct ("Hlazy" with "Hnext'") as "Hlazy".
        iDestruct "Hclose" as "[_ Hclose]".
        iMod ("Hclose" $! pred succ with "[Hlazy]") as "AR".
        {
          iDestruct (singleton_frag_in with "Hsucc Hlazy") as %Hsucc.
          rewrite elem_of_union elem_of_singleton in Hsucc.
          iFrame "Hlazy"; iPureIntro. split.
          + intros ->; destruct Hsucc as [->|Hsucc]; last set_solver.
            exfalso. rewrite /node_key/= in Hk; lia.
          + intros Hin. destruct (decide (node_key succ = k)); first done.
            exfalso. by apply (Hdisj k); last (rewrite zrange_spec; lia).
        }

        iMod (ares_commit with "AR") as "HΦ".
        iModIntro. wp_let; wp_lam; wp_pures.
        case_bool_decide; last lia; wp_if.
        wp_pure. iApply "HΦ". iModIntro.
        iFrame "# ∗". iPureIntro; lia.
      + wp_load. iDestruct ("Hlazy" with "Hnext") as "Hlazy".
        iDestruct "Hclose" as "[Hclose _]".
        iMod ("Hclose" with "Hlazy") as "AI". clear dependent S.
        iModIntro. wp_let; wp_lam; wp_pures.
        case_bool_decide; first lia; wp_if.

        wp_apply (release_spec with "Hacq").
        iApply (ainv_ainv_frame with "AI Hnext'"); try done.
        iIntros "!> %S Hlazy !>".
        iDestruct (lazy_node_has_lock with "Hpred Hlazy") as "[Hlock Hlazy]".
        iDestruct "Hlock" as (st) "[Hlock Hin]". iExists st. iFrame.
        iSplit. { iIntros "Hlock". iApply "Hlazy". iExists st. iFrame. }
        iIntros "Hlock !> ?".
        iLeft. iSplitR "". { iApply "Hlazy". iExists Free. iFrame. } clear dependent S.
        iIntros "AI !>". wp_pures.

        iDestruct "Hsucc" as "[->|Hsucc]"; first (rewrite /node_key/= in Hcase; lia).
        iApply ("IH" with "[%] [$] AI"); lia.
    Qed.
  End proofs.
End FindSpec.