From iris.algebra Require Import gset excl_auth.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import zrange.
From SkipList.lazy_list Require Import code inv.


Module FindSpec (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module Invariant := LazyListInv Params.
  Export Invariant.

  Section proofs.
    Context `{!heapGS Σ, !lazyG Σ} (N: namespace).
    Local Open Scope Z.
    
    Theorem find_spec (k: Z) (head curr: node_rep) (Γi: inv_gname) (Γs: set_gname) :
      node_key curr < k < INT_MAX →
      (⌜ curr = head ⌝ ∨ own Γi.(auth_gname) (◯ {[curr]})) -∗
      inv (lazyN N) (lazy_list_inv head Γi Γs) -∗
      <<< ∀∀ (s: gset Z), own Γs.(excl_gname) (◯E s) >>>
        find (rep_to_node curr) #k @ ↑(lazyN N)
      <<< ∃∃ pred succ,
        own Γs.(excl_gname) (◯E s)
        ∗
        ⌜ k = node_key succ ↔ k ∈ s ⌝
        ∗
        (⌜ pred = head ⌝ ∨ own Γi.(auth_gname) (◯ {[pred]}))
        ∗
        (⌜ succ = tail ⌝ ∨ own Γi.(auth_gname) (◯ {[succ]}))
        ∗
        ⌜ node_key pred < k ≤ node_key succ ⌝
        ∗
        ∃ (γl: gname), is_lock γl (node_lock pred) (in_lock (node_next pred)),
      RET ((rep_to_node pred), (rep_to_node succ)) >>>.
    Proof.
      iIntros "%Hk Hcurr #Hinv %Φ"; iRevert (curr Hk) "Hcurr".
      iLöb as "IH"; iIntros "%curr %Hk #Hcurr AU".
      wp_lam. wp_let. wp_lam. wp_pures.

      wp_bind (Load _).
      iInv "Hinv" as (S) "(>Hauth & >Hdisj & Hlocks & Hnexts & >Hexcl●)".

      iDestruct (singleton_frag_in with "Hauth Hcurr") as %Hcurr.
      rewrite (big_sepS_delete has_lock _ curr) // (big_sepS_delete (has_next _) _ curr) //.
      iDestruct "Hlocks" as "(Hlock & Hlocks)"; iDestruct "Hnexts" as "(Hnext & Hnexts)".
      iDestruct "Hlock" as (γl) "#His_lock"; iDestruct "Hnext" as (succ) ">(Hnext & #Hsucc & Hkeys)".

      destruct (decide (k ≤ node_key succ)) as [|Hcase].
      + iMod "AU" as (?) "[Hexcl◯ [_ Hclose]]".
        iDestruct (own_valid_2 with "Hexcl● Hexcl◯") as %<-%excl_auth_agree_L.
        iDestruct (own_valid_2 with "Hdisj Hkeys") as %[Hdisj _]%ZRange_disj.
        iDestruct (singleton_frag_in with "Hauth Hsucc") as %Hsucc%elem_of_union.
        rewrite elem_of_singleton in Hsucc.

        wp_load.
        iAssert (has_lock curr) as "Hlock".
        { iExists γl; iFrame "#". }
        iAssert (has_next _ curr) with "[Hnext Hkeys]" as "Hnext".
        { iExists succ; by iFrame. }
        iCombine "Hlock Hlocks" as "Hlocks"; iCombine "Hnext Hnexts" as "Hnexts".
        do 2 rewrite -big_sepS_delete //.

        iDestruct ("Hclose" with "[Hexcl◯]") as ">HΦ"; last iModIntro.
        {
          iFrame "# ∗"; iPureIntro.
          split; last lia; split.
          + intros ->; destruct Hsucc as [->|Hsucc]; last set_solver.
            exfalso. rewrite /node_key/= in Hk; lia.
          + intros Hin. destruct (decide (node_key succ = k)); first done.
            exfalso. by apply (Hdisj k); last (rewrite zrange_spec; lia).
        }

        iModIntro; iSplitL "Hauth Hdisj Hlocks Hnexts Hexcl●".
        { iNext; iExists S; by iFrame. }
        wp_let; wp_lam; wp_pures.

        case_bool_decide; last lia; wp_if.
        by wp_pure.
      + wp_load.
        iAssert (has_lock curr) as "Hlock".
        { iExists γl; iFrame "#". }
        iAssert (has_next _ curr) with "[Hnext Hkeys]" as "Hnext".
        { iExists succ; by iFrame. }
        iCombine "Hlock Hlocks" as "Hlocks"; iCombine "Hnext Hnexts" as "Hnexts".
        do 2 rewrite -big_sepS_delete //.

        iModIntro; iSplitL "Hauth Hdisj Hlocks Hnexts Hexcl●".
        { iNext; iExists S; by iFrame. }
        wp_let; wp_lam; wp_pures.

        case_bool_decide; first lia; wp_if.
        iDestruct "Hsucc" as "[->|Hsucc]"; first (rewrite /node_key/= in Hcase; lia).
        iApply ("IH" with "[%] [$] AU"); lia.
    Qed.

    Theorem findLock_spec (k: Z) (head curr: node_rep) (Γi: inv_gname) (Γs: set_gname) :
      node_key curr < k < INT_MAX →
      (⌜ curr = head ⌝ ∨ own Γi.(auth_gname) (◯ {[curr]})) -∗
      inv (lazyN N) (lazy_list_inv head Γi Γs) -∗
      <<< ∀∀ (s: gset Z), own Γs.(excl_gname) (◯E s) >>>
        findLock (rep_to_node curr) #k @ ↑(lazyN N)
      <<< ∃∃ pred succ,
        own Γs.(excl_gname) (◯E s)
        ∗
        ⌜ k = node_key succ ↔ k ∈ s ⌝
        ∗
        (⌜ pred = head ⌝ ∨ own Γi.(auth_gname) (◯ {[pred]}))
        ∗
        (⌜ succ = tail ⌝ ∨ own Γi.(auth_gname) (◯ {[succ]}))
        ∗
        ⌜ node_key pred < k ≤ node_key succ ⌝
        ∗
        ∃ (γl: gname), is_lock γl (node_lock pred) (in_lock (node_next pred))
                      ∗
                      node_next pred ↦{#1 / 2} rep_to_node succ
                      ∗
                      locked γl,
      RET ((rep_to_node pred), (rep_to_node succ)) >>>.
    Proof.
      iIntros "%Hk Hcurr #Hinv %Φ"; iRevert (curr Hk) "Hcurr".
      iLöb as "IH"; iIntros (curr Hk) "#Hcurr AU".
      wp_lam. wp_let.
      
      awp_apply (find_spec with "Hcurr Hinv"); first done.
      iApply (aacc_aupd with "AU"); first done.
      iIntros (s) "Hexcl◯"; iAaccIntro with "Hexcl◯".
      { do 2 (iIntros "?"; iModIntro; iFrame). }
      iIntros (pred succ') "(Hexcl◯ & _ & #Hpred & _ & (%Hk' & _) & His_lock)".
      iDestruct "His_lock" as (γl) "#His_lock".

      iModIntro; iLeft; iFrame. 
      iIntros "AU"; iModIntro.
      wp_pures; wp_lam; wp_pures.

      wp_bind (acquire _).
      iApply (acquire_spec with "His_lock").
      iNext; iIntros "(Hlocked & Hin_lock)".
      iDestruct "Hin_lock" as (succ) "Hnext'".
      wp_pures; wp_lam; wp_pures.

      wp_bind (Load _). 
      iInv "Hinv" as (S) "(>Hauth & >Hdisj & Hlocks & Hnexts & >Hexcl●)".

      iDestruct (singleton_frag_in with "Hauth Hpred") as %Hpred.
      rewrite (big_sepS_delete (has_next _) _ pred) //.
      iDestruct "Hnexts" as "(Hnext & Hnexts)".
      iDestruct "Hnext" as (?) ">(Hnext & #Hsucc & Hkeys)".
      iDestruct (mapsto_agree with "Hnext Hnext'") as %->%rep_to_node_inj.

      destruct (decide (k ≤ node_key succ)) as [|Hcase].
      + iMod "AU" as (?) "[Hexcl◯ [_ Hclose]]".
        iDestruct (own_valid_2 with "Hexcl● Hexcl◯") as %<-%excl_auth_agree_L.
        iDestruct (own_valid_2 with "Hdisj Hkeys") as %[Hdisj _]%ZRange_disj.
        iDestruct (singleton_frag_in with "Hauth Hsucc") as %Hsucc%elem_of_union.
        rewrite elem_of_singleton in Hsucc.

        wp_load.
        iAssert (has_next _ pred) with "[Hnext Hkeys]" as "Hnext".
        { iExists succ; by iFrame. }
        iCombine "Hnext Hnexts" as "Hnexts".
        rewrite -big_sepS_delete //.

        iDestruct ("Hclose" with "[Hexcl◯ Hlocked Hnext']") as ">HΦ"; last iModIntro.
        {
          iFrame "# ∗". iSplit; first last.
          { iSplit; first (iPureIntro; lia). iExists γl; iFrame "# ∗". }
          iPureIntro; split.
          + intros ->; destruct Hsucc as [->|Hsucc]; last set_solver.
            exfalso. rewrite /node_key/= in Hk; lia.
          + intros Hin; destruct (decide (node_key succ = k)); first done.
            exfalso. rewrite zrange_disj in Hdisj; apply (Hdisj k); first lia; done.
        }

        iModIntro; iSplitL "Hauth Hdisj Hlocks Hnexts Hexcl●".
        { iNext; iExists S; by iFrame. }
        wp_let; wp_lam; wp_pures.

        case_bool_decide; last lia; wp_if.
        by wp_pure.
      + wp_load.
        iAssert (has_next _ pred) with "[Hnext Hkeys]" as "Hnext".
        { iExists succ; by iFrame. }
        iCombine "Hnext Hnexts" as "Hnexts".
        rewrite -big_sepS_delete //.

        iModIntro; iSplitL "Hauth Hdisj Hlocks Hnexts Hexcl●".
        { iNext; iExists S; by iFrame. }
        wp_let; wp_lam; wp_pures.

        case_bool_decide; first lia; wp_if.
        wp_apply (release_spec with "[Hlocked Hnext']").
        { iFrame "# ∗"; iExists succ; iFrame. }
        iIntros "_"; wp_pures.
        iDestruct "Hsucc" as "[->|Hsucc]"; first (rewrite /node_key/= in Hcase; lia).
        iApply ("IH" with "[%] [$] AU"); lia.
    Qed.
  End proofs.
End FindSpec.