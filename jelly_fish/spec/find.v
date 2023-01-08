From iris.algebra Require Import gmap gset excl_auth dfrac_agree.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import zrange.
From SkipList.jelly_fish Require Import code inv.


Module FindSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Invariant := SkipListInv Params.
  Export Invariant.

  Section proofs.
    Context `{!heapGS Σ, !skipG Σ} (N: namespace).
    Local Open Scope Z.
    
    Theorem find_spec (k lvl: Z) (head curr: node_rep) (Γm: map_gname) (Γ: gmap Z inv_gname) :
      node_key curr < k < INT_MAX →
      0 ≤ lvl ≤ MAX_HEIGHT →
      (⌜ curr = head ⌝ ∨ own (Γ !!! lvl).(auth_gname) (◯ {[curr]})) -∗
      inv (skipN N) (skip_list_inv head Γm Γ) -∗
      <<< ∀∀ (s: gset Z), own Γm.(excl_gname) (◯E s) >>>
        find (rep_to_node curr) #k #lvl @ ↑(skipN N)
      <<< ∃∃ pred succ,
        own Γm.(excl_gname) (◯E s)
        ∗
        ⌜ k ≠ node_key succ → lvl = 0 → k ∉ s ⌝
        ∗
        (⌜ pred = head ⌝ ∨ own (Γ !!! lvl).(auth_gname) (◯ {[pred]}))
        ∗
        (⌜ succ = tail ⌝ ∨ own (Γ !!! lvl).(auth_gname) (◯ {[succ]}))
        ∗
        ⌜ node_key pred < k ≤ node_key succ ⌝
        ∗
        has_lock lvl pred,
      RET ((rep_to_node pred), (rep_to_node succ)) >>>.
    Proof.
      iIntros "%Hk %Hlvl Hcurr #Hinv %Φ"; iRevert (curr Hk) "Hcurr".
      iLöb as "IH"; iIntros "%curr %Hk #Hcurr AU".
      wp_lam. wp_let. wp_let. wp_lam. wp_pures.

      wp_bind (Load #(node_next curr +ₗ lvl)). iInv "Hinv" as "Hskip". 
      iDestruct (has_lvl_inv with "Hskip") as "(Hlvl & Hskip)"; first done.
      iDestruct "Hlvl" as (S) "(>Hauth & >Hdisj & >Htoks & Hlocks & Hnexts & Hmap)".

      iDestruct (singleton_frag_in with "Hauth Hcurr") as %Hcurr.
      rewrite (big_sepS_delete (has_lock _)) // (big_sepS_delete (has_next _ _)) //.
      iDestruct "Hlocks" as "(#Hlock & Hlocks)"; iDestruct "Hnexts" as "(Hnext & Hnexts)".
      iDestruct "Hnext" as (s succ) ">(Hnext & #Hs & #Hsucc & Hkeys)".

      destruct (decide (k ≤ node_key succ)) as [|Hcase].
      + iMod "AU" as (d) "[Hexcl◯ [_ Hclose]]".
        iDestruct (own_valid_2 with "Hdisj Hkeys") as %[Hdisj _]%ZRange_disj.
        iDestruct (singleton_frag_in with "Hauth Hsucc") as %Hsucc%elem_of_union.
        rewrite elem_of_singleton in Hsucc.

        wp_load.
        iAssert (has_next _ _ curr) with "[Hnext Hkeys]" as "Hnext".
        { iExists s, succ; iFrame "# ∗". }
        iCombine "Hlock Hlocks" as "Hlocks"; iCombine "Hnext Hnexts" as "Hnexts".
        do 2 rewrite -big_sepS_delete //.

        iAssert ⌜ lvl = 0 → set_map node_key S = d ⌝%I with "[Hmap Hexcl◯]" as %Heqd.
        { 
          iIntros (->); iDestruct "Hmap" as "(Hexcl● & _)".
          by iDestruct (own_valid_2 with "Hexcl● Hexcl◯") as %<-%excl_auth_agree_L.
        }
        iDestruct ("Hclose" with "[Hexcl◯]") as ">HΦ"; last iModIntro.
        {
          iFrame "# ∗"; iPureIntro; split; last lia.
          intros Hneq <-%Heqd Hfalse.
          by apply (Hdisj k); last (rewrite zrange_spec; lia).
        }

        iModIntro; iSplitR "HΦ".
        { iNext; iApply "Hskip"; iExists S; iFrame. }
        wp_load; wp_let; wp_lam; wp_pures.
        case_bool_decide; last lia; wp_if.
        by wp_pure.
      + wp_load.
        iAssert (has_next _ _ curr) with "[Hnext Hkeys]" as "Hnext".
        { iExists s, succ; iFrame "# ∗". }
        iCombine "Hlock Hlocks" as "Hlocks"; iCombine "Hnext Hnexts" as "Hnexts".
        do 2 rewrite -big_sepS_delete //.

        iModIntro; iSplitR "AU".
        { iNext; iApply "Hskip"; iExists S; iFrame. }
        wp_load; wp_let; wp_lam; wp_pures.
        case_bool_decide; first lia; wp_if.
        iDestruct "Hsucc" as "[->|Hsucc]"; first (rewrite /node_key/= in Hcase; lia).
        iApply ("IH" with "[%] [$] AU"); lia.
    Qed.

    Theorem findLock_spec (k lvl: Z) (head curr: node_rep) (Γm: map_gname) (Γ: gmap Z inv_gname) :
      node_key curr < k < INT_MAX →
      0 ≤ lvl ≤ MAX_HEIGHT →
      (⌜ curr = head ⌝ ∨ own (Γ !!! lvl).(auth_gname) (◯ {[curr]})) -∗
      inv (skipN N) (skip_list_inv head Γm Γ) -∗
      <<< ∀∀ (s: gset Z), own Γm.(excl_gname) (◯E s) >>>
        findLock (rep_to_node curr) #k #lvl @ ↑(skipN N)
      <<< ∃∃ pred succ,
        own Γm.(excl_gname) (◯E s)
        ∗
        ⌜ k ≠ node_key succ → lvl = 0 → k ∉ s ⌝
        ∗
        (⌜ pred = head ⌝ ∨ own (Γ !!! lvl).(auth_gname) (◯ {[pred]}))
        ∗
        (⌜ succ = tail ⌝ ∨ own (Γ !!! lvl).(auth_gname) (◯ {[succ]}))
        ∗
        ⌜ node_key pred < k ≤ node_key succ ⌝
        ∗
        ∃ (γl: gname) (l: val) (s: loc), 
          (node_lock pred +ₗ lvl) ↦□ l
          ∗
          is_lock γl l (in_lock lvl (node_next pred))
          ∗
          (node_next pred +ₗ lvl) ↦{#1 / 2} #s
          ∗
          s ↦□ rep_to_node succ
          ∗
          locked_val lvl s
          ∗
          locked γl,
      RET ((rep_to_node pred), (rep_to_node succ)) >>>.
    Proof.
      iIntros "%Hk %Hlvl Hcurr #Hinv %Φ"; iRevert (curr Hk) "Hcurr".
      iLöb as "IH"; iIntros (curr Hk) "#Hcurr AU".
      wp_lam. wp_let. wp_let.
      
      awp_apply (find_spec with "Hcurr Hinv"); first done; first done.
      iApply (aacc_aupd with "AU"); first done.
      iIntros (d) "Hexcl◯"; iAaccIntro with "Hexcl◯".
      { do 2 (iIntros "?"; iModIntro; iFrame). }
      iIntros (pred succ') "(Hexcl◯ & _ & #Hpred & _ & (%Hk' & _) & Hlock)".
      iDestruct "Hlock" as (γl l) "(#Hlock & #His_lock)".

      iModIntro; iLeft; iFrame. 
      iIntros "AU"; iModIntro.
      wp_pures; wp_lam; wp_pures; wp_load; wp_let.

      wp_bind (acquire _).
      iApply (acquire_spec with "His_lock").
      iNext; iIntros "(Hlocked & Hin_lock)".
      iDestruct "Hin_lock" as (s) "(Hnext' & Hval)".
      wp_pures; wp_lam; wp_pures.

      wp_bind (Load #(node_next pred +ₗ lvl)). iInv "Hinv" as "Hskip". 
      iDestruct (has_lvl_inv with "Hskip") as "(Hlvl & Hskip)"; first done.
      iDestruct "Hlvl" as (S) "(>Hauth & >Hdisj & >Htoks & Hlocks & Hnexts & Hmap)".

      iDestruct (singleton_frag_in with "Hauth Hpred") as %Hpred.
      rewrite (big_sepS_delete (has_next _ _)) //.
      iDestruct "Hnexts" as "(Hnext & Hnexts)".
      iDestruct "Hnext" as (? succ) ">(Hnext & #Hs & #Hsucc & Hkeys)".
      iDestruct (mapsto_agree with "Hnext Hnext'") as %Hs; inversion Hs; subst.

      destruct (decide (k ≤ node_key succ)) as [|Hcase].
      + clear d; iMod "AU" as (d) "[Hexcl◯ [_ Hclose]]".
        iDestruct (own_valid_2 with "Hdisj Hkeys") as %[Hdisj _]%ZRange_disj.
        iDestruct (singleton_frag_in with "Hauth Hsucc") as %Hsucc%elem_of_union.
        rewrite elem_of_singleton in Hsucc.

        wp_load.
        iAssert (has_next _ _ pred) with "[Hnext Hkeys]" as "Hnext".
        { iExists s, succ; iFrame "# ∗". }
        iCombine "Hnext Hnexts" as "Hnexts".
        rewrite -big_sepS_delete //.

        iAssert ⌜ lvl = 0 → set_map node_key S = d ⌝%I with "[Hmap Hexcl◯]" as %Heqd.
        { 
          iIntros (->); iDestruct "Hmap" as "(Hexcl● & _)".
          by iDestruct (own_valid_2 with "Hexcl● Hexcl◯") as %<-%excl_auth_agree_L.
        }
        iDestruct ("Hclose" with "[Hexcl◯ Hlocked Hnext' Hval]") as ">HΦ"; last iModIntro.
        {
          iFrame "# ∗". iSplit. 
          + iPureIntro; intros Hneq <-%Heqd Hfalse.
            by apply (Hdisj k); last (rewrite zrange_spec; lia).
          + iSplit; first (iPureIntro; lia). iExists γl, l, s; iFrame "# ∗".
        }

        iModIntro; iSplitR "HΦ".
        { iNext; iApply "Hskip"; iExists S; iFrame. }
        wp_load; wp_let; wp_lam; wp_pures.
        case_bool_decide; last lia; wp_if.
        by wp_pure.
      + wp_load.
        iAssert (has_next _ _ pred) with "[Hnext Hkeys]" as "Hnext".
        { iExists s, succ; iFrame "# ∗". }
        iCombine "Hnext Hnexts" as "Hnexts".
        rewrite -big_sepS_delete //.

        iModIntro; iSplitR "AU Hlocked Hnext' Hval".
        { iNext; iApply "Hskip"; iExists S; iFrame. }
        wp_load; wp_let; wp_lam; wp_pures.
        case_bool_decide; first lia; wp_if.
        wp_apply (release_spec with "[Hlocked Hnext' Hval]").
        { iFrame "# ∗"; iExists s; iFrame. }
        iIntros "_"; wp_pures.
        iDestruct "Hsucc" as "[->|Hsucc]"; first (rewrite /node_key/= in Hcase; lia).
        iApply ("IH" with "[%] [$] AU"); lia.
    Qed.
  End proofs.
End FindSpec.