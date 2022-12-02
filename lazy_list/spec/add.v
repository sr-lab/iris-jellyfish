From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lazy_list Require Import code.
From SkipList.lib Require Import misc node_rep node_lt.
From SkipList.lazy_list.inv Require Import list_equiv inv.


Local Open Scope Z.

Module AddSpec (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module Invariant := LazyListInv Params.
  Export Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !lazyGS Σ, !lockG Σ}.
    
    Theorem find_spec (k: Z) (head curr: node_rep) 
      (Γ: lazy_gname) :
      {{{ 
        inv lazyN (lazy_list_inv head Γ)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth Γ) (◯ {[curr]}))
        ∗
        ⌜ node_key curr < k < INT_MAX ⌝
      }}}
        find (rep_to_node curr) #k
      {{{ pred succ, RET ((rep_to_node pred), (rep_to_node succ));
        ⌜ node_key pred < k ≤ node_key succ ⌝
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth Γ) (◯ {[pred]}))
        ∗
        (own (s_auth Γ) (◯ {[succ]}) ∨ ⌜ succ = tail ⌝)
        ∗
        ∃ (γ: gname), is_lock γ (node_lock pred) (in_lock (node_next pred))
      }}}.
    Proof.
      iIntros (Φ) "(#Hinv & Hown_curr & Hrange) HΦ".
      iRevert (curr) "Hown_curr Hrange HΦ".
      iLöb as "IH".
      iIntros (curr) "#Hown_curr %Hrange HΦ".
      wp_lam. wp_let. wp_lam. wp_pures.

      wp_bind (Load _).
      iInv lazyN as (S L) "(>%Hperm & >%Hsort & >Hown_auth & >Hown_frac & Hlist)" "Hclose".

      iMod (own_update with "Hown_auth") as "[Hown_auth Hown_frag]".
      { by apply auth_update_alloc, (gset_local_update S _ S). }

      iAssert ((⌜ curr = head ∨ In curr L ⌝)%I) with "[Hown_auth Hown_curr]" as %Hcurr_range.
      {
        iDestruct "Hown_curr" as "[Heq|Hown]"; first by iLeft.
        iDestruct (own_valid_2 with "Hown_auth Hown") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.
        iPureIntro; right.
        rewrite -elem_of_list_In Hperm elem_of_elements.
        set_solver.
      }

      rewrite list_equiv_invert; last done.
      iDestruct "Hlist" as (succ γ) "(>%Hsucc_range & Hpt & #Hlock & Himp)".
      rewrite -elem_of_list_In Hperm elem_of_elements in Hsucc_range.

      wp_load.
      iPoseProof ("Himp" with "Hpt") as "Hlist".
      iMod ("Hclose" with "[Hlist Hown_auth Hown_frac]") as "_".
      { iNext; iExists S, L; by iFrame. }

      iModIntro. wp_let. wp_lam. wp_pures.
      case_bool_decide as Hcase; wp_if.
      - wp_pures. iApply "HΦ".
        iModIntro; iFrame "#".

        iSplit; first by (iPureIntro; lia).
        iSplit.
        { 
          destruct Hsucc_range as [Hin|Heq]; last by iRight.
          assert (S ≡ S ⋅ {[ succ ]}) as -> by set_solver.
          iDestruct "Hown_frag" as "(? & ?)"; iLeft; iFrame.
        }

        iExists γ. by iFrame "#".
      - iApply ("IH" $! succ with "[Hown_frag] [%]").
        {
          iRight.
          assert (S ≡ S ⋅ {[ succ ]}) as ->.
          {
            destruct Hsucc_range as [Hin|Heq]; first set_solver.
            subst; exfalso; rewrite /node_key/tail//= in Hcase; lia.
          }
          iDestruct "Hown_frag" as "(? & ?)"; iFrame.
        }
        { lia. }

        iNext; iApply "HΦ".
    Qed.

    Theorem findLock_spec (k: Z) (head curr: node_rep)
      (Γ: lazy_gname) :
      {{{ 
        inv lazyN (lazy_list_inv head Γ)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth Γ) (◯ {[curr]}))
        ∗
        ⌜ node_key curr < k < INT_MAX ⌝
      }}}
        findLock (rep_to_node curr) #k
      {{{ pred succ, RET ((rep_to_node pred), (rep_to_node succ));
        ⌜ node_key pred < k ≤ node_key succ ⌝
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth Γ) (◯ {[pred]}))
        ∗
        (own (s_auth Γ) (◯ {[succ]}) ∨ ⌜ succ = tail ⌝)
        ∗
        ∃ (γ: gname), is_lock γ (node_lock pred) (in_lock (node_next pred))
                      ∗
                      node_next pred ↦{#1 / 2} rep_to_node succ
                      ∗
                      locked γ
      }}}.
    Proof.
      iIntros (Φ) "(#Hinv & Hown_curr & Hrange) HΦ".
      iRevert (curr) "Hown_curr Hrange".
      iLöb as "IH". 
      iIntros (curr) "#Hown_curr %Hrange".
      
      wp_lam. wp_let.
      wp_apply (find_spec with "[Hown_curr]").
      { by iFrame "#". }
      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & Hlock)".
      iDestruct "Hlock" as (γ) "#Hlock".
      wp_pures. wp_lam. wp_pures.

      wp_bind (acquire _).
      iApply (acquire_spec with "Hlock").
      iNext; iIntros "(Hlocked & Hnode)".
      iDestruct "Hnode" as (rep) "Hnode".
      wp_pures. wp_lam. wp_pures.

      wp_bind (Load _).
      iInv lazyN as (S L) "(>%Hperm & >%Hsort & >Hown_auth & >Hown_frac & Hlist)" "Hclose".

      iMod (own_update with "Hown_auth") as "[Hown_auth Hown_frag]".
      { by apply auth_update_alloc, (gset_local_update S _ S). }

      iAssert ⌜ pred = head ∨ In pred L ⌝%I
        with "[Hown_auth Hown_pred]" as %Hpred_range.
      {
        iDestruct "Hown_pred" as "[Heq|Hown]"; first by iLeft.
        iDestruct (own_valid_2 with "Hown_auth Hown") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.
        iPureIntro; right.
        rewrite -elem_of_list_In Hperm elem_of_elements. 
        set_solver.
      }

      rewrite list_equiv_invert; last done.
      iDestruct "Hlist" as (succ' γ') "(>%Hsucc_range & >Hpt & _ & Himp)".
      rewrite -elem_of_list_In Hperm elem_of_elements in Hsucc_range.
      iDestruct (mapsto_agree with "Hnode Hpt") as %Hs%rep_to_node_inj; subst.

      iAssert (own (s_auth Γ) (◯ {[succ']}) ∨ ⌜ succ' = tail ⌝)%I
        with "[Hown_frag]" as "#Hown_succ'".
      {
        destruct Hsucc_range as [Hin|Heq]; last by iRight.
        assert (S = S ⋅ {[ succ' ]}) as -> by set_solver.
        iDestruct "Hown_frag" as "(? & ?)"; iLeft; iFrame.
      }

      wp_load.
      iPoseProof ("Himp" with "Hpt") as "Hlist".
      iMod ("Hclose" with "[Hlist Hown_auth Hown_frac]") as "_".
      { iNext; iExists S, L; by iFrame. }

      iModIntro. wp_let. wp_lam. wp_pures.
      case_bool_decide as Hle; wp_if.
      + wp_pures; iModIntro.
        iApply "HΦ"; iFrame "# ∗".
        iSplit; first by (iPureIntro; lia). 
        iExists γ. iFrame "# ∗".
      + wp_apply (release_spec with "[Hnode Hlocked]").
        { iFrame "# ∗"; iExists succ'; iFrame. }
        iIntros. wp_pures.

        iApply ("IH" with "HΦ [] [%]").
        {
          iRight.
          iDestruct "Hown_succ'" as "[Hown|%Htail]"; first done.
          rewrite Htail /node_key/tail/= in Hle; lia.
        }
        { lia. }
    Qed.

    Theorem add_spec (p: loc) (k: Z) 
      (S: gset Z) (q: frac)  (Γ: lazy_gname)
      (Hrange: INT_MIN < k < INT_MAX) :
      {{{ is_lazy_list p S q Γ }}}
        add #p #k
      {{{ RET #(); is_lazy_list p (S ∪ {[ k ]}) q Γ }}}.
    Proof.
      iIntros (Φ) "H HΦ".
      iDestruct "H" as (head) "(#Hpt_head & %Hmin & Hown_frag & #Hinv)".
      wp_lam. wp_let. wp_load.

      wp_apply findLock_spec.
      { iFrame "#". iSplit; first by iLeft. iPureIntro; lia. }
      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & Hlock)".
      iDestruct "Hlock" as (γ) "(#Hlock & Hpt & Hlocked)".

      wp_pures. wp_lam. wp_pures.
      case_bool_decide as Hcase; wp_if.
      + assert (k = node_key succ) as Heq by congruence.
        iDestruct "Hown_succ" as "[Hown_succ|%Hsucc]"; last first.
        { subst; exfalso. rewrite /node_key/tail/= in Hrange; lia. }

        wp_lam. wp_bind (Fst _).
        iInv lazyN as (S' L) "(>%Hperm & >%Hsort & >Hown_auth & >Hown_frac & Hlist)" "Hclose".
        
        iDestruct (own_valid_2 with "Hown_auth Hown_succ") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.
        iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
          as %Hsub%frac_auth_included_total%gset_included.
        iMod (own_update_2 with "Hown_frac Hown_frag") as "[Hown_frac Hown_frag]".
        { apply frac_auth_update, (gset_local_update_union _ _ {[ k ]}). }
        assert (set_map node_key S' ∪ {[ k ]} = set_map node_key S') as -> by set_solver.

        wp_proj.
        iMod ("Hclose" with "[Hlist Hown_auth Hown_frac]") as "_".
        { iNext; iExists S', L; by iFrame. }
        iModIntro; wp_proj.

        wp_apply (release_spec with "[Hlock Hpt Hlocked]").
        { iFrame "# ∗"; iExists succ; iFrame. }
        iIntros "_"; iApply "HΦ".
        iExists head. by iFrame "# ∗".
      + assert (k ≠ node_key succ) as Hneq by congruence.
        wp_lam. wp_pures.
        wp_load.

        wp_alloc l as "Hpt'". wp_let.
        iDestruct "Hpt'" as "(Hpt' & Hpt'_dup)".
        wp_apply (newlock_spec (in_lock l) with "[Hpt'_dup]").
        { iExists succ; iFrame. }
        iIntros (lk γ') "#Hlock'".

        wp_pures.
        set (new := (k, dummy_null, l, @None loc, lk, dummy_null)).
        rewrite (fold_rep_to_node new).
        
        wp_bind (Store _ _).
        iInv lazyN as (S' L) "(>%Hperm & >%Hsort & >Hown_auth & >Hown_frac & Hlist)" "Hclose".

        iAssert ⌜ pred = head ∨ In pred L ⌝%I
          with "[Hown_auth Hown_pred]" as %Hpred_range.
        {
          iDestruct "Hown_pred" as "[Heq|Hown]"; first by iLeft.
          iDestruct (own_valid_2 with "Hown_auth Hown") 
            as %[Hvalid%gset_included]%auth_both_valid_discrete.
          iPureIntro; right. 
          rewrite -elem_of_list_In Hperm elem_of_elements.
          set_solver.
        }

        rewrite (list_equiv_insert _ _ new succ); first last.
        { done. }
        { done. }
        { assert (node_key new = k) as -> by auto; lia. }
        { rewrite /node_key/=; lia. }

        iDestruct ("Hlist" with "[Hpt Hpt' Hlock]") as "Hlist".
        { iNext; by iFrame "# ∗". }
        iDestruct "Hlist" as (L' L1 L2) "(Hpt & >%Hsplit & >%Hsort' & >%Hperm' & Himp)".
          
        iMod (own_update with "Hown_auth") as "[Hown_auth Hown_auth_frag]".
        { apply auth_update_alloc, (gset_local_update_union _ _ {[ new ]}). }
        assert (ε ∪ {[ new ]} = {[ new ]}) as -> by set_solver.
  
        iMod (own_update_2 with "Hown_frac Hown_frag") as "[Hown_frac Hown_frac_frag]".
        { apply frac_auth_update, (gset_local_update_union _ _ {[ k ]}). }

        assert ({[node_key new]} ## (set_map node_key S' : gset Z)) as Hdisj.
        { 
          rewrite disjoint_singleton_l elem_of_map. 
          intros [x [Hkey Hin]].
          rewrite -elem_of_elements -Hperm elem_of_list_In in Hin.
          
          apply (sorted_node_lt_nin L1 L2 pred succ x).
          { rewrite -Hsplit //. }
          { assert (node_key x = k) as -> by auto; lia. }
          rewrite -Hsplit. apply in_or_app; right. apply in_or_app; by left.
        }
  
        wp_store.
        iDestruct "Hpt" as "(Hpt & Hpt_dup)".
        iPoseProof ("Himp" with "Hpt_dup") as "Hlist".
        iMod ("Hclose" with "[Hlist Hown_auth Hown_frac]") as "_".
        {
          iNext; iExists (S' ∪ {[ new ]}), L'. 
          rewrite set_map_union_L set_map_singleton_L comm_L.
          iFrame. iPureIntro. 
          
          split; last done.
          apply NoDup_Permutation.
          { 
            apply node_rep_sorted_app in Hsort'; destruct Hsort' as [_ Hsort']. 
            apply node_rep_sorted_app in Hsort'; destruct Hsort' as [Hsort' _].
            by apply sorted_node_lt_no_dup.
          } 
          { apply NoDup_elements. }
  
          simpl in Hperm'; apply Permutation_cons_inv in Hperm'.
          intros x; split.
          + rewrite elem_of_elements Hperm' elem_of_list_In.
            intros Hin. destruct Hin as [Heq|Hin].
            - set_solver.
            - apply elem_of_union_r. 
              by rewrite -elem_of_elements -Hperm elem_of_list_In.
          + rewrite elem_of_elements Hperm'. 
            intros Hin. apply elem_of_union in Hin as [Hin|Heq].
            - set_solver.
            - rewrite elem_of_list_In. right.
              by rewrite -elem_of_list_In Hperm elem_of_elements.
        }
  
        iModIntro. wp_pures. wp_lam. wp_pures.
        wp_apply (release_spec with "[Hlock Hpt Hlocked]").
        { iFrame "# ∗"; iExists new; iFrame. }
        iIntros "_"; iApply "HΦ".
        iExists head; by iFrame "# ∗".
    Qed.

  End Proofs.
End AddSpec.