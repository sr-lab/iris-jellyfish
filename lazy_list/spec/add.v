From Coq Require Import Sorting.Sorted.

From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc node_rep node_lt key_equiv.
From SkipList.lazy_list Require Import code.
From SkipList.lazy_list.inv Require Import list_equiv inv.


Local Open Scope Z.

Module AddSpec (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module Invariant := LazyListInv Params.
  Export Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ}.
    
    Theorem find_spec (key: Z) (head curr: node_rep) (Γ: lazy_gname) :
      {{{ 
        inv lazyN (lazy_list_inv head Γ)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth Γ) (◯ {[curr]}))
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
        find (rep_to_node curr) #key
      {{{ pred succ, RET ((rep_to_node pred), (rep_to_node succ));
        ⌜ node_key pred < key ≤ node_key succ ⌝
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth Γ) (◯ {[pred]}))
        ∗
        (own (s_auth Γ) (◯ {[succ]}) ∨ ⌜ succ = tail ⌝)
        ∗
        ∃ (γ: gname), is_lock γ (node_lock pred) (node_inv (node_next pred))
      }}}.
    Proof.
      iIntros (Φ) "(#Hinv & Hown_curr & Hrange) HΦ".
      iRevert (curr) "Hown_curr Hrange HΦ".
      iLöb as "IH".
      iIntros (curr) "#Hown_curr %Hrange HΦ".
      wp_lam. wp_let. wp_lam. wp_pures.

      wp_bind (Load _).
      iInv lazyN as (S Skeys L) "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_frac & >Hown_keys & Hlist)" "Hclose".

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

      rewrite (list_equiv_invert); last done.
      iDestruct "Hlist" as (succ γ) "(>%Hsucc_range & Hpt & #Hlock & Himp)".
      rewrite -elem_of_list_In Hperm elem_of_elements in Hsucc_range.

      wp_load.
      iPoseProof ("Himp" with "Hpt") as "Hlist".
      iMod ("Hclose" with "[Hlist Hown_auth Hown_frac Hown_keys]") as "_".
      { iNext; iExists S, Skeys, L; by iFrame. }

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

    Theorem findLock_spec (key: Z) (head curr: node_rep) (Γ: lazy_gname) :
      {{{ 
        inv lazyN (lazy_list_inv head Γ)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth Γ) (◯ {[curr]}))
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
        findLock (rep_to_node curr) #key
      {{{ pred succ, RET ((rep_to_node pred), (rep_to_node succ));
        ⌜ node_key pred < key ≤ node_key succ ⌝
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth Γ) (◯ {[pred]}))
        ∗
        (own (s_auth Γ) (◯ {[succ]}) ∨ ⌜ succ = tail ⌝)
        ∗
        ∃ (γ: gname), is_lock γ (node_lock pred) (node_inv (node_next pred))
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
      iApply (acquire_spec with "Hlock"); first done.
      iNext; iIntros (v) "(Hnode & Hlocked)".
      iDestruct "Hnode" as (rep) "Hnode".
      wp_pures. wp_lam. wp_pures.

      wp_bind (Load _).
      iInv lazyN as (S Skeys L) "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_frac & >Hown_keys & Hlist)" "Hclose".

      iAssert (⌜ pred = head ∨ In pred L ⌝ ∗ ⌜ In succ L ∨ succ = tail ⌝)%I
        with "[Hown_auth Hown_pred Hown_succ]" as "(%Hpred_range & %Hsucc_range)".
      {
        iSplit.
        + iDestruct "Hown_pred" as "[Heq|Hown]"; first by iLeft.
          iDestruct (own_valid_2 with "Hown_auth Hown") 
            as %[Hvalid%gset_included]%auth_both_valid_discrete.
          iPureIntro; right.
          rewrite -elem_of_list_In Hperm elem_of_elements. 
          set_solver.
        + iDestruct "Hown_succ" as "[Hown|Heq]"; last by iRight.
          iDestruct (own_valid_2 with "Hown_auth Hown") 
            as %[Hvalid%gset_included]%auth_both_valid_discrete.
          iPureIntro; left.
          rewrite -elem_of_list_In Hperm elem_of_elements.
          set_solver.
      }

      rewrite (list_equiv_invert L head pred); last done.
      iDestruct "Hlist" as (succ' γ') "(>%Hsucc'_in_L & >Hpt & _ & Himp)".
      iDestruct (mapsto_agree with "Hnode Hpt") as %Hsucc%rep_to_node_inj; subst.

      wp_load.
      iPoseProof ("Himp" with "Hpt") as "Hlist".
      iMod ("Hclose" with "[Hlist Hown_auth Hown_frac Hown_keys]") as "_".
      { iNext; iExists S, Skeys, L; by iFrame. }

      iModIntro. wp_let. wp_lam. wp_pures. wp_lam. wp_pures.
      case_bool_decide as Heq; wp_if.
      + iModIntro; iApply "HΦ".
        iFrame "# ∗".
        iSplit; first done. iExists γ.
        assert (succ = succ') as <-; last by iFrame "# ∗".
        apply (sorted_node_key_unique (L ++ [tail])).
        - apply node_rep_sorted_app in Hsort; by destruct Hsort.
        - by rewrite in_inv_rev.
        - by rewrite in_inv_rev. 
        - congruence.
      + wp_lam. wp_pures.
        wp_apply (release_spec with "[Hnode Hlocked]"); first done.
        { iFrame "# ∗"; iExists succ'; iFrame. }
        iIntros. wp_pures.
        iApply ("IH" with "HΦ").
        iFrame "#". iPureIntro; lia.
    Qed.

    Theorem add_spec (key: Z) (v: val) (S: gset Z) (q: frac)  (Γ: lazy_gname)
      (Hrange: INT_MIN < key < INT_MAX) :
      {{{ is_lazy_list v S q Γ }}}
        add v #key
      {{{ (b: bool), RET #b; is_lazy_list v (S ∪ {[ key ]}) q Γ }}}.
    Proof.
      iIntros (Φ) "H HΦ".
      iDestruct "H" as (h head) "(%Hv & Hpt_head & %Hmin & Hown_frag & #Hinv)".
      wp_lam. wp_let. rewrite -Hv. wp_load. wp_let.

      wp_apply findLock_spec.
      { iFrame "#". iSplit; first by iLeft. iPureIntro; lia. }
      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & Hlock)".
      iDestruct "Hlock" as (γ) "(#Hlock & Hpt & Hlocked)".

      wp_pures. wp_lam. wp_pures.
      case_bool_decide as Hcase; wp_if.
      + assert (key = node_key succ) as Heq by congruence.
        iDestruct "Hown_succ" as "[Hown_succ|%Hsucc]"; last first.
        { subst; exfalso. rewrite /node_key/tail/= in Hrange; lia. }

        wp_lam. wp_bind (Snd _).
        iInv lazyN as (S' Skeys L) "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_frac & >Hown_keys & Hlist)" "Hclose".
        
        iDestruct (own_valid_2 with "Hown_auth Hown_succ") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.
        iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
          as %Hsub%frac_auth_included_total%gset_included.
        iMod (own_update_2 with "Hown_frac Hown_frag") as "[Hown_frac Hown_frag]".
        { apply frac_auth_update, (gset_local_update_union _ _ {[ key ]}). }
        assert (key ∈ Skeys) as Hin.
        { rewrite Heq. eapply key_equiv_in; first done. set_solver. }
        assert (Skeys ∪ {[ key ]} = Skeys) as -> by set_solver.

        wp_proj.
        iMod ("Hclose" with "[Hlist Hown_auth Hown_frac Hown_keys]") as "_".
        { iNext; iExists S', Skeys, L; by iFrame. }
        iModIntro.

        wp_apply (release_spec with "[Hlock Hpt Hlocked]"); first done.
        { iFrame "# ∗"; iExists succ; iFrame. }
        iIntros "_". wp_pures. 
        iModIntro. iApply "HΦ".
        iExists h, head. by iFrame "# ∗".
      + assert (key ≠ node_key succ) as Hneq by congruence.
        wp_lam. wp_pures.
        wp_load. wp_let. 
        wp_alloc l as "Hpt'". wp_let.
        iDestruct "Hpt'" as "(Hpt' & Hpt'_dup)".

        wp_apply (newlock_spec (node_inv l) with "[Hpt'_dup]").
        { iExists succ; iFrame. }
        iIntros (lk) "#Hlock'". iDestruct "Hlock'" as (γ') "Hlock'".

        wp_pures.
        rewrite (fold_rep_to_node (key, l, None, lk)).
        set (new := (key, l, None, lk)).
        
        wp_bind (Store _ _).
        iInv lazyN as (S' Skeys L) "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_frac & >Hown_keys & Hlist)" "Hclose".

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

        rewrite (list_equiv_insert head pred new succ L γ'); first last.
        { done. }
        { auto. }
        { assert (node_key new = key) as -> by auto; lia. }
        { rewrite /node_key/=; lia. }

        iDestruct ("Hlist" with "[Hpt Hpt' Hlock]") as "Hlist".
        { iNext; by iFrame "# ∗". }
        iDestruct "Hlist" as (L' L1 L2) "(Hpt & >%Hsplit & >%Hsort' & >%Hperm' & Himp)".
          
        assert (key ∉ Skeys) as Hnin'.
        {
          intros Hfalse.
          rewrite -elem_of_elements Hequiv elem_of_list_In -Hperm in_map_iff in Hfalse.
          destruct Hfalse as [x [Hkey Hin]].
          
          apply (sorted_node_lt_nin L1 L2 pred succ x).
          { rewrite -Hsplit //. }
          { rewrite Hkey; lia. }
          rewrite -Hsplit. apply in_or_app; right. apply in_or_app; by left.
        }
  
        iMod (own_update with "Hown_auth") as "[Hown_auth Hown_auth_frag]".
        { apply auth_update_alloc, (gset_local_update_union _ _ {[ new ]}). }
        assert (ε ∪ {[ new ]} = {[ new ]}) as -> by set_solver.
  
        iMod (own_update_2 with "Hown_frac Hown_frag") as "[Hown_frac Hown_frac_frag]".
        { apply frac_auth_update, (gset_local_update_union _ _ {[ key ]}). }

        rewrite (gset_union_diff key); first last.
        { done. }
        { rewrite Zlt_range_spec; lia. }
        rewrite -gset_disj_union; last set_solver.
        iDestruct "Hown_keys" as "(Hown_keys & Hown_key)".
  
        wp_store.
        iDestruct "Hpt" as "(Hpt & Hpt_dup)".
        iPoseProof ("Himp" with "Hpt_dup") as "Hlist".
        iMod ("Hclose" with "[Hlist Hown_auth Hown_frac Hown_keys]") as "_".
        {
          iNext; iExists (S' ∪ {[ new ]}), (Skeys ∪ {[ key ]}), L'. 
          iFrame. iSplit; last first. iSplit; first done.
          by (iPureIntro; apply key_equiv_insert_nin).
          
          iPureIntro.
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
            - apply elem_of_union_l. 
              by rewrite -elem_of_elements -Hperm elem_of_list_In.
          + rewrite elem_of_elements Hperm'. 
            intros Hin. apply elem_of_union in Hin as [Hin|Heq].
            - rewrite elem_of_list_In. right.
              by rewrite -elem_of_list_In Hperm elem_of_elements.
            - set_solver.
        }
  
        iModIntro. wp_pures. wp_lam. wp_pures.
        wp_apply (release_spec with "[Hlock Hpt Hlocked]"); first done.
        { iFrame "# ∗"; iExists new; iFrame. }
        iIntros "_". wp_pures.
        iModIntro. iApply "HΦ".
        iExists h, head. by iFrame "# ∗".
    Qed.

  End Proofs.
End AddSpec.