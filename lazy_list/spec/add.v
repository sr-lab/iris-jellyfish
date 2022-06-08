From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc.
From SkipList.lazy_list Require Import inv node_rep code key_equiv.


Local Open Scope Z.
Module AddSpec (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module Invariant := LazyListInv Params.
  Import Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ} (N : namespace).
    
    Theorem find_spec (head curr: node_rep) (key: Z) (Γ: lazy_gname) :
      {{{ 
        inv N (lazy_list_inv head Γ)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth Γ) (◯ {[curr]}))
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
      find (rep_to_node curr) #key
      {{{ pred succ, RET SOMEV ((rep_to_node pred), (rep_to_node succ));
        ⌜ node_key pred < key ≤ node_key succ ⌝
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth Γ) (◯ {[pred]}))
        ∗
        (own (s_auth Γ) (◯ {[succ]}) ∨ ⌜ succ = tail ⌝)
        ∗
        ∃ (l:loc) (γ: gname), ⌜ node_next pred = Some l ⌝ 
                              ∗ 
                              is_lock γ (node_lock pred) (node_inv l)
      }}}.
    Proof.
      iIntros (Φ) "(#Hinv & Hown_curr & Hrange) HΦ".
      iRevert (curr) "Hown_curr Hrange HΦ".
      iLöb as "IH".
      iIntros (curr) "#Hown_curr %Hrange HΦ".
      wp_lam. wp_let. wp_lam. wp_pures.

      destruct (node_next curr) as [l|] eqn:Hcurr_next; wp_pures.
      + wp_bind (Load _).
        iInv N as (S Skeys L) "(>%Hperm & >%Hsort & >%Hequiv & Hown_auth & Hown_frac & Hlist)" "Hclose".

        iMod "Hown_auth"; iMod (own_update with "Hown_auth") as "[Hown_auth Hown_frag]".
        { by apply auth_update_alloc, (gset_local_update S _ S). }

        iAssert ((⌜ curr = head ∨ curr ∈ S ⌝)%I) with "[Hown_auth Hown_curr]" as %Hcurr_range.
        {
         iDestruct "Hown_curr" as "[Heq|Hown]"; first by iLeft.
         iDestruct (own_valid_2 with "Hown_auth Hown") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.
         iPureIntro; right; set_solver.
        }

        rewrite (list_equiv_invert); last first.
        { by rewrite -elem_of_list_In Hperm elem_of_elements. }
        iDestruct "Hlist" as (succ l' γ) "(Hsucc_range & Hsome & Hpt & #Hlock & Himp)".
        iMod "Hsucc_range" as %Hsucc_range;
          rewrite -elem_of_list_In Hperm elem_of_elements in Hsucc_range.
        iMod "Hsome" as %Hsome; assert (l = l') as <- by congruence.
        iMod "Hpt"; wp_load.
        iMod ("Hclose" with "[Hpt Himp Hown_auth Hown_frac]").
        {
          iNext; iExists S, Skeys, L.
          iPoseProof ("Himp" with "Hpt") as "Hlist".
          by iFrame.
        }

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

          iExists l, γ. by iFrame "#".
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
      + iInv N as (S Skeys L) "(>%Hperm & >%Hsort & >%Hequiv & Hown_auth & Hown_frac & Hlist)" "Hclose".

        iMod "Hown_auth"; iAssert ((⌜ curr = head ∨ curr ∈ S ⌝)%I) 
          with "[Hown_auth Hown_curr]" as %Hcurr_range.
        {
         iDestruct "Hown_curr" as "[Heq|Hown]"; first by iLeft.
         iDestruct (own_valid_2 with "Hown_auth Hown") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.
         iPureIntro; right; set_solver.
        }

        rewrite (list_equiv_invert); last first.
        { by rewrite -elem_of_list_In Hperm elem_of_elements. }
        iDestruct "Hlist" as (succ l γ) "(Hsucc_range & Hsome & Hpt & #Hlock & Himp)".
        iMod "Hsome" as %Hsome; congruence.
    Qed.

    Theorem findLock_spec (head curr: node_rep) (key: Z) (Γ: lazy_gname) :
      {{{ 
        inv N (lazy_list_inv head Γ)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth Γ) (◯ {[curr]}))
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
      findLock (rep_to_node curr) #key
      {{{ pred succ, RET SOMEV ((rep_to_node pred), (rep_to_node succ));
        ⌜ node_key pred < key ≤ node_key succ ⌝
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth Γ) (◯ {[pred]}))
        ∗
        (own (s_auth Γ) (◯ {[succ]}) ∨ ⌜ succ = tail ⌝)
        ∗
        ∃ (l: loc) (γ: gname), ⌜ node_next pred = Some l ⌝
                               ∗
                               is_lock γ (node_lock pred) (node_inv l)
                               ∗
                               l ↦{#1 / 2} (rep_to_node succ)
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
      iDestruct "Hlock" as (l γ) "(%Hsome & #Hlock)".
      wp_pures. wp_lam. wp_pures.

      wp_bind (acquire _).
      iApply (acquire_spec with "Hlock"); first done.
      iNext; iIntros (v) "(Hnode & Hlocked)".
      wp_pures. wp_lam. wp_pures.
      rewrite Hsome; wp_match.
      iDestruct "Hnode" as (rep) "Hnode".

      wp_bind (Load _).
      iInv N as (S Skeys L) "(>%Hperm & >%Hsort & >%Hequiv & Hown_auth & Hown_frac & Hlist)" "Hclose".

      iMod "Hown_auth"; iAssert ((⌜ pred = head ∨ pred ∈ S ⌝ ∗ ⌜succ ∈ S ∨ succ = tail⌝)%I) 
        with "[Hown_auth Hown_pred Hown_succ]" as "(%Hpred_range & %Hsucc_range)".
      {
        iSplit.
        - iDestruct "Hown_pred" as "[Heq|Hown]"; first by iLeft.
          iDestruct (own_valid_2 with "Hown_auth Hown") 
            as %[Hvalid%gset_included]%auth_both_valid_discrete.
          iPureIntro; right; set_solver.
        - iDestruct "Hown_succ" as "[Hown|Heq]"; last by iRight.
          iDestruct (own_valid_2 with "Hown_auth Hown") 
            as %[Hvalid%gset_included]%auth_both_valid_discrete.
          iPureIntro; left; set_solver.
      }

      rewrite (list_equiv_invert L head pred); last first.
      { by rewrite -elem_of_list_In Hperm elem_of_elements. }
      iDestruct "Hlist" as (succ' l' γ') "(>%Hsucc'_in_L & >%Hsome' & Hpt & _ & Himp)".
      assert (l = l') as <- by congruence.

      wp_load.
      iDestruct (mapsto_agree with "Hnode Hpt") as "%Hsucc".
      assert (rep = succ') as -> by by apply rep_to_node_inj.
      iMod ("Hclose" with "[Hpt Himp Hown_auth Hown_frac]").
      {
        iNext; iExists S, Skeys, L.
        iPoseProof ("Himp" with "Hpt") as "Hlist".
        by iFrame.
      }

      iModIntro. wp_let. wp_lam. wp_pures. wp_lam. wp_pures.
      case_bool_decide as Heq; wp_if.
      + wp_pures. iApply "HΦ". iModIntro; iFrame "# ∗".
        iSplit. done. iExists l, γ.
        assert (succ = succ') as <-; last by iFrame "# ∗".
        apply (sorted_node_key_unique (L ++ [tail])).
        - apply node_rep_sorted_app in Hsort; by destruct Hsort.
        - by rewrite in_inv_rev -elem_of_list_In Hperm elem_of_elements.
        - by apply in_inv_rev. 
        - congruence.
      + wp_lam. wp_pures.
        wp_apply (release_spec with "[Hnode Hlocked]"); first done.
        { iFrame "# ∗"; iExists succ'; iFrame. }
        iIntros. wp_pures.
        by iApply ("IH" with "HΦ").
    Qed.

    Theorem add_spec (v: val) (key: Z) (Skeys: gset Z) (q: frac)  (Γ: lazy_gname)
      (Hrange: INT_MIN < key < INT_MAX) :
      {{{
        is_lazy_list N v Skeys q Γ
      }}}
        add v #key
      {{{ RET #();
        is_lazy_list N v (Skeys ∪ {[ key ]}) q Γ
      }}}.
    Proof.
      iIntros (Φ) "H HΦ".
      iDestruct "H" as (h head Sfrag) "(%Hv & Hpt_head & %Hmin & %Hequiv & Hown_frag & #Hinv)".
      wp_lam. wp_let. rewrite -Hv. wp_load.

      wp_apply findLock_spec.
      { iFrame "#". iSplit; first by iLeft. by rewrite Hmin. }
      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & Hlock)".
      iDestruct "Hlock" as (l γ) "(%Hsome & #Hlock & Hpt & Hlocked)".

      wp_pures. wp_lam. wp_pures.
      case_bool_decide as Hcase; wp_if.
      + wp_lam. wp_bind (Snd _).
        assert (key = node_key succ) as Heq by congruence.
        iDestruct "Hown_succ" as "[Hown_succ|%Hsucc]"; last first.
        { subst; exfalso. rewrite /node_key/tail/= in Hrange; lia. }

        iInv N as (S Skeys' L) "(>%Hperm & >%Hsort & >%Hequiv' & >Hown_auth & >Hown_frac & Hlist)" "Hclose".
        iDestruct (own_valid_2 with "Hown_auth Hown_succ") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.
        iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
          as %Hsub%frac_auth_included_total%gset_included.
        iMod (own_update_2 with "Hown_frac Hown_frag") as "[Hown_frac Hown_frag]".
        { apply frac_auth_update, (gset_local_update_union _ _ {[ succ ]}). }

        wp_pures.
        iMod ("Hclose" with "[Hlist Hown_auth Hown_frac]") as "_".
        {
          iNext; iExists S, Skeys', L.
          assert (S ∪ {[ succ ]} ≡ S) as -> by set_solver.
          by iFrame.
        }
        iModIntro.

        wp_apply (release_spec with "[Hlock Hpt Hlocked]"); first done.
        { iFrame "# ∗"; iExists succ; iFrame. }
        iIntros "_". iApply "HΦ".
        iExists h, head, (Sfrag ∪ {[succ]}).
        iFrame "# ∗". iPureIntro. 
        split; first done. split; first done.

        eapply key_equiv_union.
        { done. }
        { by do 2 apply node_rep_sorted_app in Hsort as [? Hsort]. }
        { done. }
        { rewrite Heq /key_equiv ?elements_singleton //. }
        { by apply union_subseteq. }
      + assert (key ≠ node_key succ) as Hneq by congruence.
        wp_lam. wp_pures.
        rewrite Hsome; wp_match.
        wp_load. wp_let. 
        wp_alloc l' as "Hpt'". wp_let.
        iDestruct "Hpt'" as "(Hpt' & Hpt'_dup)".

        wp_apply (newlock_spec (node_inv l') with "[Hpt'_dup]").
        { iExists succ; iFrame. }
        iIntros (lk) "#Hlock'". iDestruct "Hlock'" as (γ') "Hlock'".

        wp_pures.
        set (new := (key, Some l', lk)).
        rewrite (fold_rep_to_node new).
        
        wp_bind (Store _ _).
        iInv N as (S Skeys' L) "(>%Hperm & >%Hsort & >%Hequiv' & >Hown_auth & >Hown_frac & Hlist)" "Hclose".

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

        rewrite (list_equiv_insert head pred new succ L l l' γ'); first last.
        { done. }
        { auto. }
        { assert (node_key new = key) as -> by auto; lia. }
        { rewrite /node_key//=; lia. }

        iDestruct ("Hlist" with "[Hpt Hpt' Hlock]") as "Hlist".
        { iNext; by iFrame "# ∗". }
        iDestruct "Hlist" as (L' L1 L2) "(Hpt & >%Hsplit & >%Hsort' & >%Hperm' & Himp)".
  
        iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
          as %HsubS%frac_auth_included_total%gset_included.
        
        assert (key ∉ Skeys') as Hnin'.
        {
          intros Hfalse.
          rewrite -elem_of_elements Hequiv' elem_of_list_In -Hperm in_map_iff in Hfalse.
          destruct Hfalse as [x [Hkey Hin]].
          
          apply (sorted_node_lt_nin L1 L2 pred succ x).
          { rewrite -Hsplit //. }
          { rewrite Hkey; lia. }
          rewrite -Hsplit. apply in_or_app; right. apply in_or_app; by left.
        }
  
        assert (key ∉ Skeys) as Hnin.
        {
          intros Hfalse.
          rewrite -elem_of_elements Hequiv elem_of_list_In in_map_iff in Hfalse.
          destruct Hfalse as [x [Hkey Hin]].
          rewrite -elem_of_list_In elem_of_elements in Hin.
          assert (x ∈ S) as HinS by set_solver; clear Hin.
          rewrite -elem_of_elements -Hperm elem_of_list_In in HinS.
          
          apply (sorted_node_lt_nin L1 L2 pred succ x).
          { rewrite -Hsplit //. }
          { rewrite Hkey; lia. }
          rewrite -Hsplit. apply in_or_app; right. apply in_or_app; by left.
        }
  
        iMod (own_update with "Hown_auth") as "[Hown_auth Hown_auth_frag]".
        { apply auth_update_alloc, (gset_local_update_union _ _ {[ new ]}). }
        assert (ε ∪ {[ new ]} = {[ new ]}) as -> by set_solver.
  
        iMod (own_update_2 with "Hown_frac Hown_frag") as "[Hown_frac Hown_frac_frag]".
        { apply frac_auth_update, (gset_local_update_union _ _ {[ new ]}). }
  
        wp_store.
        iDestruct "Hpt" as "(Hpt & Hpt_dup)".
        iPoseProof ("Himp" with "Hpt_dup") as "Hlist".
        iMod ("Hclose" with "[Hlist Hown_auth Hown_frac]") as "_".
        {
          iNext; iExists (S ∪ {[ new ]}), (Skeys' ∪ {[ key ]}), L'. 
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
          - rewrite elem_of_elements Hperm' elem_of_list_In.
            intros Hin. destruct Hin as [Heq|Hin].
            * set_solver.
            * apply elem_of_union_l. 
              by rewrite -elem_of_elements -Hperm elem_of_list_In.
          - rewrite elem_of_elements Hperm'. 
            intros Hin. apply elem_of_union in Hin as [Hin|Heq].
            * rewrite elem_of_list_In. right.
              by rewrite -elem_of_list_In Hperm elem_of_elements.
            * set_solver.
        }
  
        iModIntro. wp_pures. wp_lam. wp_pures.
        wp_apply (release_spec with "[Hlock Hpt Hlocked]"); first done.
        { iFrame "# ∗"; iExists new; iFrame. }
        iIntros "_". iApply "HΦ".
        iExists h, head, (Sfrag ∪ {[ new ]}).
        iFrame "# ∗". iPureIntro.
        split; first done. split; first done.
        apply key_equiv_insert_nin; auto.
    Qed.

  End Proofs.
End AddSpec.