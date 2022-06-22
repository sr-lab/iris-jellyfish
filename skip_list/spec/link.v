From Coq Require Import Sorting.Sorted.

From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc.
From SkipList.skip_list Require Import node_rep code key_equiv.
From SkipList.skip_list.inv Require Import list_equiv lazy_inv skip_inv.
From SkipList.skip_list.spec Require Import find.


Local Open Scope Z.
Module LinkSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Find := FindSpec Params.
  Export Find.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ} (N : namespace).

    Theorem link_bot_spec (key: Z) (head pred succ: node_rep) (Skeys: gset Z) (q: frac)
      (sub: sub_gname) (bot: bot_gname) (l: loc) (γ: gname) (odown: option loc) :
      INT_MIN < key < INT_MAX →
      {{{ 
        is_bot_list N head Skeys q sub bot
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth sub) (◯ {[ pred ]}))
        ∗
        ⌜ node_key pred < key < node_key succ ⌝
        ∗
        ⌜ node_next pred = Some l ⌝
        ∗
        is_lock γ (node_lock pred) (node_inv l)
        ∗
        l ↦{#1 / 2} rep_to_node succ
        ∗
        locked γ
        ∗
        from_bot_list key odown
      }}}
        link (rep_to_node pred) #key (oloc_to_val odown)
      {{{ new, RET SOMEV (rep_to_node new);
        is_bot_list N head (Skeys ∪ {[ key ]}) q sub bot
        ∗ 
        own (s_auth sub) (◯ {[ new ]})
        ∗ 
        own (s_toks sub) (GSet {[ node_key new ]})
        ∗ 
        own (s_keys bot) (GSet {[ node_key new ]})
        ∗ 
        ⌜ node_key new = key ⌝
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(Hbot & #Hown_pred & %Hrange & %Hpred_next & #Hlock & Hpt & Hlocked & HP) HΦ".
      iDestruct "Hbot" as (Sfrag) "(%Hequiv & Hown_frag & #Hinv)".

      wp_lam. wp_pures. 
      wp_lam. wp_pures.
      rewrite Hpred_next; wp_match.
      wp_load. wp_let. 
      wp_alloc l' as "Hpt'". wp_let.
      iDestruct "Hpt'" as "(Hpt' & Hpt'_dup)".
      
      wp_apply (newlock_spec (node_inv l') with "[Hpt'_dup]").
      { iExists succ; iFrame. }
      iIntros (lk) "#Hlock'". iDestruct "Hlock'" as (γ') "Hlock'".

      wp_pures.
      set (new := (key, Some l', odown, lk)).
      rewrite (fold_rep_to_node new).
      
      wp_bind (Store _ _).
      iInv N as (S Skeys' L) "(Hinv_sub & Hinv_bot)" "Hclose".
      iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv' & >Hown_auth & >Hown_toks & Hlist)".
      iDestruct "Hinv_bot" as "(>Hown_frac & >Hown_keys)".

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
      { rewrite /node_key/=; lia. }

      iDestruct ("Hlist" with "[Hpt Hpt' Hlock HP]") as "Hlist".
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

      rewrite (gset_union_diff key); first last.
      { done. }
      { rewrite Zlt_range_spec; lia. }
      rewrite -gset_disj_union; last set_solver.
      iDestruct "Hown_toks" as "(Hown_toks & Hown_tok)".
      iDestruct "Hown_keys" as "(Hown_keys & Hown_key)".

      wp_store.
      iDestruct "Hpt" as "(Hpt & Hpt_dup)".
      iPoseProof ("Himp" with "Hpt_dup") as "Hlist".
      iMod ("Hclose" with "[Hlist Hown_auth Hown_toks Hown_frac Hown_keys]") as "_".
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
      iIntros "_". wp_pures. 
      iModIntro. iApply "HΦ".
      iSplitR "Hown_tok Hown_key Hown_auth_frag"; last by iFrame.
      iExists (Sfrag ∪ {[ new ]}).
      iFrame "# ∗". iPureIntro.
      apply key_equiv_insert_nin; auto.
    Qed.

    Theorem link_top_spec (key: Z) (head pred succ: node_rep) 
      (top bot: sub_gname) (l: loc) (γ: gname) (odown: option loc) :
      INT_MIN < key < INT_MAX →
      {{{ 
        inv N (lazy_list_inv head top None (from_top_list bot))
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth top) (◯ {[ pred ]}))
        ∗
        ⌜ node_key pred < key < node_key succ ⌝
        ∗
        ⌜ node_next pred = Some l ⌝
        ∗
        is_lock γ (node_lock pred) (node_inv l)
        ∗
        l ↦{#1 / 2} rep_to_node succ
        ∗
        locked γ
        ∗
        from_top_list bot key odown
      }}}
        link (rep_to_node pred) #key (oloc_to_val odown)
      {{{ new, RET SOMEV (rep_to_node new);
        own (s_auth top) (◯ {[ new ]})
        ∗ 
        own (s_toks top) (GSet {[ node_key new ]})
        ∗ 
        ⌜ node_key new = key ⌝
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(#Hinv & #Hown_pred & %Hrange & %Hpred_next & #Hlock & Hpt & Hlocked & HP) HΦ".

      wp_lam. wp_pures. 
      wp_lam. wp_pures.
      rewrite Hpred_next; wp_match.
      wp_load. wp_let. 
      wp_alloc l' as "Hpt'". wp_let.
      iDestruct "Hpt'" as "(Hpt' & Hpt'_dup)".
      
      wp_apply (newlock_spec (node_inv l') with "[Hpt'_dup]").
      { iExists succ; iFrame. }
      iIntros (lk) "#Hlock'". iDestruct "Hlock'" as (γ') "Hlock'".

      wp_pures.
      set (new := (key, Some l', odown, lk)).
      rewrite (fold_rep_to_node new).
      
      wp_bind (Store _ _).
      iInv N as (S Skeys' L) "(Hinv_sub & _)" "Hclose".
      iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv' & >Hown_auth & >Hown_toks & Hlist)".

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
      { rewrite /node_key/=; lia. }

      iDestruct ("Hlist" with "[Hpt Hpt' Hlock HP]") as "Hlist".
      { iNext; by iFrame "# ∗". }
      iDestruct "Hlist" as (L' L1 L2) "(Hpt & >%Hsplit & >%Hsort' & >%Hperm' & Himp)".
      
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

      iMod (own_update with "Hown_auth") as "[Hown_auth Hown_auth_frag]".
      { apply auth_update_alloc, (gset_local_update_union _ _ {[ new ]}). }
      assert (ε ∪ {[ new ]} = {[ new ]}) as -> by set_solver.

      rewrite (gset_union_diff key); first last.
      { done. }
      { rewrite Zlt_range_spec; lia. }
      rewrite -gset_disj_union; last set_solver.
      iDestruct "Hown_toks" as "(Hown_toks & Hown_tok)".

      wp_store.
      iDestruct "Hpt" as "(Hpt & Hpt_dup)".
      iPoseProof ("Himp" with "Hpt_dup") as "Hlist".
      iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
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
      iIntros "_". wp_pures. 
      iModIntro. iApply "HΦ". 
      by iFrame.
    Qed.

  End Proofs.
End LinkSpec.