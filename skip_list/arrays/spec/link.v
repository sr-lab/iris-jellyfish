From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.skip_list.arrays Require Import code.
From SkipList.lib Require Import misc node_rep node_lt.
From SkipList.skip_list.arrays.inv Require Import list_equiv lazy_inv skip_inv.
From SkipList.skip_list.arrays.spec Require Import find.


Local Open Scope Z.

Module LinkSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Find := FindSpec Params.
  Export Find.

  Section Proofs.
    Context `{!heapGS Σ, !skipGS Σ, !lockG Σ}.

    Theorem link_spec (h lvl: Z) (head pred new succ: node_rep) 
      (Γ γ: sub_gname) (γ': gname) (s n: loc) :
      INT_MIN < node_key new < INT_MAX →
      {{{ 
        inv (levelN lvl) (lazy_list_inv lvl head None Γ (Some γ))
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth Γ) (◯ {[ pred ]}))
        ∗
        ⌜ node_key pred < node_key new < node_key succ ⌝
        ∗
        (node_next pred +ₗ lvl) ↦{#1 / 2} #s
        ∗
        s ↦□ rep_to_node succ
        ∗
        ⌜ 0 < lvl < h ⌝
        ∗
        is_node (Some γ) new
        ∗
        n ↦□ rep_to_node new
        ∗
        (node_next new +ₗ lvl) ↦ #()
        ∗
        is_lock γ' (node_lock new) (is_array (node_next new) h)
      }}}
        link (rep_to_node pred) #lvl #n
      {{{ RET #();
        own (s_auth Γ) (◯ {[ new ]})
        ∗ 
        own (s_toks Γ) (◯ GSet {[ node_key new ]})
        ∗
        (node_next pred +ₗ lvl) ↦{#1 / 2} #n
        ∗
        (node_next new +ₗ lvl) ↦{#1 / 2} #s
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(#Hinv & #Hown_pred & %Hrange & Hpt & #Hs & %Hlvl & Hnode & #Hn & Hnext & #Hlock) HΦ".

      wp_lam. wp_pures.
      wp_load. wp_let.
      wp_lam. wp_pures. wp_load.
      wp_lam. wp_pures.   
      wp_store; iDestruct "Hnext" as "(Hnext & Hnext')".
      
      wp_lam. wp_pures.
      iInv (levelN lvl) as (S L) "(Hinv_sub & _)" "Hclose".
      iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >Hown_auth & >Hown_toks & Hlist)".

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

      rewrite list_equiv_insert; first last.
      { done. }
      { done. }
      { done. }
      { rewrite /tail/node_key/=; rewrite /node_key in Hkey_range; lia. }

      iDestruct ("Hlist" with "[Hs Hpt Hnext Hnode]") as "Hlist".
      { iNext; iFrame "# ∗". iPureIntro; lia. }
      iDestruct "Hlist" as (L' L1 L2) "(Hpt & >%Hsplit & >%Hsort' & >%Hperm' & Himp)".

      iMod (own_update with "Hown_auth") as "[Hown_auth Hown_auth_frag]".
      { apply auth_update_alloc, (gset_local_update_union _ _ {[ new ]}). }
      assert (ε ∪ {[ new ]} = {[ new ]}) as -> by set_solver.

      assert ({[node_key new]} ## (set_map node_key S : gset Z)) as Hdisj.
      {
        rewrite disjoint_singleton_l; intros Hfalse.
        rewrite elem_of_map in Hfalse.
        destruct Hfalse as [x [Hkey HinS']].
        rewrite -elem_of_elements -Hperm elem_of_list_In in HinS'.
        
        apply (sorted_node_lt_nin L1 L2 pred succ x).
        { rewrite -Hsplit //. }
        { rewrite -Hkey; lia. }
        rewrite -Hsplit. apply in_or_app; right. apply in_or_app; by left.
      }
      
      iMod (own_update with "Hown_toks") as "[Hown_toks Hown_toks_frag]".
      { by apply auth_update_alloc, (gset_disj_alloc_op_local_update _ _ {[ node_key new ]}). }
      rewrite gset_disj_union // gset_disj_union // right_id_L.

      wp_store.
      iDestruct "Hpt" as "(Hpt & Hpt_dup)".
      iPoseProof ("Himp" with "Hpt_dup") as "Hlist".
      iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
      {
        iNext; iExists (S ∪ {[ new ]}), L'. 
        rewrite /sub_list_inv comm_L set_map_union_L set_map_singleton_L.
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

      iModIntro; iApply "HΦ". 
      iFrame. 
    Qed.

    Theorem createAndLink_spec (k h: Z) (head pred succ: node_rep) 
      (Skeys: gset Z) (q: frac)
      (bot: bot_gname) (Γ: sub_gname) (s: loc) :
      INT_MIN < k < INT_MAX →
      {{{ 
        inv (levelN 0) (lazy_list_inv 0 head (Some bot) Γ None)
        ∗
        own (s_frac bot) (◯F{q} Skeys)
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth Γ) (◯ {[ pred ]}))
        ∗
        ⌜ node_key pred < k < node_key succ ⌝
        ∗
        node_next pred ↦{#1 / 2} #s
        ∗
        s ↦□ rep_to_node succ
        ∗
        ⌜ 0 ≤ h ⌝ 
      }}}
        createAndLink (rep_to_node pred) #k #h
      {{{ (n: loc) (new: node_rep), RET #n;
        own (s_frac bot) (◯F{q} (Skeys ∪ {[ k ]}))
        ∗
        own (s_auth Γ) (◯ {[ new ]})
        ∗ 
        own (s_toks Γ) (◯ GSet {[ node_key new ]})
        ∗ 
        ⌜ node_key new = k ⌝
        ∗ 
        node_next pred ↦{#1 / 2} #n
        ∗
        n ↦□ rep_to_node new
        ∗
        (node_next new +ₗ 1) ↦∗{#1 / 2} replicate (Z.to_nat h) #()
        ∗
        ∃ (γ': gname), 
          is_lock γ' (node_lock new) (is_array (node_next new) (h + 1))
          ∗
          is_array (node_next new) (h + 1)
          ∗
          locked γ'
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(#Hinv & Hown_frag & #Hown_pred & %Hrange & Hpt & #Hs & %Hlvl) HΦ".
      wp_lam. wp_pures.
      
      wp_alloc next as "Hnext"; first lia. wp_let.
      iDestruct "Hnext" as "(Hnext' & Hnext)".
      wp_apply (newlock_spec (is_array next (h + 1)) with "[Hnext']").
      { 
        iExists (replicate (Z.to_nat (h + 1)) #()); iFrame.
        rewrite replicate_length //.
      }
      iIntros (lk γ) "#Hlock'".

      wp_pures.
      set (new := (k, dummy_null, next, @None loc, lk, dummy_null)).
      rewrite (fold_rep_to_node new).

      wp_alloc n as "Hn". wp_let.
      iMod (mapsto_persist with "Hn") as "#Hn".
      wp_load. wp_lam. wp_pures.

      wp_bind (acquire _).
      iApply (acquire_spec with "[$]").
      iNext; iIntros "(Hlocked & Harray)".
      iDestruct "Harray" as (vs) "(Hnext' & %Hlength)".
      
      pose proof (list_split vs (Z.to_nat h) 0) as Hsplit.
      destruct Hsplit as [a Hsplit]; try lia.
      destruct Hsplit as [vs1 Hsplit]; destruct Hsplit as [vs2 Hsplit].
      destruct Hsplit as [Hvs Hsplit]; destruct Hsplit as [Hlength1 Hlength2].
      destruct vs1; last inversion Hlength1.
      simpl in Hvs; clear Hlength1.

      rewrite Hvs array_cons.
      iDestruct "Hnext'" as "(Hnext' & Hnext'2)".
      assert (Z.to_nat (h + 1) = S (Z.to_nat h)) as -> by lia.
      rewrite replicate_S array_cons.
      iDestruct "Hnext" as "(Hnext & Hreplicate)".

      iDestruct (mapsto_agree with "Hnext Hnext'") as %<-.
      iCombine "Hnext Hnext'" as "Hnext".

      wp_pures. wp_lam. wp_let. wp_let.
      wp_load. wp_let.
      wp_lam; wp_pures; rewrite loc_add_0.
      wp_load.
      wp_lam; wp_pures; rewrite loc_add_0.
      wp_store; iDestruct "Hnext" as "(Hnext & Hnext')".

      iCombine "Hnext' Hnext'2" as "Hnext'".
      rewrite -array_cons.
      iAssert (is_array (node_next new) (h + 1)) 
        with "[Hnext']" as "Harray".
      { 
        iExists (#s :: vs2); iFrame. 
        iPureIntro. rewrite Hvs // in Hlength.
      }

      wp_lam; wp_pures; rewrite loc_add_0.
      wp_bind (Store _ _).
      iInv (levelN 0) as (S L) "(Hinv_sub & >Hown_frac)" "Hclose".
      iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >Hown_auth & >Hown_toks & Hlist)".

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

      rewrite (list_equiv_insert _ _ _ _ _ new succ); first last.
      { done. }
      { done. }
      { done. }
      { rewrite /node_key/=; lia. }

      rewrite ?loc_add_0.
      iDestruct ("Hlist" with "[Hpt Hnext]") as "Hlist".
      { iNext; iFrame "# ∗". iPureIntro; lia. }
      iDestruct "Hlist" as (L' L1 L2) "(Hpt & >%Hsplit & >%Hsort' & >%Hperm' & Himp)".

      iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
        as %HsubS%frac_auth_included_total%gset_included.

      iMod (own_update with "Hown_auth") as "[Hown_auth Hown_auth_frag]".
      { apply auth_update_alloc, (gset_local_update_union _ _ {[ new ]}). }
      assert (ε ∪ {[ new ]} = {[ new ]}) as -> by set_solver.

      iMod (own_update_2 with "Hown_frac Hown_frag") as "[Hown_frac Hown_frac_frag]".
      { apply frac_auth_update, (gset_local_update_union _ _ {[ k ]}). }

      assert ({[node_key new]} ## (set_map node_key S : gset Z)) as Hdisj.
      { 
        rewrite disjoint_singleton_l elem_of_map. 
        intros [x [Hkey Hin]].
        rewrite -elem_of_elements -Hperm elem_of_list_In in Hin.
        
        apply (sorted_node_lt_nin L1 L2 pred succ x).
        { rewrite -Hsplit //. }
        { assert (node_key x = k) as -> by auto; lia. }
        rewrite -Hsplit. apply in_or_app; right. apply in_or_app; by left.
      }

      iMod (own_update with "Hown_toks") as "[Hown_toks Hown_toks_frag]".
      { by apply auth_update_alloc, (gset_disj_alloc_op_local_update _ _ {[ node_key new ]}). }
      rewrite gset_disj_union // gset_disj_union // right_id_L.

      wp_store.
      iDestruct "Hpt" as "(Hpt & Hpt_dup)".
      iPoseProof ("Himp" with "Hpt_dup") as "Hlist".
      iMod ("Hclose" with "[Hlist Hown_auth Hown_toks Hown_frac]") as "_".
      {
        iNext; iExists (S ∪ {[ new ]}), L'. 
        rewrite /sub_list_inv set_map_union_L set_map_singleton_L.
        iFrame; rewrite comm_L; iFrame. iPureIntro. 
        
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
          - apply elem_of_union_l. 
            by rewrite -elem_of_elements -Hperm elem_of_list_In.
        + rewrite elem_of_elements Hperm'. 
          intros Hin. apply elem_of_union in Hin as [Hin|Heq].
          - rewrite elem_of_list_In. right.
            by rewrite -elem_of_list_In Hperm elem_of_elements.
          - set_solver.
      }

      iModIntro; wp_pures. 
      iModIntro; iApply "HΦ".
      iFrame "# ∗". iSplit; first done.
      iExists γ. iFrame "# ∗".
    Qed.

  End Proofs.
End LinkSpec.