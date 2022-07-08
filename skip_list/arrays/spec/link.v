From Coq Require Import Sorting.Sorted.

From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc node_rep node_lt key_equiv.
From SkipList.skip_list.arrays Require Import code.
From SkipList.skip_list.arrays.inv Require Import list_equiv lazy_inv skip_inv.
From SkipList.skip_list.arrays.spec Require Import find.


Local Open Scope Z.

Module LinkSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Find := FindSpec Params.
  Export Find.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ} (lvl: nat).

    Theorem createAndLink_spec (key: Z) (head pred succ: node_rep) (Skeys: gset Z) (q: frac)
      (sub: sub_gname) (bot: bot_gname) (s: loc) (h: nat) :
      INT_MIN < key < INT_MAX →
      {{{ 
        is_bot_list 0 head Skeys q sub bot
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth sub) (◯ {[ pred ]}))
        ∗
        ⌜ node_key pred < key < node_key succ ⌝
        ∗
        node_next pred ↦{#1 / 2} #s
        ∗
        inv (nodeN s) (node_inv s succ)
      }}}
        createAndLink (rep_to_node pred) #key #h
      {{{ (n: loc) (new: node_rep), RET #n;
        is_bot_list 0 head (Skeys ∪ {[ key ]}) q sub bot
        ∗
        own (s_auth sub) (◯ {[ new ]})
        ∗ 
        own (s_toks sub) (GSet {[ node_key new ]})
        ∗ 
        ⌜ node_key new = key ⌝
        ∗ 
        node_next pred ↦{#1 / 2} #n
        ∗
        inv (nodeN n) (node_inv n new)
        ∗ 
        n ↦{#1 / 2 / 2} rep_to_node new
        ∗
        (node_next new +ₗ 1) ↦∗{#1 / 2} replicate h #()
        ∗
        ∃ (γ: gname), 
          is_lock γ (node_lock new) (in_lock (node_next new) (S h))
          ∗
          in_lock (node_next new) (S h)
          ∗
          locked γ
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(Hbot & #Hown_pred & %Hrange & Hpt & #Hinvs) HΦ".
      iDestruct "Hbot" as "(Hown_frag & #Hinv)".

      wp_lam. wp_pures. 
      wp_lam. wp_pures.
      wp_load. wp_let. 

      wp_alloc next as "Hnext"; first lia. wp_let.
      assert (Z.to_nat (h + 1) = S h) as -> by lia.
      iDestruct "Hnext" as "(Hnext' & Hnext)".
      
      wp_apply (newlock_spec (in_lock next (S h)) with "[Hnext']").
      { 
        iExists (replicate (S h) #()); iFrame.
        rewrite replicate_length //.
      }
      iIntros (lk) "#Hlock'". iDestruct "Hlock'" as (γ) "Hlock'".

      wp_pures.
      rewrite (fold_rep_to_node (key, next, None, lk)).
      set (new := (key, next, None, lk)).

      wp_alloc n as "Hn". wp_let.
      iDestruct "Hn" as "(Hn & Hn')".
      iMod (inv_alloc (nodeN n) ⊤ (node_inv n new) with "Hn'") as "#Hinvn".
      iDestruct "Hn" as "(Hn & Hn')".
      wp_load. wp_lam. wp_pures.

      wp_bind (acquire _).
      iApply (acquire_spec with "[$]"); first done.
      iNext; iIntros (v) "(Hin_lock & Hlocked)".
      iDestruct "Hin_lock" as (vs) "(Hnext' & %Hlength)".
      
      pose proof (list_split vs h 0) as Hsplit.
      destruct Hsplit as [a Hsplit]; try lia.
      destruct Hsplit as [vs1 Hsplit]; destruct Hsplit as [vs2 Hsplit].
      destruct Hsplit as [Hvs Hsplit]; destruct Hsplit as [Hlength1 Hlength2].
      destruct vs1; last inversion Hlength1.
      simpl in Hvs; clear Hlength1.

      rewrite Hvs array_cons.
      iDestruct "Hnext'" as "(Hnext' & Hnext'2)".
      rewrite replicate_S array_cons.
      iDestruct "Hnext" as "(Hnext & Hreplicate)".

      iDestruct (mapsto_agree with "Hnext Hnext'") as %<-.
      iCombine "Hnext Hnext'" as "Hnext".

      wp_pures. wp_store.
      iDestruct "Hnext" as "(Hnext & Hnext')".

      iCombine "Hnext' Hnext'2" as "Hnext'".
      rewrite -array_cons.
      iAssert (in_lock (node_next new) (S h)) 
        with "[Hnext']" as "Hin_lock".
      { 
        iExists (#s :: vs2); iFrame. 
        iPureIntro. rewrite Hvs // in Hlength.
      }

      wp_bind (Store _ _).
      iInv (nodeN s) as "Hs" "Hclose'"; unfold node_inv.
      iInv (levelN 0) as (S Skeys' L) "(Hinv_sub & Hinv_bot)" "Hclose".
      iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_toks & Hlist)".
      iDestruct "Hinv_bot" as ">Hown_frac"; unfold bot_list_inv.

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

      rewrite (list_equiv_insert 0 s n head pred new succ L γ (Datatypes.S h)); first last.
      { done. }
      { done. }
      { assert (node_key new = key) as -> by auto; lia. }
      { rewrite /node_key/=; lia. }

      rewrite ?loc_add_0.
      iDestruct ("Hlist" with "[Hs Hpt Hnext Hn']") as "Hlist".
      { 
        rewrite /lfrac //= Qp_mul_1_r -Qp_div_div.
        iNext; iFrame "# ∗". 
        iPureIntro; lia.
      }
      iDestruct "Hlist" as (L' L1 L2) "(Hs & Hpt & >%Hsplit & >%Hsort' & >%Hperm' & Himp)".

      iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
        as %HsubS%frac_auth_included_total%gset_included.
      
      assert (key ∉ Skeys') as Hnin'.
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
      iDestruct "Hown_toks" as "(Hown_toks & Hown_tok)".

      wp_store.
      iDestruct "Hpt" as "(Hpt & Hpt_dup)".
      iPoseProof ("Himp" with "Hpt_dup") as "Hlist".
      iMod ("Hclose" with "[Hlist Hown_auth Hown_toks Hown_frac]") as "_".
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

      iMod ("Hclose'" with "[$]") as "_".
      iApply fupd_mask_intro_subseteq; first done.

      wp_pures. iModIntro. iApply "HΦ".
      iFrame "# ∗". iSplit; first done.
      iExists γ. iFrame "# ∗".
    Qed.

    Theorem link_spec (key: Z) (head pred new succ: node_rep) 
      (top bot: sub_gname) (γ: gname) (s n: loc) (h: nat) :
      INT_MIN < key < INT_MAX →
      {{{ 
        inv (levelN lvl) (lazy_list_inv lvl head top None (from_top_list bot))
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth top) (◯ {[ pred ]}))
        ∗
        ⌜ node_key pred < key < node_key succ ⌝
        ∗
        (node_next pred +ₗ lvl) ↦{#1 / 2} #s
        ∗
        inv (nodeN s) (node_inv s succ)
        ∗
        inv (nodeN n) (node_inv n new)
        ∗ 
        n ↦{#lfrac lvl} rep_to_node new
        ∗
        (node_next new +ₗ lvl) ↦ #()
        ∗
        is_lock γ (node_lock new) (in_lock (node_next new) h)
        ∗
        ⌜ lvl < h ⌝
        ∗
        from_top_list bot new
        ∗ 
        ⌜ node_key new = key ⌝
      }}}
        link (rep_to_node pred) #lvl #n
      {{{ RET #();
        own (s_auth top) (◯ {[ new ]})
        ∗ 
        own (s_toks top) (GSet {[ node_key new ]})
        ∗
        (node_next pred +ₗ lvl) ↦{#1 / 2} #n
        ∗
        (node_next new +ₗ lvl) ↦{#1 / 2} #s
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(#Hinv & #Hown_pred & %Hrange & Hpt & #Hinvs & #Hinvn & Hn & Hnext & #Hlock & #Hlvl & HP & %Hkey) HΦ".

      wp_lam. wp_pures. wp_lam. wp_pures.
      wp_load. wp_let. wp_load. 
      wp_lam. wp_pures.
      wp_store. wp_pures.
      
      iInv (nodeN s) as "Hs" "Hclose'".
      iInv (levelN lvl) as (S Skeys' L) "(Hinv_sub & _)" "Hclose".
      iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_toks & Hlist)".

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

      rewrite (list_equiv_insert lvl s n head pred new succ L γ h); first last.
      { done. }
      { auto. }
      { assert (node_key new = key) as -> by auto; lia. }
      { rewrite Hkey /node_key/=; lia. }

      iDestruct "Hnext" as "(Hnext & Hnext')".
      iDestruct ("Hlist" with "[Hs Hpt Hnext' Hn HP]") as "Hlist".
      { iNext; iFrame "# ∗". }
      iDestruct "Hlist" as (L' L1 L2) "(Hs & Hpt & >%Hsplit & >%Hsort' & >%Hperm' & Himp)".
      
      assert (node_key new ∉ Skeys') as Hnin'.
      {
        intros Hfalse.
        rewrite -elem_of_elements Hequiv elem_of_list_In -Hperm in_map_iff in Hfalse.
        destruct Hfalse as [x [Hkey' Hin]].
        
        apply (sorted_node_lt_nin L1 L2 pred succ x).
        { rewrite -Hsplit //. }
        { rewrite Hkey'; lia. }
        rewrite -Hsplit. apply in_or_app; right. apply in_or_app; by left.
      }

      iMod (own_update with "Hown_auth") as "[Hown_auth Hown_auth_frag]".
      { apply auth_update_alloc, (gset_local_update_union _ _ {[ new ]}). }
      assert (ε ∪ {[ new ]} = {[ new ]}) as -> by set_solver.

      rewrite (gset_union_diff (node_key new)); first last.
      { done. }
      { rewrite Zlt_range_spec; lia. }
      rewrite -gset_disj_union; last set_solver.
      iDestruct "Hown_toks" as "(Hown_toks & Hown_tok)".

      wp_store.
      iDestruct "Hpt" as "(Hpt & Hpt_dup)".
      iPoseProof ("Himp" with "Hpt_dup") as "Hlist".
      iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
      {
        iNext; iExists (S ∪ {[ new ]}), (Skeys' ∪ {[ node_key new ]}), L'. 
        iFrame. iPureIntro.
        split; first last. split; first done.
        by apply key_equiv_insert_nin.
        
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

      iMod ("Hclose'" with "[$]") as "_".
      iApply fupd_mask_intro_subseteq; first done.
      iApply "HΦ". iFrame "# ∗". 
    Qed.

  End Proofs.
End LinkSpec.