From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gmap gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import arg_max.
From SkipList.jellyfish Require Import code.
From SkipList.lib Require Import misc node_rep node_lt key_equiv.
From SkipList.jellyfish.inv Require Import list_equiv lazy_inv skip_inv.
From SkipList.jellyfish.spec Require Import find.


Local Open Scope Z.

Module LinkSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Find := FindSpec Params.
  Export Find.

  Section Proofs.
    Context `{!heapGS Σ, !skipGS Σ, !lockG Σ}.

    Theorem link_spec (lvl: Z) (head pred new succ: node_rep) 
      (bot: bot_gname) (top_sub bot_sub: sub_gname) 
      (v: val_rep) (s n: loc) :
      INT_MIN < node_key new < INT_MAX →
      {{{ 
        inv (levelN lvl) (lazy_list_inv lvl head bot top_sub (Some bot_sub))
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth top_sub) (◯ {[ pred ]}))
        ∗
        ⌜ node_key pred < node_key new < node_key succ ⌝
        ∗
        (node_next pred +ₗ lvl) ↦{#1 / 2} #s
        ∗
        s ↦□ rep_to_node succ
        ∗
        is_node (Some bot_sub) new v
        ∗
        n ↦□ rep_to_node new
        ∗
        (node_next new +ₗ lvl) ↦ #()
        ∗
        (node_locks new +ₗ lvl) ↦ #()
      }}}
        link (rep_to_node pred) #lvl #n
      {{{ RET #();
        own (s_auth top_sub) (◯ {[ new ]})
        ∗ 
        own (s_toks top_sub) (GSet {[ node_key new ]})
        ∗
        (node_next pred +ₗ lvl) ↦{#1 / 2} #n
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(#Hinv & #Hown_pred & %Hrange & Hpt & #Hs & Hnode & #Hn & Hnext & Hl) HΦ".

      wp_lam. wp_pures.
      wp_load. wp_let.
      wp_lam. wp_pures. wp_load.
      wp_lam. wp_pures.       
      wp_store; iDestruct "Hnext" as "(Hnext & Hnext')".

      wp_apply (newlock_spec (in_lock lvl (Some bot_sub) new) with "[Hnext']").
      { iExists s; iFrame. }
      iIntros (l γ) "#Hlock".
      wp_lam. wp_pures.
      wp_store; iMod (mapsto_persist with "Hl") as "#Hl".
      
      wp_lam. wp_pures.
      iInv (levelN lvl) as (M' S' L) "(Hinv_sub & _)" "Hclose".
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

      rewrite (list_equiv_join lvl (Some bot_sub) s head pred succ); auto.
      iDestruct ("Hlist" with "[Hpt]") as "Hlist".
      { iNext; iFrame "# ∗". }
      iDestruct "Hlist" as (L1 L2) "(>%Hsplit & Hpt & Hlist)".

      assert (node_key new ∉ dom M') as Hnin'.
      {
        intros Hfalse.
        rewrite -elem_of_elements Hequiv elem_of_list_In -Hperm in_map_iff in Hfalse.
        destruct Hfalse as [x [Hkey Hin]].
        
        apply (sorted_node_lt_nin L1 L2 pred succ x).
        { rewrite -Hsplit //. }
        { rewrite Hkey; lia. }
        rewrite -Hsplit. apply in_or_app; right. apply in_or_app; by left.
      }

      assert (M' !! node_key new = None) as Hnone.
      { rewrite -not_elem_of_dom //. }

      rewrite (list_equiv_insert lvl (Some bot_sub) s n head pred new succ L v γ l); first last.
      { done. }
      { done. }
      { done. }
      { done. }
      { rewrite /tail/node_key/=; rewrite /node_key in Hkey_range; lia. }

      iDestruct ("Hlist" with "[Hs Hpt Hnext Hnode]") as "Hlist".
      { iNext; iFrame "# ∗". }
      iDestruct "Hlist" as (L') "(Hpt & >%Hsort' & >%Hperm' & Himp)".

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
        iNext; iExists (<[ node_key new := prodZ {[ val_v v ]} (val_ts v) ]>M'), (S' ∪ {[ new ]}), L'.
        pose proof (dom_insert M' (node_key new) (prodZ {[ val_v v ]} (val_ts v))) as Hdom.
        rewrite leibniz_equiv_iff comm_L in Hdom.
        rewrite Hdom.
        iFrame. iPureIntro.

        split; first last. 
        { split; first done. by apply key_equiv_insert_nin. }
        
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

      iModIntro. iApply "HΦ". 
      iFrame "# ∗". 
    Qed.

    Theorem createAndLink_spec (k v t h: Z) (head pred succ: node_rep) 
      (M: gmap Z (argmax Z)) (q: frac)
      (sub: sub_gname) (bot: bot_gname) (s: loc) :
      INT_MIN < k < INT_MAX →
      {{{ 
        inv (levelN 0) (lazy_list_inv 0 head bot sub None)
        ∗
        own (s_frac bot) (◯F{q} M)
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth sub) (◯ {[ pred ]}))
        ∗
        ⌜ node_key pred < k < node_key succ ⌝
        ∗
        node_next pred ↦{#1 / 2} #s
        ∗
        s ↦□ rep_to_node succ
        ∗
        locked_val None s
        ∗
        ⌜ 0 ≤ h ⌝ 
      }}}
        createAndLink (rep_to_node pred) #k #v #t #h
      {{{ (n: loc) (new: node_rep), RET #n;
        own (s_frac bot) (◯F{q} (M ⋅ {[ k := prodZ {[ v ]} t ]}))
        ∗
        own (s_auth sub) (◯ {[ new ]})
        ∗ 
        own (s_toks sub) (GSet {[ node_key new ]})
        ∗ 
        ⌜ node_key new = k ⌝
        ∗ 
        node_next pred ↦{#1 / 2} #n
        ∗
        n ↦□ rep_to_node new
        ∗
        node_val new ↦{#1 / 2} rep_to_val (v, t, dummy_null)%core
        ∗
        (node_next new +ₗ 1) ↦∗ replicate (Z.to_nat h) #()
        ∗
        (node_locks new +ₗ 1) ↦∗ replicate (Z.to_nat h) #()
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(#Hinv & Hown_frag & #Hown_pred & %Hrange & Hpt & #Hs & Hval & %Hlvl) HΦ".
      wp_lam. wp_pures.
      
      wp_alloc next as "Hnext"; first lia. wp_let.
      wp_alloc locks as "Hlocks"; first lia. wp_let.
      assert (Z.to_nat (h + 1) = S (Z.to_nat h)) as -> by lia.
      rewrite replicate_S ?array_cons.
      iDestruct "Hnext" as "(Hn & Hnext)".
      iDestruct "Hlocks" as "(Hlocks' & Hlocks)".

      set (val := (v, t, dummy_null)).
      wp_alloc vpt as "Hvpt". wp_let.
      iDestruct "Hvpt" as "(Hvpt & Hvpt')".
      rewrite (fold_rep_to_val val).

      set (new := (k, vpt, next, @None loc, #(), locks)).
      wp_alloc node as "Hnode". wp_let.
      iMod (mapsto_persist with "Hnode") as "#Hnode".
      rewrite (fold_rep_to_node new).

      wp_lam. wp_let. wp_let.
      wp_load. wp_let.
      wp_lam; wp_pures; rewrite loc_add_0.
      wp_load.
      wp_lam; wp_pures; rewrite loc_add_0.
      wp_store; iDestruct "Hn" as "(Hn & Hn')".

      wp_apply (newlock_spec (in_lock 0 None new) with "[Hn' Hval]").
      { iExists s; rewrite loc_add_0; iFrame. }
      iIntros (l γ) "#Hlock".
      wp_lam; wp_pures; rewrite loc_add_0.
      wp_store; iMod (mapsto_persist with "Hlocks'") as "#Hl".

      wp_lam; wp_pures; rewrite loc_add_0.
      wp_bind (Store _ _).
      iInv (levelN 0) as (M' S' L) "(Hinv_sub & >Hown_frac)" "Hclose".
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

      rewrite (list_equiv_join 0 None s head pred succ); auto.
      rewrite loc_add_0. 
      iDestruct ("Hlist" with "[Hpt]") as "Hlist".
      { iNext; iFrame "# ∗". }
      iDestruct "Hlist" as (L1 L2) "(>%Hsplit & Hpt & Hlist)".

      assert (k ∉ dom M') as Hnin'.
      {
        intros Hfalse.
        rewrite -elem_of_elements Hequiv elem_of_list_In -Hperm in_map_iff in Hfalse.
        destruct Hfalse as [x [Hkey Hin]].
        
        apply (sorted_node_lt_nin L1 L2 pred succ x).
        { rewrite -Hsplit //. }
        { rewrite Hkey; lia. }
        rewrite -Hsplit. apply in_or_app; right. apply in_or_app; by left.
      }

      assert (M' !! k = None) as Hnone.
      { rewrite -not_elem_of_dom //. }

      rewrite (list_equiv_insert 0 None s node head pred new succ L val γ l); first last.
      { done. }
      { done. }
      { done. }
      { assert (node_key new = k) as -> by auto; lia. }
      { rewrite /node_key/=; lia. }

      rewrite ?loc_add_0.
      iDestruct ("Hlist" with "[Hpt Hn Hvpt']") as "Hlist".
      { iNext; iFrame "# ∗". }
      iDestruct "Hlist" as (L') "(Hpt & >%Hsort' & >%Hperm' & Himp)".

      iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
        as %HsubM%frac_auth_included_total.

      iMod (own_update with "Hown_auth") as "[Hown_auth Hown_auth_frag]".
      { apply auth_update_alloc, (gset_local_update_union _ _ {[ new ]}). }
      assert (ε ∪ {[ new ]} = {[ new ]}) as -> by set_solver.

      iMod (own_update_2 with "Hown_frac Hown_frag") as "[Hown_frac Hown_frac_frag]".
      { apply frac_auth_update, (alloc_local_update _ _ k (prodZ {[ v ]} t)); done. }

      rewrite (gset_union_diff k); first last.
      { done. }
      { rewrite Zlt_range_spec; lia. }
      rewrite -gset_disj_union; last set_solver.
      iDestruct "Hown_toks" as "(Hown_toks & Hown_tok)".

      wp_store.
      iDestruct "Hpt" as "(Hpt & Hpt_dup)".
      iPoseProof ("Himp" with "Hpt_dup") as "Hlist".
      iMod ("Hclose" with "[Hlist Hown_auth Hown_toks Hown_frac]") as "_".
      {
        iNext; iExists (<[ k := prodZ {[ v ]} t ]>M'), (S' ∪ {[ new ]}), L'.
        pose proof (dom_insert M' k (prodZ {[v]} t)) as Hdom.
        rewrite leibniz_equiv_iff comm_L in Hdom.
        rewrite Hdom.
        iFrame. iPureIntro.

        split; first last. 
        { split; first done. by apply key_equiv_insert_nin. }
        
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

      rewrite insert_singleton_op; last first.
      {
        rewrite lookup_included in HsubM.
        destruct (HsubM k) as [z Heq%leibniz_equiv_iff].
        rewrite Hnone comm op_None in Heq.
        by destruct Heq.
      }
      rewrite comm_L. by iFrame "# ∗". 
    Qed.

  End Proofs.
End LinkSpec.