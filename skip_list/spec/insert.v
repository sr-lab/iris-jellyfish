From Coq Require Import Sorting.Sorted.

From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc.
From SkipList.skip_list Require Import node_rep code key_equiv.
From SkipList.skip_list.inv Require Import lazy_inv skip_inv.
From SkipList.skip_list.spec Require Import find.


Local Open Scope Z.
Module AddSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Find := FindSpec Params.
  Import Find.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ} (lvlN : namespace).

    Theorem linkNode_spec (head pred succ: node_rep) (key: Z)
      (q: frac) (Skeys: gset Z) (Γ: lazy_gname) (obot: option lazy_gname) 
      (l: loc) (γ: gname) (odown: option loc) :
      INT_MIN < key < INT_MAX →
      {{{ 
        is_lazy_list lvlN head q Skeys Γ (from_bot_list obot)
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth Γ) (◯ {[ pred ]}))
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
        from_bot_list obot key odown
      }}}
        linkNode (rep_to_node pred) #key (oloc_to_val odown)
      {{{ new, RET SOMEV (rep_to_node new);
        is_lazy_list lvlN head q (Skeys ∪ {[ key ]}) Γ (from_bot_list obot)
        ∗ 
        own (s_auth Γ) (◯ {[ new ]})
        ∗ 
        own (s_toks Γ) (GSet {[ node_key new ]})
        ∗ 
        ⌜ node_key new = key ⌝
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(Hlazy & #Hown_pred & %Hrange & %Hpred_next & #Hlock & Hpt & Hlocked & HP) HΦ".
      iDestruct "Hlazy" as (Sfrag) "(%Hequiv & Hown_frag & #Hinv)".

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
      iInv lvlN as (S Skeys' L) "(>%Hperm & >%Hsort & >%Hequiv' & >Hown_auth & >Hown_frac & Hown_toks & Hlist)" "Hclose".

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

      wp_store.
      iDestruct "Hpt" as "(Hpt & Hpt_dup)".
      iPoseProof ("Himp" with "Hpt_dup") as "Hlist".
      iMod ("Hclose" with "[Hlist Hown_auth Hown_frac Hown_toks]") as "_".
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
      iSplitR "Hown_tok Hown_auth_frag"; last by iFrame.
      iExists (Sfrag ∪ {[ new ]}).
      iFrame "# ∗". iPureIntro.
      apply key_equiv_insert_nin; auto.
    Qed.

    Theorem tryInsert_spec (curr head: node_rep) (key: Z) 
      (q: frac) (Skeys: gset Z) (bot: lazy_gname) :
      INT_MIN < key < INT_MAX →
      {{{
        is_lazy_list lvlN head q Skeys bot (from_bot_list None)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth bot) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key ⌝
      }}}
        tryInsert (rep_to_node curr) #key
      {{{ v new, RET v;
        is_lazy_list lvlN head q (Skeys ∪ {[ key ]}) bot (from_bot_list None)
        ∗
        ( 
          ⌜ v = NONEV ⌝ ∨ 
          ( 
            ⌜ v = SOMEV (rep_to_node new) ⌝ 
            ∗ 
            own (s_auth bot) (◯ {[ new ]})
            ∗ 
            own (s_toks bot) (GSet {[ node_key new ]})
            ∗ 
            ⌜ node_key new = key ⌝
          )
        )
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(Hlazy & #Hown_curr & %Hrange) HΦ".
      iDestruct "Hlazy" as (Sfrag) "(%Hequiv & Hown_frag & #Hinv)".
      wp_lam. wp_let.

      wp_apply findLock_spec.
      { iFrame "#". iPureIntro; lia. }
      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & Hlock)".
      iDestruct "Hlock" as (l γ) "(%Hsome & #Hlock & Hpt & Hlocked)".

      wp_pures. wp_lam. wp_pures.
      case_bool_decide as Hcase; wp_if.
      + assert (key = node_key succ) as Heq by congruence.
        iDestruct "Hown_succ" as "[Hown_succ|%Hsucc]"; last first.
        { subst; exfalso. rewrite /node_key/tail/= in Hkey_range; lia. }

        wp_lam. wp_bind (Snd _).
        iInv lvlN as (S Skeys' L) "(>%Hperm & >%Hsort &>%Hequiv' & >Hown_auth & >Hown_frac & >Hown_toks & Hlist)" "Hclose".
        iDestruct (own_valid_2 with "Hown_auth Hown_succ") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.
        iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
          as %Hsub%frac_auth_included_total%gset_included.
        iMod (own_update_2 with "Hown_frac Hown_frag") as "[Hown_frac Hown_frag]".
        { apply frac_auth_update, (gset_local_update_union _ _ {[ succ ]}). }

        wp_proj.
        iMod ("Hclose" with "[Hlist Hown_auth Hown_frac Hown_toks]") as "_".
        {
          iNext; iExists S, Skeys', L.
          assert (S = S ∪ {[ succ ]}) as <- by set_solver.
          by iFrame.
        }
        iModIntro.

        wp_apply (release_spec with "[Hlock Hpt Hlocked]"); first done.
        { iFrame "# ∗"; iExists succ; iFrame. }
        iIntros "_". wp_pures.
        iModIntro. iApply ("HΦ" $! _ succ).
        iSplitR ""; last by iLeft.
        iExists (Sfrag ∪ {[ succ ]}). 
        iFrame "# ∗". iPureIntro.

        eapply key_equiv_union.
        { done. }
        { by do 2 apply node_rep_sorted_app in Hsort as [? Hsort]. }
        { done. }
        { rewrite Heq /key_equiv ?elements_singleton //. }
        { by apply union_subseteq. }
      + assert (key ≠ node_key succ) as Hneq by congruence.
        assert (oloc_to_val None = NONEV) as <- by auto.

        wp_apply (linkNode_spec with "[Hpt Hlocked Hown_frag]").
        { done. }
        { 
          iFrame "# ∗". 
          iSplit. iExists Sfrag; by iFrame.
          iPureIntro. by split; first lia.
        }
        
        iIntros (new) "(Hlazy & Hkey & Hown_frag & Hown_tok)".
        iApply "HΦ". iSplitL "Hlazy"; last iRight; by iFrame.
    Qed.

    Theorem insert_spec (curr down head: node_rep) (key: Z) 
      (q: frac) (Stop Sbot: gset Z) (top bot: lazy_gname) :
      INT_MIN < key < INT_MAX →
      {{{
        is_lazy_list lvlN head q Stop top (from_bot_list (Some bot))
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth top) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key ⌝
        ∗ 
        own (s_auth bot) (◯ {[ down ]})
        ∗ 
        own (s_toks bot) (GSet {[ node_key down ]})
        ∗ 
        ⌜ node_key down = key ⌝
      }}}
        insert (rep_to_node curr) #key (rep_to_node down)
      {{{ new, RET SOMEV (rep_to_node new);
        is_lazy_list lvlN head q (Stop ∪ {[ key ]}) top (from_bot_list (Some bot))
        ∗ 
        own (s_auth top) (◯ {[ new ]})
        ∗ 
        own (s_toks top) (GSet {[ node_key new ]})
        ∗ 
        ⌜ node_key new = key ⌝
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(Hlazy & #Hown_curr & %Hrange & #Hown_down & Hown_tok & %Hdown) HΦ".
      iDestruct "Hlazy" as (Sfrag) "(%Hequiv & Hown_frag & #Hinv)".
      wp_lam. wp_let. wp_let.

      wp_apply findLock_spec.
      { iFrame "#". iPureIntro; lia. }
      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & Hlock)".
      iDestruct "Hlock" as (l γ) "(%Hsome & #Hlock & Hpt & Hlocked)".

      wp_let. wp_match.
      wp_bind (Fst _).
      iInv lvlN as (S Skeys' L) "(>%Hperm & >%Hsort & >%Hequiv' & Hown_auth & Hown_frac & Hown_toks & Hlist)" "Hclose".
      wp_proj.

      iAssert ⌜ key ≠ node_key succ ⌝%I
        with "[Hown_auth Hown_succ Hown_tok Hlist]" as %Hneq.
      {
        iDestruct "Hown_succ" as "[Hown|%Heq]"; last first.
        { iPureIntro; rewrite Heq /node_key /=; lia. } 

        iDestruct (own_valid_2 with "Hown_auth Hown") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.
        assert (succ ∈ S) by set_solver.

        rewrite list_equiv_invert_L; last first.
        { by rewrite -elem_of_list_In Hperm elem_of_elements. }
        iDestruct "Hlist" as (? ? ? ? ? ) "(_ & _ & _ & _ & _ & HP & _)".
        destruct (node_down succ) as [d|]; last by iExFalso.
        iDestruct "HP" as (?) "(_ & _ & Hown_tok' & %Hsucc)".

        iDestruct (own_valid_2 with "Hown_tok Hown_tok'") as 
          %Hdisj%gset_disj_valid_op.
        iPureIntro; set_solver.
      }

      iMod ("Hclose" with "[Hlist Hown_auth Hown_frac Hown_toks]") as "_".
      { iNext; iExists S, Skeys', L; by iFrame "# ∗". }

      iModIntro; wp_pures. 
      wp_alloc d as "Hpt_down". 
      wp_pures.

      assert (oloc_to_val (Some d) = SOMEV #d) as <- by auto.
      iAssert (from_bot_list (Some bot) key (Some d)) 
        with "[Hpt_down Hown_tok]" as "HP".
      { iExists down; by iFrame "# ∗". }

      wp_apply (linkNode_spec with "[Hpt Hlocked Hown_frag HP]").
      { done. }
      { 
        iFrame "# ∗". 
        iSplit. iExists Sfrag; by iFrame.
        iPureIntro. by split; first lia.
      }
      iApply "HΦ".
    Qed.

  End Proofs.
End AddSpec.