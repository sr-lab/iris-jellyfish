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

    Theorem findLock_spec (head curr: node_rep) (key: Z)
      (Γ: lazy_gname) (P: node_rep → iProp Σ) :
      {{{ 
        inv lvlN (lazy_list_inv head Γ P)
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
                               is_lock γ (node_lock pred) (node_inv l (s_tok Γ) (node_key pred))
                               ∗
                               l ↦{#1 / 2} (rep_to_node succ)
                               ∗
                               own (s_tok Γ) (GSet (Zlt_range (node_key pred) (node_key succ)))
                               ∗
                               locked γ
      }}}.
    Proof.
      iIntros (Φ) "(#Hinv & Hown_curr & Hrange) HΦ".
      iRevert (curr) "Hown_curr Hrange".
      iLöb as "IH". 
      iIntros (curr) "#Hown_curr %Hrange".
      
      wp_lam. wp_let.
      wp_apply (find_frac_spec with "[Hown_curr]").
      { by iFrame "#". }
      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & Hlock)".
      iDestruct "Hlock" as (l γ) "(%Hsome & #Hlock)".
      wp_pures. wp_lam. wp_pures.

      wp_bind (acquire _).
      iApply (acquire_spec with "Hlock"); first done.
      iNext; iIntros (v) "(Hnode & Hlocked)".
      wp_pures. wp_lam. wp_pures.
      rewrite Hsome; wp_match.
      iDestruct "Hnode" as (rep) "(Hnode & Hown_tok_range)".

      wp_bind (Load _).
      iInv lvlN as (S Skeys L) "(>%Hperm & >%Hsort & >%Hequiv & Hown_auth & Hown_frac & Hown_tok & Hlist)" "Hclose".

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
      iMod ("Hclose" with "[Hpt Himp Hown_auth Hown_frac Hown_tok]").
      {
        iNext. iExists S, Skeys, L.
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
        wp_apply (release_spec with "[Hnode Hlocked Hown_tok_range]"); first done.
        { iFrame "# ∗"; iExists succ'; iFrame. }
        iIntros. wp_pures.
        by iApply ("IH" with "HΦ").
    Qed.

    Theorem tryInsert_spec (curr head: node_rep) (key: Z) 
      (q: frac) (Skeys: gset Z) (Γ: lazy_gname) :
      {{{
        is_lazy_list lvlN head q Skeys Γ from_bot_list
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth Γ) (◯ {[curr]}))
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
        tryInsert (rep_to_node curr) #key
      {{{ v new, RET v;
        is_lazy_list lvlN head q (Skeys ∪ {[key]}) Γ from_bot_list
        ∗
        ( 
          ⌜ v = NONEV ⌝ ∨ 
          ( 
            ⌜ v = SOMEV (rep_to_node new) ⌝ 
            ∗ 
            ⌜ node_key new = key ⌝
          )
        )
      }}}.
    Proof.
      iIntros (Φ) "(Hlazy & #Hown_curr & %Hrange) HΦ".
      iDestruct "Hlazy" as (Sfrag) "(%Hequiv & Hown_frag & #Hinv)".
      wp_lam. wp_let.

      wp_apply findLock_spec.
      { by iFrame "#". }
      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & Hlock)".
      iDestruct "Hlock" as (l γ) "(%Hsome & #Hlock & Hpt & Hown_tok_range & Hlocked)".

      wp_pures. wp_lam. wp_pures.
      case_bool_decide as Hcase; wp_if.
      + wp_lam. wp_bind (Snd _).
        iDestruct "Hown_succ" as "[Hown_succ|%Hsucc]"; last first.
        { 
          subst; exfalso. inversion Hcase as [Heq]. 
          rewrite /node_key/tail//= in Heq; lia. 
        }

        iInv lvlN as (S Skeys' L) "(>%Hperm & >%Hsort & >%Hequiv' & Hown_auth & Hown_frac & Hown_tok & Hlist)" "Hclose".
        iMod "Hown_auth"; iDestruct (own_valid_2 with "Hown_auth Hown_succ") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.
        iMod "Hown_frac"; iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
          as %Hsub%frac_auth_included_total%gset_included.
        iMod (own_update_2 with "Hown_frac Hown_frag") as "[Hown_frac Hown_frag]".
        { apply frac_auth_update, (gset_local_update_union _ _ {[ succ ]}). }
        iMod "Hown_tok".

        wp_pures.
        iMod ("Hclose" with "[Hlist Hown_auth Hown_frac Hown_tok]") as "_".
        {
          iNext. iExists S, Skeys', L.
          assert (S ∪ {[ succ ]} ≡ S) as -> by set_solver.
          by iFrame.
        }
        iModIntro.

        wp_apply (release_spec with "[Hlock Hpt Hown_tok_range Hlocked]"); first done.
        { iFrame "# ∗"; iExists succ; iFrame. }
        iIntros "_". wp_pures.
        iModIntro. iApply "HΦ".
        iSplit; last by iLeft.
        iExists (Sfrag ∪ {[succ]}). 
        iFrame "# ∗". iPureIntro.

        assert (key = node_key succ) as -> by congruence.
        assert (key_equiv {[ succ ]} {[ node_key succ ]}) as Hequiv''.
        { rewrite /key_equiv ?elements_singleton //. }
        assert (Skeys ⊆ Skeys') as HsubSkeys.
        { by apply (key_equiv_subseteq Sfrag S). }
        assert ({[ node_key succ ]} ⊆ Skeys') as Hsub_succ.
        { by apply (key_equiv_subseteq {[ succ ]} S). }
        assert (Skeys ∪ {[ node_key succ ]} ⊆ Skeys') as Hsub_union_Skeys.
        { by apply union_subseteq. }
        assert (Sfrag ∪ {[ succ ]} ⊆ S) as Hsub_union_S.
        { by apply union_subseteq. }
        by apply (key_equiv_union S Sfrag {[ succ ]} Skeys' Skeys {[ node_key succ ]}).
      + wp_lam. wp_pures.
        rewrite Hsome; wp_match.
        wp_load. wp_let. wp_alloc l' as "Hpt'". wp_let.
        iDestruct "Hpt'" as "(Hpt' & Hpt'_dup)".

        assert (key ≠ node_key succ) as Hneq by congruence.
        rewrite (Zlt_range_split_op (node_key pred) (node_key succ) key); last lia.
        iDestruct "Hown_tok_range" as "((Htok_range1 & Htok_range2) & Htok_k)".

        wp_apply (newlock_spec (node_inv l' (s_tok Γ) key) with "[Hpt'_dup Htok_range2]").
        { iExists succ; iFrame. }
        iIntros (lk) "#Hlock'". iDestruct "Hlock'" as (γ') "Hlock'".
        wp_pures.

        rewrite (fold_rep_to_node (key, Some l', None, lk)).
        set (new := (key, Some l', None, lk)).
        
        wp_bind (Store _ _).
        iInv lvlN as (S Skeys' L) "(>%Hperm & >%Hsort & >%Hequiv' & Hown_auth & Hown_frac & Hown_tok & Hlist)" "Hclose".
        iMod "Hown_auth"; iMod "Hown_frac"; iMod "Hown_tok".

        iAssert ((⌜ pred = head ∨ pred ∈ S ⌝)%I) 
          with "[Hown_auth Hown_pred]" as %Hpred_range.
        {
          iDestruct "Hown_pred" as "[Heq|Hown]"; first by iLeft.
          iDestruct (own_valid_2 with "Hown_auth Hown") 
            as %[Hvalid%gset_included]%auth_both_valid_discrete.
          iPureIntro; right; set_solver.
        }

        rewrite (list_equiv_insert head pred new succ L l l' γ'); first last.
        { by rewrite -elem_of_list_In Hperm elem_of_elements. }
        { auto. }
        { rewrite /node_key//=; rewrite /node_key in Hrange'; rewrite /node_key in Hneq; lia. }
        { rewrite /node_key//=; lia. }

        iDestruct ("Hlist" with "[Hpt Hpt' Hlock]") as "Hlist".
        { iNext. unfold from_bot_list. by iFrame "# ∗". }
        iDestruct "Hlist" as (L') "(Hpt & Hsort & Hperm & Himp)".
        iMod "Hsort" as %Hsort'; iMod "Hperm" as %Hperm'; iMod "Hpt".
        wp_store.

        iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
          as %HsubS%frac_auth_included_total%gset_included.
        iDestruct (own_valid_2 with "Hown_tok Htok_k") as 
            %Hdisj%gset_disj_valid_op.
        iMod (own_update_2 with "Hown_frac Hown_frag") as "[Hown_frac Hown_frac_frag]".
        { apply frac_auth_update, (gset_local_update_union _ _ {[ new ]}). }
        iMod (own_update with "Hown_auth") as "[Hown_auth Hown_auth_frag]".
        { apply auth_update_alloc, (gset_local_update_union _ _ {[ new ]}). }
        
        iCombine "Hown_tok Htok_k" as "Hown_tok". 
        rewrite gset_disj_union; last done.

        assert (Skeys ⊆ Skeys') as HsubSkeys.
        { by apply (key_equiv_subseteq Sfrag S). }

        iDestruct "Hpt" as "(Hpt & Hpt_dup)".
        iMod ("Hclose" with "[Hpt_dup Himp Hown_auth Hown_frac Hown_tok]") as "_".
        {
          iNext. iExists _, _, L'. 
          iPoseProof ("Himp" with "Hpt_dup") as "Hlist".
          iFrame. iPureIntro. split; last first.
          {
            split; first done.
            apply key_equiv_insert_nin; auto.
            set_solver.
          }

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
        wp_apply (release_spec with "[Hlock Hpt Hlocked Htok_range1]"); first done.
        { iFrame "# ∗"; iExists new; iFrame. }
        iIntros "_". wp_pures. 
        iModIntro. iApply "HΦ".
        iSplit; last by iRight.
        iExists (Sfrag ∪ {[new]}).
        iFrame "# ∗". iPureIntro.
        apply key_equiv_insert_nin; auto.
        set_solver.

        Unshelve. auto. (* Why ;-; *)
    Qed.

  End Proofs.
End AddSpec.