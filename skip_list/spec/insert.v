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
      iDestruct "Hnode" as (rep) "Hnode".

      wp_bind (Load _).
      iInv lvlN as (S L) "(>%Hperm & >%Hsort & Hown_auth & Hown_frac & Hlist)" "Hclose".

      iMod "Hown_auth"; iAssert ⌜ pred = head ∨ In pred L ⌝%I
        with "[Hown_auth Hown_pred]" as %Hpred_range.
      {
        iDestruct "Hown_pred" as "[Heq|Hown]"; first by iLeft.
        iDestruct (own_valid_2 with "Hown_auth Hown") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.
        iPureIntro; right. 
        rewrite -elem_of_list_In Hperm elem_of_elements.
        set_solver.
      }

      iAssert ⌜ In succ L ∨ succ = tail ⌝%I
        with "[Hown_auth Hown_succ]" as %Hsucc_range.
      {
        iDestruct "Hown_succ" as "[Hown|Heq]"; last by iRight.
        iDestruct (own_valid_2 with "Hown_auth Hown") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.
        iPureIntro; left. 
        rewrite -elem_of_list_In Hperm elem_of_elements.
        set_solver.
      }

      rewrite (list_equiv_invert L head pred); last done.
      iDestruct "Hlist" as (succ' ? ? l' γ') "(>%Hsucc'_in_L & _ & >%Hsome' & Hpt & _ & Himp)".
      assert (l = l') as <- by congruence.

      wp_load.
      iDestruct (mapsto_agree with "Hnode Hpt") as "%Hsucc".
      assert (rep = succ') as -> by by apply rep_to_node_inj.
      iMod ("Hclose" with "[Hpt Himp Hown_auth Hown_frac]").
      {
        iNext. iExists S, L.
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
        - by rewrite in_inv_rev.
        - by rewrite in_inv_rev. 
        - congruence.
      + wp_lam. wp_pures.
        wp_apply (release_spec with "[Hnode Hlocked]"); first done.
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
      iDestruct "Hlock" as (l γ) "(%Hsome & #Hlock & Hpt & Hlocked)".

      wp_pures. wp_lam. wp_pures.
      case_bool_decide as Hcase; wp_if.
      + iDestruct "Hown_succ" as "[Hown_succ|%Hsucc]"; last first.
        { 
          subst; exfalso. inversion Hcase as [Heq]. 
          rewrite /node_key/tail//= in Heq; lia. 
        }

        wp_lam. wp_bind (Snd _).
        iInv lvlN as (S L) "(>%Hperm & >%Hsort & Hown_auth & Hown_frac & Hlist)" "Hclose".
        iMod "Hown_auth"; iDestruct (own_valid_2 with "Hown_auth Hown_succ") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.
        iMod "Hown_frac"; iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
          as %Hsub%frac_auth_included_total%gset_included.
        iMod (own_update_2 with "Hown_frac Hown_frag") as "[Hown_frac Hown_frag]".
        { apply frac_auth_update, (gset_local_update_union _ _ {[ succ ]}). }

        wp_pures.
        iMod ("Hclose" with "[Hlist Hown_auth Hown_frac]") as "_".
        {
          iNext. iExists S, L.
          assert (S ∪ {[ succ ]} ≡ S) as -> by set_solver.
          by iFrame.
        }
        iModIntro.

        wp_apply (release_spec with "[Hlock Hpt Hlocked]"); first done.
        { iFrame "# ∗"; iExists succ; iFrame. }
        iIntros "_". wp_pures.
        iModIntro. iApply "HΦ".
        iSplit; last by iLeft.
        iExists (Sfrag ∪ {[succ]}). 
        iFrame "# ∗". iPureIntro.

        assert (key = node_key succ) as -> by congruence.
        assert (key_equiv {[ succ ]} {[ node_key succ ]}) as Hequiv''.
        { rewrite /key_equiv ?elements_singleton //. }

        assert (Sfrag ∪ {[ succ ]} ⊆ S) as Hsub_union_S.
        { by apply union_subseteq. }

        apply node_rep_sorted_app in Hsort as [_ Hsort].
        apply node_rep_sorted_app in Hsort as [Hsort _].

        by apply (key_equiv_union L S Sfrag {[ succ ]} Skeys {[ node_key succ ]}).
      + wp_lam. wp_pures.
        rewrite Hsome; wp_match.
        wp_load. wp_let. wp_alloc l' as "Hpt'". wp_let.
        iDestruct "Hpt'" as "(Hpt' & Hpt'_dup)".

        assert (key ≠ node_key succ) as Hneq by congruence.
        
        wp_apply (newlock_spec (node_inv l') with "[Hpt'_dup]").
        { iExists succ; iFrame. }
        iIntros (lk) "#Hlock'". iDestruct "Hlock'" as (γ') "Hlock'".

        wp_bind (InjR _).
        iInv lvlN as (S L) "(>%Hperm & >%Hsort & Hown_auth & Hown_frac & Hlist)" "Hclose".
        
        wp_inj.
        iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
          as %HsubS%frac_auth_included_total%gset_included.

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

        iAssert ⌜ key ∉ Skeys ⌝%I
          with "[Hlist Hpt Hown_auth Hown_pred]" as %Hnin.
        {
          rewrite (list_equiv_invert L head pred); last done.
          iDestruct "Hlist" as (succ'' L1 L2 l'' γ'') "(_ & %Hsplit & %Hsome'' & Hpt'' & _)".
          assert (l = l'') as <- by congruence.
          iDestruct (mapsto_agree with "Hpt Hpt''") as %Hsucc.
          iPureIntro.
          apply rep_to_node_inj in Hsucc. rewrite -Hsucc in Hsplit.

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

        iMod ("Hclose" with "[Hown_auth Hown_frac Hlist]") as "_".
        { iNext; iExists S, L; by iFrame. }
        clear Hperm Hsort Hpred_range HsubS S L.

        iModIntro; wp_pures.
        rewrite (fold_rep_to_node (key, Some l', None, lk)).
        set (new := (key, Some l', None, lk)).
        
        wp_bind (Store _ _).
        iInv lvlN as (S L) "(>%Hperm & >%Hsort & Hown_auth & Hown_frac & Hlist)" "Hclose".
        iMod "Hown_auth"; iMod "Hown_frac".

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
        { rewrite /node_key//=; rewrite /node_key in Hrange'; rewrite /node_key in Hneq; lia. }
        { rewrite /node_key//=; lia. }

        iMod (own_update with "Hown_auth") as "[Hown_auth Hown_auth_frag]".
        { apply auth_update_alloc, (gset_local_update_union _ _ {[ new ]}). }
        iMod (own_update_2 with "Hown_frac Hown_frag") as "[Hown_frac Hown_frac_frag]".
        { apply frac_auth_update, (gset_local_update_union _ _ {[ new ]}). }

        iDestruct ("Hlist" with "[Hpt Hpt' Hlock]") as "Hlist".
        { iNext; by iFrame "# ∗". }
        iDestruct "Hlist" as (L') "(Hpt & Hsort & Hperm & Himp)".
        iMod "Hsort" as %Hsort'; iMod "Hperm" as %Hperm'; iMod "Hpt".
        wp_store.

        iDestruct "Hpt" as "(Hpt & Hpt_dup)".
        iMod ("Hclose" with "[Hpt_dup Himp Hown_auth Hown_frac]") as "_".
        {
          iNext. iExists _, L'. 
          iPoseProof ("Himp" with "Hpt_dup") as "Hlist".
          iFrame. iPureIntro. split; last done.

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
        iSplit; last by iRight.
        iExists (Sfrag ∪ {[new]}).
        iFrame "# ∗". iPureIntro.
        apply key_equiv_insert_nin; auto.

        Unshelve. auto. (* Why ;-; *)
    Qed.

  End Proofs.
End AddSpec.