From SkipList.lazy_list Require Import inv.

From SkipList.lib Require Import lock.


Local Open Scope Z.
Module LazyListSpec (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module Invariant := LazyListInv Params.
  Import Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, lockG Σ} (N : namespace).

    Theorem new_spec :
      {{{ True }}}
        new #()
      {{{ Γ v, RET v; 
        is_lazy_list N v ∅ 1 Γ
      }}}.
    Proof.
      iIntros (Φ) "_ HΦ".
      wp_lam. wp_alloc t as "Ht". wp_let.
      iDestruct "Ht" as "(Ht1&Ht2)".
      wp_apply (newlock_spec (node_inv t) with "[Ht1]").
      { iExists tail. iFrame. }
      iIntros (l) "#Hlock". iDestruct "Hlock" as (γ) "Hlock".
      set (head := (INT_MIN, Some t, l)).
      wp_pures; rewrite (fold_rep_to_node head).

      iMod (own_alloc (● (∅ : gset node_rep) ⋅ ◯ (∅: gset node_rep)))
        as (γauth) "[Hown_auth Hown_auth_frag]"; first by apply auth_both_valid.
      iMod (own_alloc (●F (∅ : gset node_rep) ⋅ ◯F (∅: gset node_rep)))
        as (γfrac) "[Hown_frac Hown_frac_frag]"; first by apply auth_both_valid.

      iMod (inv_alloc N ⊤ (lazy_list_inv head γauth γfrac) 
        with "[Ht2 Hlock Hown_auth Hown_frac]") as "#Hinv".
      + iNext. iExists ∅, nil. iFrame.
        iSplit. done. iSplit. 
        assert (node_lt head tail); last (simpl; auto).
        { rewrite /node_lt/node_key//=; apply HMIN_MAX. }
        iExists t, γ. by iFrame "# ∗".
      + iModIntro; iApply ("HΦ" $! (mk_lazy_gname γauth γfrac)).
        iExists head, ∅.
        iSplit; first by unfold key_equiv.
        by (repeat iSplit).
    Qed.
    
    Theorem find_spec1 (head curr: node_rep) (key: Z) (S: gset node_rep) (γs γf: gname) :
      {{{ 
        inv N (lazy_list_inv head γs γf)
        ∗
        own γf (◯F S)
        ∗
        ⌜ curr = head ∨ curr ∈ S ⌝
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
      find (rep_to_node curr) #key
      {{{ pred succ, RET SOMEV ((rep_to_node pred), (rep_to_node succ));
        own γf (◯F S)
        ∗
        ⌜ key ∈ map node_key (elements S) ↔ node_key succ = key ⌝
      }}}.
    Proof.
      iIntros (Φ) "(#Hinv & Hown_frag & Hcurr_range & Hrange) HΦ".
      iRevert (curr) "Hown_frag Hcurr_range Hrange HΦ".
      iLöb as "IH".
      iIntros (curr) "Hown_frag %Hcurr_range %Hrange HΦ".
      wp_lam. wp_let. wp_lam. wp_pures.

      destruct (node_next curr) as [l|] eqn:Hcurr_next; wp_pures.
      + wp_bind (Load _).
        iInv N as (S' L) "(>%Hperm & >%Hsort & Hown_auth & Hown_frac & Hlist)" "Hclose".
        iMod "Hown_frac"; iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
          as %->%frac_auth_agree_L.

        edestruct (in_split curr ([head] ++ L)) as (Ls&Lf&Hcurr).
        { destruct Hcurr_range; first by left.
          by right; rewrite -elem_of_list_In Hperm elem_of_elements. }
  
        edestruct (node_rep_split_join Lf curr key) as (pred&succ&L1&L2&?&Hsplit_join); auto.
  
        feed pose proof (node_rep_split_sep L Ls Lf L1 L2 head curr pred succ key) 
          as Htemp; auto.
        destruct Htemp as [Lm Hsplit_sep].

        destruct Lm as [|next Lm].
        - rewrite (list_equiv_split curr succ ([head] ++ L)); last first.
          { simpl in *. by rewrite -Hsplit_sep. }
          iDestruct "Hlist" as (l' γ) "(>%Hsome & Hpt & #Hlock & Himp)".
          assert (l = l') as <- by congruence.

          wp_load.
          iMod ("Hclose" with "[Hpt Himp Hown_auth Hown_frac]").
          {
            iNext. iExists S, L.
            iPoseProof ("Himp" with "Hpt") as "Hlist".
            by iFrame.
          }

          iModIntro. wp_let. wp_lam. wp_pures.
          case_bool_decide; last lia.
          wp_pures. iApply "HΦ".
          iModIntro; iFrame.

          iPureIntro.
          rewrite -Hperm; split; intros.
          * eapply (sorted_node_lt_cover_gap (Ls ++ L1) L2 pred); try lia.
            ++ by rewrite app_ass -Hsplit_join //= app_comm_cons -app_ass -Hcurr app_ass.
            ++ assert (In key (map node_key ([head] ++ L ++ [tail]))) as Hin.
               { rewrite -app_ass map_app in_app_iff; left; right. 
                 by apply elem_of_list_In. }
               rewrite -app_ass Hcurr app_ass in Hin.
               by rewrite app_ass -Hsplit_join.
          * rewrite elem_of_list_In in_map_iff. exists succ; split; auto.
            cut (In succ Lf).
            { destruct Ls; inversion Hcurr; subst; auto.
              intros; by rewrite in_app_iff; right; right. }

            cut (In succ (Lf ++ [tail])).
            { rewrite /tail ?in_app_iff.
              intros [|[|[]]]; auto; subst. 
              unfold node_key in Hrange. simpl in Hrange; lia. }

            destruct L1.
            ** rewrite //= in Hsplit_join. 
               inversion Hsplit_join as [[Heq1 Heq2]]; subst.
               by rewrite Heq2; left.
            ** inversion Hsplit_join as [[Heq1 Heq2]]; subst.
               by rewrite Heq2 in_app_iff; right; right; left.
        - rewrite (list_equiv_split curr next ([head] ++ L)); last first.
          { simpl in *. by rewrite -Hsplit_sep. }
          iDestruct "Hlist" as (l' γ) "(>%Hsome & Hpt & #Hlock & Himp)".
          assert (l = l') as <- by congruence.

          wp_load.
          iMod ("Hclose" with "[Hpt Himp Hown_auth Hown_frac]").
          {
            iNext. iExists S, L.
            iPoseProof ("Himp" with "Hpt") as "Hlist".
            by iFrame.
          }

          iModIntro. wp_let. wp_lam. wp_pures.
          case_bool_decide as Hcase.
          * exfalso.
            assert (node_key next <= node_key pred); last by lia.

            assert (In pred (next :: Lm)) as Hpred_in_m.
            {
              symmetry in Hsplit_sep.
              rewrite Hsplit_sep //= in Hsort.
              rewrite //= app_comm_cons in Hsplit_join.
              rewrite -app_ass Hcurr app_ass Hsplit_join //= in Hsplit_sep.
              apply sorted_node_lt_no_dup in Hsort.

              destruct Lm as [|next' Lm] using rev_ind.
              -- left. eapply (no_dup_pred_unique (Ls ++ [curr]) L2 (Ls ++ L1) L2 succ).
                 { apply NoDup_ListNoDup. rewrite app_ass //=. }
                 rewrite app_ass //= app_ass //=.
              -- right. apply in_app_iff. right. left.
                 eapply (no_dup_pred_unique (Ls ++ [curr; next] ++ Lm) L2 (Ls ++ L1) L2 succ).
                 { apply NoDup_ListNoDup. rewrite app_ass //= in Hsort. rewrite app_ass //=. }
                 rewrite app_ass //= in Hsplit_sep.
                 rewrite //= app_ass app_ass //=.
            }

            assert (Sorted node_lt ([next] ++ Lm)) as Hsort'.
            { rewrite -Hsplit_sep in Hsort.
              by repeat (apply node_rep_sorted_app in Hsort as (? & Hsort)). }

            apply Sorted_StronglySorted in Hsort'; last first.
            { unfold Relations_1.Transitive; apply node_lt_transitive. } 
            inversion Hsort'; subst. 
            inversion Hpred_in_m; first by (subst; lia).
            eapply node_lt_le_incl, Forall_forall; eauto.
            rewrite elem_of_list_In //=.
          * wp_if.
            iApply ("IH" $! next with "[Hown_frag] [%] [%]").
            { iFrame. }
            { 
              right. rewrite -elem_of_elements -Hperm.
              destruct Ls; assert (In next (L ++ [tail])) as Hin.
              -- inversion Hsplit_sep. by left.
              -- apply in_app_iff in Hin.
                 destruct Hin as [|[|[]]]; first by eapply elem_of_list_In.
                 subst; exfalso. 
                 rewrite /node_key/tail//= in Hcase; lia.
              -- inversion Hsplit_sep. 
                 by apply in_app_iff; right; right; left.
              -- apply in_app_iff in Hin.
                 destruct Hin as [|[|[]]]; first by eapply elem_of_list_In.
                 subst; exfalso. 
                 rewrite /node_key/tail//= in Hcase; lia.
            }
            { lia. }

            iNext. iApply "HΦ".
      + iInv N as (S' L) "(>%Hperm & >%Hsort & Hown_auth & Hown_frac & Hlist)" "Hclose".
        iMod "Hown_frac"; iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
          as %->%frac_auth_agree_L.

        rewrite (list_equiv_invert); last first.
        { by rewrite -elem_of_list_In Hperm elem_of_elements. }
        iDestruct "Hlist" as (succ l γ) "(Hsucc_range & Hsome & Hpt & #Hlock & Himp)".
        iMod "Hsome" as %Hsome; congruence.
    Qed.
    
    Theorem contains_spec (v: val) (key: Z) (Skeys: gset Z) (Γ: lazy_gname)
      (Hrange: INT_MIN < key < INT_MAX) :
      {{{ is_lazy_list N v Skeys 1 Γ }}}
        contains v #key
      {{{ (b: bool), RET #b; 
        is_lazy_list N v Skeys 1 Γ
        ∗
        ⌜ if b then key ∈ Skeys else key ∉ Skeys ⌝
      }}}.
    Proof.
      iIntros (Φ) "H HΦ".
      iDestruct "H" as (head S) "(%Hequiv & Hown & %Hv & %Hmin & #Hinv)".
      wp_lam. wp_let. rewrite -Hv.
      wp_apply (find_spec1 with "[Hown]").
      { iFrame "# ∗". iPureIntro; split. by left. lia. }
      iIntros (pred succ) "(Hown & %Hkey_in_S)".
      wp_let. wp_match. wp_pures. wp_lam. wp_pures.

      iModIntro; case_bool_decide.
      + iApply "HΦ". iSplit. 
        iExists head, S. by iFrame "# ∗".
        iPureIntro. unfold key_equiv in Hequiv. 
        rewrite -elem_of_elements Hequiv Hkey_in_S.
        congruence.
      + iApply "HΦ". iSplit. 
        iExists head, S. by iFrame "# ∗".
        iPureIntro. intros Hin. 
        rewrite -elem_of_elements Hequiv Hkey_in_S in Hin.
        congruence.
    Qed.
    
    Theorem find_spec2 (head curr: node_rep) (key: Z) (γs γf: gname) :
      {{{ 
        inv N (lazy_list_inv head γs γf)
        ∗
        (⌜ curr = head ⌝ ∨ own γs (◯ {[curr]}))
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
      find (rep_to_node curr) #key
      {{{ pred succ, RET SOMEV ((rep_to_node pred), (rep_to_node succ));
        ⌜ node_key pred < key ≤ node_key succ ⌝
        ∗
        (⌜ pred = head ⌝ ∨ own γs (◯ {[pred]}))
        ∗
        (own γs (◯ {[succ]}) ∨ ⌜ succ = tail ⌝)
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
        iInv N as (S L) "(>%Hperm & >%Hsort & Hown_auth & Hown_frac & Hlist)" "Hclose".

        iMod "Hown_auth".
        iMod (own_update with "Hown_auth") as "[Hown_auth Hown_frag]".
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
          iNext. iExists S, L.
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
      + iInv N as (S L) "(>%Hperm & >%Hsort & Hown_auth & Hown_frac & Hlist)" "Hclose".

        iMod "Hown_auth".
        iAssert ((⌜ curr = head ∨ curr ∈ S ⌝)%I) with "[Hown_auth Hown_curr]" as %Hcurr_range.
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

    Theorem findLock_spec (head curr: node_rep) (key: Z) (γs γf: gname) :
      {{{ 
        inv N (lazy_list_inv head γs γf)
        ∗
        (⌜ curr = head ⌝ ∨ own γs (◯ {[curr]}))
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
      findLock (rep_to_node curr) #key
      {{{ pred succ, RET ((rep_to_node pred), (rep_to_node succ));
        ⌜ node_key pred < key ≤ node_key succ ⌝
        ∗
        (⌜ pred = head ⌝ ∨ own γs (◯ {[pred]}))
        ∗
        (own γs (◯ {[succ]}) ∨ ⌜ succ = tail ⌝)
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
      wp_apply ((find_spec2 head curr key γs) with "[Hown_curr]").
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
      iInv N as (S L) "(>%Hperm & >%Hsort & Hown_auth & Hown_frac & Hlist)" "Hclose".

      iMod "Hown_auth".
      iAssert ((⌜ pred = head ∨ pred ∈ S ⌝ ∗ ⌜succ ∈ S ∨ succ = tail⌝)%I) 
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
      iDestruct (mapsto_agree with "Hnode Hpt") as "%Hsucc"; rewrite Hsucc.
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
        - by rewrite in_inv_rev -elem_of_list_In Hperm elem_of_elements.
        - by apply in_inv_rev. 
        - congruence.
      + wp_lam. wp_pures.
        wp_apply (release_spec with "[Hnode Hlocked]"); first done.
        { iFrame "# ∗"; by iExists succ'. }
        iIntros. wp_pures.
        by iApply ("IH" with "HΦ").
    Qed.

  End Proofs.
End LazyListSpec.