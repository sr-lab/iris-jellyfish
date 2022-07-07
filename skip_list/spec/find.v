From Coq Require Import Sorting.Sorted.

From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc node_rep node_lt key_equiv.
From SkipList.skip_list Require Import code.
From SkipList.skip_list.inv Require Import list_equiv lazy_inv skip_inv.


Local Open Scope Z.

Module FindSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Invariant := SkipListInv Params.
  Export Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ} (N: namespace).
    
    Theorem find_bot_spec (key: Z) (head curr: node_rep) (Skeys: gset Z) 
      (bot: bot_gname) (sub: sub_gname) (P: Z → option loc → iProp Σ) :
      {{{ 
        inv N (lazy_list_inv head sub (Some bot) P)
        ∗
        own (s_frac bot) (◯F Skeys)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
        find (rep_to_node curr) #key
      {{{ pred succ, RET ((rep_to_node pred), (rep_to_node succ));
        own (s_frac bot) (◯F Skeys)
        ∗
        ⌜ node_key pred < key ⌝
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth sub) (◯ {[ pred ]}))
        ∗
        ⌜ key ∈ Skeys ↔ node_key succ = key ⌝
      }}}.
    Proof.
      iIntros (Φ) "(#Hinv & Hown_frag & Hown_curr & Hrange) HΦ".
      iRevert (curr) "Hown_frag Hown_curr Hrange HΦ".
      iLöb as "IH".
      iIntros (curr) "Hown_frac_frag #Hown_curr %Hrange HΦ".
      wp_lam. wp_let. wp_lam. wp_pures.

      wp_bind (Load _).
      iInv N as (S ? L) "(Hinv_sub & Hinv_bot)" "Hclose".
      iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_toks & Hlist)".
      iDestruct "Hinv_bot" as "(>Hown_frac & >Hown_keys)".
      iDestruct (own_valid_2 with "Hown_frac Hown_frac_frag") 
        as %->%frac_auth_agree_L.

      iAssert ((⌜ curr = head ∨ In curr L ⌝)%I) with "[Hown_auth Hown_curr]" as %Hcurr_range.
      {
        iDestruct "Hown_curr" as "[Heq|Hown]"; first by iLeft.
        iDestruct (own_valid_2 with "Hown_auth Hown") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.
        iPureIntro; right.
        rewrite -elem_of_list_In Hperm elem_of_elements.
        set_solver.
      }

      edestruct (in_split curr ([head] ++ L)) 
        as (Ls&Lf&Hcurr).
      { rewrite in_inv //. }

      edestruct (node_rep_split_join Lf curr tail key) 
        as (pred&succ&L1&L2&?&?&Hsplit_join); auto.
      {
        rewrite -app_ass Hcurr app_ass in Hsort.
        apply node_rep_sorted_app in Hsort.
        simpl in *. by destruct Hsort as [_ ?].
      }

      feed pose proof (node_rep_split_sep L Ls Lf L1 L2 head curr pred succ tail key) 
        as Htemp; auto.
      destruct Htemp as [Lm Hsplit_sep].

      destruct Lm as [|next Lm].
      - rewrite (list_equiv_split curr succ ([head] ++ L)); last first.
        { rewrite app_ass -Hsplit_sep //. }
        iDestruct "Hlist" as "(Hpt & Himp)".

        wp_load.
        iPoseProof ("Himp" with "Hpt") as "Hlist".
        iMod ("Hclose" with "[Hlist Hown_auth Hown_toks Hown_frac Hown_keys]") as "_".
        { iNext; iExists S, Skeys, L; by iFrame. }

        iModIntro. wp_let. wp_lam. wp_pures.
        case_bool_decide; last lia.
        wp_pures. iApply "HΦ".
        iModIntro; iFrame "# ∗".

        iPureIntro.
        split; first lia.
        rewrite -elem_of_elements Hequiv -Hperm. 
        split; intros.
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
            rewrite /node_key /= in Hrange; lia. }

          destruct L1.
          ++ rewrite //= in Hsplit_join. 
              inversion Hsplit_join as [[Heq1 Heq2]]; subst.
              by rewrite Heq2; left.
          ++ inversion Hsplit_join as [[Heq1 Heq2]]; subst.
              by rewrite Heq2 in_app_iff; right; right; left.
      - assert (next ∈ S).
        {
          rewrite -elem_of_elements -Hperm.
          destruct Ls; assert (In next (L ++ [tail])) as Hin.
          + inversion Hsplit_sep. by left.
          + apply in_app_iff in Hin.
            destruct Hin as [|[|[]]]; first by eapply elem_of_list_In.
            inversion Hsplit_sep. inversion Hcurr.
            subst; exfalso.
            rewrite -Hsplit_sep in Hsort.
            do 2 apply node_rep_sorted_app in Hsort as (_ & Hsort).
            apply Sorted_StronglySorted in Hsort; last first.
            { unfold Relations_1.Transitive; apply node_lt_transitive. } 
            inversion Hsort as [|? ? _ Hall]; subst.
            apply node_rep_forall_app in Hall.
            destruct Hall as [_ Hall].
            inversion Hall as [|? ? Hfalse]; subst.
            rewrite /node_lt in Hfalse.
            assert (node_key tail = INT_MAX) by auto.
            lia.
          + inversion Hsplit_sep. 
            by apply in_app_iff; right; right; left.
          + apply in_app_iff in Hin.
            destruct Hin as [|[|[]]]; first by eapply elem_of_list_In.
            inversion Hsplit_sep. inversion Hcurr.
            subst; exfalso.
            rewrite -Hsplit_sep in Hsort.
            do 2 apply node_rep_sorted_app in Hsort as (_ & Hsort).
            apply Sorted_StronglySorted in Hsort; last first.
            { unfold Relations_1.Transitive; apply node_lt_transitive. } 
            inversion Hsort as [|? ? _ Hall]; subst.
            apply node_rep_forall_app in Hall.
            destruct Hall as [_ Hall].
            inversion Hall as [|? ? Hfalse]; subst.
            rewrite /node_lt in Hfalse.
            assert (node_key tail = INT_MAX) by auto.
            lia.
        }

        iMod (own_update with "Hown_auth") as "[Hown_auth Hown_auth_frag']".
        { apply auth_update_alloc, (gset_local_update_union _ _ {[ next ]}). }
        assert (ε ∪ {[ next ]} = {[ next ]}) as -> by set_solver.
        assert (S ∪ {[ next ]} = S) as -> by set_solver.

        rewrite (list_equiv_split curr next ([head] ++ L)); last first.
        { rewrite app_ass -Hsplit_sep //. }
        iDestruct "Hlist" as "(Hpt & Himp)".

        wp_load.
        iPoseProof ("Himp" with "Hpt") as "Hlist".
        iMod ("Hclose" with "[Hlist Hown_auth Hown_toks Hown_frac Hown_keys]") as "_".
        { iNext; iExists S, Skeys, L; by iFrame. }

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
            + left. eapply (no_dup_elem_unique (Ls ++ [curr]) L2 (Ls ++ L1) L2 succ).
                { rewrite app_ass //=. }
                rewrite app_ass //= app_ass //=.
            + right. apply in_app_iff. right. left.
                eapply (no_dup_elem_unique (Ls ++ [curr; next] ++ Lm) L2 (Ls ++ L1) L2 succ).
                { rewrite app_ass //= in Hsort. rewrite app_ass //=. }
                rewrite app_ass //= in Hsplit_sep.
                rewrite //= app_ass app_ass //=.
          }

          rewrite -Hsplit_sep in Hsort.
          do 2 apply node_rep_sorted_app in Hsort as (_ & Hsort).
          apply node_rep_sorted_app in Hsort as (Hsort & _).

          apply Sorted_StronglySorted in Hsort; last first.
          { unfold Relations_1.Transitive; apply node_lt_transitive. } 
          inversion Hsort; subst. 
          inversion Hpred_in_m; first by (subst; lia).
          eapply node_lt_le_incl, Forall_forall; eauto.
          rewrite elem_of_list_In //=.
        * wp_if.
          iApply ("IH" $! next with "[$] [$] [%]").
          { lia. }

          iNext; iApply "HΦ".
    Qed.
    
    Theorem find_sub_spec (key: Z) (head curr: node_rep)
      (sub: sub_gname) (obot: option bot_gname) (P: Z → option loc → iProp Σ) :
      {{{ 
        inv N (lazy_list_inv head sub obot P)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
        find (rep_to_node curr) #key
      {{{ pred succ, RET ((rep_to_node pred), (rep_to_node succ));
        ⌜ node_key pred < key ≤ node_key succ ⌝
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth sub) (◯ {[ pred ]}))
        ∗
        (own (s_auth sub) (◯ {[ succ ]}) ∨ ⌜ succ = tail ⌝)
        ∗
        ∃ (γ: gname), is_lock γ (node_lock pred) (in_lock (node_next pred))
      }}}.
    Proof.
      iIntros (Φ) "(#Hinv & Hown_curr & Hrange) HΦ".
      iRevert (curr) "Hown_curr Hrange HΦ".
      iLöb as "IH".
      iIntros (curr) "#Hown_curr %Hrange HΦ".
      wp_lam. wp_let. wp_lam. wp_pures.

      wp_bind (Load _).
      iInv N as (S Skeys L) "(Hinv_sub & Hmatch)" "Hclose".
      iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_toks & Hlist)".

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
      iDestruct "Hlist" as (γ succ) "(>%Hsucc_range & Hpt & #Hlock & Himp)".
      rewrite -elem_of_list_In Hperm elem_of_elements in Hsucc_range.

      wp_load.
      iPoseProof ("Himp" with "Hpt") as "Hlist".
      iMod ("Hclose" with "[Hmatch Hlist Hown_auth Hown_toks]") as "_".
      { iNext; iExists S, Skeys, L; by iFrame. }

      iModIntro. wp_let. wp_lam. wp_pures.
      case_bool_decide as Hcase; wp_if.
      - wp_pures. iApply "HΦ".
        iModIntro; iFrame "#".

        iSplit; first by (iPureIntro; lia).
        iSplit.
        { 
          destruct Hsucc_range as [Hin|Heq]; last by iRight.
          assert (S = S ⋅ {[ succ ]}) as -> by set_solver.
          iDestruct "Hown_frag" as "(? & ?)"; iLeft; iFrame.
        }

        iExists γ. by iFrame "#".
      - iApply ("IH" $! succ with "[Hown_frag] [%]").
        {
          iRight.
          assert (S = S ⋅ {[ succ ]}) as ->.
          {
            destruct Hsucc_range as [Hin|Heq]; first set_solver.
            subst; exfalso; rewrite /node_key/tail//= in Hcase; lia.
          }
          iDestruct "Hown_frag" as "(? & ?)"; iFrame.
        }
        { lia. }

        iNext; iApply "HΦ".
    Qed.

    Theorem findLock_spec (key: Z) (head curr: node_rep)
      (sub: sub_gname) (obot: option bot_gname) (P: Z → option loc → iProp Σ) :
      {{{ 
        inv N (lazy_list_inv head sub obot P)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
        findLock (rep_to_node curr) #key
      {{{ pred succ, RET ((rep_to_node pred), (rep_to_node succ));
        ⌜ node_key pred < key ≤ node_key succ ⌝
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth sub) (◯ {[ pred ]}))
        ∗
        (own (s_auth sub) (◯ {[ succ ]}) ∨ ⌜ succ = tail ⌝)
        ∗
        ∃ (γ: gname), is_lock γ (node_lock pred) (in_lock (node_next pred))
                      ∗
                      node_next pred ↦{#1 / 2} (rep_to_node succ)
                      ∗
                      locked γ
      }}}.
    Proof.
      iIntros (Φ) "(#Hinv & Hown_curr & Hrange) HΦ".
      iRevert (curr) "Hown_curr Hrange".
      iLöb as "IH". 
      iIntros (curr) "#Hown_curr %Hrange".
      
      wp_lam. wp_let.
      wp_apply (find_sub_spec with "[Hown_curr]").
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
      iInv N as (S Skeys L) "(Hinv_sub & Hmatch)" "Hclose".
      iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_toks & Hlist)".

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
      iDestruct "Hlist" as (γ' succ') "(>%Hsucc'_in_L & >Hpt & _ & Himp)".
      iDestruct (mapsto_agree with "Hnode Hpt") as %Hsucc%rep_to_node_inj; subst.

      wp_load.
      iPoseProof ("Himp" with "Hpt") as "Hlist".
      iMod ("Hclose" with "[Hmatch Hlist Hown_auth Hown_toks]") as "_".
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

  End Proofs.
End FindSpec.