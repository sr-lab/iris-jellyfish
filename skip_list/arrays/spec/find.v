From Coq Require Import Sorting.Sorted.

From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc node_rep node_lt key_equiv.
From SkipList.skip_list.arrays Require Import code.
From SkipList.skip_list.arrays.inv Require Import list_equiv lazy_inv skip_inv.


Local Open Scope Z.

Module FindSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Invariant := SkipListInv Params.
  Export Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ} (lvl: Z).
    
    Theorem find_bot_spec (key: Z) (head curr: node_rep) (Skeys: gset Z) 
      (bot: bot_gname) (sub: sub_gname) :
      {{{ 
        inv (levelN lvl) (lazy_list_inv lvl head sub (Some bot) from_bot_list)
        ∗
        own (s_frac bot) (◯F Skeys)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
        find (rep_to_node curr) #key #lvl
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
      wp_lam. wp_let. wp_let. 
      wp_lam. wp_pures.

      wp_bind (Load #(node_next curr +ₗ lvl)).
      iInv (levelN lvl) as (S ? L) "(Hinv_sub & Hinv_bot)" "Hclose".
      iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_toks & Hlist)".
      iDestruct "Hinv_bot" as ">Hown_frac"; unfold bot_list_inv.
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
      - rewrite (list_equiv_split lvl curr succ ([head] ++ L)); last first.
        { rewrite app_ass -Hsplit_sep //. }
        iDestruct "Hlist" as (s) "(Hpt & #Hs & Himp)".

        wp_load.
        iPoseProof ("Himp" with "Hpt") as "Hlist".
        iMod ("Hclose" with "[Hlist Hown_auth Hown_toks Hown_frac]") as "_".
        { iNext; iExists S, Skeys, L; by iFrame. }

        iModIntro. wp_bind (Load _).
        iInv (nodeN s) as "Hpt" "Hclose"; unfold node_inv.
        wp_load.
        iMod ("Hclose" with "Hpt") as "_".
        
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

        rewrite (list_equiv_split lvl curr next ([head] ++ L)); last first.
        { rewrite app_ass -Hsplit_sep //. }
        iDestruct "Hlist" as (n) "(Hpt & #Hn & Himp)".

        wp_load.
        iPoseProof ("Himp" with "Hpt") as "Hlist".
        iMod ("Hclose" with "[Hlist Hown_auth Hown_toks Hown_frac]") as "_".
        { iNext; iExists S, Skeys, L; by iFrame. }

        iModIntro. wp_bind (Load _).
        iInv (nodeN n) as "Hpt" "Hclose"; unfold node_inv.
        wp_load.
        iMod ("Hclose" with "Hpt") as "_".

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
      (sub: sub_gname) (obot: option bot_gname) (P: node_rep → iProp Σ) :
      {{{ 
        inv (levelN lvl) (lazy_list_inv lvl head sub obot P)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
        find (rep_to_node curr) #key #lvl
      {{{ pred succ, RET ((rep_to_node pred), (rep_to_node succ));
        ⌜ node_key pred < key ≤ node_key succ ⌝
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth sub) (◯ {[ pred ]}))
        ∗
        (own (s_auth sub) (◯ {[ succ ]}) ∨ ⌜ succ = tail ⌝)
        ∗
        ∃ (γ: gname) (h: Z), 
          ⌜ lvl < h ⌝
          ∗
          is_lock γ (node_lock pred) (in_lock (node_next pred) h)
      }}}.
    Proof.
      iIntros (Φ) "(#Hinv & Hown_curr & Hrange) HΦ".
      iRevert (curr) "Hown_curr Hrange HΦ".
      iLöb as "IH".
      iIntros (curr) "#Hown_curr %Hrange HΦ".
      wp_lam. wp_let. wp_let. 
      wp_lam. wp_pures.

      wp_bind (Load #(node_next curr +ₗ lvl)).
      iInv (levelN lvl) as (S Skeys L) "(Hinv_sub & Hmatch)" "Hclose".
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
      iDestruct "Hlist" as (γ h s succ) "(>%Hsucc_range & Hpt & #Hinvs & Hs & #Hlock & #Hlvl & Himp)".
      rewrite -elem_of_list_In Hperm elem_of_elements in Hsucc_range.

      wp_load.
      iPoseProof ("Himp" with "[$]") as "Hlist".
      iMod ("Hclose" with "[Hmatch Hlist Hown_auth Hown_toks]") as "_".
      { iNext; iExists S, Skeys, L; by iFrame. }

      iModIntro. wp_bind (Load _).
      iInv (nodeN s) as "Hpt" "Hclose"; unfold node_inv.
      wp_load.
      iMod ("Hclose" with "Hpt") as "_".

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

        iExists γ, h. iFrame "#".
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
      (sub: sub_gname) (obot: option bot_gname) (P: node_rep → iProp Σ) :
      {{{ 
        inv (levelN lvl) (lazy_list_inv lvl head sub obot P)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
        ∗
        ⌜ 0 ≤ lvl ⌝ 
      }}}
        findLock (rep_to_node curr) #key #lvl
      {{{ pred succ, RET ((rep_to_node pred), (rep_to_node succ));
        ⌜ node_key pred < key ≤ node_key succ ⌝
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth sub) (◯ {[ pred ]}))
        ∗
        (own (s_auth sub) (◯ {[ succ ]}) ∨ ⌜ succ = tail ⌝)
        ∗
        ∃ (γ: gname) (h: Z) (s: loc), 
          ⌜ lvl < h ⌝
          ∗
          is_lock γ (node_lock pred) (in_lock (node_next pred) h)
          ∗
          in_lock (node_next pred) lvl
          ∗
          (node_next pred +ₗ lvl) ↦{#1 / 2} #s
          ∗
          inv (nodeN s) (node_inv s succ)
          ∗
          in_lock (node_next pred +ₗ lvl +ₗ 1) (h - 1 - lvl)
          ∗
          locked γ
      }}}.
    Proof.
      iIntros (Φ) "(#Hinv & Hown_curr & Hrange & Hlvl) HΦ".
      iRevert (curr) "Hown_curr Hrange Hlvl".
      iLöb as "IH". 
      iIntros (curr) "#Hown_curr %Hrange %Hlvl".
      
      wp_lam. wp_let. wp_let.
      wp_apply (find_sub_spec with "[Hown_curr]").
      { by iFrame "#". }
      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & Hlock)".
      iDestruct "Hlock" as (γ h) "(%Hh & #Hlock)".
      wp_pures. wp_lam. wp_pures.

      wp_bind (acquire _).
      iApply (acquire_spec with "Hlock"); first done.
      iNext; iIntros (v) "(Hin_lock & Hlocked)".
      iDestruct "Hin_lock" as (vs) "(Hnext & %Hlength)".

      pose proof (list_split vs (Z.to_nat (h - 1)) (Z.to_nat lvl)) as Hsplit.
      destruct Hsplit as [next Hsplit]; try lia.
      destruct Hsplit as [vs1 Hsplit]; destruct Hsplit as [vs2 Hsplit].
      destruct Hsplit as [Hvs Hsplit]; destruct Hsplit as [Hlength1 Hlength2].

      rewrite Hvs array_app array_cons Hlength1.
      assert (lvl = Z.to_nat lvl) as <- by lia.
      iDestruct "Hnext" as "(Hnext1 & Hnext & Hnext2)".

      wp_pures. wp_lam. wp_pures.
      wp_bind (Load #(node_next pred +ₗ lvl)).
      iInv (levelN lvl) as (S Skeys L) "(Hinv_sub & Hmatch)" "Hclose".
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

      rewrite (list_equiv_invert lvl L head pred); last done.
      iDestruct "Hlist" as (γ' h' s' succ') "(>%Hsucc'_in_L & >Hpt & #Hinvs' & >Hs' & _ & #Hlvl' & Himp)".
      iDestruct (mapsto_agree with "Hnext Hpt") as %->.

      wp_load.
      iPoseProof ("Himp" with "[$]") as "Hlist".
      iMod ("Hclose" with "[Hmatch Hlist Hown_auth Hown_toks]") as "_".
      { iNext; iExists S, Skeys, L; by iFrame. }

      iModIntro. wp_bind (Load _).
      iInv (nodeN s') as "Hpt" "Hclose"; unfold node_inv.
      wp_load.
      iMod ("Hclose" with "Hpt") as "_".

      iModIntro. wp_let. wp_lam. wp_pures. wp_lam. wp_pures.
      case_bool_decide as Heq; wp_if.
      + iModIntro; iApply "HΦ".
        iFrame "# ∗".
        iSplit; first done. iExists γ, h, s'.

        iAssert (in_lock (node_next pred) lvl) 
          with "[Hnext1]" as "Hin_lock1".
        { iExists vs1; by iFrame. }
        iAssert (in_lock (node_next pred +ₗ lvl +ₗ 1) (h - 1 - lvl)) 
          with "[Hnext2]" as "Hin_lock2".
        { iExists vs2; iFrame; iPureIntro; lia. }

        assert (succ = succ') as <-; last by iFrame "# ∗".
        apply (sorted_node_key_unique (L ++ [tail])).
        - apply node_rep_sorted_app in Hsort; by destruct Hsort.
        - by rewrite in_inv_rev.
        - by rewrite in_inv_rev. 
        - congruence.
      + wp_lam. wp_pures.

        iCombine "Hnext1 Hnext Hnext2" as "Hnext".
        assert (lvl = Z.to_nat lvl) as -> by lia.
        rewrite -Hlength1 -array_cons -array_app -Hvs.
        iAssert (in_lock (node_next pred) h) 
          with "[Hnext]" as "Hin_lock".
        { iExists vs; by iFrame. }

        wp_apply (release_spec with "[Hin_lock Hlocked]"); first done.
        { iFrame "# ∗"; iExists succ'; iFrame. }
        iIntros. wp_pures.
        iApply ("IH" with "HΦ"). iFrame "#". 
        all: iPureIntro; lia.
    Qed.

  End Proofs.
End FindSpec.