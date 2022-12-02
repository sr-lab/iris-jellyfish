From Coq Require Import Sorting.Sorted.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lazy_list Require Import code.
From SkipList.lib Require Import misc node_rep node_lt.
From SkipList.lazy_list.inv Require Import list_equiv inv.


Local Open Scope Z.

Module ContainsSpec (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module Invariant := LazyListInv Params.
  Export Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !lazyGS Σ, !lockG Σ}.
    
    Theorem find_spec (k: Z) (head curr: node_rep) 
      (Skeys: gset Z) (Γ: lazy_gname) :
      {{{ 
        inv lazyN (lazy_list_inv head Γ)
        ∗
        own (s_frac Γ) (◯F Skeys)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth Γ) (◯ {[curr]}))
        ∗
        ⌜ node_key curr < k < INT_MAX ⌝
      }}}
        find (rep_to_node curr) #k
      {{{ pred succ, RET ((rep_to_node pred), (rep_to_node succ));
        own (s_frac Γ) (◯F Skeys)
        ∗
        ⌜ k ∈ Skeys ↔ node_key succ = k ⌝
      }}}.
    Proof.
      iIntros (Φ) "(#Hinv & Hown_frag & Hown_curr & Hrange) HΦ".
      iRevert (curr) "Hown_frag Hown_curr Hrange HΦ".
      iLöb as "IH".
      iIntros (curr) "Hown_frag #Hown_curr %Hrange HΦ".
      wp_lam. wp_let. wp_lam. wp_pures.

      wp_bind (Load _). 
      iInv lazyN as (S L) "(>%Hperm & >%Hsort & >Hown_auth & >Hown_frac & Hlist)" "Hclose".
      iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
        as %<-%frac_auth_agree_L.

      iAssert ⌜ curr = head ∨ In curr L ⌝%I with "[Hown_auth Hown_curr]" as %Hcurr_range.
      {
        iDestruct "Hown_curr" as "[Heq|Hown]"; first by iLeft.
        iDestruct (own_valid_2 with "Hown_auth Hown") 
        as %[Hvalid%gset_included]%auth_both_valid_discrete.
        iPureIntro; right.
        rewrite -elem_of_list_In Hperm elem_of_elements.
        set_solver.
      }

      edestruct (in_cons_split curr head L) 
        as (Ls&Lf&(Hcurr&Hsub)).
      { rewrite in_inv //. }

      edestruct (node_rep_split_join Lf curr tail k) 
        as (pred&succ&L1&L2&?&?&Hpred_range&Hsucc_range&Hsplit_join); auto.
      {
        rewrite /= app_comm_cons Hcurr app_ass in Hsort.
        apply node_rep_sorted_app in Hsort.
        simpl in *. by destruct Hsort as [_ ?].
      }

      feed pose proof (node_rep_split_sep L Ls Lf L1 L2 head curr pred succ tail k) 
        as Htemp; auto.
      destruct Htemp as [Lm Hsplit_sep].

      destruct Lm as [|next Lm].
      - rewrite (list_equiv_split curr succ ([head] ++ L)); last first.
        { rewrite app_ass -Hsplit_sep //. }
        iDestruct "Hlist" as "(Hpt & Himp)".

        wp_load.
        iPoseProof ("Himp" with "Hpt") as "Hlist".
        iMod ("Hclose" with "[Hlist Hown_auth Hown_frac]") as "_".
        { iNext; iExists S, L; by iFrame.  }

        iModIntro. wp_let. wp_lam. wp_pures.
        case_bool_decide; last lia.
        wp_pures. iApply "HΦ".
        iModIntro; iFrame.

        iPureIntro.
        rewrite elem_of_map. 
        split.
        * intros [rep [Hkey HinS]].
          rewrite -elem_of_elements -Hperm in HinS.
          eapply (sorted_node_lt_cover_gap (Ls ++ L1) L2 pred); try lia.
          ++ by rewrite app_ass -Hsplit_join //= app_comm_cons -app_ass -Hcurr -app_comm_cons.
          ++ assert (In k (map node_key (head :: L ++ [tail]))) as Hin.
             { 
               right. 
               rewrite map_app in_app_iff -elem_of_list_In.
               left. rewrite elem_of_list_In in_map_iff.
               exists rep. rewrite -elem_of_list_In //.
             }        
             rewrite app_comm_cons Hcurr app_ass in Hin.
             by rewrite app_ass -Hsplit_join.
        * intros; exists succ. split; first done.
          rewrite -elem_of_elements -Hperm elem_of_list_In.

          assert (In succ Lf).
          { 
            rewrite -in_inv_rev /tail ?in_app_iff in Hsucc_range.
            destruct Hsucc_range as [|[|[]]]; auto; subst. 
            rewrite /node_key /= in Hrange; lia. 
          }

          destruct Ls; inversion Hcurr; subst; auto.
          intros; by rewrite in_app_iff; right; right.
      - assert (next ∈ S).
        {
          rewrite -elem_of_elements -Hperm elem_of_list_In.
          destruct Ls.
          + inversion Hsplit_sep as [[Heq Hnext]]; subst. 
            destruct L; inversion Hnext as [[Heq Htail]]; subst.
            - exfalso. 
              pose proof (app_cons_not_nil Lm L2 succ).
              congruence.
            - by left.
          + inversion Hsplit_sep as [[Heq Hnext]]; subst.
            inversion Hcurr as [Heq]; subst.
            apply in_app_iff; right; right.
            rewrite app_ass -app_comm_cons in Hnext.
            apply app_eq in Hnext.
            destruct Lf; inversion Hnext as [[Heq Htail]]; subst.
            - exfalso. 
              pose proof (app_cons_not_nil Lm L2 succ).
              congruence.
            - by left.
        }

        iMod (own_update with "Hown_auth") as "[Hown_auth Hown_auth_frag]".
        { apply auth_update_alloc, (gset_local_update_union _ _ {[ next ]}). }
        assert (ε ∪ {[ next ]} = {[ next ]}) as -> by set_solver.
        assert (S ∪ {[ next ]} = S) as -> by set_solver.
      
        rewrite list_equiv_split; last first.
        { rewrite app_ass -Hsplit_sep //. }
        iDestruct "Hlist" as "(Hpt & Himp)".

        wp_load.
        iPoseProof ("Himp" with "Hpt") as "Hlist".
        iMod ("Hclose" with "[Hlist Hown_auth Hown_frac]") as "_".
        { iNext; iExists S, L; by iFrame. }

        iModIntro. wp_let. wp_lam. wp_pures.
        case_bool_decide as Hcase.
        * exfalso.
          assert (node_key next <= node_key pred); last by lia.

          assert (In pred (next :: Lm)) as Hpred_in_m.
          {
            symmetry in Hsplit_sep.
            rewrite Hsplit_sep //= in Hsort.
            rewrite //= app_comm_cons in Hsplit_join.
            rewrite //= app_comm_cons Hcurr app_ass Hsplit_join in Hsplit_sep.
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

    Theorem contains_spec (p: loc) (k: Z) 
      (S: gset Z) (Γ: lazy_gname)
      (Hrange: INT_MIN < k < INT_MAX) :
      {{{ is_lazy_list p S 1 Γ }}}
        contains #p #k
      {{{ (b: bool), RET #b; 
        is_lazy_list p S 1 Γ
        ∗
        ⌜ if b then k ∈ S else k ∉ S ⌝
      }}}.
    Proof.
      iIntros (Φ) "H HΦ".
      iDestruct "H" as (head) "(Hpt & %Hmin & Hown & #Hinv)".
      wp_lam. wp_let. wp_load.

      wp_apply (find_spec with "[Hown]").
      { iFrame "# ∗". iSplit. by iLeft. iPureIntro; lia. }
      iIntros (pred succ) "(Hown & %Hkey_in_S)".
      wp_pures. wp_lam. wp_pures.

      iModIntro; case_bool_decide.
      + iApply "HΦ". iSplit. 
        { iExists head; by iFrame "# ∗". }
        iPureIntro.
        rewrite Hkey_in_S; congruence.
      + iApply "HΦ". iSplit. 
        { iExists head; by iFrame "# ∗". }
        iPureIntro; intros Hin. 
        rewrite Hkey_in_S in Hin; congruence.
    Qed.

  End Proofs.
End ContainsSpec.