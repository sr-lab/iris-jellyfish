From Coq Require Import Sorting.Sorted.

From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc.
From SkipList.lazy_list Require Import node_rep code key_equiv.
From SkipList.lazy_list.inv Require Import list_equiv inv.


Local Open Scope Z.
Module ContainsSpec (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module Invariant := LazyListInv Params.
  Import Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ}.
    
    Theorem find_spec (key: Z) (head curr: node_rep) (S: gset node_rep) (Γ: lazy_gname) :
      {{{ 
        inv lazyN (lazy_list_inv head Γ)
        ∗
        own (s_frac Γ) (◯F S)
        ∗
        ⌜ curr = head ∨ curr ∈ S ⌝
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
      find (rep_to_node curr) #key
      {{{ pred succ, RET SOMEV ((rep_to_node pred), (rep_to_node succ));
        own (s_frac Γ) (◯F S)
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
        iInv lazyN as (S' Skeys L) "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_frac & >Hown_keys & Hlist)" "Hclose".
        iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
          as %->%frac_auth_agree_L.

        edestruct (in_split curr ([head] ++ L)) 
          as (Ls&Lf&Hcurr).
        { destruct Hcurr_range; first by left.
          by right; rewrite -elem_of_list_In Hperm elem_of_elements. }
  
        edestruct (node_rep_split_join Lf curr key) 
          as (pred&succ&L1&L2&?&Hsplit_join); auto.
  
        feed pose proof (node_rep_split_sep L Ls Lf L1 L2 head curr pred succ key) 
          as Htemp; auto.
        destruct Htemp as [Lm Hsplit_sep].

        destruct Lm as [|next Lm].
        - rewrite (list_equiv_split curr succ ([head] ++ L)); last first.
          { simpl in *. by rewrite -Hsplit_sep. }
          iDestruct "Hlist" as (l' γ) "(>%Hsome & Hpt & #Hlock & Himp)".
          assert (l = l') as <- by congruence.

          wp_load.
          iMod ("Hclose" with "[Hpt Himp Hown_auth Hown_frac Hown_keys]").
          {
            iNext; iExists S, Skeys, L.
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
              rewrite /node_key /= in Hrange; lia. }

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
          iMod ("Hclose" with "[Hpt Himp Hown_auth Hown_frac Hown_keys]").
          {
            iNext; iExists S, Skeys, L.
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
              -- left. eapply (no_dup_elem_unique (Ls ++ [curr]) L2 (Ls ++ L1) L2 succ).
                 { rewrite app_ass //=. }
                 rewrite app_ass //= app_ass //=.
              -- right. apply in_app_iff. right. left.
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

            iNext; iApply "HΦ".
      + iInv lazyN as (? ? ?) "(>%Hperm & _ & _ & _ & >Hown_frac & _ & Hlist)" "_".
        iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
          as %->%frac_auth_agree_L.

        rewrite (list_equiv_invert); last first.
        { by rewrite -elem_of_list_In Hperm elem_of_elements. }
        iDestruct "Hlist" as (? ? ?) "(_ & >%Hsome & _ & _ & _)".
        congruence.
    Qed.
    
    Theorem contains_spec (key: Z) (v: val) (Skeys: gset Z) (Γ: lazy_gname)
      (Hrange: INT_MIN < key < INT_MAX) :
      {{{ is_lazy_list v Skeys 1 Γ }}}
        contains v #key
      {{{ (b: bool), RET #b; 
        is_lazy_list v Skeys 1 Γ
        ∗
        ⌜ if b then key ∈ Skeys else key ∉ Skeys ⌝
      }}}.
    Proof.
      iIntros (Φ) "H HΦ".
      iDestruct "H" as (h head S) "(%Hv & Hpt & %Hmin & %Hequiv & Hown & #Hinv)".
      wp_lam. wp_let. rewrite -Hv. wp_load.
      wp_apply (find_spec with "[Hown]").
      { iFrame "# ∗". iPureIntro; split. by left. lia. }
      iIntros (pred succ) "(Hown & %Hkey_in_S)".
      wp_let. wp_match. wp_pures. wp_lam. wp_pures.

      iModIntro; case_bool_decide.
      + iApply "HΦ". iSplit. 
        iExists h, head, S. by iFrame "# ∗".
        iPureIntro. rewrite /key_equiv in Hequiv. 
        rewrite -elem_of_elements Hequiv Hkey_in_S.
        congruence.
      + iApply "HΦ". iSplit. 
        iExists h, head, S. by iFrame "# ∗".
        iPureIntro. intros Hin. 
        rewrite -elem_of_elements Hequiv Hkey_in_S in Hin.
        congruence.
    Qed.

  End Proofs.
End ContainsSpec.