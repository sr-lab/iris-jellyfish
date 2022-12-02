From Coq Require Import Sorting.Sorted.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gmap gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import arg_max.
From SkipList.jellyfish Require Import code.
From SkipList.lib Require Import misc node_rep node_lt.
From SkipList.jellyfish.inv Require Import list_equiv lazy_inv skip_inv.


Local Open Scope Z.

Module FindSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Invariant := SkipListInv Params.
  Export Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !skipGS Σ, !lockG Σ}.
    
    Theorem find_bot_spec (k: Z) (head curr: node_rep) 
      (M: gmap Z (argmax Z)) (bot: bot_gname) (sub: sub_gname) :
      {{{ 
        inv (levelN 0) (lazy_list_inv 0 head (Some bot) sub None)
        ∗
        own (s_frac bot) (◯F M)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < k < INT_MAX ⌝
      }}}
        find (rep_to_node curr) #k #0
      {{{ pred succ, RET ((rep_to_node pred), (rep_to_node succ));
        own (s_frac bot) (◯F M)
        ∗
        ⌜ node_key pred < k ⌝
        ∗
        (own (s_auth sub) (◯ {[ succ ]}) ∨ ⌜ succ = tail ⌝)
        ∗
        ⌜ k ∈ dom M ↔ node_key succ = k ⌝
      }}}.
    Proof.
      iIntros (Φ) "(#Hinv & Hown_frag & Hown_curr & Hrange) HΦ".
      iRevert (curr) "Hown_frag Hown_curr Hrange HΦ".
      iLöb as "IH".
      iIntros (curr) "Hown_frac_frag #Hown_curr %Hrange HΦ".
      wp_lam. wp_pures. 
      wp_lam. wp_pures.

      wp_bind (Load #(node_next curr +ₗ 0)).
      iInv (levelN 0) as (? S L) "(Hinv_sub & >Hown_frac & >%Hequiv)" "Hclose".
      iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >Hown_auth & >Hown_toks & Hlist)".
      iDestruct (own_valid_2 with "Hown_frac Hown_frac_frag") 
        as %->%frac_auth_agree_L.

      iMod (own_update with "Hown_auth") as "[Hown_auth Hown_frag]".
      { by apply auth_update_alloc, (gset_local_update S _ S). }

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
      - rewrite list_equiv_split; last first.
        { rewrite app_ass -Hsplit_sep //. }
        iDestruct "Hlist" as (s) "(Hpt & #Hs & Himp)".

        wp_load.
        iPoseProof ("Himp" with "Hpt") as "Hlist".
        iMod ("Hclose" with "[Hlist Hown_auth Hown_toks Hown_frac]") as "_".
        { iNext; iExists M, S, L; by iFrame. }

        iModIntro. wp_load. 
        wp_let. wp_lam. wp_pures.
        case_bool_decide; last lia.
        wp_pures. iApply "HΦ".
        iModIntro; iFrame "# ∗".

        iSplit; first by (iPureIntro; lia).
        iSplit.
        { 
          destruct Hsucc_range as [Hin|Heq]; last by iRight.
          rewrite -elem_of_list_In in Hin.
          rewrite Hperm in Hsub.
          assert (S = S ⋅ {[ succ ]}) as -> by set_solver.
          iDestruct "Hown_frag" as "(? & ?)"; iLeft; iFrame.
        }

        iPureIntro.
        rewrite Hequiv elem_of_map.
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

        iMod (own_update with "Hown_auth") as "[Hown_auth Hown_auth_frag']".
        { apply auth_update_alloc, (gset_local_update_union _ _ {[ next ]}). }
        assert (ε ∪ {[ next ]} = {[ next ]}) as -> by set_solver.
        assert (S ∪ {[ next ]} = S) as -> by set_solver.

        rewrite list_equiv_split; last first.
        { rewrite app_ass -Hsplit_sep //. }
        iDestruct "Hlist" as (n) "(Hpt & #Hn & Himp)".

        wp_load.
        iPoseProof ("Himp" with "Hpt") as "Hlist".
        iMod ("Hclose" with "[Hlist Hown_auth Hown_toks Hown_frac]") as "_".
        { iNext; iExists M, S, L; by iFrame. }

        iModIntro. wp_load. 
        wp_let. wp_lam. wp_pures.
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
    
    Theorem find_sub_spec (k lvl: Z) (head curr: node_rep)
      (obot: option bot_gname) (sub: sub_gname) (osub: option sub_gname) :
      {{{ 
        inv (levelN lvl) (lazy_list_inv lvl head obot sub osub)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < k < INT_MAX ⌝
      }}}
        find (rep_to_node curr) #k #lvl
      {{{ pred succ, RET ((rep_to_node pred), (rep_to_node succ));
        ⌜ node_key pred < k ≤ node_key succ ⌝
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth sub) (◯ {[ pred ]}))
        ∗
        (own (s_auth sub) (◯ {[ succ ]}) ∨ ⌜ succ = tail ⌝)
        ∗
        ∃ (γ: gname) (l: val), 
          (node_locks pred +ₗ lvl) ↦□ l
          ∗
          is_lock γ l (in_lock lvl osub pred)
      }}}.
    Proof.
      iIntros (Φ) "(#Hinv & Hown_curr & Hrange) HΦ".
      iRevert (curr) "Hown_curr Hrange HΦ".
      iLöb as "IH".
      iIntros (curr) "#Hown_curr %Hrange HΦ".
      wp_lam. wp_pures. 
      wp_lam. wp_pures.

      wp_bind (Load #(node_next curr +ₗ lvl)).
      iInv (levelN lvl) as (M S L) "(Hinv_sub & Hmatch)" "Hclose".
      iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >Hown_auth & >Hown_toks & Hlist)".

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

      rewrite list_equiv_invert; last done.
      iDestruct "Hlist" as (γ l s succ) "(>%Hsucc_range & Hpt & #Hs & #Hl & #Hlock & Himp)".
      rewrite -elem_of_list_In Hperm elem_of_elements in Hsucc_range.

      wp_load.
      iPoseProof ("Himp" with "Hpt") as "Hlist".
      iMod ("Hclose" with "[Hmatch Hlist Hown_auth Hown_toks]") as "_".
      { iNext; iExists M, S, L; by iFrame. }

      iModIntro. wp_load.
      wp_let. wp_lam. wp_pures.
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

        iExists γ, l. iFrame "#".
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

    Theorem findLock_spec (k lvl: Z) (head curr: node_rep)
      (obot: option bot_gname) (sub: sub_gname) (osub: option sub_gname) :
      {{{ 
        inv (levelN lvl) (lazy_list_inv lvl head obot sub osub)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < k < INT_MAX ⌝
      }}}
        findLock (rep_to_node curr) #k #lvl
      {{{ pred succ, RET ((rep_to_node pred), (rep_to_node succ));
        ⌜ node_key pred < k ≤ node_key succ ⌝
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth sub) (◯ {[ pred ]}))
        ∗
        (own (s_auth sub) (◯ {[ succ ]}) ∨ ⌜ succ = tail ⌝)
        ∗
        ∃ (γ: gname) (l: val) (s: loc), 
          (node_locks pred +ₗ lvl) ↦□ l
          ∗
          is_lock γ l (in_lock lvl osub pred)
          ∗
          (node_next pred +ₗ lvl) ↦{#1 / 2} #s
          ∗
          s ↦□ rep_to_node succ
          ∗
          locked_val osub s
          ∗
          locked γ
      }}}.
    Proof.
      iIntros (Φ) "(#Hinv & Hown_curr & Hrange) HΦ".
      iRevert (curr) "Hown_curr Hrange".
      iLöb as "IH". 
      iIntros (curr) "#Hown_curr %Hrange".
      
      wp_lam. wp_pures.
      wp_apply (find_sub_spec with "[Hown_curr]").
      { by iFrame "#". }
      iIntros (pred succ') "(%Hrange' & #Hown_pred & _ & Hlock)".
      iDestruct "Hlock" as (γ l) "(#Hl & #Hlock)".
      wp_pures. wp_lam. wp_pures.

      wp_load. wp_let.
      wp_bind (acquire _).
      iApply (acquire_spec with "Hlock").
      iNext; iIntros "(Hlocked & Hin_lock)".
      iDestruct "Hin_lock" as (s) "(Hnext & Hval)".

      wp_pures. wp_lam. wp_pures.
      wp_bind (Load #(node_next pred +ₗ lvl)).
      iInv (levelN lvl) as (M S L) "(Hinv_sub & Hmatch)" "Hclose".
      iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >Hown_auth & >Hown_toks & Hlist)".

      iMod (own_update with "Hown_auth") as "[Hown_auth Hown_frag]".
      { by apply auth_update_alloc, (gset_local_update S _ S). }

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

      rewrite list_equiv_invert; last done.
      iDestruct "Hlist" as (γ' l' s' succ) "(>%Hsucc_range & >Hpt & >#Hs' & _ & _ & Himp)".
      rewrite -elem_of_list_In Hperm elem_of_elements in Hsucc_range.
      iDestruct (mapsto_agree with "Hpt Hnext") as %Hs.
      inversion Hs; subst.

      iAssert (own (s_auth sub) (◯ {[succ]}) ∨ ⌜ succ = tail ⌝)%I
        with "[Hown_frag]" as "#Hown_succ".
      {
        destruct Hsucc_range as [Hin|Heq]; last by iRight.
        assert (S = S ⋅ {[ succ ]}) as -> by set_solver.
        iDestruct "Hown_frag" as "(? & ?)"; iLeft; iFrame.
      }

      wp_load.
      iPoseProof ("Himp" with "Hpt") as "Hlist".
      iMod ("Hclose" with "[Hmatch Hlist Hown_auth Hown_toks]") as "_".
      { iNext; iExists M, S, L; by iFrame. }

      iModIntro. wp_load.
      wp_let. wp_lam. wp_pures.
      case_bool_decide as Hle; wp_if.
      + wp_pures; iModIntro.
        iApply "HΦ"; iFrame "# ∗".
        iSplit; first by (iPureIntro; lia).
        iExists γ, l, s. iFrame "# ∗".
      + wp_apply (release_spec with "[Hnext Hval Hlocked]").
        { iFrame "# ∗"; iExists s; iFrame. }
        iIntros "_". wp_pures.

        iApply ("IH" with "HΦ [] [%]").
        {
          iRight.
          iDestruct "Hown_succ" as "[Hown|%Htail]"; first done.
          rewrite Htail /node_key/tail/= in Hle; lia.
        }
        { lia. }
    Qed.

  End Proofs.
End FindSpec.