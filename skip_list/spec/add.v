From Coq Require Import Sorting.Sorted.

From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc.
From SkipList.skip_list Require Import node_rep code key_equiv.
From SkipList.skip_list.inv Require Import list_equiv lazy_inv skip_inv.
From SkipList.skip_list.spec Require Import insert.


Local Open Scope Z.
Module AddSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Insert := InsertSpec Params.
  Import Insert.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ}.

    Theorem topLevel_spec (curr top_head: node_rep) (key h lvl: Z) (q: frac)
      (S: gset Z) (bot: bot_gname) (top_sub: sub_gname) (bot_subs: list sub_gname) :
      {{{
        skip_list_equiv top_head lvl q S bot (top_sub :: bot_subs)
        ∗
        (⌜ curr = top_head ⌝ ∨ own (s_auth top_sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
        ∗
        ⌜ 1 ≤ h ≤ lvl ⌝
      }}}
        topLevel (rep_to_node curr) #key #h #lvl
      {{{ curr' top_head' top_sub' bot_subs', RET SOMEV (rep_to_node curr');
        skip_list_equiv top_head' h q S bot (top_sub' :: bot_subs')
        ∗
        ( 
          skip_list_equiv top_head' h q (S ∪ {[ key ]}) bot (top_sub' :: bot_subs')
          -∗
          skip_list_equiv top_head lvl q (S ∪ {[ key ]}) bot (top_sub :: bot_subs)
        )
        ∗
        (⌜ curr' = top_head' ⌝ ∨ own (s_auth top_sub') (◯ {[ curr' ]}))
        ∗
        ⌜ node_key curr' < key < INT_MAX ⌝
      }}}.
    Proof.
      iIntros (Φ) "(Hlist & Hown_curr & Hcurr_range & Hh) HΦ".
      iRevert (curr top_head lvl top_sub bot_subs) "Hlist Hown_curr Hcurr_range Hh HΦ".
      iLöb as "IH".
      iIntros (curr top_head lvl top_sub bot_subs) "Hlist #Hown_curr %Hcurr_range %Hh HΦ".

      wp_lam. wp_let. wp_let. wp_let.

      rewrite skip_list_equiv_cons.
      iDestruct "Hlist" as (P obot) "(Hinv & Hlist)".
      wp_apply (find_sub_spec with "[Hinv]").
      { by iFrame "# ∗". }

      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & _)".
      wp_pures.
      case_bool_decide; wp_if.
      + assert (h = lvl) as <- by congruence.
        wp_pures. iModIntro.
        iApply "HΦ". iFrame "# ∗". 
        iSplit; last (iPureIntro; lia).
        iIntros "?"; iFrame.
      + assert (h ≠ lvl) by congruence.
        destruct bot_subs as [|bot_sub bot_subs].
        { iDestruct "Hlist" as "(%Hfalse & _)"; lia. }
        iDestruct "Hlist" as (l down) "(%Hlvl & #Hinv & %Hsome & Hpt & %Heq_key & Hmatch)".
        unfold is_top_list.

        wp_lam. wp_pures.
        destruct (node_down pred) as [d|] eqn:Hpred_down; wp_pures.
        - wp_bind (Load _).
          iInv (levelN lvl) as (S' Skeys L) "(Hinv_sub & _)" "Hclose".
          iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & Hown_toks & Hlist)".

          iDestruct "Hown_pred" as "[%Heq | #Hown_pred]".
          * assert (d = l) as -> by congruence.
            wp_load.
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists S', Skeys, L; by iFrame. }

            iModIntro; wp_pures.
            iApply ("IH" with "[$] [] [%] [%]").
            { by iLeft. }
            { rewrite -Heq_key -Heq; lia. }
            { lia. }

            iNext. 
            iIntros (curr' top_head' top_sub' bot_subs').
            iIntros "(Hlist & Himp & Hown_curr' & Hcurr_range')".
            iApply "HΦ". iFrame "# ∗".
            iIntros "Hlist".
            iPoseProof ("Himp" with "Hlist") as "Hlist".
            iExists l, down. by iFrame.
          * iDestruct (own_valid_2 with "Hown_auth Hown_pred") 
              as %[Hvalid%gset_included]%auth_both_valid_discrete.
            rewrite (list_equiv_invert_L L top_head pred); last first.
            { rewrite Hperm -elem_of_list_In elem_of_elements; set_solver. }

            iDestruct "Hlist" as (succ' ? ? l' ?) "(_ & _ & _ & Hpt' & _ & HP & Himp)".
            rewrite Hpred_down.
            iDestruct "HP" as (down') "(Hpt_down & >Hauth_down' & >Htoks_down' & >%Hdown'_key)".

            assert ({[ down' ]} = {[ down' ]} ⋅ {[ down' ]}) as -> by set_solver.
            iDestruct "Hauth_down'" as "(Hauth_down' & Hauth_down'_dup)".

            wp_load.
            iPoseProof ("Himp" with "[Hpt' Hpt_down Hauth_down' Htoks_down']") as "Hlist".
            { iFrame; iExists down'; by iFrame. }
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists S', Skeys, L; by iFrame. }

            iModIntro; wp_pures.
            iApply ("IH" with "[$] [$] [%] [%]").
            { lia. }
            { lia. }

            iNext. 
            iIntros (curr' top_head' top_sub' bot_subs').
            iIntros "(Hlist & Himp & Hown_curr' & Hcurr_range')".
            iApply "HΦ". iFrame "# ∗".
            iIntros "Hlist".
            iPoseProof ("Himp" with "Hlist") as "Hlist".
            iExists l, down. by iFrame.
        - iInv (levelN lvl) as (? ? L) "(Hinv_sub & _)" "_".
          iDestruct "Hinv_sub" as "(>%Hperm & _ & _ & >Hown_auth & _ & Hlist)".

          iDestruct "Hown_pred" as "[%Heq | #Hown_pred]"; first by congruence.
          iDestruct (own_valid_2 with "Hown_auth Hown_pred") 
            as %[Hvalid%gset_included]%auth_both_valid_discrete.
          rewrite (list_equiv_invert_L L top_head pred); last first.
          { rewrite Hperm -elem_of_list_In elem_of_elements; set_solver. }

          iDestruct "Hlist" as (? ? ? ? ?) "(_ & _ & _ & _ & _ & >HP & _)".
          rewrite Hpred_down; by iExFalso.
    Qed.

    Theorem addAll_spec (curr top_head: node_rep) (key lvl: Z) (q: frac)
      (S: gset Z) (bot: bot_gname) (top_sub: sub_gname) (bot_subs: list sub_gname) :
      INT_MIN < key < INT_MAX →
      {{{
        skip_list_equiv top_head lvl q S bot (top_sub :: bot_subs)
        ∗
        (⌜ curr = top_head ⌝ ∨ own (s_auth top_sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key ⌝
      }}}
        addAll (rep_to_node curr) #key
      {{{ v new, RET v;
        skip_list_equiv top_head lvl q (S ∪ {[ key ]}) bot (top_sub :: bot_subs)
        ∗
        ( 
          ⌜ v = NONEV ⌝ ∨ 
          ( 
            ⌜ v = SOMEV (rep_to_node new) ⌝ 
            ∗ 
            own (s_auth top_sub) (◯ {[ new ]})
            ∗ 
            own (s_toks top_sub) (GSet {[ node_key new ]})
            ∗ 
            own (s_keys bot) (GSet {[ node_key new ]})
            ∗ 
            ⌜ node_key new = key ⌝
          )
        )
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(Hlist & Hown_curr & Hrange) HΦ".
      iRevert (Φ curr top_head lvl top_sub bot_subs) "Hlist Hown_curr Hrange HΦ".
      iLöb as "IH".
      iIntros (Φ curr top_head lvl top_sub bot_subs) "Hlist #Hown_curr %Hrange HΦ".

      wp_lam. wp_let.
      iPoseProof (skip_list_equiv_cons with "Hlist") as (P obot) "(Hinv & Hlist)".
      wp_apply (find_sub_spec with "[Hinv]").
      { iFrame "# ∗". iPureIntro; lia. }

      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & _)".
      wp_pures. wp_lam. wp_pures.

      destruct bot_subs as [|bot_sub bot_subs].
      + iDestruct "Hlist" as "(%Hlvl & Hbot & %Hnone)".
        iDestruct "Hbot" as (Sfrac) "(%Hequiv & Hown_frag & #Hinv)".
        destruct (node_down pred) as [d|] eqn:Hpred_down; wp_pures.
        - wp_bind (Load _).
          iInv (levelN lvl) as (? Skeys L) "(Hinv_sub & _)" "_".
          iDestruct "Hinv_sub" as "(>%Hperm & _ & _ & >Hown_auth & _ & Hlist)".

          iDestruct "Hown_pred" as "[%Heq | #Hown_pred]"; first by congruence.
          iDestruct (own_valid_2 with "Hown_auth Hown_pred") 
            as %[Hvalid%gset_included]%auth_both_valid_discrete.
          rewrite (list_equiv_invert_L L top_head pred); last first.
          { rewrite Hperm -elem_of_list_In elem_of_elements; set_solver. }

          iDestruct "Hlist" as (? ? ? ? ?) "(_ & _ & _ & _ & _ & >HP & _)".
          rewrite Hpred_down; by iExFalso.
        - wp_apply (tryInsert_spec with "[Hown_frag]").
          { done. }
          { iFrame "#". iSplit; last (iPureIntro; lia). iExists Sfrac; by iFrame. }

          iIntros (v new) "(Hbot & Hopt)".
          iApply "HΦ". iFrame "# ∗".
          iSplit; first done. iSplit; last done.
          iDestruct "Hbot" as (Sfrac') "(Hequiv' & Hown_frac' & _)".
          iExists Sfrac'. iFrame.         
      + iDestruct "Hlist" as (l down) "(%Hlvl & #Hinv & %Hsome & Hpt & %Heq_key & Hmatch)".
        unfold is_top_list.
        destruct (node_down pred) as [d|] eqn:Hpred_down; wp_match.
        - wp_bind (Load _).
          iInv (levelN lvl) as (S' Skeys L) "(Hinv_sub & _)" "Hclose".
          iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & Hown_toks & Hlist)".
          iDestruct "Hown_pred" as "[%Heq | #Hown_pred]".
          * assert (d = l) as -> by congruence.
            wp_load.
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists S', Skeys, L; by iFrame. }

            iModIntro; wp_pures.
            wp_apply ("IH" with "[$] [] [%]").
            { by iLeft. }
            { rewrite -Heq_key -Heq; lia. }

            iIntros (v new) "(Hlist & Hopt)".
            iDestruct "Hopt" as "[%Hopt | (%Hopt & Hown_new & Hown_tok & Hown_key & %Hkey)]".
            ++ rewrite Hopt. wp_pures.
               iModIntro. iApply "HΦ".
               iFrame "# ∗".
               iSplitR ""; last by iLeft.
               iExists l, down. by iFrame.
               Unshelve. auto.
            ++ rewrite Hopt. wp_pures.
               wp_apply (insert_spec with "[Hown_new Hown_tok]").
               { done. }
               { 
                 iFrame "# ∗".
                 iSplit; first by iLeft.
                 iPureIntro; lia.
               }

               iIntros (new') "(Hown_new & Hown_tok & %Hkey')".
               rewrite Hkey -Hkey'.
               iApply "HΦ". iFrame "# ∗".
               iSplitR "Hown_new Hown_tok Hown_key"; last first.
               { iRight; by iFrame. }
               iExists l, down. by iFrame.
          * iDestruct (own_valid_2 with "Hown_auth Hown_pred") 
              as %[Hvalid%gset_included]%auth_both_valid_discrete.
            rewrite (list_equiv_invert_L L top_head pred); last first.
            { rewrite Hperm -elem_of_list_In elem_of_elements; set_solver. }

            iDestruct "Hlist" as (succ' ? ? l' ?) "(_ & _ & _ & Hpt' & _ & HP & Himp)".
            rewrite Hpred_down.
            iDestruct "HP" as (down') "(Hpt_down & >Hauth_down' & >Htoks_down' & >%Hdown'_key)".

            assert ({[ down' ]} = {[ down' ]} ⋅ {[ down' ]}) as -> by set_solver.
            iDestruct "Hauth_down'" as "(Hauth_down' & Hauth_down'_dup)".

            wp_load.
            iPoseProof ("Himp" with "[Hpt' Hpt_down Hauth_down' Htoks_down']") as "Hlist".
            { iFrame; iExists down'; by iFrame. }
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists S', Skeys, L; by iFrame. }

            iModIntro; wp_pures.
            wp_apply ("IH" with "[$] [$] [%]").
            { lia. }

            iIntros (v new) "(Hlist & Hopt)".
            iDestruct "Hopt" as "[%Hopt | (%Hopt & Hown_new & Hown_tok & Hown_key & %Hkey)]".
            ++ rewrite Hopt. wp_pures.
               iModIntro. iApply "HΦ".
               iFrame "# ∗".
               iSplitR ""; last by iLeft.
               iExists l, down. by iFrame.
            ++ rewrite Hopt. wp_pures.
               wp_apply (insert_spec with "[Hown_new Hown_tok]").
               { done. }
               { iFrame "# ∗". iPureIntro; lia. }

               iIntros (new') "(Hown_new & Hown_tok & %Hkey')".
               rewrite Hkey -Hkey'.
               iApply ("HΦ" $! _ new'). iFrame "# ∗".
               iSplitR "Hown_new Hown_tok Hown_key"; last first.
               { iRight; by iFrame. }
               iExists l, down. by iFrame.
        - iAssert (|={⊤}=> False)%I as "Hfalse"; last by iMod "Hfalse".
          iInv (levelN lvl) as (? Skeys L) "(Hinv_sub & _)" "_".
          iDestruct "Hinv_sub" as "(>%Hperm & _ & _ & >Hown_auth & _ & Hlist)".
        
          iDestruct "Hown_pred" as "[%Heq | #Hown_pred]"; first by congruence.
          iDestruct (own_valid_2 with "Hown_auth Hown_pred") 
            as %[Hvalid%gset_included]%auth_both_valid_discrete.
          rewrite (list_equiv_invert_L L top_head pred); last first.
          { rewrite Hperm -elem_of_list_In elem_of_elements; set_solver. }

          iDestruct "Hlist" as (? ? ? ? ?) "(_ & _ & _ & _ & _ & >HP & _)".
          by rewrite Hpred_down.
    Qed.

    Theorem add_spec (v: val) (key height: Z) (q: frac)
      (S: gset Z) (bot: bot_gname) (subs: list sub_gname)
      (Hrange: INT_MIN < key < INT_MAX) 
      (Hheight: 1 ≤ height ≤ MAX_HEIGHT):
      {{{ is_skip_list v q S bot subs }}}
        add v #key #height
      {{{ (b: bool), RET #b; 
        is_skip_list v q (S ∪ {[ key ]}) bot subs
      }}}.
    Proof.
      iIntros (Φ) "H HΦ".
      iDestruct "H" as (h head) "(%Hv & Hpt & %Hmin & Hlist)".

      wp_lam. wp_let. wp_let.
      rewrite -Hv. wp_load.

      destruct subs as [|sub subs]; first by iExFalso.
      wp_apply (topLevel_spec  with "[Hlist]").
      { iFrame. iSplit; first by iLeft. iPureIntro; lia. }

      iIntros (curr top_head top_sub bot_subs).
      iIntros "(Hlist & Himp & #Hown_curr & %Hcurr_range)".
      wp_let. wp_match.

      wp_apply (addAll_spec with "[Hlist]").
      { done. }
      { iFrame "# ∗". iPureIntro; lia. }

      iIntros (n new) "(Hlist & Hopt)".
      iPoseProof ("Himp" with "Hlist") as "Hlist".
      wp_let.

      iDestruct "Hopt" as "[%Hnone | (%Hsome & Hown_new & Hown_tok & Hown_key & %Heq_key)]".
      + rewrite Hnone. wp_match.
        iModIntro. iApply "HΦ".
        iExists h, head. by iFrame.
      + rewrite Hsome. wp_match.
        iModIntro. iApply "HΦ".
        iExists h, head. by iFrame.
    Qed.

  End Proofs.
End AddSpec.