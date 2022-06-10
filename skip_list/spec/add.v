From Coq Require Import Sorting.Sorted.

From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc.
From SkipList.skip_list Require Import node_rep code key_equiv.
From SkipList.skip_list.inv Require Import lazy_inv skip_inv.
From SkipList.skip_list.spec Require Import insert.


Local Open Scope Z.
Module AddSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Insert := InsertSpec Params.
  Import Insert.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ}.

    Theorem topLevel_spec (curr top_head: node_rep) (key h lvl: Z) (q: frac)
      (Stop: gset Z) (Sbots: list (gset Z)) 
      (top: lazy_gname) (bots: list lazy_gname) :
      {{{ 
        skip_list_equiv top_head lvl q (Stop :: Sbots) (top :: bots)
        ∗
        (⌜ curr = top_head ⌝ ∨ own (s_auth top) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
        ∗
        ⌜ 1 ≤ h ≤ lvl ⌝
      }}}
        topLevel (rep_to_node curr) #key #h #lvl
      {{{ curr' top_head' Stops Stop' Sbots' tops top' bots', RET SOMEV (rep_to_node curr');
        ⌜ Stop :: Sbots = Stops ++ (Stop' :: Sbots') ⌝
        ∗
        ⌜ top :: bots = tops ++ (top' :: bots') ⌝
        ∗
        level_range top_head lvl (h + 1) q Stops tops top'
        ∗
        skip_list_equiv top_head' h q (Stop' :: Sbots') (top' :: bots')
        ∗
        (⌜ curr' = top_head' ⌝ ∨ own (s_auth top') (◯ {[ curr' ]}))
        ∗
        ⌜ node_key curr' < key < INT_MAX ⌝
      }}}.
    Proof.
      iIntros (Φ) "(Hlist & Hown_curr & Hrange & Hh) HΦ".
      iRevert (curr top_head lvl Stop Sbots top bots) "Hlist Hown_curr Hrange Hh HΦ".
      iLöb as "IH".
      iIntros (curr top_head lvl Stop Sbots top bots) "Hlist #Hown_curr %Hrange %Hh HΦ".

      wp_lam. wp_let. wp_let. wp_let.

      rewrite skip_list_equiv_cons.
      iDestruct "Hlist" as (P) "(Hinv & Hlist)".
      wp_apply (find_frac_spec with "[Hinv]").
      { by iFrame "# ∗". }

      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & _)".
      wp_pures.
      case_bool_decide; wp_if.
      + assert (h = lvl) as <- by congruence.
        wp_pures. iModIntro.
        iApply ("HΦ" $! _ _ nil _ _ nil _ _).
        iFrame "# ∗". iPureIntro. 
        do 2 (split; first done). lia.
      + assert (h ≠ lvl) by congruence.
        destruct Sbots as [|Sbot Sbots]; destruct bots as [|bot bots]; try by iExFalso.
        { iDestruct "Hlist" as "(%Hfalse & _)"; lia. }
        iDestruct "Hlist" as (l down) "(%Hlvl & Hlazy & %Hsome & Hpt & %Heq_key & Hmatch)".
        iDestruct "Hlazy" as (Sfrac) "(%Hequiv & Hown_frag & #Hinv)".

        wp_lam. wp_pures.
        destruct (node_down pred) as [d|] eqn:Hpred_down; wp_pures.
        - wp_bind (Load _).
          iInv (levelN lvl) as (S Skeys L) "(>%Hperm & >%Hsort & >%Hequiv' & >Hown_auth & >Hown_frac & Hown_toks & Hlist)" "Hclose".

          iDestruct "Hown_pred" as "[%Heq | #Hown_pred]".
          * assert (d = l) as -> by congruence.
            wp_load.
            iMod ("Hclose" with "[Hlist Hown_auth Hown_frac Hown_toks]") as "_".
            { iNext; iExists S, Skeys, L; by iFrame. }

            iModIntro; wp_pures.
            iApply ("IH" with "[$] [] [%] [%]").
            { by iLeft. }
            { rewrite -Heq_key -Heq; lia. }
            { lia. }

            iNext. 
            iIntros (curr' top_head' Stops Stop' Sbots' tops top' bots').
            iIntros "(%HSbot_eq & %Hbot_eq & Hlvl_range & Hlist & Hown_curr')".
            iApply "HΦ". iFrame "# ∗". 
            iSplit; first rewrite HSbot_eq app_comm_cons //.
            iSplit; first rewrite Hbot_eq app_comm_cons //.
            destruct Stops; destruct tops; try by iExFalso.
            ++ iDestruct "Hlvl_range" as %Hlvl_range.
               inversion Hbot_eq; subst.
               iExists l, down. iFrame "# ∗". 
               iSplit; first (iPureIntro; lia).
               iSplit; last done. 
               iExists Sfrac. by iFrame.
            ++ iAssert ⌜ lvl - 1 >= h + 1 ⌝%I with "[Hlvl_range]" as %Hge.
               {
                 destruct Stops; destruct tops; try by iExFalso.
                 + iDestruct "Hlvl_range" as (? ?) "(%Hlvl_eq & _)". 
                   iPureIntro; lia.
                 + iDestruct "Hlvl_range" as (? ?) "(%Hlvl_gt & _)".
                   iPureIntro; lia.
               }
               inversion Hbot_eq; subst.
               iExists l, down. iFrame "# ∗".
               iSplit; first (iPureIntro; lia).
               iSplit; last done.
               iExists Sfrac. by iFrame.
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
            iMod ("Hclose" with "[Hlist Hown_auth Hown_frac Hown_toks]") as "_".
            { iNext; iExists S, Skeys, L; by iFrame. }

            iModIntro; wp_pures.
            iApply ("IH" with "[$] [$] [%] [%]").
            { lia. }
            { lia. }

            iNext. 
            iIntros (curr' top_head' Stops Stop' Sbots' tops top' bots').
            iIntros "(%HSbot_eq & %Hbot_eq & Hlvl_range & Hlist & Hown_curr')".
            iApply "HΦ". iFrame "# ∗". 
            iSplit; first rewrite HSbot_eq app_comm_cons //.
            iSplit; first rewrite Hbot_eq app_comm_cons //.
            destruct Stops; destruct tops; try by iExFalso.
            ++ iDestruct "Hlvl_range" as %Hlvl_range.
               inversion Hbot_eq; subst.
               iExists l, down. iFrame "# ∗". 
               iSplit; first (iPureIntro; lia).
               iSplit; last done. 
               iExists Sfrac. by iFrame.
            ++ iAssert ⌜ lvl - 1 >= h + 1 ⌝%I with "[Hlvl_range]" as %Hge.
               {
                 destruct Stops; destruct tops; try by iExFalso.
                 + iDestruct "Hlvl_range" as (? ?) "(%Hlvl_eq & _)". 
                   iPureIntro; lia.
                 + iDestruct "Hlvl_range" as (? ?) "(%Hlvl_gt & _)".
                   iPureIntro; lia.
               }
               inversion Hbot_eq; subst.
               iExists l, down. iFrame "# ∗".
               iSplit; first (iPureIntro; lia).
               iSplit; last done.
               iExists Sfrac. by iFrame.
        - iInv (levelN lvl) as (S Skeys L) "(>%Hperm & _ & _ & >Hown_auth & _ & _ & Hlist)" "_".

          iDestruct "Hown_pred" as "[%Heq | #Hown_pred]"; first by congruence.
          iDestruct (own_valid_2 with "Hown_auth Hown_pred") 
            as %[Hvalid%gset_included]%auth_both_valid_discrete.
          rewrite (list_equiv_invert_L L top_head pred); last first.
          { rewrite Hperm -elem_of_list_In elem_of_elements; set_solver. }

          iDestruct "Hlist" as (? ? ? ? ?) "(_ & _ & _ & _ & _ & >HP & _)".
          rewrite Hpred_down; by iExFalso.
    Qed.

    Fixpoint add_key (L: list (gset Z)) (key: Z) : list (gset Z) :=
      match L with
      | nil => nil
      | Stop :: Sbots => (Stop ∪ {[ key ]}) :: (add_key Sbots key)
      end.

    Theorem addAll_spec (curr top_head: node_rep) (key lvl: Z) (q: frac)
      (Stop: gset Z) (Sbots: list (gset Z)) 
      (top: lazy_gname) (bots: list lazy_gname) :
      INT_MIN < key < INT_MAX →
      {{{
        skip_list_equiv top_head lvl q (Stop :: Sbots) (top :: bots)
        ∗
        (⌜ curr = top_head ⌝ ∨ own (s_auth top) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key ⌝
      }}}
        addAll (rep_to_node curr) #key
      {{{ v new, RET v;
        (
          ⌜ v = NONEV ⌝
          ∗
          skip_list_equiv top_head lvl q (Stop :: Sbots) (top :: bots)
        )
        ∨ 
        (
          ⌜ v = SOMEV (rep_to_node new) ⌝
          ∗ 
          own (s_auth top) (◯ {[ new ]})
          ∗ 
          own (s_toks top) (GSet {[ node_key new ]})
          ∗ 
          ⌜ node_key new = key ⌝
          ∗
          skip_list_equiv top_head lvl q (add_key (Stop :: Sbots) key) (top :: bots)
        )
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(Hlist & Hown_curr & Hrange) HΦ".
      iRevert (Φ curr top_head lvl Stop Sbots top bots) "Hlist Hown_curr Hrange HΦ".
      iLöb as "IH".
      iIntros (Φ curr top_head lvl Stop Sbots top bots) "Hlist #Hown_curr %Hrange HΦ".

      wp_lam. wp_let.
      iPoseProof (skip_list_equiv_cons with "Hlist") as (P) "(Hinv & Hlist)".
      wp_apply (find_frac_spec with "[Hinv]").
      { iFrame "# ∗". iPureIntro; lia. }

      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & _)".
      wp_pures. wp_lam. wp_pures.

      destruct Sbots as [|Sbot Sbots]; destruct bots as [|bot bots]; try by iExFalso.
      + iDestruct "Hlist" as "(%Hlvl & Hlazy & %Hnone)".
        iDestruct "Hlazy" as (Sfrac) "(%Hequiv & Hown_frag & #Hinv)".
        destruct (node_down pred) as [d|] eqn:Hpred_down; wp_pures.
        - wp_bind (Load _).
          iInv (levelN lvl) as (S Skeys L) "(>%Hperm & _ & _ & >Hown_auth & _ & _ & Hlist)" "_".

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

          iIntros (v new) "(Hlazy & Hopt)".
          iApply "HΦ".
          iDestruct "Hopt" as "[Hnone | (? & ? & ? & ?)]".
          * iLeft. iFrame "# ∗".
            admit.
          * iRight. by iFrame.          
      + iDestruct "Hlist" as (l down) "(%Hlvl & Hlazy & %Hsome & Hpt & %Heq_key & Hmatch)".
        iDestruct "Hlazy" as (Sfrac) "(%Hequiv & Hown_frag & #Hinv)".
        destruct (node_down pred) as [d|] eqn:Hpred_down; wp_match.
        - wp_bind (Load _).
          iInv (levelN lvl) as (S Skeys L) "(>%Hperm & >%Hsort & >%Hequiv' & >Hown_auth & >Hown_frac & >Hown_toks & Hlist)" "Hclose".
          iDestruct "Hown_pred" as "[%Heq | #Hown_pred]".
          * assert (d = l) as -> by congruence.
            wp_load.
            iMod ("Hclose" with "[Hlist Hown_auth Hown_frac Hown_toks]") as "_".
            { iNext; iExists S, Skeys, L; by iFrame. }

            iModIntro; wp_pures.
            wp_apply ("IH" with "[$] [] [%]").
            { by iLeft. }
            { rewrite -Heq_key -Heq; lia. }

            iIntros (v new) "Hopt".
            iDestruct "Hopt" as "[(%Hopt & ?) | (%Hopt & Hown_new & Hown_tok & %Hkey & ?)]".
            ++ rewrite Hopt. wp_pures.
               iModIntro. iApply "HΦ".
               iLeft. iSplit; first done.
               iFrame "# ∗". iExists l, down. iFrame. 
               iSplit; first done. iSplit; last done.
               iExists Sfrac. by iFrame.
            ++ rewrite Hopt. wp_pures.
               wp_apply (insert_spec with "[Hown_frag Hown_new Hown_tok]"); auto.
               { 
                 iFrame "# ∗".
                 iSplit; last first.
                 { iSplit; first by iLeft. iSplit; last done. iPureIntro; lia. }
                 iExists Sfrac; by iFrame.
               }

               clear Hkey Hopt new.
               iIntros (new) "(Hlazy & Hown_new & Hown_tok & %Hkey)".
               iApply "HΦ". iRight.
               iFrame. iSplit; first done. iSplit; first done.
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
            iMod ("Hclose" with "[Hlist Hown_auth Hown_frac Hown_toks]") as "_".
            { iNext; iExists S, Skeys, L; by iFrame. }

            iModIntro; wp_pures.
            wp_apply ("IH" with "[$] [$] [%]").
            { lia. }

            iIntros (v new) "Hopt".
            iDestruct "Hopt" as "[(%Hopt & ?) | (%Hopt & Hown_new & Hown_tok & %Hkey & ?)]".
            ++ rewrite Hopt. wp_pures.
               iModIntro. iApply "HΦ".
               iLeft. iSplit; first done.
               iFrame "# ∗". iExists l, down. iFrame. 
               iSplit; first done. iSplit; last done.
               iExists Sfrac. by iFrame.
            ++ rewrite Hopt. wp_pures.
               wp_apply (insert_spec with "[Hown_frag Hown_new Hown_tok]"); auto.
               { 
                 iFrame "# ∗".
                 iSplit; last first.
                 { iSplit; last done. iPureIntro; lia. }
                 iExists Sfrac; by iFrame.
               }

               clear Hkey Hopt new.
               iIntros (new) "(Hlazy & Hown_new & Hown_tok & %Hkey)".
               iApply "HΦ". iRight.
               iFrame. iSplit; first done. iSplit; first done.
               iExists l, down. by iFrame.
        - iAssert (|={⊤}=> False)%I as "Hfalse"; last by iMod "Hfalse".
          iInv (levelN lvl) as (S Skeys L) "(>%Hperm & _ & _ & >Hown_auth & _ & _ & Hlist)" "_".
        
          iDestruct "Hown_pred" as "[%Heq | #Hown_pred]"; first by congruence.
          iDestruct (own_valid_2 with "Hown_auth Hown_pred") 
            as %[Hvalid%gset_included]%auth_both_valid_discrete.
          rewrite (list_equiv_invert_L L top_head pred); last first.
          { rewrite Hperm -elem_of_list_In elem_of_elements; set_solver. }

          iDestruct "Hlist" as (? ? ? ? ?) "(_ & _ & _ & _ & _ & >HP & _)".
          by rewrite Hpred_down.
    Admitted.

  End Proofs.
End AddSpec.