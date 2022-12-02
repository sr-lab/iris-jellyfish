From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.skip_list.lists Require Import code.
From SkipList.lib Require Import misc node_rep node_lt.
From SkipList.skip_list.lists.inv Require Import list_equiv lazy_inv skip_inv.
From SkipList.skip_list.lists.spec Require Import insert.


Local Open Scope Z.

Module AddSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Insert := InsertSpec Params.
  Export Insert.

  Section Proofs.
    Context `{!heapGS Σ, !skipGS Σ, !lockG Σ}.

    Theorem findLevel_spec (k h lvl: Z) (head curr: node_rep) 
      (Skeys: gset Z) (q: frac) (bot: bot_gname) 
      (Γ: sub_gname) (subs: list sub_gname) :
      {{{
        skip_list_equiv lvl head Skeys q bot (Γ :: subs)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth Γ) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < k < INT_MAX ⌝
        ∗
        ⌜ 0 ≤ h ≤ lvl ⌝
      }}}
        findLevel (rep_to_node curr) #k #lvl #h
      {{{ curr' head' Γ' subs', RET rep_to_node curr';
        ⌜ Γ' = nth (Z.to_nat (lvl - h)) (Γ :: subs) Γ' ⌝
        ∗
        skip_list_equiv h head' Skeys q bot (Γ' :: subs')
        ∗
        (⌜ curr' = head' ⌝ ∨ own (s_auth Γ') (◯ {[ curr' ]}))
        ∗
        ⌜ node_key curr' < k < INT_MAX ⌝
        ∗
        ( 
          skip_list_equiv h head' (Skeys ∪ {[ k ]}) q bot (Γ' :: subs')
          -∗
          skip_list_equiv lvl head (Skeys ∪ {[ k ]}) q bot (Γ :: subs)
        )
      }}}.
    Proof.
      iIntros (Φ) "(Hlist & Hown_curr & Hcurr_range & Hh) HΦ".
      iRevert (curr head lvl Γ subs) "Hlist Hown_curr Hcurr_range Hh HΦ".
      iLöb as "IH".
      iIntros (curr head lvl Γ subs) "Hlist #Hown_curr %Hcurr_range %Hh HΦ".

      wp_lam. wp_pures.

      rewrite skip_list_equiv_cons.
      iDestruct "Hlist" as (obot osub) "(Hinv & Hlist)".
      wp_apply (find_sub_spec with "[Hinv]").
      { by iFrame "# ∗". }

      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & _)".
      wp_pures.
      case_bool_decide as Hcase; wp_if.
      + inversion Hcase; subst. 
        iModIntro; iApply "HΦ". 
        iFrame "# ∗". 
        iSplit; first (iPureIntro; by assert (h - h = 0) as -> by lia).
        iSplit; first (iPureIntro; lia).
        iIntros "?"; iFrame.
      + assert (h ≠ lvl) by congruence.
        destruct subs as [|γ subs].
        { iDestruct "Hlist" as "(%Hfalse & _)"; lia. }
        iDestruct "Hlist" as (l down) "(%Hlvl & #Hinv & %Hsome & Hpt & %Heq_key & Hmatch)"; unfold is_sub_list.

        wp_lam. wp_pures.
        destruct (node_down pred) as [d|] eqn:Hpred_down; wp_pures.
        - wp_bind (Load _).
          iInv (levelN lvl) as (S L) "(Hinv_sub & _)" "Hclose".
          iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >Hown_auth & >Hown_toks & Hlist)".

          iDestruct "Hown_pred" as "[%Heq | #Hown_pred]".
          * assert (d = l) as -> by congruence.
            wp_load.
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists S, L; by iFrame. }
            iModIntro; wp_pures.
            
            iApply ("IH" with "Hmatch [] [%] [%]").
            { by iLeft. }
            { rewrite -Heq_key -Heq; lia. }
            { lia. }

            iNext. 
            iIntros (curr' head' Γ' subs').
            iIntros "(%Hnth & Hlist & Hown_curr' & Hcurr_range' & Himp)".
            iApply "HΦ". iFrame "# ∗".
            iSplit; first by assert (Z.to_nat (lvl - h) = Datatypes.S (Z.to_nat (lvl - 1 - h))) as -> by lia.
            iIntros "Hlist".
            iPoseProof ("Himp" with "Hlist") as "Hlist".
            iExists l, down. by iFrame.
          * iDestruct (own_valid_2 with "Hown_auth Hown_pred") 
              as %[Hvalid%gset_included]%auth_both_valid_discrete.

            rewrite (list_equiv_invert_L _ _ pred); last first.
            { rewrite Hperm -elem_of_list_In elem_of_elements; set_solver. }

            iDestruct "Hlist" as (? ?) "(_ & Hpt' & _ & Hnode & Himp)".
            rewrite Hpred_down.
            iDestruct "Hnode" as (down') "(Hpt_down & >Hauth_down' & >Htoks_down' & >%Hdown'_key)".
            assert ({[ down' ]} = {[ down' ]} ⋅ {[ down' ]}) as -> by set_solver.
            iDestruct "Hauth_down'" as "(Hauth_down' & Hauth_down'_dup)".

            wp_load.
            iPoseProof ("Himp" with "[Hpt' Hpt_down Hauth_down' Htoks_down']") as "Hlist".
            { iFrame; iExists down'; by iFrame. }
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists S, L; by iFrame. }
            iModIntro; wp_pures.

            iApply ("IH" with "Hmatch [$] [%] [%]").
            { lia. }
            { lia. }

            iNext. 
            iIntros (curr' head' Γ' subs').
            iIntros "(%Hnth & Hlist & Hown_curr' & Hcurr_range' & Himp)".
            iApply "HΦ". iFrame "# ∗".
            iSplit; first by assert (Z.to_nat (lvl - h) = Datatypes.S (Z.to_nat (lvl - 1 - h))) as -> by lia.
            iIntros "Hlist".
            iPoseProof ("Himp" with "Hlist") as "Hlist".
            iExists l, down. by iFrame.
        - iInv (levelN lvl) as (? L) "(Hinv_sub & _)" "_".
          iDestruct "Hinv_sub" as "(>%Hperm & _ & >Hown_auth & _ & Hlist)".

          iDestruct "Hown_pred" as "[%Heq | #Hown_pred]"; first by congruence.
          iDestruct (own_valid_2 with "Hown_auth Hown_pred") 
            as %[Hvalid%gset_included]%auth_both_valid_discrete.
          rewrite (list_equiv_invert_L _ _ pred); last first.
          { rewrite Hperm -elem_of_list_In elem_of_elements; set_solver. }

          iDestruct "Hlist" as (? ?) "(_ & _ & _ & >? & _)".
          rewrite Hpred_down; by iExFalso.
    Qed.

    Theorem insertAll_spec (k lvl: Z) (head curr: node_rep) 
      (Skeys: gset Z) (q: frac) (bot: bot_gname) 
      (Γ: sub_gname) (subs: list sub_gname) :
      INT_MIN < k < INT_MAX →
      {{{
        skip_list_equiv lvl head Skeys q bot (Γ :: subs)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth Γ) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < k ⌝
      }}}
        insertAll (rep_to_node curr) #k
      {{{ v new, RET v;
        skip_list_equiv lvl head (Skeys ∪ {[ k ]}) q bot (Γ :: subs)
        ∗
        ( 
          ⌜ v = NONEV ⌝ ∨ 
          ( 
            ⌜ v = SOMEV (rep_to_node new) ⌝ 
            ∗ 
            own (s_auth Γ) (◯ {[ new ]})
            ∗ 
            own (s_toks Γ) (◯ GSet {[ node_key new ]})
            ∗ 
            ⌜ node_key new = k ⌝
          )
        )
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(Hlist & Hown_curr & Hrange) HΦ".
      iRevert (Φ curr head lvl Γ subs) "Hlist Hown_curr Hrange HΦ".
      iLöb as "IH".
      iIntros (Φ curr head lvl Γ subs) "Hlist #Hown_curr %Hrange HΦ".
      wp_lam. wp_let.
      wp_lam. wp_pures.

      destruct subs as [|γ subs].
      + iDestruct "Hlist" as "(%Hlvl & (Hown_frag & #Hinv) & %Hnone)".
        destruct (node_down curr) as [d|] eqn:Hcurr_down; wp_match.
        - wp_bind (Load _).
          iInv (levelN lvl) as (? L) "(Hinv_sub & _)" "_".
          iDestruct "Hinv_sub" as "(>%Hperm & _ & >Hown_auth & _ & Hlist)".

          iDestruct "Hown_curr" as "[%Heq | #Hown_curr]"; first by congruence.
          iDestruct (own_valid_2 with "Hown_auth Hown_curr") 
            as %[Hvalid%gset_included]%auth_both_valid_discrete.
          rewrite (list_equiv_invert_L _ _ curr); last first.
          { rewrite Hperm -elem_of_list_In elem_of_elements; set_solver. }

          iDestruct "Hlist" as (? ?) "(_ & _ & _ & >? & _)".
          rewrite Hcurr_down; by iExFalso.
        - wp_apply (tryInsert_spec with "[Hown_frag]").
          { done. }
          { iFrame "# ∗". iPureIntro; lia. }

          iIntros (v new) "(Hbot & Hopt)".
          iApply "HΦ". by iFrame "# ∗".
      + iPoseProof (skip_list_equiv_cons_down with "Hlist") as (l' down' obot osub) "(%Hsome' & Hl' & Hinv' & Hlist)".
        iDestruct "Hlist" as (l down) "(%Hlvl & #Hinv & %Hsome & Hpt & %Heq_key & Hmatch)"; unfold is_sub_list.
        assert (l = l') as <- by congruence.
        iDestruct (mapsto_agree with "Hpt Hl'") as %<-%rep_to_node_inj; iClear "Hl'".

        destruct (node_down curr) as [d|] eqn:Hcurr_down; wp_match.
        - wp_bind (Load _).
          iInv (levelN lvl) as (S L) "(Hinv_sub & _)" "Hclose".
          iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >Hown_auth & >Hown_toks & Hlist)".
          iDestruct "Hown_curr" as "[%Heq | #Hown_curr]".
          * assert (d = l) as -> by congruence.
            wp_load.
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists S, L; by iFrame. }
            iModIntro.

            wp_apply (find_sub_spec with "[Hinv']").
            { iFrame "Hinv'". iSplit; first by iLeft. iPureIntro; subst; lia. }
            iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & _)".
            wp_pures.

            wp_apply ("IH" with "[$] [$] [%]").
            { lia. }

            iIntros (v new) "(Hlist & Hopt)".
            iDestruct "Hopt" as "[%Hopt | (%Hopt & Hown_new & Hown_tok & %Hkey)]".
            ++ rewrite Hopt; wp_pures.
               iModIntro. iApply "HΦ".
               iFrame "# ∗".
               iSplitR ""; last by iLeft.
               iExists l, down. by iFrame.
               Unshelve. done.
            ++ rewrite Hopt; wp_pures.
               wp_apply (insert_spec with "[Hown_new Hown_tok]").
               { rewrite Hkey //. }
               { 
                 iFrame "# ∗".
                 iSplit; first by iLeft.
                 iPureIntro; lia.
               }

               iIntros (new') "(Hown_new & Hown_tok & %Hkey')"; subst.
               wp_pures.
               iModIntro; iApply ("HΦ" $! _ new').
               iSplitR "Hown_new Hown_tok"; last first.
               { iRight; by iFrame. }
               iFrame "# ∗"; iExists l, down; by iFrame.
          * iDestruct (own_valid_2 with "Hown_auth Hown_curr") 
              as %[Hvalid%gset_included]%auth_both_valid_discrete.
            rewrite (list_equiv_invert_L _ _ curr); last first.
            { rewrite Hperm -elem_of_list_In elem_of_elements; set_solver. }

            iDestruct "Hlist" as (? succ') "(_ & Hpt' & _ & Hnode & Himp)".
            rewrite Hcurr_down.
            iDestruct "Hnode" as (down') "(Hpt_down & >#Hauth_down' & >Htoks_down' & >%Hdown'_key)".

            assert ({[ down' ]} = {[ down' ]} ⋅ {[ down' ]}) as -> by set_solver.
            iDestruct "Hauth_down'" as "(Hauth_down' & Hauth_down'_dup)".

            wp_load.
            iPoseProof ("Himp" with "[Hpt' Hpt_down Htoks_down']") as "Hlist".
            { iFrame; iExists down'; by iFrame "# ∗". }
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists S, L; by iFrame. }
            iModIntro; wp_pures.

            wp_apply (find_sub_spec with "[Hinv']").
            { iFrame "Hinv'". iSplit; first by iRight. iPureIntro; subst; lia. }
            iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & _)".
            wp_pures.

            wp_apply ("IH" with "[$] [$] [%]").
            { lia. }

            iIntros (v new) "(Hlist & Hopt)".
            iDestruct "Hopt" as "[%Hopt | (%Hopt & Hown_new & Hown_tok & %Hkey)]".
            ++ rewrite Hopt; wp_pures.
               iModIntro; iApply "HΦ".
               iSplitR ""; last by iLeft.
               iFrame "# ∗"; iExists l, down; by iFrame.
               Unshelve. done.
            ++ rewrite Hopt; wp_pures.
               wp_apply (insert_spec with "[Hown_new Hown_tok]").
               { rewrite Hkey //. }
               { iFrame "# ∗". iPureIntro; lia. }

               iIntros (new') "(Hown_new & Hown_tok & %Hkey')"; subst.
               wp_pures.
               iModIntro; iApply ("HΦ" $! _ new'). 
               iSplitR "Hown_new Hown_tok"; last first.
               { iRight; by iFrame. }
               iFrame "# ∗"; iExists l, down; by iFrame.
        - iAssert (|={⊤}=> False)%I as "Hfalse"; last by iMod "Hfalse".
          iInv (levelN lvl) as (? L) "(Hinv_sub & _)" "_".
          iDestruct "Hinv_sub" as "(>%Hperm & _ & >Hown_auth & _ & Hlist)".
        
          iDestruct "Hown_curr" as "[%Heq | #Hown_curr]"; first by congruence.
          iDestruct (own_valid_2 with "Hown_auth Hown_curr") 
            as %[Hvalid%gset_included]%auth_both_valid_discrete.
          rewrite (list_equiv_invert_L _ _ curr); last first.
          { rewrite Hperm -elem_of_list_In elem_of_elements; set_solver. }

          iDestruct "Hlist" as (? ?) "(_ & _ & _ & >? & _)".
          by rewrite Hcurr_down.  
    Qed.

    Theorem addH_spec (p: loc) (k h: Z) 
      (S: gset Z) (q: frac) (bot: bot_gname) (subs: list sub_gname)
      (Hrange: INT_MIN < k < INT_MAX) 
      (Hheight: 0 ≤ h ≤ MAX_HEIGHT) :
      {{{ is_skip_list p S q bot subs }}}
        addH #p #k #h
      {{{ opt, RET opt; 
        is_skip_list p (S ∪ {[ k ]}) q bot subs 
        ∗
        (⌜ opt = NONEV ⌝ ∨ 
          ∃ (sub : sub_gname), 
            own (s_toks sub) (◯ GSet {[ k ]}) 
            ∗ 
            ⌜ sub = nth (Z.to_nat (MAX_HEIGHT - h)) subs sub ⌝)
      }}}.
    Proof.
      iIntros (Φ) "H HΦ".
      iDestruct "H" as (head) "(Hpt & %Hmin & Hlist)".
      wp_lam. wp_pures. wp_load.

      destruct subs as [|Γ subs]; first by iExFalso.
      wp_apply (findLevel_spec  with "[Hlist]").
      { iFrame. iSplit; first by iLeft. iPureIntro; lia. }
      iIntros (pred succ Γ' subs').
      iIntros "(%Hnth & Hlist & #Hown_pred & %Hpred_range & Himp)".
      wp_pures.

      wp_apply (insertAll_spec with "[Hlist]").
      { done. }
      { iFrame "# ∗". iPureIntro; lia. }

      iIntros (opt new) "(Hlist & Hopt)".
      iPoseProof ("Himp" with "Hlist") as "Hlist".

      iDestruct "Hopt" as "[->|(-> & _ & Htok & ->)]".
      + iApply "HΦ". 
        iSplitR ""; last by iLeft.
        iExists head; by iFrame.
      + iApply "HΦ". 
        iSplitR "Htok"; last (iRight; iExists Γ'; by iFrame).
        iExists head; by iFrame.
    Qed.

    Theorem add_spec (p: loc) (k: Z) 
      (S: gset Z) (q: frac) (bot: bot_gname) (subs: list sub_gname)
      (Hrange: INT_MIN < k < INT_MAX) :
      {{{ is_skip_list p S q bot subs }}}
        add #p #k
      {{{ RET #(); is_skip_list p (S ∪ {[ k ]}) q bot subs }}}.
    Proof.
      iIntros (Φ) "H HΦ".
      wp_lam. wp_pures. wp_lam. wp_pures.

      wp_apply (addH_spec with "H").
      { done. }
      { pose proof HMAX_HEIGHT; lia. }
      iIntros (?) "(H & _)".
      wp_let; iModIntro; by iApply "HΦ".
    Qed.

  End Proofs.
End AddSpec.