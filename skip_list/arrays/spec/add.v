From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.skip_list.arrays Require Import code.
From SkipList.lib Require Import misc node_rep node_lt.
From SkipList.skip_list.arrays.inv Require Import list_equiv lazy_inv skip_inv.
From SkipList.skip_list.arrays.spec Require Import insert.


Local Open Scope Z.

Module AddSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Insert := InsertSpec Params.
  Export Insert.

  Section Proofs.
    Context `{!heapGS Σ, !skipGS Σ, !lockG Σ}.

    Theorem findAll_spec (k h lvl: Z) (head curr: node_rep) 
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
        findAll (rep_to_node curr) #k #lvl #h
      {{{ pred succ Γ' subs', RET ((rep_to_node pred), (rep_to_node succ));
        ⌜ Γ' = nth (Z.to_nat (lvl - h)) (Γ :: subs) Γ' ⌝
        ∗
        skip_list_equiv h head Skeys q bot (Γ' :: subs')
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth Γ') (◯ {[ pred ]}))
        ∗
        ⌜ node_key pred < k < INT_MAX ⌝
        ∗
        (
          skip_list_equiv h head (Skeys ∪ {[ k ]}) q bot (Γ' :: subs')
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
        iDestruct "Hlist" as "(#Hlvl & #Hinv & Hmatch)"; unfold is_sub_list.

        wp_bind (BinOp _ _ _).
        iInv (levelN lvl) as (S L) "(Hinv_sub & _)" "Hclose".
        iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >Hown_auth & >Hown_toks & Hlist)".

        iDestruct "Hown_pred" as "[%Heq | #Hown_pred]".
        - wp_op.
          iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
          { iNext; iExists S, L; by iFrame. }
          iModIntro.

          iApply ("IH" with "Hmatch [] [%] [%]").
          { by iLeft. }
          { lia. }
          { lia. }

          iNext. 
          iIntros (pred' succ' Γ' subs').
          iIntros "(%Hnth & Hlist & Hown_pred' & Hpred'_range & Himp)".
          iApply "HΦ". iFrame "# ∗". iPureIntro.
          by assert (Z.to_nat (lvl - h) = Datatypes.S (Z.to_nat (lvl - 1 - h))) as -> by lia.
        - iDestruct (own_valid_2 with "Hown_auth Hown_pred") 
            as %[Hvalid%gset_included]%auth_both_valid_discrete.

          rewrite (list_equiv_invert_L _ _ _ pred); last first.
          { rewrite Hperm -elem_of_list_In elem_of_elements; set_solver. }

          iDestruct "Hlist" as (? ? ? ?) "(_ & Hpt & #Hs & _ & _ & Hnode & Himp)".
          iDestruct "Hnode" as "(Hown_frag & Hown_tok)".
          assert ({[ pred ]} = {[ pred ]} ⋅ {[ pred ]}) as -> by set_solver.
          iDestruct "Hown_frag" as "(Hown_frag & Hown_frag_dup)".
          assert ({[ pred ]} = {[ pred ]} ⋅ {[ pred ]}) as <- by set_solver.

          wp_op.
          iPoseProof ("Himp" with "[$]") as "Hlist".
          iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
          { iNext; iExists S, L; by iFrame. }
          iModIntro.
        
          iApply ("IH" with "Hmatch [$] [%] [%]").
          { lia. }
          { lia. }

          iNext.
          iIntros (pred' succ' Γ' subs').
          iIntros "(%Hnth & Hlist & Hown_pred' & Hpred'_range & Himp)".
          iApply "HΦ". iFrame "# ∗". iPureIntro.
          by assert (Z.to_nat (lvl - h) = Datatypes.S (Z.to_nat (lvl - 1 - h))) as -> by lia.
    Qed.

    Theorem insertAll_spec (k h lvl: Z) (head curr: node_rep) 
      (Skeys: gset Z) (q: frac) (bot: bot_gname) 
      (Γ: sub_gname) (subs: list sub_gname) :
      INT_MIN < k < INT_MAX →
      {{{
        skip_list_equiv lvl head Skeys q bot (Γ :: subs)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth Γ) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < k ⌝
        ∗
        ⌜ 0 ≤ lvl ≤ h ⌝
      }}}
        insertAll (rep_to_node curr) #k #h #lvl
      {{{ (opt: val) (n: loc) (new: node_rep), RET opt;
        skip_list_equiv lvl head (Skeys ∪ {[ k ]}) q bot (Γ :: subs)
        ∗
        ( 
          ⌜ opt = NONEV ⌝ ∨ 
          ( 
            ⌜ opt = SOMEV #n ⌝ 
            ∗ 
            own (s_auth Γ) (◯ {[ new ]})
            ∗ 
            own (s_toks Γ) (◯ GSet {[ node_key new ]})
            ∗ 
            ⌜ node_key new = k ⌝
            ∗
            n ↦□ rep_to_node new
            ∗
            (node_next new +ₗ lvl +ₗ 1) ↦∗{#1 / 2} replicate (Z.to_nat (h - lvl)) #()
            ∗
            ∃ (γ: gname), 
              is_lock γ (node_lock new) (is_array (node_next new) (h + 1))
              ∗
              is_array (node_next new) (h + 1)
              ∗
              locked γ
          )
        )
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(Hlist & Hown_curr & Hrange & Hh) HΦ".
      iRevert (Φ curr head lvl Γ subs) "Hlist Hown_curr Hrange Hh HΦ".
      iLöb as "IH".
      iIntros (Φ curr head lvl Γ subs) "Hlist #Hown_curr %Hrange %Hh HΦ".
      wp_lam. wp_pures.

      destruct subs as [|γ subs].
      + iDestruct "Hlist" as "(%Hlvl & (Hown_frag & #Hinv))".
        rewrite Hlvl; wp_pures.

        wp_apply (tryInsert_spec with "[Hown_frag]").
        { done. }
        { iFrame "# ∗". iPureIntro; lia. }
        iIntros (opt n new) "(Hown_frac & Hopt)".

        iApply "HΦ". 
        rewrite loc_add_0.
        assert (h - 0 = h) as -> by lia.
        by iFrame "# ∗".
      + iDestruct "Hlist" as "(%Hlvl & #Hinv & Hmatch)"; unfold is_sub_list.
        case_bool_decide as Hcase; wp_if.
        - exfalso; inversion Hcase; lia.
        - wp_bind (BinOp _ _ _).
          iInv (levelN lvl) as (S' L) "(Hinv_sub & _)" "Hclose".
          iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >Hown_auth & >Hown_toks & Hlist)".
      
          iDestruct "Hown_curr" as "[%Heq | #Hown_curr]".
          * wp_op.
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists S', L; by iFrame. }
            iModIntro. 

            iPoseProof (skip_list_equiv_cons with "Hmatch") as (obot osub) "(Hinv' & Hlist')".
            wp_apply (find_sub_spec with "[Hinv']").
            { iFrame "Hinv'". iSplit; first by iLeft. iPureIntro; lia. }
            iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & _)".
            wp_pures.

            wp_bind (insertAll _ _ _ _).
            iApply ("IH" with "[$] [$] [%] [%]").
            { lia. }
            { lia. }

            iNext; iIntros (opt n new) "(Hlist & Hopt)".
            iDestruct "Hopt" as "[%Hopt | (%Hopt & Hown_frag & Hown_tok & %Hkey & #Hn & Hnext & Hlock)]".
            ++ rewrite Hopt; wp_pures.
               iModIntro; iApply ("HΦ" $! _ n new).
               iSplitR ""; last by iLeft.
               by iFrame "# ∗".
            ++ rewrite Hopt. wp_pures.

               rewrite loc_add_assoc.
               assert (Z.to_nat (h - (lvl - 1)) = S (Z.to_nat (h - lvl)))%nat as -> by lia.
               rewrite replicate_S array_cons.
               iDestruct "Hnext" as "(Hnext & Hreplicate)".

               iDestruct "Hlock" as (γl) "(#Hlock & Harray & Hlocked)".
               iDestruct "Harray" as (vs) "(Hnext' & %Hlength)".
               pose proof (list_split vs (Z.to_nat h) (Z.to_nat lvl)) as Hsplit.
               destruct Hsplit as [next Hsplit]; try lia.
               destruct Hsplit as [vs1 Hsplit]; destruct Hsplit as [vs2 Hsplit].
               destruct Hsplit as [Hvs Hsplit]; destruct Hsplit as [Hlength1 Hlength2].
               rewrite Hvs array_app array_cons Hlength1.
               iDestruct "Hnext'" as "(Hnext1 & Hnext' & Hnext2)".
               assert (lvl = Z.to_nat lvl) as <- by lia.
               assert (lvl - 1 + 1 = lvl) as -> by lia.
               iDestruct (mapsto_agree with "Hnext Hnext'") as %<-.
               iCombine "Hnext Hnext'" as "Hnext".

               wp_apply (insert_spec _ _ _ _ new with "[Hown_frag Hown_tok Hnext]").
               { rewrite Hkey //. }
               { 
                 iFrame "# ∗".
                 iSplit; first by iLeft.
                 iPureIntro; lia.
               }

               iIntros (n') "(Hown_frag & Hown_tok & Hnext)".
               wp_pures.
               iModIntro; iApply "HΦ". 
               iFrame "# ∗". iSplit; first done.
               iRight. iFrame "# ∗".
               iSplit; first done. iSplit; first done.
               iExists γl. iFrame "# ∗".

               iCombine "Hnext1 Hnext Hnext2" as "Hnext".
               assert (lvl = Z.to_nat lvl) as -> by lia.
               rewrite -array_cons -Hlength1 -array_app.
               iExists (vs1 ++ #n' :: vs2); iFrame.
               iPureIntro; rewrite app_length cons_length; lia.
          * iDestruct (own_valid_2 with "Hown_auth Hown_curr") 
              as %[Hvalid%gset_included]%auth_both_valid_discrete.

            rewrite (list_equiv_invert_L _ _ _ curr); last first.
            { rewrite Hperm -elem_of_list_In elem_of_elements; set_solver. }

            iDestruct "Hlist" as (γl ? ? succ') "(_ & Hpt & #Hs & _ & _ & Hnode & Himp)"; clear γl.
            iDestruct "Hnode" as "(Hown_frag & Hown_tok)".
            assert ({[ curr ]} = {[ curr ]} ⋅ {[ curr ]}) as -> by set_solver.
            iDestruct "Hown_frag" as "(Hown_frag & Hown_frag_dup)".
            assert ({[ curr ]} = {[ curr ]} ⋅ {[ curr ]}) as <- by set_solver.

            wp_op.
            iPoseProof ("Himp" with "[$]") as "Hlist".
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists S', L; by iFrame. }
            iModIntro.

            iPoseProof (skip_list_equiv_cons with "Hmatch") as (obot osub) "(Hinv' & Hlist')".
            wp_apply (find_sub_spec with "[Hinv' Hown_frag]").
            { iFrame. iPureIntro; lia. }
            iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & _)".
            wp_pures.
          
            wp_bind (insertAll _ _ _ _).
            iApply ("IH" with "[$] [$] [%] [%]").
            { lia. }
            { lia. }

            iNext. iIntros (opt n new) "(Hlist & Hopt)".
            iDestruct "Hopt" as "[%Hopt | (%Hopt & Hown_frag & Hown_tok & %Hkey & #Hn & Hnext & Hlock)]".
            ++ rewrite Hopt. wp_pures.
               iModIntro; iApply ("HΦ" $! _ n new).
               iSplitR ""; last by iLeft.
               by iFrame "# ∗".
            ++ rewrite Hopt. wp_pures.

               rewrite loc_add_assoc.
               assert (Z.to_nat (h - (lvl - 1)) = S (Z.to_nat (h - lvl)))%nat as -> by lia.
               rewrite replicate_S array_cons.
               iDestruct "Hnext" as "(Hnext & Hreplicate)".

               iDestruct "Hlock" as (γl) "(#Hlock & Harray & Hlocked)".
               iDestruct "Harray" as (vs) "(Hnext' & %Hlength)".
               pose proof (list_split vs (Z.to_nat h) (Z.to_nat lvl)) as Hsplit.
               destruct Hsplit as [next Hsplit]; try lia.
               destruct Hsplit as [vs1 Hsplit]; destruct Hsplit as [vs2 Hsplit].
               destruct Hsplit as [Hvs Hsplit]; destruct Hsplit as [Hlength1 Hlength2].
               rewrite Hvs array_app array_cons Hlength1.
               iDestruct "Hnext'" as "(Hnext1 & Hnext' & Hnext2)".
               assert (lvl = Z.to_nat lvl) as <- by lia.
               assert (lvl - 1 + 1 = lvl) as -> by lia.
               iDestruct (mapsto_agree with "Hnext Hnext'") as %<-.
               iCombine "Hnext Hnext'" as "Hnext".

               wp_apply (insert_spec _ _ _ _ new with "[Hown_frag Hown_tok Hnext]").
               { rewrite Hkey //. }
               { iFrame "# ∗". iPureIntro; lia. }

               iIntros (n') "(Hown_frag & Hown_tok & Hnext)".
               wp_pures.
               iModIntro; iApply "HΦ". 
               iFrame "# ∗". iSplit; first done.
               iRight. iFrame "# ∗".
               iSplit; first done. iSplit; first done.
               iExists γl. iFrame "# ∗".
               
               iCombine "Hnext1 Hnext Hnext2" as "Hnext".
               assert (lvl = Z.to_nat lvl) as -> by lia.
               rewrite -array_cons -Hlength1 -array_app.
               iExists (vs1 ++ #n' :: vs2); iFrame.
               iPureIntro; rewrite app_length cons_length; lia.
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
      wp_apply (findAll_spec  with "[Hlist]").
      { iFrame. iSplit; first by iLeft. iPureIntro; lia. }
      iIntros (pred succ Γ' subs').
      iIntros "(%Hnth & Hlist & #Hown_pred & %Hpred_range & Himp)".
      wp_pures.

      wp_apply (insertAll_spec with "[Hlist]").
      { done. }
      { iFrame "# ∗". iPureIntro; lia. }

      iIntros (opt n new) "(Hlist & Hopt)".
      iPoseProof ("Himp" with "Hlist") as "Hlist".

      wp_let.
      iDestruct "Hopt" as "[->|(-> & _ & Htok & -> & #Hn & _ & Hlock)]"; wp_match.
      + iModIntro; iApply "HΦ". 
        iSplitR ""; last by iLeft.
        iExists head; by iFrame.
      + wp_load. wp_lam. wp_pures.

        iDestruct "Hlock" as (γl) "(#Hlock & Harray & Hlocked)".
        wp_apply (release_spec with "[Harray Hlocked]").
        { iFrame "# ∗". }
        iIntros "_"; wp_pures.
        iModIntro; iApply "HΦ".

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