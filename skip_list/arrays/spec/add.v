From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.skip_list.arrays Require Import code.
From SkipList.lib Require Import misc node_rep node_lt key_equiv.
From SkipList.skip_list.arrays.inv Require Import list_equiv lazy_inv skip_inv.
From SkipList.skip_list.arrays.spec Require Import insert.


Local Open Scope Z.

Module AddSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Insert := InsertSpec Params.
  Export Insert.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ}.

    Theorem topLevel_spec (key h lvl: Z) (head curr: node_rep) 
      (Skeys: gset Z) (q: frac) (bot: bot_gname) 
      (top_sub: sub_gname) (bot_subs: list sub_gname) :
      {{{
        skip_list_equiv lvl head Skeys q bot (top_sub :: bot_subs)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth top_sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
        ∗
        ⌜ 0 ≤ h ≤ lvl ⌝
      }}}
        topLevel (rep_to_node curr) #key #h #lvl
      {{{ curr' top_sub' bot_subs', RET rep_to_node curr';
        skip_list_equiv h head Skeys q bot (top_sub' :: bot_subs')
        ∗
        ( 
          skip_list_equiv h head (Skeys ∪ {[ key ]}) q bot (top_sub' :: bot_subs')
          -∗
          skip_list_equiv lvl head (Skeys ∪ {[ key ]}) q bot (top_sub :: bot_subs)
        )
        ∗
        (⌜ curr' = head ⌝ ∨ own (s_auth top_sub') (◯ {[ curr' ]}))
        ∗
        ⌜ node_key curr' < key < INT_MAX ⌝
      }}}.
    Proof.
      iIntros (Φ) "(Hlist & Hown_curr & Hcurr_range & Hh) HΦ".
      iRevert (curr head lvl top_sub bot_subs) "Hlist Hown_curr Hcurr_range Hh HΦ".
      iLöb as "IH".
      iIntros (curr head lvl top_sub bot_subs) "Hlist #Hown_curr %Hcurr_range %Hh HΦ".

      wp_lam. wp_let. wp_let. wp_let.

      rewrite skip_list_equiv_inv.
      iDestruct "Hlist" as (P obot) "(Hinv & Hlist)".
      wp_apply (find_sub_spec with "[Hinv]").
      { by iFrame "# ∗". }

      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & _)".
      wp_pures.
      case_bool_decide as Hcase; wp_if.
      + assert (h = lvl) as <- by congruence.
        iModIntro; iApply "HΦ". 
        iFrame "# ∗". 
        iSplit; last (iPureIntro; lia).
        iIntros "?"; iFrame.
      + assert (h ≠ lvl) by congruence.
        destruct bot_subs as [|bot_sub bot_subs].
        { iDestruct "Hlist" as "(%Hfalse & _)"; lia. }
        iDestruct "Hlist" as "(#Hlvl & #Hinv & Hmatch)"; unfold is_top_list.

        wp_bind (BinOp _ _ _).
        iInv (levelN lvl) as (S' Skeys' L) "(Hinv_sub & _)" "Hclose".
        iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_toks & Hlist)".

        iDestruct "Hown_pred" as "[%Heq | #Hown_pred]".
        - wp_op.
          iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
          { iNext; iExists S', Skeys', L; by iFrame. }
          iModIntro.

          iApply ("IH" with "[$] [] [%] [%]").
          { by iLeft. }
          { lia. }
          { lia. }

          iNext. 
          iIntros (curr' top_sub' bot_subs').
          iIntros "(Hlist & Himp & Hown_curr' & Hcurr_range')".
          iApply "HΦ". iFrame "# ∗".
        - iDestruct (own_valid_2 with "Hown_auth Hown_pred") 
            as %[Hvalid%gset_included]%auth_both_valid_discrete.

          rewrite (list_equiv_invert_L lvl L head pred); last first.
          { rewrite Hperm -elem_of_list_In elem_of_elements; set_solver. }

          iDestruct "Hlist" as (? ? ? ?) "(_ & Hpt & _ & Hs & _ & _ & HP & Himp)".
          iDestruct "HP" as "(Hown_frag & Hown_tok)".
          assert ({[ pred ]} = {[ pred ]} ⋅ {[ pred ]}) as -> by set_solver.
          iDestruct "Hown_frag" as "(Hown_frag & Hown_frag_dup)".

          wp_op.
          iPoseProof ("Himp" with "[$]") as "Hlist".
          iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
          { iNext; iExists S', Skeys', L; by iFrame. }
          iModIntro.
        
          iApply ("IH" with "[$] [$] [%] [%]").
          { lia. }
          { lia. }

          iNext.
          iIntros (curr' top_sub' bot_subs').
          iIntros "(Hlist & Himp & Hown_curr' & Hcurr_range')".
          iApply "HΦ". iFrame "# ∗".
    Qed.

    Theorem addAll_spec (key h lvl: Z) (head curr: node_rep) 
      (Skeys: gset Z) (q: frac) (bot: bot_gname) 
      (top_sub: sub_gname) (bot_subs: list sub_gname) :
      INT_MIN < key < INT_MAX →
      {{{
        skip_list_equiv lvl head Skeys q bot (top_sub :: bot_subs)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth top_sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key ⌝
        ∗
        ⌜ 0 ≤ lvl ≤ h ⌝
      }}}
        addAll (rep_to_node curr) #key #h #lvl
      {{{ (v: val) (n: loc) (new: node_rep), RET v;
        skip_list_equiv lvl head (Skeys ∪ {[ key ]}) q bot (top_sub :: bot_subs)
        ∗
        ( 
          ⌜ v = NONEV ⌝ ∨ 
          ( 
            ⌜ v = SOMEV #n ⌝ 
            ∗ 
            own (s_auth top_sub) (◯ {[ new ]})
            ∗ 
            own (s_toks top_sub) (GSet {[ node_key new ]})
            ∗ 
            ⌜ node_key new = key ⌝
            ∗
            inv (nodeN n) (node_inv n new)
            ∗ 
            n ↦{#lfrac lvl} rep_to_node new
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
      iRevert (Φ curr head lvl top_sub bot_subs) "Hlist Hown_curr Hrange Hh HΦ".
      iLöb as "IH".
      iIntros (Φ curr head lvl top_sub bot_subs) "Hlist #Hown_curr %Hrange %Hh HΦ".

      wp_lam. wp_let. wp_let. wp_let.
      iPoseProof (skip_list_equiv_inv with "Hlist") as (P obot) "(Hinv & Hlist)".
      wp_apply (find_sub_spec with "[Hinv]").
      { iFrame "# ∗". iPureIntro; lia. }

      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & _)".
      wp_pures. 

      destruct bot_subs as [|bot_sub bot_subs].
      + iDestruct "Hlist" as "(%Hlvl & (Hown_frag & #Hinv))".
        rewrite Hlvl; wp_pures.

        wp_apply (tryInsert_spec with "[Hown_frag]").
        { done. }
        { iFrame "# ∗". iPureIntro; lia. }
        iIntros (v n new) "((Hown_frac & _) & Hopt)".

        iApply "HΦ". 
        rewrite loc_add_0.
        assert (h - 0 = h) as -> by lia.
        assert (1 / 2 / 2 = lfrac 0)%Qp as ->.
        { rewrite /lfrac /= Qp_mul_1_r -Qp_div_div //. }
        by iFrame "# ∗".
      + iDestruct "Hlist" as "(%Hlvl & #Hinv & Hmatch)"; unfold is_top_list.
        case_bool_decide as Hcase; wp_if.
        - exfalso; inversion Hcase; lia.
        - wp_bind (BinOp _ _ _).
          iInv (levelN lvl) as (S' Skeys' L) "(Hinv_sub & _)" "Hclose".
          iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_toks & Hlist)".
      
          iDestruct "Hown_pred" as "[%Heq | #Hown_pred]".
          * wp_op.
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists S', Skeys', L; by iFrame. }
            iModIntro. 

            wp_bind (addAll _ _ _ _).
            iApply ("IH" with "[$] [] [%] [%]").
            { by iLeft. }
            { lia. }
            { lia. }

            iNext. 
            iIntros (v n new) "(Hlist & Hopt)".
            iDestruct "Hopt" as "[%Hopt | (%Hopt & Hown_frag & Hown_tok & %Hkey & #Hinvn & Hn & Hnext & Hlock)]".
            ++ rewrite Hopt; wp_pures.
               iModIntro; iApply ("HΦ" $! _ n new).
               iSplitR ""; last by iLeft.
               by iFrame "# ∗".
            ++ rewrite Hopt. wp_pures.
               iDestruct "Hn" as "(Hn & Hn')".
               assert (lfrac (lvl - 1) / 2 = lfrac lvl)%Qp as ->.
               {
                 rewrite /lfrac.
                 assert (Z.to_nat (lvl - 1) + 2 = S (Z.to_nat lvl))%nat as -> by lia.
                 assert (Z.to_nat lvl + 2 = S (S (Z.to_nat lvl)))%nat as -> by lia.
                 rewrite /= Qp_div_div Qp_mul_comm //.
               }

               rewrite loc_add_assoc.
               assert (Z.to_nat (h - (lvl - 1)) = S (Z.to_nat (h - lvl)))%nat as -> by lia.
               rewrite replicate_S array_cons.
               iDestruct "Hnext" as "(Hnext & Hreplicate)".

               iDestruct "Hlock" as (γ) "(#Hlock & Harray & Hlocked)".
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

               wp_apply (insert_spec with "[Hown_frag Hown_tok Hn' Hnext]").
               { done. }
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
               iExists γ. iFrame "# ∗".

               iCombine "Hnext1 Hnext Hnext2" as "Hnext".
               assert (lvl = Z.to_nat lvl) as -> by lia.
               rewrite -array_cons -Hlength1 -array_app.
               iExists (vs1 ++ #n' :: vs2); iFrame.
               iPureIntro; rewrite app_length cons_length; lia.
          * iDestruct (own_valid_2 with "Hown_auth Hown_pred") 
              as %[Hvalid%gset_included]%auth_both_valid_discrete.

            rewrite (list_equiv_invert_L lvl L head pred); last first.
            { rewrite Hperm -elem_of_list_In elem_of_elements; set_solver. }

            iDestruct "Hlist" as (γ ? ? ?) "(_ & Hpt & _ & Hs & _ & _ & HP & Himp)"; clear γ.
            iDestruct "HP" as "(Hown_frag & Hown_tok)".
            assert ({[ pred ]} = {[ pred ]} ⋅ {[ pred ]}) as -> by set_solver.
            iDestruct "Hown_frag" as "(Hown_frag & Hown_frag_dup)".
            assert ({[ pred ]} = {[ pred ]} ⋅ {[ pred ]}) as <- by set_solver.

            wp_op.
            iPoseProof ("Himp" with "[$]") as "Hlist".
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists S', Skeys', L; by iFrame. }
            iModIntro.
          
            wp_bind (addAll _ _ _ _).
            iApply ("IH" with "[$] [$] [%] [%]").
            { lia. }
            { lia. }

            iNext. 
            iIntros (v n new) "(Hlist & Hopt)".
            iDestruct "Hopt" as "[%Hopt | (%Hopt & Hown_frag & Hown_tok & %Hkey & #Hinvn & Hn & Hnext & Hlock)]".
            ++ rewrite Hopt. wp_pures.
               iModIntro; iApply ("HΦ" $! _ n new).
               iSplitR ""; last by iLeft.
               by iFrame "# ∗".
            ++ rewrite Hopt. wp_pures.
               iDestruct "Hn" as "(Hn & Hn')".
               assert (lfrac (lvl - 1) / 2 = lfrac lvl)%Qp as ->.
               {
                 rewrite /lfrac.
                 assert (Z.to_nat (lvl - 1) + 2 = S (Z.to_nat lvl))%nat as -> by lia.
                 assert (Z.to_nat lvl + 2 = S (S (Z.to_nat lvl)))%nat as -> by lia.
                 rewrite /= Qp_div_div Qp_mul_comm //.
               }

               rewrite loc_add_assoc.
               assert (Z.to_nat (h - (lvl - 1)) = S (Z.to_nat (h - lvl)))%nat as -> by lia.
               rewrite replicate_S array_cons.
               iDestruct "Hnext" as "(Hnext & Hreplicate)".

               iDestruct "Hlock" as (γ) "(#Hlock & Harray & Hlocked)".
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

               wp_apply (insert_spec with "[Hown_frag Hown_tok Hn' Hnext]").
               { done. }
               { iFrame "# ∗". iPureIntro; lia. }

               iIntros (n') "(Hown_frag & Hown_tok & Hnext)".
               wp_pures.
               iModIntro; iApply "HΦ". 
               iFrame "# ∗". iSplit; first done.
               iRight. iFrame "# ∗".
               iSplit; first done. iSplit; first done.
               iExists γ. iFrame "# ∗".
               
               iCombine "Hnext1 Hnext Hnext2" as "Hnext".
               assert (lvl = Z.to_nat lvl) as -> by lia.
               rewrite -array_cons -Hlength1 -array_app.
               iExists (vs1 ++ #n' :: vs2); iFrame.
               iPureIntro; rewrite app_length cons_length; lia.
    Qed.

    Theorem add_spec (v: val) (key height: Z) 
      (S: gset Z) (q: frac) (bot: bot_gname) (subs: list sub_gname)
      (Hrange: INT_MIN < key < INT_MAX) 
      (Hheight: 0 ≤ height ≤ MAX_HEIGHT) :
      {{{ is_skip_list v S q bot subs }}}
        add v #key #height
      {{{ (b: bool), RET #b; is_skip_list v (S ∪ {[ key ]}) q bot subs }}}.
    Proof.
      iIntros (Φ) "H HΦ".
      iDestruct "H" as (h head) "(%Hv & Hpt & %Hmin & Hlist)".

      wp_lam. wp_let. wp_let.
      rewrite -Hv. wp_load. wp_let.

      destruct subs as [|sub subs]; first by iExFalso.
      wp_apply (topLevel_spec  with "[Hlist]").
      { iFrame. iSplit; first by iLeft. iPureIntro; lia. }

      iIntros (curr top_sub bot_subs).
      iIntros "(Hlist & Himp & #Hown_curr & %Hcurr_range)".
      wp_let.

      wp_apply (addAll_spec with "[Hlist]").
      { done. }
      { iFrame "# ∗". iPureIntro; lia. }

      iIntros (s n new) "(Hlist & Hopt)".
      iPoseProof ("Himp" with "Hlist") as "Hlist".
      wp_let.

      iDestruct "Hopt" as "[%Hnone | (%Hsome & Hown_frag & Hown_tok & %Heq_key & #Hinvn & Hn & _ & Hlock)]".
      + rewrite Hnone. wp_match.
        iModIntro. iApply "HΦ".
        iExists h, head. by iFrame.
      + rewrite Hsome. wp_match.
        iDestruct "Hlock" as (γ) "(#Hlock & Harray & Hlocked)".

        wp_load. wp_lam. wp_pures.
        wp_apply (release_spec with "[Harray Hlocked]").
        { iFrame "# ∗". }

        iIntros "_". wp_pures.
        iModIntro. iApply "HΦ".
        iExists h, head. by iFrame.
    Qed.

  End Proofs.
End AddSpec.