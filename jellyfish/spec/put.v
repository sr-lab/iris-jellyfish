From iris.algebra Require Import auth frac_auth gmap gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import arg_max.
From SkipList.jellyfish Require Import code.
From SkipList.lib Require Import misc node_rep node_lt key_equiv.
From SkipList.jellyfish.inv Require Import list_equiv lazy_inv skip_inv.
From SkipList.jellyfish.spec Require Import insert.


Local Open Scope Z.

Module PutSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Insert := InsertSpec Params.
  Export Insert.

  Section Proofs.
    Context `{!heapGS Σ, !skipGS Σ, !lockG Σ}.

    Theorem topLevel_spec (key h lvl: Z) (head curr: node_rep) 
      (Smap: gmap Z (argmax Z)) (q: frac) (bot: bot_gname) 
      (top_sub: sub_gname) (bot_subs: list sub_gname) :
      {{{
        skip_list_equiv lvl head Smap q bot (top_sub :: bot_subs)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth top_sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
        ∗
        ⌜ 0 ≤ h ≤ lvl ⌝
      }}}
        topLevel (rep_to_node curr) #key #h #lvl
      {{{ curr' top_sub' bot_subs', RET rep_to_node curr';
        skip_list_equiv h head Smap q bot (top_sub' :: bot_subs')
        ∗
        (⌜ curr' = head ⌝ ∨ own (s_auth top_sub') (◯ {[ curr' ]}))
        ∗
        ⌜ node_key curr' < key < INT_MAX ⌝
        ∗
        ∀ (v ts: Z),
          skip_list_equiv h head (Smap ⋅ {[ key := prodZ {[ v ]} ts ]}) q bot (top_sub' :: bot_subs')
          -∗
          skip_list_equiv lvl head (Smap ⋅ {[ key := prodZ {[ v ]} ts ]}) q bot (top_sub :: bot_subs)
      }}}.
    Proof.
      iIntros (Φ) "(Hlist & Hown_curr & Hcurr_range & Hh) HΦ".
      iRevert (curr head lvl top_sub bot_subs) "Hlist Hown_curr Hcurr_range Hh HΦ".
      iLöb as "IH".
      iIntros (curr head lvl top_sub bot_subs) "Hlist #Hown_curr %Hcurr_range %Hh HΦ".

      wp_lam. wp_let. wp_let. wp_let.

      rewrite skip_list_equiv_cons.
      iDestruct "Hlist" as (obot) "(Hinv & Hlist)".
      wp_apply (find_sub_spec with "[Hinv]").
      { by iFrame "# ∗". }

      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & _)".
      wp_pures.
      case_bool_decide as Hcase; wp_if.
      + inversion Hcase; subst.
        iModIntro; iApply "HΦ".
        iFrame "# ∗". 
        iSplit; first (iPureIntro; lia).
        iIntros (v ts) "?"; iFrame.
      + assert (h ≠ lvl) by congruence.
        destruct bot_subs as [|bot_sub bot_subs].
        { iDestruct "Hlist" as "(%Hfalse & _)"; lia. }
        iDestruct "Hlist" as "(#Hlvl & #Hinv & Hmatch)"; unfold is_sub_list.

        wp_bind (BinOp _ _ _).
        iInv (levelN lvl) as (S' Smap' L) "(Hinv_sub & _)" "Hclose".
        iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_toks & Hlist)".

        iDestruct "Hown_pred" as "[%Heq | #Hown_pred]".
        - wp_op.
          iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
          { iNext; iExists S', Smap', L; by iFrame. }
          iModIntro.

          iApply ("IH" with "Hmatch [] [%] [%]").
          { by iLeft. }
          { lia. }
          { lia. }

          iNext. 
          iIntros (curr' top_sub' bot_subs').
          iIntros "(Hlist & Hown_curr' & Hcurr_range' & Himp)".
          iApply "HΦ". iFrame "# ∗".
        - iDestruct (own_valid_2 with "Hown_auth Hown_pred") 
            as %[Hvalid%gset_included]%auth_both_valid_discrete.

          rewrite (list_equiv_invert_L _ _ _ _ pred); last first.
          { rewrite Hperm -elem_of_list_In elem_of_elements; set_solver. }

          iDestruct "Hlist" as (? ? ? ? ?) "(_ & Hpt & #Hs & _ & _ & Hnode & _ & Himp)".
          iDestruct "Hnode" as "(Hown_frag & Hown_tok)".
          assert ({[ pred ]} = {[ pred ]} ⋅ {[ pred ]}) as -> by set_solver.
          iDestruct "Hown_frag" as "(Hown_frag & Hown_frag_dup)".
          assert ({[ pred ]} = {[ pred ]} ⋅ {[ pred ]}) as <- by set_solver.

          wp_op.
          iPoseProof ("Himp" $! {[ val_v dummy_val ]} dummy_val with "[Hpt Hown_frag_dup Hown_tok]") as "Hlist".
          { iFrame; rewrite elem_of_singleton //. }
          iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
          { iNext; iExists S', Smap', L; by iFrame. }
          iModIntro.
        
          iApply ("IH" with "Hmatch [$] [%] [%]").
          { lia. }
          { lia. }

          iNext.
          iIntros (curr' top_sub' bot_subs').
          iIntros "(Hlist & Hown_curr' & Hcurr_range' & Himp)".
          iApply "HΦ". iFrame "# ∗".
    Qed.

    Theorem putAll_spec (key v ts h lvl: Z) (head curr: node_rep) 
      (Smap: gmap Z (argmax Z)) (q: frac) (bot: bot_gname) 
      (top_sub: sub_gname) (bot_subs: list sub_gname) :
      INT_MIN < key < INT_MAX →
      {{{
        skip_list_equiv lvl head Smap q bot (top_sub :: bot_subs)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth top_sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key ⌝
        ∗
        ⌜ 0 ≤ lvl ≤ h ⌝
      }}}
        putAll (rep_to_node curr) #key #v #ts #h #lvl
      {{{ (opt: val) (n: loc) (new: node_rep), RET opt;
        skip_list_equiv lvl head (Smap ⋅ {[ key := prodZ {[ v ]} ts ]}) q bot (top_sub :: bot_subs)
        ∗
        ( 
          ⌜ opt = NONEV ⌝ ∨ 
          ( 
            ⌜ opt = SOMEV #n ⌝ 
            ∗ 
            own (s_auth top_sub) (◯ {[ new ]})
            ∗ 
            own (s_toks top_sub) (GSet {[ node_key new ]})
            ∗ 
            own (s_keys bot) (GSet {[ node_key new ]})
            ∗ 
            ⌜ node_key new = key ⌝
            ∗
            n ↦□ rep_to_node new
            ∗
            (node_next new +ₗ lvl +ₗ 1) ↦∗ replicate (Z.to_nat (h - lvl)) #()
            ∗
            (node_locks new +ₗ lvl +ₗ 1) ↦∗ replicate (Z.to_nat (h - lvl)) #()
          )
        )
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(Hlist & Hown_curr & Hrange & Hh) HΦ".
      iRevert (Φ curr head lvl top_sub bot_subs) "Hlist Hown_curr Hrange Hh HΦ".
      iLöb as "IH".
      iIntros (Φ curr head lvl top_sub bot_subs) "Hlist #Hown_curr %Hrange %Hh HΦ".

      wp_lam. wp_pures.
      iPoseProof (skip_list_equiv_cons with "Hlist") as (obot) "(Hinv & Hlist)".
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
        iIntros (opt n new) "((Hown_frac & _) & Hopt)".

        iApply "HΦ". 
        do 2 rewrite loc_add_0.
        assert (h - 0 = h) as -> by lia.
        by iFrame "# ∗".
      + iDestruct "Hlist" as "(%Hlvl & #Hinv & Hmatch)"; unfold is_sub_list.
        case_bool_decide as Hcase; wp_if.
        - exfalso; inversion Hcase; lia.
        - wp_bind (BinOp _ _ _).
          iInv (levelN lvl) as (S' Smap' L) "(Hinv_sub & _)" "Hclose".
          iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_toks & Hlist)".
      
          iDestruct "Hown_pred" as "[%Heq | #Hown_pred]".
          * wp_op.
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists S', Smap', L; by iFrame. }
            iModIntro. 

            wp_bind (putAll _ _ _ _ _ _).
            iApply ("IH" with "Hmatch [] [%] [%]").
            { by iLeft. }
            { lia. }
            { lia. }

            iNext; iIntros (opt n new) "(Hlist & Hopt)".
            iDestruct "Hopt" as "[%Hopt | (%Hopt & Hown_frag & Hown_tok & Hown_key & %Hkey & #Hn & Hnext & Hlocks)]".
            ++ rewrite Hopt; wp_pures.
               iModIntro; iApply ("HΦ" $! _ n new).
               iSplitR ""; last by iLeft.
               by iFrame "# ∗".
            ++ rewrite Hopt. wp_pures.

               do 2 rewrite loc_add_assoc.
               assert (Z.to_nat (h - (lvl - 1)) = S (Z.to_nat (h - lvl)))%nat as -> by lia.
               assert (lvl - 1 + 1 = lvl) as -> by lia.
               rewrite replicate_S ?array_cons.
               iDestruct "Hnext" as "(Hnext' & Hnext)".
               iDestruct "Hlocks" as "(Hlocks' & Hlocks)".

               wp_apply (insert_spec _ _ _ new with "[Hown_frag Hown_tok Hnext' Hlocks']").
               { rewrite Hkey //. }
               { 
                 iFrame "# ∗".
                 iSplit; first by iLeft.
                 iPureIntro; lia.
               }

               iIntros "(Hown_frag & Hown_tok)".
               wp_pures.
               iModIntro; iApply "HΦ". 
               iFrame "# ∗". iSplit; first done.
               iRight. by iFrame "# ∗".
          * iDestruct (own_valid_2 with "Hown_auth Hown_pred") 
              as %[Hvalid%gset_included]%auth_both_valid_discrete.

            rewrite (list_equiv_invert_L _ _ _ _ pred); last first.
            { rewrite Hperm -elem_of_list_In elem_of_elements; set_solver. }

            iDestruct "Hlist" as (? ? ? ? ?) "(_ & Hpt & #Hs & _ & _ & Hnode & _ & Himp)".
            iDestruct "Hnode" as "(Hown_frag & Hown_tok)".
            assert ({[ pred ]} = {[ pred ]} ⋅ {[ pred ]}) as -> by set_solver.
            iDestruct "Hown_frag" as "(Hown_frag & Hown_frag_dup)".
            assert ({[ pred ]} = {[ pred ]} ⋅ {[ pred ]}) as <- by set_solver.

            wp_op.
            iPoseProof ("Himp" $! {[ val_v dummy_val ]} dummy_val with "[Hpt Hown_frag_dup Hown_tok]") as "Hlist".
            { iFrame; rewrite elem_of_singleton //. }
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists S', Smap', L; by iFrame. }
            iModIntro.
          
            wp_bind (putAll _ _ _ _ _ _).
            iApply ("IH" with "Hmatch [$] [%] [%]").
            { lia. }
            { lia. }

            iNext. 
            iIntros (opt n new) "(Hlist & Hopt)".
            iDestruct "Hopt" as "[%Hopt | (%Hopt & Hown_frag & Hown_tok & Hown_key & %Hkey & #Hn & Hnext & Hlocks)]".
            ++ rewrite Hopt; wp_pures.
               iModIntro; iApply ("HΦ" $! _ n new).
               iSplitR ""; last by iLeft.
               by iFrame "# ∗".
            ++ rewrite Hopt; wp_pures.

               do 2 rewrite loc_add_assoc.
               assert (Z.to_nat (h - (lvl - 1)) = S (Z.to_nat (h - lvl)))%nat as -> by lia.
               assert (lvl - 1 + 1 = lvl) as -> by lia.
               rewrite replicate_S ?array_cons.
               iDestruct "Hnext" as "(Hnext' & Hnext)".
               iDestruct "Hlocks" as "(Hlocks' & Hlocks)".

               wp_apply (insert_spec _ _ _ new with "[Hown_frag Hown_tok Hnext' Hlocks']").
               { rewrite Hkey //. }
               { iFrame "# ∗"; iPureIntro; lia. }

               iIntros "(Hown_frag & Hown_tok)".
               wp_pures.
               iModIntro; iApply "HΦ". 
               iFrame "# ∗". iSplit; first done.
               iRight. by iFrame "# ∗".
    Qed.

    Theorem put_spec (v: val) (key val ts height: Z) 
      (Smap: gmap Z (argmax Z)) (q: frac) (bot: bot_gname) (subs: list sub_gname)
      (Hrange: INT_MIN < key < INT_MAX) 
      (Hheight: 0 ≤ height ≤ MAX_HEIGHT) :
      {{{ is_skip_list v Smap q bot subs }}}
        put v #key #val #ts #height
      {{{ RET #(); is_skip_list v (Smap ⋅ {[ key := prodZ {[ val ]} ts ]}) q bot subs }}}.
    Proof.
      iIntros (Φ) "H HΦ".
      iDestruct "H" as (h head) "(%Hv & Hpt & %Hmin & Hlist)".

      wp_lam. wp_pures.
      rewrite -Hv. wp_load. wp_let.

      destruct subs as [|sub subs]; first by iExFalso.
      wp_apply (topLevel_spec  with "[Hlist]").
      { iFrame. iSplit; first by iLeft. iPureIntro; lia. }
      iIntros (curr top_sub bot_subs).
      iIntros "(Hlist & #Hown_curr & %Hcurr_range & Himp)".
      wp_let.

      wp_apply (putAll_spec with "[Hlist]").
      { done. }
      { iFrame "# ∗". iPureIntro; lia. }

      iIntros (opt n new) "(Hlist & Hopt)".
      iPoseProof ("Himp" with "Hlist") as "Hlist".
      wp_let.

      iModIntro; iApply "HΦ". 
      iExists h, head. by iFrame.
    Qed.

  End Proofs.
End PutSpec.