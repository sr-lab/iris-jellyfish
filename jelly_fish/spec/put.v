From iris.algebra Require Import auth frac_auth gmap gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import arg_max.
From SkipList.jelly_fish Require Import code.
From SkipList.lib Require Import misc node_rep node_lt.
From SkipList.jelly_fish.inv Require Import list_equiv lazy_inv skip_inv.
From SkipList.jelly_fish.spec Require Import insert.


Local Open Scope Z.

Module PutSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Insert := InsertSpec Params.
  Export Insert.

  Section Proofs.
    Context `{!heapGS Σ, !skipGS Σ, !lockG Σ}.

    Theorem findAll_spec (k h lvl: Z) (head curr: node_rep) 
      (M: gmap Z (argmax Z)) (q: frac) (bot: bot_gname) 
      (Γ: sub_gname) (subs: list sub_gname) :
      {{{
        skip_list_equiv lvl head M q bot (Γ :: subs)
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
        skip_list_equiv h head M q bot (Γ' :: subs')
        ∗
        (⌜ pred = head ⌝ ∨ own (s_auth Γ') (◯ {[ pred ]}))
        ∗
        ⌜ node_key pred < k < INT_MAX ⌝
        ∗
        ∀ (v t: Z),
          skip_list_equiv h head (M ⋅ {[ k := prodZ {[ v ]} t ]}) q bot (Γ' :: subs')
          -∗
          skip_list_equiv lvl head (M ⋅ {[ k := prodZ {[ v ]} t ]}) q bot (Γ :: subs)
      }}}.
    Proof.
      iIntros (Φ) "(Hlist & Hown_curr & Hcurr_range & Hh) HΦ".
      iRevert (curr head lvl Γ subs) "Hlist Hown_curr Hcurr_range Hh HΦ".
      iLöb as "IH".
      iIntros (curr head lvl Γ subs) "Hlist #Hown_curr %Hcurr_range %Hh HΦ".

      wp_lam. wp_let. wp_let. wp_let.

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
        iIntros (v t) "?"; iFrame.
      + assert (h ≠ lvl) by congruence.
        destruct subs as [|γ subs].
        { iDestruct "Hlist" as "(%Hfalse & _)"; lia. }
        iDestruct "Hlist" as "(#Hlvl & #Hinv & Hmatch)"; unfold is_sub_list.

        wp_bind (BinOp _ _ _).
        iInv (levelN lvl) as (M' S' L) "(Hinv_sub & _)" "Hclose".
        iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >Hown_auth & >Hown_toks & Hlist)".

        iDestruct "Hown_pred" as "[%Heq | #Hown_pred]".
        - wp_op.
          iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
          { iNext; iExists M', S', L; by iFrame. }
          iModIntro.

          iApply ("IH" with "Hmatch [] [%] [%]").
          { by iLeft. }
          { lia. }
          { lia. }

          iNext. 
          iIntros (pred' succ' Γ' subs').
          iIntros "(%Hnth & Hlist & Hown_pred' & Hpred'_range & Himp)".
          iApply "HΦ". iFrame "# ∗". iPureIntro.
          by assert (Z.to_nat (lvl - h) = S (Z.to_nat (lvl - 1 - h))) as -> by lia.
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
          { iNext; iExists M', S', L; by iFrame. }
          iModIntro.
        
          iApply ("IH" with "Hmatch [$] [%] [%]").
          { lia. }
          { lia. }

          iNext.
          iIntros (pred' succ' Γ' subs').
          iIntros "(%Hnth & Hlist & Hown_pred' & Hpred'_range & Himp)".
          iApply "HΦ". iFrame "# ∗". iPureIntro.
          by assert (Z.to_nat (lvl - h) = S (Z.to_nat (lvl - 1 - h))) as -> by lia.
    Qed.

    Theorem insertAll_spec (k v t h lvl: Z) (head curr: node_rep) 
      (M: gmap Z (argmax Z)) (q: frac) (bot: bot_gname) 
      (Γ: sub_gname) (subs: list sub_gname) :
      INT_MIN < k < INT_MAX →
      {{{
        skip_list_equiv lvl head M q bot (Γ :: subs)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth Γ) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < k ⌝
        ∗
        ⌜ 0 ≤ lvl ≤ h ⌝
      }}}
        insertAll (rep_to_node curr) #k #v #t #h #lvl
      {{{ (opt: val) (n: loc) (new: node_rep), RET opt;
        skip_list_equiv lvl head (M ⋅ {[ k := prodZ {[ v ]} t ]}) q bot (Γ :: subs)
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
            (node_next new +ₗ lvl +ₗ 1) ↦∗ replicate (Z.to_nat (h - lvl)) #()
            ∗
            (node_locks new +ₗ lvl +ₗ 1) ↦∗ replicate (Z.to_nat (h - lvl)) #()
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
        do 2 rewrite loc_add_0.
        assert (h - 0 = h) as -> by lia.
        by iFrame "# ∗".
      + iDestruct "Hlist" as "(%Hlvl & #Hinv & Hmatch)"; unfold is_sub_list.
        case_bool_decide as Hcase; wp_if.
        - exfalso; inversion Hcase; lia.
        - wp_bind (BinOp _ _ _).
          iInv (levelN lvl) as (M' S' L) "(Hinv_sub & _)" "Hclose".
          iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >Hown_auth & >Hown_toks & Hlist)".
          
          iDestruct "Hown_curr" as "[%Heq | #Hown_curr]".
          * wp_op.
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists M', S', L; by iFrame. }
            iModIntro.

            iPoseProof (skip_list_equiv_cons with "Hmatch") as (obot osub) "(Hinv' & Hlist')".
            wp_apply (find_sub_spec with "[Hinv']").
            { iFrame "Hinv'". iSplit; first by iLeft. iPureIntro; lia. }
            iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & _)".
            wp_pures.
            
            wp_bind (insertAll _ _ _ _ _ _).
            iApply ("IH" with "Hlist' [$] [%] [%]").
            { lia. }
            { lia. }

            iNext; iIntros (opt n new) "(Hlist & Hopt)".
            iDestruct "Hopt" as "[%Hopt | (%Hopt & Hown_frag & Hown_tok & %Hkey & #Hn & Hnext & Hlocks)]".
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
          * iDestruct (own_valid_2 with "Hown_auth Hown_curr") 
              as %[Hvalid%gset_included]%auth_both_valid_discrete.

            rewrite (list_equiv_invert_L _ _ _ _ curr); last first.
            { rewrite Hperm -elem_of_list_In elem_of_elements; set_solver. }

            iDestruct "Hlist" as (v' γl l s succ') "(_ & Hpt & #Hs & _ & _ & Hnode & _ & Himp)".
            iDestruct "Hnode" as "(Hown_frag & Hown_tok)".
            assert ({[ curr ]} = {[ curr ]} ⋅ {[ curr ]}) as -> by set_solver.
            iDestruct "Hown_frag" as "(Hown_frag & Hown_frag_dup)".
            assert ({[ curr ]} = {[ curr ]} ⋅ {[ curr ]}) as <- by set_solver.

            wp_op.
            iPoseProof ("Himp" $! {[ val_v dummy_val ]} dummy_val with "[Hpt Hown_frag_dup Hown_tok]") as "Hlist".
            { iFrame; rewrite elem_of_singleton //. }
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists M', S', L; by iFrame. }
            iModIntro.

            iPoseProof (skip_list_equiv_cons with "Hmatch") as (obot osub) "(Hinv' & Hlist')".
            wp_apply (find_sub_spec with "[Hinv' Hown_frag]").
            { iFrame. iPureIntro; lia. }
            iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & _)".
            wp_pures.

            wp_bind (insertAll _ _ _ _ _ _).
            iApply ("IH" with "Hlist' [] [%] [%]").
            { iFrame "#". }
            { lia. }
            { lia. }

            iNext; iIntros (opt n new) "(Hlist & Hopt)".
            iDestruct "Hopt" as "[%Hopt | (%Hopt & Hown_frag' & Hown_tok & %Hkey & #Hn & Hnext & Hlocks)]".
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

               wp_apply (insert_spec _ _ _ new with "[Hown_frag' Hown_tok Hnext' Hlocks']").
               { rewrite Hkey //. }
               { 
                 iFrame "# ∗".
                 iPureIntro; lia. 
               }

               iIntros "(Hown_frag' & Hown_tok)".
               wp_pures.
               iModIntro; iApply "HΦ". 
               iFrame "# ∗". iSplit; first done.
               iRight. by iFrame "# ∗".
    Qed.

    Theorem putH_spec (p: loc) (k v t h: Z) 
      (M: gmap Z (argmax Z)) (q: frac) (bot: bot_gname) (subs: list sub_gname)
      (Hrange: INT_MIN < k < INT_MAX) 
      (Hheight: 0 ≤ h ≤ MAX_HEIGHT) :
      {{{ is_skip_list p M q bot subs }}}
        putH #p #k #v #t #h
      {{{ opt, RET opt; 
        is_skip_list p (M ⋅ {[ k := prodZ {[ v ]} t ]}) q bot subs 
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

      iDestruct "Hopt" as "[->|(-> & _ & Htok & -> & _)]".
      + iApply "HΦ". 
        iSplitR ""; last by iLeft.
        iExists head; by iFrame.
      + iApply "HΦ".
        iSplitR "Htok"; last (iRight; iExists Γ'; by iFrame).
        iExists head; by iFrame.
    Qed.

    Theorem put_spec (p: loc) (k v t: Z) 
      (M: gmap Z (argmax Z)) (q: frac) (bot: bot_gname) (subs: list sub_gname)
      (Hrange: INT_MIN < k < INT_MAX) :
      {{{ is_skip_list p M q bot subs }}}
        put #p #k #v #t
      {{{ RET #(); is_skip_list p (M ⋅ {[ k := prodZ {[ v ]} t ]}) q bot subs }}}.
    Proof.
      iIntros (Φ) "H HΦ".
      wp_lam. wp_pures. wp_lam. wp_pures.

      wp_apply (putH_spec with "H").
      { done. }
      { pose proof HMAX_HEIGHT; lia. }

      iIntros (?) "(H & _)".
      wp_pures; iModIntro; by iApply "HΦ".
    Qed.

  End Proofs.
End PutSpec.