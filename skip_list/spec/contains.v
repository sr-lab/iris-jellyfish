From Coq Require Import Sorting.Sorted.

From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc.
From SkipList.skip_list Require Import node_rep code key_equiv.
From SkipList.skip_list.inv Require Import lazy_inv skip_inv.
From SkipList.skip_list.spec Require Import find.


Local Open Scope Z.
Module ContainsSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Find := FindSpec Params.
  Import Find.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ}.
    
    Theorem findPred_spec (curr top_head: node_rep) (lvl key: Z)
      (Stop: gset Z) (Sbots: list (gset Z)) 
      (top: lazy_gname) (bots: list lazy_gname) :
      {{{ 
        skip_list_equiv top_head lvl 1 (Stop :: Sbots) (top :: bots)
        ∗
        (⌜ curr = top_head ⌝ ∨ own (s_auth top) (◯ {[curr]}))
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
        findPred (rep_to_node curr) #key
      {{{ pred succ S, RET SOMEV ((rep_to_node pred), (rep_to_node succ));
        skip_list_equiv top_head lvl 1 (Stop :: Sbots) (top :: bots)
        ∗
        ⌜ last (Stop :: Sbots) = Some S ⌝
        ∗
        ⌜ key ∈ S ↔ node_key succ = key ⌝
      }}}.
    Proof.
      iIntros (Φ) "(Hlist & Hcurr_range & Hrange) HΦ".
      iRevert (curr top_head lvl Stop Sbots top bots) "Hlist Hcurr_range Hrange HΦ".
      iLöb as "IH".
      iIntros (curr top_head lvl Stop Sbots top bots) "Hlist #Hcurr_range %Hrange HΦ".

      wp_lam. wp_let.
      destruct Sbots as [|Sbot]; destruct bots as [|bot]; try by iExFalso.
      + iDestruct "Hlist" as "(%Hlvl & Hlazy & %Hnone)".
        iDestruct "Hlazy" as (Sfrac) "(%Hequiv & Hown_frag & #Hinv)".
        wp_apply (find_full_spec with "[Hown_frag]").
        { by iFrame "# ∗". }

        iIntros (pred succ) "(Hown_frag & %Hpred_range & %Hpred_key & %Hkey_in_S)".
        wp_pures. wp_lam. wp_pures.
        destruct (node_down pred) as [d|] eqn:Hcurr_down; wp_pures.
        - wp_bind (Load _).
          iInv (levelN lvl) as (S Skeys L) "(>%Hperm & _ & _ & _ & Hown_frac & _ & Hlist)" "_".
          iMod "Hown_frac"; iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
            as %<-%frac_auth_agree_L.
          
          destruct Hpred_range as [|Hin]; first by congruence.
          rewrite -elem_of_elements elem_of_list_In -Hperm in Hin.
          rewrite list_equiv_invert_L; last done.
          iDestruct "Hlist" as (? ? ?) "(_ & _ & _ & _ & HP & _)".
          iMod "HP" as %Hfalse; congruence.
        - iModIntro. iApply "HΦ". iSplit. 
          { 
            iSplit; first done. iSplit; last done. 
            iExists Sfrac; by iFrame "# ∗". 
          }
          by rewrite -Hequiv elem_of_elements in Hkey_in_S.
      + iDestruct "Hlist" as (l down) "(%Hlvl & Hlazy & %Hsome & Hpt & %Hmin & Hmatch)".
        iDestruct "Hlazy" as (Sfrac) "(%Hequiv & Hown_frag & #Hinv)".
        wp_apply (find_full_spec with "[Hown_frag]").
        { by iFrame "# ∗". }

        iIntros (pred succ) "(Hown_frag & %Hpred_range & %Hpred_key & %Hkey_in_S)". 
        wp_pures. wp_lam. wp_pures.
        destruct (node_down pred) as [d|] eqn:Hcurr_down; wp_pures.
        - wp_bind (Load _).
          iInv (levelN lvl) as (S Skeys L) "(>%Hperm & >%Hsort & >%Hequiv' & Hown_auth & Hown_frac & Hown_tok & Hlist)" "Hclose".
          iMod "Hown_frac"; iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
            as %<-%frac_auth_agree_L.

          destruct Hpred_range as [Heq|Hin].
          * assert (d = l) as -> by congruence.
            wp_load.
            iMod ("Hclose" with "[Hlist Hown_auth Hown_frac Hown_tok]") as "_".
            { iNext; iExists S, Skeys, L; by iFrame. }

            iModIntro; wp_let.
            iApply ("IH" with "[$] [] [%]").
            { by iLeft. }
            { rewrite -Hmin -Heq; lia. }
            iNext; iIntros (pred' succ' Sfrac') "(Hlist & %Hlast & %Hkey_in_S')".
            iApply "HΦ". iSplitL "Hpt Hlist Hown_frag"; last done. 
            iExists l, down. iFrame "# ∗".
            iSplit; first done. iSplit; last done.
            iExists S; by iFrame "# ∗". 
          * rewrite -elem_of_elements elem_of_list_In -Hperm in Hin.
            rewrite list_equiv_invert_L; last done.
            iDestruct "Hlist" as (succ' l' γ) "(Hsucc'_range & Hsome' & Hpt' & Hlock & HP & Himp)".
            iDestruct "HP" as (d' down') "(Hsome_down & Hpt_down & Hown_down' & Hdown'_key)".
            iMod "Hsome_down" as %Hsome_down; iMod "Hdown'_key" as %Hdown'_key.

            iMod "Hown_down'".
            assert ({[down']} ≡ {[down']} ⋅ {[down']}) as -> by set_solver.
            iDestruct "Hown_down'" as "(Hown_down' & Hown_down'_dup)".

            assert (d = d') as <- by congruence.
            iMod "Hpt_down"; wp_load.
            iPoseProof ("Himp" with "[Hpt' Hpt_down Hown_down']") as "Hlist".
            { iFrame; iExists d, down'; by iFrame. }
            iMod ("Hclose" with "[Hown_auth Hown_frac Hown_tok Hlist]") as "_".
            { iNext; iExists S, Skeys, L. by iFrame. }

            iModIntro; wp_let.
            iDestruct "Hsucc'_range" as %Hsucc'_range; iDestruct "Hsome'" as %Hsome'.
            iApply ("IH" with "[$] [Hown_down'_dup] [%]").
            { by iRight. }
            { rewrite -Hdown'_key; lia. }
            iNext; iIntros (? ? S') "(Hlist & %Hlast & %Hkey_in_S')".
            iApply "HΦ". iSplitL "Hpt Hlist Hown_frag"; last done. 
            iExists l, down. iFrame "# ∗".
            iSplit; first done. iSplit; last done.
            iExists S; by iFrame "# ∗". 
        - iInv (levelN lvl) as (S Skeys L) "(>%Hperm & _ & _ & _ & Hown_frac & _ & Hlist)" "_".
          iMod "Hown_frac"; iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
            as %<-%frac_auth_agree_L.

          destruct Hpred_range as [|Hin]; first by congruence.
          rewrite -elem_of_elements elem_of_list_In -Hperm in Hin.
          rewrite list_equiv_invert_L; last done.
          iDestruct "Hlist" as (? ? ?) "(_ & _ & _ & _ & HP & _)".
          iDestruct "HP" as (? ?) "(Hfalse & _)".
          iMod "Hfalse" as %Hfalse; congruence.
    Qed.
    
    Theorem contains_spec (v: val) (key: Z) 
      (L_gset: list (gset Z)) (L_gname: list lazy_gname)
      (Hrange: INT_MIN < key < INT_MAX) :
      {{{ is_skip_list v 1 L_gset L_gname }}}
        contains v #key
      {{{ (b: bool) S, RET #b; 
        is_skip_list v 1 L_gset L_gname
        ∗
        ⌜ last L_gset = Some S ⌝
        ∗
        ⌜ if b then key ∈ S else key ∉ S ⌝
      }}}.
    Proof.
      iIntros (Φ) "H HΦ".
      iDestruct "H" as (h head) "(%Hv & Hpt & %Hmin & Hlist)".
      wp_lam. wp_let. rewrite -Hv. wp_load.
      destruct L_gname as [|top bots]; destruct L_gset as [|Stop Sbots]; try by iExFalso.
      wp_apply (findPred_spec with "[Hlist]").
      { iFrame. iSplit. by iLeft. iPureIntro; lia. }

      iIntros (pred succ S) "(Hlist & %Hlast & %Hkey_in_S)".
      wp_let. wp_match. wp_pures. wp_lam. wp_pures.
      iModIntro; case_bool_decide.
      + iApply "HΦ". iSplit.
        { iExists h, head. by iFrame. }
        iPureIntro; split; first done.
        rewrite Hkey_in_S; congruence.
      + iApply "HΦ". iSplit. 
        { iExists h, head. by iFrame. }
        iPureIntro; split; first done.
        intros Hin. 
        rewrite Hkey_in_S in Hin; congruence.
    Qed.

  End Proofs.
End ContainsSpec.