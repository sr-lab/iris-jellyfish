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
    
    Theorem findPred_spec (curr top_head: node_rep) (lvl: Z) (key: Z)
      (Sfrac: gset node_rep) (Stop: gset Z) (Sbots: list (gset Z)) 
      (top: lazy_gname) (bots: list lazy_gname) :
      {{{ 
        skip_list_equiv top_head lvl (top :: bots)
        ∗
        own_frac 1 Sbots bots
        ∗
        own (s_frac top) (◯F Sfrac)
        ∗
        ⌜ key_equiv Sfrac Stop ⌝
        ∗
        (⌜ curr = top_head ⌝ ∨ own (s_auth top) (◯ {[curr]}))
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
        findPred (rep_to_node curr) #key
      {{{ pred succ S, RET SOMEV ((rep_to_node pred), (rep_to_node succ));
        skip_list_equiv top_head lvl (top :: bots)
        ∗
        own_frac 1 (Stop :: Sbots) (top :: bots)
        ∗
        ⌜ last (Stop :: Sbots) = Some S ⌝
        ∗
        ⌜ key ∈ S ↔ node_key succ = key ⌝
      }}}.
    Proof.
      iIntros (Φ) "(Hlist & Hown & Hown_frag & Hequiv & Hcurr_range & Hrange) HΦ".
      iRevert (curr top_head lvl Sfrac Stop Sbots top bots) "Hlist Hown Hown_frag Hequiv Hcurr_range Hrange HΦ".
      iLöb as "IH".
      iIntros (curr top_head lvl Sfrac Stop Sbots top bots) "Hlist Hown Hown_frag %Hequiv #Hcurr_range %Hrange HΦ".

      wp_lam. wp_let.
      iPoseProof (skip_list_equiv_cons_inv with "Hlist") as "Hlist".
      iDestruct "Hlist" as (P) "(Hinv & Hlist)".
      wp_apply (find_spec with "[Hinv Hown_frag]").
      { by iFrame "# ∗". }

      iIntros (pred succ) "(Hown_frag & %Hpred_range & %Hpred_key & %Hkey_in_S)".
      wp_pures. wp_lam. wp_pures.
      destruct (node_down pred) as [d|] eqn:Hcurr_down; wp_pures.
      + wp_bind (Load _).
        destruct bots as [|bot].
        - iDestruct "Hlist" as "(%Hlvl & #Hinv & %Hnone)".
          iInv (levelN lvl) as (S Skeys L) "(>%Hperm & >%Hsort & >%Hequiv' & Hown_auth & Hown_frac & Hown_tok & Hlist)" "Hclose".
          iMod "Hown_frac"; iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
            as %<-%frac_auth_agree_L.
          
          iMod "Hown_auth"; iAssert ((⌜ curr = top_head ∨ curr ∈ S ⌝)%I) with "[Hown_auth Hcurr_range]" as %Hcurr_range.
          {
            iDestruct "Hcurr_range" as "[Heq|Hown]"; first by iLeft.
            iDestruct (own_valid_2 with "Hown_auth Hown") 
              as %[Hvalid%gset_included]%auth_both_valid_discrete.
            iPureIntro; right; set_solver.
          }

          destruct Hpred_range as [|Hin]; first by congruence.
          rewrite -elem_of_elements elem_of_list_In -Hperm in Hin.
          rewrite list_equiv_invert_L; last done.
          iDestruct "Hlist" as (? ? ?) "(_ & _ & _ & _ & HP & _)".
          iMod "HP" as %Hfalse; congruence.
        - iDestruct "Hlist" as (l down) "(%Hlvl & #Hinv & %Hsome & Hpt & %Hmin & Hmatch)".
          iInv (levelN lvl) as (S Skeys L) "(>%Hperm & >%Hsort & >%Hequiv' & Hown_auth & Hown_frac & Hown_tok & Hlist)" "Hclose".
          iMod "Hown_frac"; iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
            as %<-%frac_auth_agree_L.

          destruct Sbots as [|Sbot]; first by iExFalso.
          iDestruct "Hown" as (Sbot_frag) "(? & ? & ?)".

          destruct Hpred_range as [Heq|Hin].
          * assert (d = l) as -> by congruence.
            wp_load.
            iMod ("Hclose" with "[Hlist Hown_auth Hown_frac Hown_tok]") as "_".
            { iNext; iExists S, Skeys, L; by iFrame. }

            iModIntro; wp_let.
            iApply ("IH" with "[$] [$] [$] [$] [] [%]").
            { by iLeft. }
            { rewrite -Hmin -Heq; lia. }
            iNext; iIntros (pred' succ' Sfrac') "(Hlist & Hown & %Hlast & %Hkey_in_S')".
            iApply "HΦ". 
            iSplitL "Hpt Hlist". iExists l, down. by iFrame "# ∗".
            iSplitL "Hown Hown_frag". iExists S. by iFrame.
            done.
          * rewrite -elem_of_elements elem_of_list_In -Hperm in Hin.
            rewrite list_equiv_invert_L; last done.
            iDestruct "Hlist" as (succ' l' γ) "(Hsucc'_range & Hsome' & Hpt' & Hlock & HP & Himp)".
            iDestruct "HP" as (d' down') "(Hsome_down & Hpt_down & Hown_down' & Hdown'_key)".
            iMod "Hsome_down" as %Hsome_down;
            iMod "Hdown'_key" as %Hdown'_key.

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
            iDestruct "Hsucc'_range" as %Hsucc'_range; 
            iDestruct "Hsome'" as %Hsome'.
            iApply ("IH" with "[$] [$] [$] [$] [Hown_down'_dup] [%]").
            { by iRight. }
            { rewrite -Hdown'_key; lia. }
            iNext; iIntros (pred'' succ'' S'') "(Hlist & Hown & %Hlast & %Hkey_in_S'')".
            iApply "HΦ".
            iSplitL "Hpt Hlist". iExists l, down. by iFrame "# ∗".
            iSplitL "Hown Hown_frag". iExists S. by iFrame.
            done.
      + destruct bots as [|bot].
        - iModIntro. iApply "HΦ".
          iDestruct "Hlist" as "(%Hlvl & #Hinv & %Hnone)".
          iSplit. by iFrame "#".
          iSplit. iExists Sfrac. by iFrame.
          iSplit; last by rewrite -Hequiv elem_of_elements in Hkey_in_S.
          by destruct Sbots; last by iExFalso.
        - iDestruct "Hlist" as (l down) "(%Hlvl & #Hinv & %Hsome & Hpt & %Heq & Hmatch)".
          iInv (levelN lvl) as (S Skeys L) "(>%Hperm & >%Hsort & >%Hequiv' & Hown_auth & Hown_frac & Hown_tok & Hlist)" "Hclose".
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
      iDestruct "H" as (h head) "(%Hv & Hpt & %Hmin & Hown_frac & Hlist)".
      wp_lam. wp_let. rewrite -Hv. wp_load.
      destruct L_gname as [|top bots]; destruct L_gset as [|Stop Sbots]; try by iExFalso.
      iDestruct "Hown_frac" as (Sfrac) "(Hequiv & Hown & Hown_frac)".
      wp_apply (findPred_spec with "[Hlist Hequiv Hown Hown_frac]").
      { iFrame. iSplit. by iLeft. iPureIntro; lia. }

      iIntros (pred succ S) "(Hlist & Hown_frac & %Hlast & %Hkey_in_S)".
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