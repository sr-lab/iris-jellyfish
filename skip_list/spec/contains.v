From Coq Require Import Sorting.Sorted.

From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc node_rep node_lt key_equiv.
From SkipList.skip_list Require Import code.
From SkipList.skip_list.inv Require Import list_equiv lazy_inv skip_inv.
From SkipList.skip_list.spec Require Import find.


Local Open Scope Z.

Module ContainsSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Find := FindSpec Params.
  Export Find.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ}.
    
    Theorem findPred_spec (key lvl: Z) (top_head curr: node_rep) (Skeys: gset Z) 
      (bot: bot_gname) (top_sub: sub_gname) (bot_subs: list sub_gname) :
      {{{ 
        skip_list_equiv lvl top_head Skeys 1 bot (top_sub :: bot_subs)
        ∗
        (⌜ curr = top_head ⌝ ∨ own (s_auth top_sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
        findPred (rep_to_node curr) #key
      {{{ pred succ, RET ((rep_to_node pred), (rep_to_node succ));
        skip_list_equiv lvl top_head Skeys 1 bot (top_sub :: bot_subs)
        ∗
        ⌜ key ∈ Skeys ↔ node_key succ = key ⌝
      }}}.
    Proof.
      iIntros (Φ) "(Hlist & Hown_curr & Hrange) HΦ".
      iRevert (curr top_head lvl top_sub bot_subs) "Hlist Hown_curr Hrange HΦ".
      iLöb as "IH".
      iIntros (curr top_head lvl top_sub bot_subs) "Hlist #Hown_curr %Hrange HΦ".

      wp_lam. wp_let.
      destruct bot_subs as [|bot_sub].
      + iDestruct "Hlist" as "(%Hlvl & Hbot & %Hnone)".
        iDestruct "Hbot" as "(Hown_frag & #Hinv)".
        wp_apply (find_bot_spec with "[Hown_frag]").
        { by iFrame "# ∗". }

        iIntros (pred succ) "(Hown_frag & %Hpred_key & #Hown_pred & %Hkey_in_S)".
        wp_pures. wp_lam. wp_pures.
        destruct (node_down pred) as [d|] eqn:Hpred_down; wp_pures.
        - wp_bind (Load _).
          iInv (levelN lvl) as (S ? L) "(Hinv_sub & Hinv_bot)" "Hclose".
          iDestruct "Hinv_sub" as "(>%Hperm & _ & _ & >Hown_auth & _ & Hlist)".
          iDestruct "Hinv_bot" as "(>Hown_frac & _)".
          iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
            as %->%frac_auth_agree_L.
          
          iAssert ((⌜ pred = top_head ∨ In pred L ⌝)%I) with "[Hown_auth Hown_pred]" as %Hpred_range.
          {
            iDestruct "Hown_pred" as "[Heq|Hown]"; first by iLeft.
            iDestruct (own_valid_2 with "Hown_auth Hown") 
              as %[Hvalid%gset_included]%auth_both_valid_discrete.
            iPureIntro; right.
            rewrite -elem_of_list_In Hperm elem_of_elements.
            set_solver.
          }
          
          destruct Hpred_range as [|Hin]; first by congruence.
          rewrite list_equiv_invert_L; last done.
          iDestruct "Hlist" as (? ? ? ?) "(_ & _ & _ & _ & >HP & _)".
          rewrite Hpred_down; by iExFalso.
        - iModIntro. iApply "HΦ". 
          by iFrame "# ∗".
      + iDestruct "Hlist" as (l down) "(%Hlvl & #Hinv & %Hsome & Hpt & %Hmin & Hmatch)".
        unfold is_top_list.
        wp_apply find_sub_spec.
        { by iFrame "# ∗". }

        iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & _)".
        wp_pures. wp_lam. wp_pures.
        destruct (node_down pred) as [d|] eqn:Hpred_down; wp_pures.
        - wp_bind (Load _).
          iInv (levelN lvl) as (S Skeys' L) "(Hinv_sub & _)" "Hclose".
          iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_toks & Hlist)".

          iDestruct "Hown_pred" as "[%Heq | #Hown_pred]".
          * assert (d = l) as -> by congruence.
            wp_load.
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists S, Skeys', L; by iFrame. }

            iModIntro; wp_let.
            iApply ("IH" with "[$] [] [%]").
            { by iLeft. }
            { rewrite -Hmin -Heq; lia. }
            iNext; iIntros (pred' succ') "(Hlist & %Hkey_in_S)".
            iApply "HΦ". iSplitL "Hpt Hlist"; last done. 
            iExists l, down. by iFrame "# ∗".
          * iAssert ⌜ In pred L ⌝%I with "[Hown_auth]" as %Hin.
            {
              iDestruct (own_valid_2 with "Hown_auth Hown_pred") 
                as %[Hvalid%gset_included]%auth_both_valid_discrete.
              rewrite -elem_of_list_In Hperm elem_of_elements.
              iPureIntro; set_solver.
            }

            rewrite list_equiv_invert_L; last done.
            iDestruct "Hlist" as (succ' ? ? γ) "(>%Hsucc'_range & _ & Hpt' & Hlock & HP & Himp)".
            rewrite Hpred_down.
            iDestruct "HP" as (down') "(Hpt_down & >Hauth_down' & >Htoks_down' & >%Hdown'_key)".

            assert ({[ down' ]} = {[ down' ]} ⋅ {[ down' ]}) as -> by set_solver.
            iDestruct "Hauth_down'" as "(Hauth_down' & Hauth_down'_dup)".

            wp_load.
            iPoseProof ("Himp" with "[Hpt' Hpt_down Hauth_down' Htoks_down']") as "Hlist".
            { iFrame; iExists down'; by iFrame. }
            iMod ("Hclose" with "[Hown_auth Hown_toks Hlist]") as "_".
            { iNext; iExists S, Skeys', L; by iFrame. }

            iModIntro; wp_let.
            iApply ("IH" with "[$] [Hauth_down'_dup] [%]").
            { by iRight. }
            { rewrite -Hdown'_key; lia. }
            iNext; iIntros (? ?) "(Hlist & %Hkey_in_S)".
            iApply "HΦ". iSplitL "Hpt Hlist"; last done. 
            iExists l, down. by iFrame "# ∗".
        - iInv (levelN lvl) as (? ? L) "(Hinv_sub & _)" "_".
          iDestruct "Hinv_sub" as "(>%Hperm & _ & _ & >Hown_auth & _ & Hlist)".

          iDestruct "Hown_pred" as "[%Heq | #Hown_pred]"; first by congruence.
          iAssert ⌜ In pred L ⌝%I with "[Hown_auth]" as %Hin.
          {
            iDestruct (own_valid_2 with "Hown_auth Hown_pred") 
              as %[Hvalid%gset_included]%auth_both_valid_discrete.
            rewrite -elem_of_list_In Hperm elem_of_elements.
            iPureIntro; set_solver.
          }

          rewrite list_equiv_invert_L; last done.
          iDestruct "Hlist" as (? ? ? ?) "(_ & _ & _ & _ & >HP & _)".
          rewrite Hpred_down; by iExFalso.
    Qed.
    
    Theorem contains_spec (key: Z) (v: val) (S: gset Z) 
      (bot: bot_gname) (subs: list sub_gname)
      (Hrange: INT_MIN < key < INT_MAX) :
      {{{ is_skip_list v S 1 bot subs }}}
        contains v #key
      {{{ (b: bool), RET #b; 
        is_skip_list v S 1 bot subs
        ∗
        ⌜ if b then key ∈ S else key ∉ S ⌝
      }}}.
    Proof.
      iIntros (Φ) "H HΦ".
      iDestruct "H" as (h head) "(%Hv & Hpt & %Hmin & Hlist)".
      wp_lam. wp_let. rewrite -Hv. wp_load. wp_let.
      destruct subs as [|sub subs]; first by iExFalso.

      wp_apply (findPred_spec with "[Hlist]").
      { iFrame. iSplit. by iLeft. iPureIntro; lia. }

      iIntros (pred succ) "(Hlist & %Hkey_in_S)".
      wp_pures. wp_lam. wp_pures.
      
      iModIntro; case_bool_decide.
      + iApply "HΦ". iSplit.
        { iExists h, head. by iFrame. }
        iPureIntro. 
        rewrite Hkey_in_S; congruence.
      + iApply "HΦ". iSplit. 
        { iExists h, head. by iFrame. }
        iPureIntro; intros Hin. 
        rewrite Hkey_in_S in Hin; congruence.
    Qed.

  End Proofs.
End ContainsSpec.