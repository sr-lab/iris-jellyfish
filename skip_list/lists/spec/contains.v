From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.skip_list.lists Require Import code.
From SkipList.lib Require Import misc node_rep node_lt.
From SkipList.skip_list.lists.inv Require Import list_equiv lazy_inv skip_inv.
From SkipList.skip_list.lists.spec Require Import find.


Local Open Scope Z.

Module ContainsSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Find := FindSpec Params.
  Export Find.

  Section Proofs.
    Context `{!heapGS Σ, !skipGS Σ, !lockG Σ}.
    
    Theorem findAll_spec (k lvl: Z) (head curr: node_rep)
      (Skeys: gset Z) (bot: bot_gname) 
      (Γ: sub_gname) (subs: list sub_gname) :
      {{{ 
        skip_list_equiv lvl head Skeys 1 bot (Γ :: subs)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth Γ) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < k < INT_MAX ⌝
      }}}
        findAll (rep_to_node curr) #k
      {{{ pred succ, RET ((rep_to_node pred), (rep_to_node succ));
        skip_list_equiv lvl head Skeys 1 bot (Γ :: subs)
        ∗
        ⌜ k ∈ Skeys ↔ node_key succ = k ⌝
      }}}.
    Proof.
      iIntros (Φ) "(Hlist & Hown_curr & Hrange) HΦ".
      iRevert (curr head lvl Γ subs) "Hlist Hown_curr Hrange HΦ".
      iLöb as "IH".
      iIntros (curr head lvl Γ subs) "Hlist #Hown_curr %Hrange HΦ".
      wp_lam. wp_let.

      destruct subs as [|γ subs].
      + iDestruct "Hlist" as "(%Hlvl & (Hown_frag & #Hinv) & %Hnone)".
        wp_apply (find_bot_spec with "[Hown_frag]").
        { by iFrame "# ∗". }
        iIntros (pred succ) "(Hown_frag & %Hpred_key & #Hown_pred & %Hkey_in_S)".

        wp_pures. wp_lam. wp_pures.
        destruct (node_down pred) as [d|] eqn:Hpred_down; wp_pures.
        - wp_bind (Load _).
          iInv (levelN lvl) as (S L) "(Hinv_sub & >Hown_frac)" "Hclose".
          iDestruct "Hinv_sub" as "(>%Hperm & _ & >Hown_auth & _ & Hlist)".
          iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
            as %<-%frac_auth_agree_L.
          
          iAssert ((⌜ pred = head ∨ In pred L ⌝)%I) with "[Hown_auth Hown_pred]" as %Hpred_range.
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
          iDestruct "Hlist" as (? ?) "(_ & _ & _ & >? & _)".
          rewrite Hpred_down; by iExFalso.
        - iModIntro; iApply "HΦ". 
          by iFrame "# ∗".
      + iDestruct "Hlist" as (l down) "(%Hlvl & #Hinv & %Hsome & Hpt & %Hmin & Hmatch)".
        wp_apply find_sub_spec.
        { by iFrame "# ∗". }
        iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & _)".

        wp_pures. wp_lam. wp_pures.
        destruct (node_down pred) as [d|] eqn:Hpred_down; wp_pures.
        - wp_bind (Load _).
          iInv (levelN lvl) as (S L) "(Hinv_sub & _)" "Hclose".
          iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >Hown_auth & >Hown_toks & Hlist)".

          iDestruct "Hown_pred" as "[%Heq | #Hown_pred]".
          * assert (d = l) as -> by congruence.
            wp_load.
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists S, L; by iFrame. }

            iModIntro.
            iApply ("IH" with "[$] [] [%]").
            { by iLeft. }
            { rewrite -Hmin -Heq; lia. }
            iNext; iIntros (? ?) "(Hlist & ?)".
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
            iDestruct "Hlist" as (γl succ') "(>%Hsucc'_range & Hpt' & Hlock & Hnode & Himp)".
            rewrite Hpred_down.
            iDestruct "Hnode" as (down') "(Hpt_down & >Hauth_down' & >Htoks_down' & >%Hdown'_key)".

            assert ({[ down' ]} = {[ down' ]} ⋅ {[ down' ]}) as -> by set_solver.
            iDestruct "Hauth_down'" as "(Hauth_down' & Hauth_down'_dup)".

            wp_load.
            iPoseProof ("Himp" with "[Hpt' Hpt_down Hauth_down' Htoks_down']") as "Hlist".
            { iFrame; iExists down'; by iFrame. }
            iMod ("Hclose" with "[Hown_auth Hown_toks Hlist]") as "_".
            { iNext; iExists S, L; by iFrame. }

            iModIntro.
            iApply ("IH" with "[$] [Hauth_down'_dup] [%]").
            { by iRight. }
            { rewrite -Hdown'_key; lia. }
            iNext; iIntros (? ?) "(Hlist & ?)".
            iApply "HΦ". iSplitL "Hpt Hlist"; last done. 
            iExists l, down. by iFrame "# ∗".
        - iInv (levelN lvl) as (? L) "(Hinv_sub & _)" "_".
          iDestruct "Hinv_sub" as "(>%Hperm & _ & >Hown_auth & _ & Hlist)".

          iDestruct "Hown_pred" as "[%Heq | #Hown_pred]"; first by congruence.
          iAssert ⌜ In pred L ⌝%I with "[Hown_auth]" as %Hin.
          {
            iDestruct (own_valid_2 with "Hown_auth Hown_pred") 
              as %[Hvalid%gset_included]%auth_both_valid_discrete.
            rewrite -elem_of_list_In Hperm elem_of_elements.
            iPureIntro; set_solver.
          }

          rewrite list_equiv_invert_L; last done.
          iDestruct "Hlist" as (? ?) "(_ & _ & _ & >? & _)".
          rewrite Hpred_down; by iExFalso.
    Qed.
    
    Theorem contains_spec (p: loc) (k: Z) 
      (S: gset Z) (bot: bot_gname) (subs: list sub_gname)
      (Hrange: INT_MIN < k < INT_MAX) :
      {{{ is_skip_list p S 1 bot subs }}}
        contains #p #k
      {{{ (b: bool), RET #b; 
        is_skip_list p S 1 bot subs
        ∗
        ⌜ if b then k ∈ S else k ∉ S ⌝
      }}}.
    Proof.
      iIntros (Φ) "H HΦ".
      iDestruct "H" as (head) "(Hpt & %Hmin & Hlist)".
      wp_lam. wp_let. wp_load.

      destruct subs as [|Γ subs]; first by iExFalso.
      wp_apply (findAll_spec with "[Hlist]").
      { iFrame. iSplit. by iLeft. iPureIntro; lia. }
      iIntros (pred succ) "(Hlist & %Hkey_in_S)".
      wp_pures. wp_lam. wp_pures.
      
      iModIntro; case_bool_decide.
      + iApply "HΦ". iSplit.
        { iExists head; by iFrame. }
        iPureIntro. 
        rewrite Hkey_in_S; congruence.
      + iApply "HΦ". iSplit. 
        { iExists head; by iFrame. }
        iPureIntro; intros Hin. 
        rewrite Hkey_in_S in Hin; congruence.
    Qed.

  End Proofs.
End ContainsSpec.