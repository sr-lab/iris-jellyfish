From Coq Require Import Sorting.Sorted.

From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc.
From SkipList.skip_list Require Import node_rep code key_equiv.
From SkipList.skip_list.spec Require Import find.


Local Open Scope Z.
Module ContainsSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Find := FindSpec Params.
  Import Find.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, lockG Σ} (N : namespace).
    
    Theorem findPred_spec (curr top_head: node_rep) (top: gset node_rep) 
      (lvl: Z) (key: Z) (L: list (gset node_rep)) (S: gset node_rep) :
      {{{ 
        skip_list_equiv top_head lvl (top :: L) S
        ∗
        ⌜ curr = top_head ∨ curr ∈ top ⌝
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
        findPred (rep_to_node curr) #key
      {{{ pred succ, RET SOMEV ((rep_to_node pred), (rep_to_node succ));
        skip_list_equiv top_head lvl (top :: L) S
        ∗
        ⌜ key ∈ map node_key (elements S) ↔ node_key succ = key ⌝
      }}}.
    Proof.
      iIntros (Φ) "(Hlist & Hcurr_range & Hrange) HΦ".
      iRevert (curr lvl top_head top L) "Hlist Hcurr_range Hrange HΦ".
      iLöb as "IH".
      iIntros (curr lvl top_head top L) "Hlist %Hcurr_range %Hrange HΦ".

      iPoseProof (skip_list_equiv_cons_inv top_head lvl S L top with "Hlist") as "Hlist".
      iDestruct "Hlist" as (P) "(Hinv & Hlist)".

      wp_lam. wp_let.
      wp_apply (find_spec with "[Hinv]").
      { by iFrame. }

      iIntros (pred succ) "(%Hpred_range & %Hpred_key & %Hkey_in_S)".
      wp_pures. wp_lam. wp_pures.
      destruct (node_down pred) as [d|] eqn:Hcurr_down; wp_pures.
      + wp_bind (Load _).
        destruct L as [|bot].
        - iDestruct "Hlist" as "(#Hinv & %Hnone & Heq)".
          iInv (levelN lvl) as (L') "(>%Hperm & >%Hsort & Hlist)" "Hclose".

          destruct Hpred_range as [|Hin]; first by congruence.
          rewrite -elem_of_elements elem_of_list_In -Hperm in Hin.
          rewrite list_equiv_invert_L; last done.
          iDestruct "Hlist" as (? ? ?) "(_ & _ & _ & _ & HP & _)".
          iMod "HP" as %Hfalse; congruence.
        - iDestruct "Hlist" as (l down) "(#Hinv & %Hsome & Hpt & %Hmin & Hmatch)".
          iInv (levelN lvl) as (L') "(>%Hperm & >%Hsort & Hlist)" "Hclose".

          destruct Hpred_range as [Heq|Hin].
          * assert (d = l) as -> by congruence.
            wp_load.
            iMod ("Hclose" with "[Hlist]") as "_".
            { iNext; iExists L'; by iFrame. }

            iModIntro; wp_let.
            iApply ("IH" $! down (lvl - 1) down bot L with "[$] [%] [%]").
            { by left. }
            { rewrite -Hmin -Heq; lia. }
            iNext; iIntros (pred' succ') "(Hlist & %Hkey_in_S')".
            iApply "HΦ"; iSplit; last done. 
            iExists l, down. by iFrame "# ∗".
          * rewrite -elem_of_elements elem_of_list_In -Hperm in Hin.
            rewrite list_equiv_invert_L; last done.
            iDestruct "Hlist" as (succ' l' γ) "(Hsucc'_range & Hsome' & Hpt' & Hlock & HP & Himp)".
            iDestruct "HP" as (d' down') "(Hsome_down & Hpt_down & Hin_bot & Hdown'_key)".
            iMod "Hsome_down" as %Hsome_down; 
            iMod "Hin_bot" as %Hin_bot; 
            iMod "Hdown'_key" as %Hdown'_key.
            
            assert (d = d') as <- by congruence.
            iMod "Hpt_down"; wp_load.
            iMod ("Hclose" with "[Hpt' Hpt_down Himp]") as "_".
            { 
              iNext; iExists L'.
              iPoseProof ("Himp" with "[Hpt' Hpt_down]") as "Hlist".
              { iFrame; iExists d, down'; by iFrame. }
              by iFrame.
            }

            iModIntro; wp_let.
            iDestruct "Hsucc'_range" as %Hsucc'_range; 
            iDestruct "Hsome'" as %Hsome'.
            iApply ("IH" $! down' (lvl - 1) down bot L with "[$] [%] [%]").
            { by right. }
            { rewrite -Hdown'_key; lia. }
            iNext; iIntros (pred'' succ'') "(Hlist & %Hkey_in_S'')".
            iApply "HΦ"; iSplit; last done.
            iExists l, down. by iFrame "# ∗".
      + destruct L as [|bot].
        - iModIntro. iApply "HΦ".
          iDestruct "Hlist" as "(#Hinv & %Hnone & %Heq)".
          rewrite -Heq; by iFrame "#".
        - iDestruct "Hlist" as (l down) "(#Hinv & %Hsome & Hpt & Hmatch)".
          iInv (levelN lvl) as (L') "(>%Hperm & >%Hsort & Hlist)" "Hclose".

          destruct Hpred_range as [|Hin]; first by congruence.
          rewrite -elem_of_elements elem_of_list_In -Hperm in Hin.
          rewrite list_equiv_invert_L; last done.
          iDestruct "Hlist" as (? ? ?) "(_ & _ & _ & _ & HP & _)".
          iDestruct "HP" as (? ?) "(Hfalse & _)".
          iMod "Hfalse" as %Hfalse; congruence.
    Qed.
    
    Theorem contains_spec (v: val) (key: Z) (Skeys: gset Z)
      (Hrange: INT_MIN < key < INT_MAX) :
      {{{ is_skip_list v Skeys }}}
        contains v #key
      {{{ (b: bool), RET #b; 
        is_skip_list v Skeys
        ∗
        ⌜ if b then key ∈ Skeys else key ∉ Skeys ⌝
      }}}.
    Proof.
      iIntros (Φ) "H HΦ".
      iDestruct "H" as (h head S L) "(%Hequiv & %Hv & Hpt & %Hmin & Hlist)".
      wp_lam. wp_let. rewrite -Hv. wp_load.
      wp_apply (findPred_spec with "[Hlist]").
      { iFrame "# ∗". iPureIntro; split. by left. lia. }
      iIntros (pred succ) "(Hlist & %Hkey_in_S)".
      wp_let. wp_match. wp_pures. wp_lam. wp_pures.

      iModIntro; case_bool_decide.
      + iApply "HΦ". iSplit. 
        iExists h, head, S, L.
        { by iFrame "# ∗". }
        iPureIntro. rewrite /key_equiv in Hequiv. 
        rewrite -elem_of_elements Hequiv Hkey_in_S.
        congruence.
      + iApply "HΦ". iSplit. 
        iExists h, head, S, L.
        { by iFrame "# ∗". }
        iPureIntro. intros Hin. 
        rewrite -elem_of_elements Hequiv Hkey_in_S in Hin.
        congruence.
    Qed.

  End Proofs.
End ContainsSpec.