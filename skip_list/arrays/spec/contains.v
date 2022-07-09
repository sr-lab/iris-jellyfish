From Coq Require Import Sorting.Sorted.

From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc node_rep node_lt key_equiv.
From SkipList.skip_list.arrays Require Import code.
From SkipList.skip_list.arrays.inv Require Import list_equiv lazy_inv skip_inv.
From SkipList.skip_list.arrays.spec Require Import find.


Local Open Scope Z.

Module ContainsSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Find := FindSpec Params.
  Export Find.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ}.
    
    Theorem findPred_spec (key lvl: Z) (head curr: node_rep) 
      (Skeys: gset Z) (bot: bot_gname) 
      (top_sub: sub_gname) (bot_subs: list sub_gname) :
      {{{ 
        skip_list_equiv lvl head Skeys 1 bot (top_sub :: bot_subs)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth top_sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
        findPred (rep_to_node curr) #key #lvl
      {{{ pred succ, RET ((rep_to_node pred), (rep_to_node succ));
        skip_list_equiv lvl head Skeys 1 bot (top_sub :: bot_subs)
        ∗
        ⌜ key ∈ Skeys ↔ node_key succ = key ⌝
      }}}.
    Proof.
      iIntros (Φ) "(Hlist & Hown_curr & Hrange) HΦ".
      iRevert (curr head lvl top_sub bot_subs) "Hlist Hown_curr Hrange HΦ".
      iLöb as "IH".
      iIntros (curr head lvl top_sub bot_subs) "Hlist #Hown_curr %Hrange HΦ".

      wp_lam. wp_let. wp_let.
      destruct bot_subs as [|bot_sub].
      + iDestruct "Hlist" as "(%Hlvl & (Hown_frag & #Hinv))".
        wp_apply (find_bot_spec with "[Hown_frag]").
        { by iFrame "# ∗". }
        iIntros (pred succ) "(Hown_frag & %Hpred_key & #Hown_pred & %Hkey_in_S)".

        wp_pures. case_bool_decide; wp_if.
        - iModIntro. iApply "HΦ". 
          by iFrame "# ∗".
        - exfalso; congruence.
      + iDestruct "Hlist" as "(%Hlvl & #Hinv & Hmatch)".
        unfold is_top_list.
        wp_apply find_sub_spec.
        { by iFrame "# ∗". }
        iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & _)".

        wp_pures. case_bool_decide as Hcase; wp_if.
        - exfalso; inversion Hcase; lia.
        - wp_bind (Fst _).
          iInv (levelN lvl) as (S Skeys' L) "(Hinv_sub & _)" "Hclose".
          iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_toks & Hlist)".

          iDestruct "Hown_pred" as "[%Heq | #Hown_pred]".
          * wp_proj.
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists S, Skeys', L; by iFrame. }

            iModIntro; wp_pures.
            iApply ("IH" with "[$] [] [%]").
            { by iLeft. }
            { lia. }
            iNext; iIntros (? ?) "(? & ?)".
            iApply "HΦ". by iFrame "# ∗".
          * iAssert ⌜ In pred L ⌝%I with "[Hown_auth]" as %Hin.
            {
              iDestruct (own_valid_2 with "Hown_auth Hown_pred") 
                as %[Hvalid%gset_included]%auth_both_valid_discrete.
              rewrite -elem_of_list_In Hperm elem_of_elements.
              iPureIntro; set_solver.
            }

            rewrite list_equiv_invert_L; last done.
            iDestruct "Hlist" as (γ h s' succ') "(>%Hsucc'_range & Hpt' & #Hinvs' & Hs' & Hlock & #Hlvl & HP & Himp)".
            iDestruct "HP" as"(>Hauth_pred & >Htoks_pred)".

            assert ({[ pred ]} = {[ pred ]} ⋅ {[ pred ]}) as -> by set_solver.
            iDestruct "Hauth_pred" as "(Hauth_pred & ?)".
            assert ({[ pred ]} = {[ pred ]} ⋅ {[ pred ]}) as <- by set_solver.

            wp_proj.
            iPoseProof ("Himp" with "[$]") as "Hlist".
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists S, Skeys', L; by iFrame. }

            iModIntro; wp_pures.
            iApply ("IH" with "[$] [Hauth_pred] [%]").
            { by iRight. }
            { lia. }
            iNext; iIntros (? ?) "(? & ?)".
            iApply "HΦ". by iFrame "# ∗".
    Qed.
    
    Theorem contains_spec (v: val) (key: Z) 
      (S: gset Z) (bot: bot_gname) (subs: list sub_gname)
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
        { iExists h, head; by iFrame. }
        iPureIntro. 
        rewrite Hkey_in_S; congruence.
      + iApply "HΦ". iSplit. 
        { iExists h, head; by iFrame. }
        iPureIntro; intros Hin. 
        rewrite Hkey_in_S in Hin; congruence.
    Qed.

  End Proofs.
End ContainsSpec.