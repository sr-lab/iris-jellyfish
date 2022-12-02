From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.skip_list.arrays Require Import code.
From SkipList.lib Require Import misc node_rep node_lt.
From SkipList.skip_list.arrays.inv Require Import list_equiv lazy_inv skip_inv. 
From SkipList.skip_list.arrays.spec Require Import link.


Local Open Scope Z.

Module InsertSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Link := LinkSpec Params.
  Export Link.

  Section Proofs.
    Context `{!heapGS Σ, !skipGS Σ, !lockG Σ}.

    Theorem tryInsert_spec (k h: Z) (head curr: node_rep) 
      (Skeys: gset Z) (q: frac)
      (bot: bot_gname) (Γ: sub_gname) :
      INT_MIN < k < INT_MAX →
      {{{
        inv (levelN 0) (lazy_list_inv 0 head (Some bot) Γ None)
        ∗
        own (s_frac bot) (◯F{q} Skeys)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth Γ) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < k ⌝
        ∗
        ⌜ 0 ≤ h ⌝ 
      }}}
        tryInsert (rep_to_node curr) #k #h
      {{{ (v: val) (n: loc) (new: node_rep), RET v;
        own (s_frac bot) (◯F{q} (Skeys ∪ {[ k ]}))
        ∗
        ( 
          ⌜ v = NONEV ⌝ ∨ 
          ( 
            ⌜ v = SOMEV #n ⌝ 
            ∗ 
            own (s_auth Γ) (◯ {[ new ]})
            ∗ 
            own (s_toks Γ) (◯ GSet {[ node_key new ]})
            ∗ 
            ⌜ node_key new = k ⌝
            ∗
            n ↦□ rep_to_node new
            ∗
            (node_next new +ₗ 1) ↦∗{#1 / 2} replicate (Z.to_nat h) #()
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
      iIntros (Hkey_range Φ) "(#Hinv & Hown_frag & #Hown_curr & %Hrange & %Hh) HΦ".
      wp_lam. wp_let. wp_let.

      wp_apply findLock_spec.
      { iFrame "#". iPureIntro; lia. }
      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & Hlock)".
      iDestruct "Hlock" as (γ' h' s) "(%Hlvl & #Hlock & _ & Hpt & #Hs & Harray & Hlocked)".
      rewrite loc_add_0.
      assert (h' - 1 - 0 = h' - 1) as -> by lia.

      wp_pures. wp_lam. wp_pures. wp_lam. wp_pures.
      case_bool_decide as Hcase; wp_if.
      + assert (k = node_key succ) as Heq by congruence.
        iDestruct "Hown_succ" as "[Hown_succ|%Hsucc]"; last first.
        { subst; exfalso. rewrite /node_key/tail/= in Hkey_range; lia. }

        wp_apply (release_spec with "[Hlock Hpt Harray Hlocked]").
        { 
          iFrame "# ∗". 
          iDestruct "Harray" as (vs) "(Hnext & %Hlength)".
          iCombine "Hpt Hnext" as "Hnext"; rewrite -array_cons.
          iExists (#s :: vs); iFrame.
          iPureIntro; rewrite cons_length; lia.
        }
        iIntros "_". wp_pures.

        iInv (levelN 0) as (S L) "(Hinv_sub & >Hown_frac)" "Hclose".
        iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >Hown_auth & >Hown_toks & Hlist)".

        iDestruct (own_valid_2 with "Hown_auth Hown_succ") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.
        iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
          as %Hsub%frac_auth_included_total%gset_included.
        iMod (own_update_2 with "Hown_frac Hown_frag") as "[Hown_frac Hown_frag]".
        { apply frac_auth_update, (gset_local_update_union _ _ {[ k ]}). }
        assert (set_map node_key S ∪ {[ k ]} = set_map node_key S) as -> by set_solver.

        iMod ("Hclose" with "[Hlist Hown_auth Hown_toks Hown_frac]") as "_".
        { iNext; iExists S, L; by iFrame. }
        iModIntro. iApply "HΦ".
        iFrame "# ∗". by iLeft.
      + assert (k ≠ node_key succ) as Hneq by congruence.

        wp_apply (createAndLink_spec with "[Hpt Hown_frag]").
        { done. }
        { iFrame "# ∗". iPureIntro; lia. }
        iIntros (n new) "(Hlazy & Hown_frag & Hown_tok & Hkey & Hpt & Hn & Hnext & Hlock')".
        wp_let.

        wp_apply (release_spec with "[Hlock Hpt Harray Hlocked]").
        { 
          iFrame "# ∗". 
          iDestruct "Harray" as (vs) "(Hnext & %Hlength)".
          iCombine "Hpt Hnext" as "Hnext"; rewrite -array_cons.
          iExists (#n :: vs); iFrame.
          iPureIntro; rewrite cons_length; lia.
        }
        iIntros "_"; wp_pures.
        iModIntro; iApply "HΦ".
        iFrame. iRight; by iFrame.
    Qed.

    Theorem insert_spec (h lvl: Z) (head curr new: node_rep) 
      (Γ γ: sub_gname) (γl: gname) (n: loc) :
      INT_MIN < node_key new < INT_MAX →
      {{{
        inv (levelN lvl) (lazy_list_inv lvl head None Γ (Some γ))
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth Γ) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < node_key new ⌝
        ∗
        ⌜ 0 < lvl < h ⌝
        ∗ 
        own (s_auth γ) (◯ {[ new ]})
        ∗ 
        own (s_toks γ) (◯ GSet {[ node_key new ]})
        ∗
        n ↦□ rep_to_node new
        ∗
        (node_next new +ₗ lvl) ↦ #()
        ∗
        is_lock γl (node_lock new) (is_array (node_next new) h)
      }}}
        insert (rep_to_node curr) #lvl #n
      {{{ s, RET #();
        own (s_auth Γ) (◯ {[ new ]})
        ∗ 
        own (s_toks Γ) (◯ GSet {[ node_key new ]})
        ∗
        (node_next new +ₗ lvl) ↦{#1 / 2} #s
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(#Hinv & #Hown_curr & %Hrange & %Hlvl & Hown_frag & Hown_tok & #Hn & Hnext & #Hlock) HΦ".
      wp_lam. wp_let. wp_let.
      wp_load. wp_lam. wp_pures.

      wp_apply findLock_spec.
      { iFrame "#". iPureIntro; lia. }
      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & Hlock')".
      iDestruct "Hlock'" as (γl' h' s) "(%Hlvl' & #Hlock' & Harray1 & Hpt & #Hs & Harray2 & Hlocked')".
      wp_let. 

      wp_bind (Fst _).
      iInv (levelN lvl) as (S L) "(Hinv_sub & _)" "Hclose".
      iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >Hown_auth & >Hown_toks & Hlist)".
      wp_proj.

      iAssert ⌜ node_key new ≠ node_key succ ⌝%I
        with "[Hown_auth Hown_succ Hown_tok Hlist]" as %Hneq.
      {
        iDestruct "Hown_succ" as "[Hown|%Heq]"; last first.
        { iPureIntro. rewrite Heq/node_key/=; rewrite /node_key/= in Hkey_range; lia. } 

        iDestruct (own_valid_2 with "Hown_auth Hown") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.

        assert (In succ L).
        { rewrite -elem_of_list_In Hperm elem_of_elements. set_solver. }

        rewrite list_equiv_invert_L; last done.
        iDestruct "Hlist" as (? ? ? ?) "(_ & _ & _ & _ & _ & Hnode & _)".
        iDestruct "Hnode" as "(_ & Hown_tok')".

        iDestruct (own_valid_2 with "Hown_tok Hown_tok'") as 
          %Hdisj%auth_frag_op_valid_1%gset_disj_valid_op.
        iPureIntro; set_solver.
      }

      iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
      { iNext; iExists S, L; by iFrame "# ∗". }
      iModIntro; wp_pures.
      wp_lam. wp_pures.

      wp_apply (link_spec with "[Hpt Hnext Hown_frag Hown_tok]").
      { done. }
      { iFrame "# ∗"; iPureIntro; lia. }
      iIntros "(Hown_frag & Hown_tok & Hpt & Hnext)".
      
      wp_pures.
      wp_apply (release_spec with "[Harray1 Hpt Harray2 Hlocked']").
      { 
        iFrame "# ∗". 
        iDestruct "Harray1" as (vs1) "(Hnext1 & %Hlength1)".
        iDestruct "Harray2" as (vs2) "(Hnext2 & %Hlength2)".
        iCombine "Hnext1 Hpt Hnext2" as "Hnext".
        assert (lvl = Z.to_nat lvl) as -> by lia.
        rewrite -array_cons -Hlength1 -array_app.
        iExists (vs1 ++ #n :: vs2); iFrame.
        iPureIntro. rewrite app_length cons_length; lia.
      }
      iIntros "_"; iApply "HΦ"; iFrame.
    Qed.

  End Proofs.
End InsertSpec.