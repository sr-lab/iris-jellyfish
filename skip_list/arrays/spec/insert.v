From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.skip_list.arrays Require Import code.
From SkipList.lib Require Import misc node_rep node_lt key_equiv.
From SkipList.skip_list.arrays.inv Require Import list_equiv lazy_inv skip_inv. 
From SkipList.skip_list.arrays.spec Require Import link.


Local Open Scope Z.

Module InsertSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Link := LinkSpec Params.
  Export Link.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ} (lvl: Z).

    Theorem tryInsert_spec (key h: Z) (head curr: node_rep) (Skeys: gset Z) (q: frac)
      (sub: sub_gname) (bot: bot_gname) :
      INT_MIN < key < INT_MAX →
      {{{
        is_bot_list 0 head Skeys q sub bot
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key ⌝
        ∗
        ⌜ 0 ≤ h ⌝ 
      }}}
        tryInsert (rep_to_node curr) #key #h
      {{{ (v: val) (n: loc) (new: node_rep), RET v;
        is_bot_list 0 head (Skeys ∪ {[ key ]}) q sub bot
        ∗
        ( 
          ⌜ v = NONEV ⌝ ∨ 
          ( 
            ⌜ v = SOMEV #n ⌝ 
            ∗ 
            own (s_auth sub) (◯ {[ new ]})
            ∗ 
            own (s_toks sub) (GSet {[ node_key new ]})
            ∗ 
            own (s_keys bot) (GSet {[ node_key new ]})
            ∗ 
            ⌜ node_key new = key ⌝
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
      iIntros (Hkey_range Φ) "(Hlazy & #Hown_curr & %Hrange & %Hh) HΦ".
      iDestruct "Hlazy" as "(Hown_frag & #Hinv)".
      wp_lam. wp_let. wp_let.

      wp_apply findLock_spec.
      { iFrame "#". iPureIntro; lia. }
      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & Hlock)".
      iDestruct "Hlock" as (γ' h' s) "(%Hlvl & #Hlock & _ & Hpt & #Hs & Harray & Hlocked)".
      rewrite loc_add_0.
      assert (h' - 1 - 0 = h' - 1) as -> by lia.

      wp_pures. wp_lam. wp_pures.
      case_bool_decide as Hcase; wp_if.
      + assert (key = node_key succ) as Heq by congruence.
        iDestruct "Hown_succ" as "[Hown_succ|%Hsucc]"; last first.
        { subst; exfalso. rewrite /node_key/tail/= in Hkey_range; lia. }

        wp_lam. wp_bind (Fst _).
        iInv (levelN 0) as (S' Skeys' L) "(Hinv_sub & Hinv_bot)" "Hclose".
        iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv' & >Hown_auth & >Hown_toks & Hlist)".
        iDestruct "Hinv_bot" as "(>Hown_frac & >Hown_keys)".

        iDestruct (own_valid_2 with "Hown_auth Hown_succ") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.
        iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
          as %Hsub%frac_auth_included_total%gset_included.
        iMod (own_update_2 with "Hown_frac Hown_frag") as "[Hown_frac Hown_frag]".
        { apply frac_auth_update, (gset_local_update_union _ _ {[ key ]}). }
        assert (key ∈ Skeys') as Hin.
        { rewrite Heq. eapply key_equiv_in; first done. set_solver. }
        assert (Skeys' ∪ {[ key ]} = Skeys') as -> by set_solver.

        wp_proj.
        iMod ("Hclose" with "[Hlist Hown_auth Hown_toks Hown_frac Hown_keys]") as "_".
        { iNext; iExists S', Skeys', L; by iFrame. }
        iModIntro. wp_proj.

        wp_apply (release_spec with "[Hlock Hpt Harray Hlocked]").
        { 
          iFrame "# ∗". 
          iDestruct "Harray" as (vs) "(Hnext & %Hlength)".
          iCombine "Hpt Hnext" as "Hnext"; rewrite -array_cons.
          iExists (#s :: vs); iFrame.
          iPureIntro; rewrite cons_length; lia.
        }

        iIntros "_". wp_pures.
        iModIntro. iApply "HΦ".
        iFrame "# ∗". by iLeft.
      + assert (key ≠ node_key succ) as Hneq by congruence.

        wp_apply (createAndLink_spec with "[Hpt Hown_frag]").
        { done. }
        { iFrame "# ∗". iPureIntro; lia. }
        
        iIntros (n new) "(Hlazy & Hown_frag & Hown_tok & Hown_key & Hkey & Hpt & Hn & Hnext & Hlock')".
        wp_let. wp_lam. wp_pures.

        wp_apply (release_spec with "[Hlock Hpt Harray Hlocked]").
        { 
          iFrame "# ∗". 
          iDestruct "Harray" as (vs) "(Hnext & %Hlength)".
          iCombine "Hpt Hnext" as "Hnext"; rewrite -array_cons.
          iExists (#n :: vs); iFrame.
          iPureIntro; rewrite cons_length; lia.
        }

        iIntros "_". wp_pures.
        iModIntro. iApply "HΦ".
        iFrame. iRight; by iFrame.
    Qed.

    Theorem insert_spec (key h: Z) (head curr new: node_rep) 
      (top bot: sub_gname) (γ: gname) (n: loc) :
      INT_MIN < key < INT_MAX →
      {{{
        inv (levelN lvl) (lazy_list_inv lvl head top None (from_top_list bot))
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth top) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key ⌝
        ∗
        ⌜ 0 < lvl < h ⌝
        ∗ 
        own (s_auth bot) (◯ {[ new ]})
        ∗ 
        own (s_toks bot) (GSet {[ node_key new ]})
        ∗ 
        ⌜ node_key new = key ⌝
        ∗
        n ↦□ rep_to_node new
        ∗
        (node_next new +ₗ lvl) ↦ #()
        ∗
        is_lock γ (node_lock new) (is_array (node_next new) h)
      }}}
        insert (rep_to_node curr) #lvl #n
      {{{ s, RET #();
        own (s_auth top) (◯ {[ new ]})
        ∗ 
        own (s_toks top) (GSet {[ node_key new ]})
        ∗
        (node_next new +ₗ lvl) ↦{#1 / 2} #s
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(#Hinv & #Hown_curr & %Hrange & %Hlvl & Hown_frag & Hown_tok & %Hkey & #Hn & Hnext & #Hlock) HΦ".
      wp_lam. wp_let. wp_let.
      wp_load. wp_lam. wp_pures.

      wp_apply findLock_spec.
      { iFrame "#". iPureIntro; lia. }
      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & Hlock')".
      iDestruct "Hlock'" as (γ' h' s) "(%Hlvl' & #Hlock' & Harray1 & Hpt & #Hs & Harray2 & Hlocked')".

      wp_let.
      wp_bind (Fst _).
      iInv (levelN lvl) as (S' Skeys' L) "(Hinv_sub & _)" "Hclose".
      iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv' & >Hown_auth & >Hown_toks & Hlist)".
      wp_proj.

      iAssert ⌜ key ≠ node_key succ ⌝%I
        with "[Hown_auth Hown_succ Hown_tok Hlist]" as %Hneq.
      {
        iDestruct "Hown_succ" as "[Hown|%Heq]"; last first.
        { iPureIntro; rewrite Heq /node_key /=; lia. } 

        iDestruct (own_valid_2 with "Hown_auth Hown") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.

        assert (In succ L).
        { rewrite -elem_of_list_In Hperm elem_of_elements. set_solver. }

        rewrite list_equiv_invert_L; last done.
        iDestruct "Hlist" as (? ? ? ?) "(_ & _ & _ & _ & _ & HP & _)".
        iDestruct "HP" as "(_ & Hown_tok')".

        iDestruct (own_valid_2 with "Hown_tok Hown_tok'") as 
          %Hdisj%gset_disj_valid_op.
        iPureIntro; set_solver.
      }

      iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
      { iNext; iExists S', Skeys', L; by iFrame "# ∗". }

      iModIntro; wp_pures.

      wp_apply (link_spec lvl key h head pred new succ with "[Hpt Hnext Hown_frag Hown_tok]").
      { done. }
      { iFrame "# ∗"; iPureIntro; lia. }

      iIntros "(Hown_frag & Hown_tok & Hpt & Hnext)".
      wp_pures. wp_lam. wp_pures.
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

      iIntros "_". iApply "HΦ". iFrame.
    Qed.

  End Proofs.
End InsertSpec.