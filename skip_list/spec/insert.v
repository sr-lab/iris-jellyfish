From Coq Require Import Sorting.Sorted.

From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc.
From SkipList.skip_list Require Import node_rep code key_equiv.
From SkipList.skip_list.inv Require Import list_equiv lazy_inv skip_inv.
From SkipList.skip_list.spec Require Import link.


Local Open Scope Z.
Module InsertSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Link := LinkSpec Params.
  Export Link.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ} (N : namespace).

    Theorem tryInsert_spec (curr head: node_rep) (key: Z) 
      (q: frac) (Skeys: gset Z) (sub: sub_gname) (bot: bot_gname) :
      INT_MIN < key < INT_MAX →
      {{{
        is_bot_list N head q Skeys sub bot
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key ⌝
      }}}
        tryInsert (rep_to_node curr) #key
      {{{ v new, RET v;
        is_bot_list N head q (Skeys ∪ {[ key ]}) sub bot
        ∗
        ( 
          ⌜ v = NONEV ⌝ ∨ 
          ( 
            ⌜ v = SOMEV (rep_to_node new) ⌝ 
            ∗ 
            own (s_auth sub) (◯ {[ new ]})
            ∗ 
            own (s_toks sub) (GSet {[ node_key new ]})
            ∗ 
            own (s_keys bot) (GSet {[ node_key new ]})
            ∗ 
            ⌜ node_key new = key ⌝
          )
        )
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(Hlazy & #Hown_curr & %Hrange) HΦ".
      iDestruct "Hlazy" as (Sfrag) "(%Hequiv & Hown_frag & #Hinv)".
      wp_lam. wp_let.

      wp_apply findLock_spec.
      { iFrame "#". iPureIntro; lia. }
      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & Hlock)".
      iDestruct "Hlock" as (l γ) "(%Hsome & #Hlock & Hpt & Hlocked)".

      wp_pures. wp_lam. wp_pures.
      case_bool_decide as Hcase; wp_if.
      + assert (key = node_key succ) as Heq by congruence.
        iDestruct "Hown_succ" as "[Hown_succ|%Hsucc]"; last first.
        { subst; exfalso. rewrite /node_key/tail/= in Hkey_range; lia. }

        wp_lam. wp_bind (Snd _).

        iInv N as (S Skeys' L) "(Hinv_sub & Hinv_bot)" "Hclose".
        iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv' & >Hown_auth & Hown_toks & Hlist)".
        iDestruct "Hinv_bot" as "(>Hown_frac & >Hown_keys)".

        iDestruct (own_valid_2 with "Hown_auth Hown_succ") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.
        iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
          as %Hsub%frac_auth_included_total%gset_included.
        iMod (own_update_2 with "Hown_frac Hown_frag") as "[Hown_frac Hown_frag]".
        { apply frac_auth_update, (gset_local_update_union _ _ {[ succ ]}). }

        wp_proj.
        iMod ("Hclose" with "[Hlist Hown_auth Hown_toks Hown_frac Hown_keys]") as "_".
        {
          iNext; iExists S, Skeys', L.
          assert (S = S ∪ {[ succ ]}) as <- by set_solver.
          by iFrame.
        }
        iModIntro.

        wp_apply (release_spec with "[Hlock Hpt Hlocked]"); first done.
        { iFrame "# ∗"; iExists succ; iFrame. }
        iIntros "_". wp_pures.
        iModIntro. iApply ("HΦ" $! _ succ).
        iSplitR ""; last by iLeft.
        iExists (Sfrag ∪ {[ succ ]}). 
        iFrame "# ∗". iPureIntro.

        eapply key_equiv_union.
        { done. }
        { by do 2 apply node_rep_sorted_app in Hsort as [? Hsort]. }
        { done. }
        { rewrite Heq /key_equiv ?elements_singleton //. }
        { by apply union_subseteq. }
      + assert (key ≠ node_key succ) as Hneq by congruence.
        assert (oloc_to_val None = NONEV) as <- by auto.

        wp_apply (link_bot_spec with "[Hpt Hlocked Hown_frag]").
        { done. }
        { 
          iFrame "# ∗". 
          iSplit. iExists Sfrag; by iFrame.
          iPureIntro. by split; first lia.
        }
        
        iIntros (new) "(Hlazy & Hkey & Hown_frag & Hown_tok & Hown_key)".
        iApply "HΦ". iSplitL "Hlazy"; last iRight; by iFrame.
    Qed.

    Theorem insert_spec (curr down head: node_rep) (key: Z) (top bot: sub_gname) :
      INT_MIN < key < INT_MAX →
      {{{
        inv N (lazy_list_inv head (from_top_list bot) top None)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth top) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key ⌝
        ∗ 
        own (s_auth bot) (◯ {[ down ]})
        ∗ 
        own (s_toks bot) (GSet {[ node_key down ]})
        ∗ 
        ⌜ node_key down = key ⌝
      }}}
        insert (rep_to_node curr) #key (rep_to_node down)
      {{{ new, RET SOMEV (rep_to_node new);
        own (s_auth top) (◯ {[ new ]})
        ∗ 
        own (s_toks top) (GSet {[ node_key new ]})
        ∗ 
        ⌜ node_key new = key ⌝
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(#Hinv & #Hown_curr & %Hrange & #Hown_down & Hown_tok & %Hdown) HΦ".
      wp_lam. wp_let. wp_let.

      wp_apply findLock_spec.
      { iFrame "#". iPureIntro; lia. }
      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & Hlock)".
      iDestruct "Hlock" as (l γ) "(%Hsome & #Hlock & Hpt & Hlocked)".

      wp_let. wp_match.
      wp_bind (Fst _).
      iInv N as (S Skeys' L) "(Hinv_sub & _)" "Hclose".
      iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv' & >Hown_auth & Hown_toks & Hlist)".
      wp_proj.

      iAssert ⌜ key ≠ node_key succ ⌝%I
        with "[Hown_auth Hown_succ Hown_tok Hlist]" as %Hneq.
      {
        iDestruct "Hown_succ" as "[Hown|%Heq]"; last first.
        { iPureIntro; rewrite Heq /node_key /=; lia. } 

        iDestruct (own_valid_2 with "Hown_auth Hown") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.
        assert (succ ∈ S) by set_solver.

        rewrite list_equiv_invert_L; last first.
        { by rewrite -elem_of_list_In Hperm elem_of_elements. }
        iDestruct "Hlist" as (? ? ? ? ? ) "(_ & _ & _ & _ & _ & HP & _)".
        destruct (node_down succ) as [d|]; last by iExFalso.
        iDestruct "HP" as (?) "(_ & _ & Hown_tok' & %Hsucc)".

        iDestruct (own_valid_2 with "Hown_tok Hown_tok'") as 
          %Hdisj%gset_disj_valid_op.
        iPureIntro; set_solver.
      }

      iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
      { iNext; iExists S, Skeys', L; by iFrame "# ∗". }

      iModIntro; wp_pures. 
      wp_alloc d as "Hpt_down". 
      wp_pures.

      assert (oloc_to_val (Some d) = SOMEV #d) as <- by auto.
      iAssert (from_top_list bot key (Some d))
        with "[Hpt_down Hown_tok]" as "HP".
      { iExists down; by iFrame "# ∗". }

      wp_apply (link_top_spec with "[Hpt Hlocked HP]").
      { done. }
      { 
        iFrame "# ∗"; iPureIntro. 
        by split; first lia.
      }
      iApply "HΦ".
    Qed.

  End Proofs.
End InsertSpec.