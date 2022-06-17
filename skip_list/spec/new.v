From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc.
From SkipList.skip_list Require Import node_rep code key_equiv.
From SkipList.skip_list.inv Require Import list_equiv lazy_inv skip_inv.


Local Open Scope Z.
Module NewSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Invariant := SkipListInv Params.
  Import Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ}.

    Theorem newLoop_spec (head: node_rep) (lvl: Z) (bot: bot_gname) 
      (bot_sub: sub_gname) (bot_subs: list sub_gname) :
      {{{ 
        ⌜ node_key head = INT_MIN ⌝
        ∗
        ⌜ 1 ≤ lvl ⌝
        ∗
        skip_list_equiv head lvl 1 ∅ bot (bot_sub :: bot_subs)
      }}}
        newLoop (rep_to_node head) #lvl
      {{{ h top_head subs, RET #h;
        h ↦ rep_to_node top_head
        ∗
        ⌜ node_key top_head = INT_MIN ⌝
        ∗
        skip_list_equiv top_head MAX_HEIGHT 1 ∅ bot subs
      }}}.
    Proof.
      iIntros (Φ) "(Hmin & Hlvl & Hlist) HΦ".
      iRevert (head lvl bot_sub bot_subs) "Hmin Hlvl Hlist HΦ".
      iLöb as "IH".
      iIntros (head lvl bot_sub bot_subs) "%Hmin %Hlvl Hlist HΦ".

      wp_lam. wp_let. wp_alloc h as "Hh".
      wp_pures. case_bool_decide; wp_if.
      + iApply "HΦ". iModIntro.
        assert (lvl = MAX_HEIGHT) as <- by congruence.
        by iFrame.
      + iMod (own_alloc (● (∅ : gset node_rep) ⋅ ◯ (∅: gset node_rep)))
          as (γauth) "[Hown_auth Hown_auth_frag]"; 
          first by apply auth_both_valid.
        iMod (own_alloc (GSet node_key_range))
          as (γtoks) "Hown_toks"; first done.
        assert (node_key_range = node_key_range ∖ ∅) as -> by set_solver.
      
        wp_alloc t as "Ht". wp_let.
        iDestruct "Ht" as "(Ht1 & Ht2)".
        wp_apply (newlock_spec (node_inv t) with "[Ht1]").
        { iExists tail; iFrame. }
        
        iIntros (l) "#Hlock". iDestruct "Hlock" as (γ) "Hlock".
        wp_pures.
        set (top_head := (INT_MIN, Some t, Some h, l)).
        rewrite (fold_rep_to_node top_head).

        set (top := mk_sub_gname γauth γtoks).
        iMod (inv_alloc (levelN (lvl + 1)) ⊤ (lazy_list_inv top_head (from_top_list bot_sub) top None) 
          with "[Ht2 Hlock Hown_auth Hown_toks]") as "#Hinv".
        {
          iNext; iExists ∅, ∅, nil. iFrame.
          iSplit; first done. iSplit.
          {
            assert (node_lt top_head tail); last (simpl; auto).
            rewrite /node_lt/node_key//=; apply HMIN_MAX.
          }
          iSplit; first rewrite /key_equiv //.
          iExists t, γ. by iFrame "# ∗".
        }

        iApply ("IH" $! top_head (lvl+1) top (bot_sub :: bot_subs) 
          with "[%] [%] [Hlist Hh]").
        { done. }
        { lia. }
        {
          iExists h, head. 
          assert (lvl + 1 - 1 = lvl) as -> by lia.
          iSplit; first (iPureIntro; lia).
          by iFrame "# ∗". 
        }
        
        iNext; iApply "HΦ".
    Qed.

    Theorem new_spec : 
      {{{ True }}}
        new #()
      {{{ v bot subs, RET v;
        is_skip_list v 1 ∅ bot subs
      }}}.
    Proof.
      iIntros (Φ) "_ HΦ".

      iMod (own_alloc (● (∅ : gset node_rep) ⋅ ◯ (∅: gset node_rep)))
        as (γauth) "[Hown_auth Hown_auth_frag]"; 
        first by apply auth_both_valid.
      iMod (own_alloc (GSet node_key_range))
        as (γtoks) "Hown_toks"; 
        first done.
      iMod (own_alloc (●F (∅ : gset node_rep) ⋅ ◯F (∅: gset node_rep)))
        as (γfrac) "[Hown_frac Hown_frac_frag]"; 
        first by apply auth_both_valid.
      iMod (own_alloc (GSet node_key_range))
        as (γkeys) "Hown_keys"; 
        first done.
      assert (node_key_range = node_key_range ∖ ∅) as -> by set_solver.

      wp_lam. wp_alloc t as "Ht". wp_let.
      iDestruct "Ht" as "(Ht1 & Ht2)".
      wp_apply (newlock_spec (node_inv t) with "[Ht1]").
      { iExists tail; iFrame. }

      iIntros (l) "#Hlock". iDestruct "Hlock" as (γ) "Hlock".
      wp_pures.
      rewrite (fold_rep_to_node (INT_MIN, Some t, None, l)).
      set (bot_head := (INT_MIN, Some t, None, l)).

      set (sub := mk_sub_gname γauth γtoks).
      set (bot := mk_bot_gname γfrac γkeys).
      iMod (inv_alloc (levelN 1) ⊤ (lazy_list_inv bot_head from_bot_list sub (Some bot)) 
        with "[Ht2 Hlock Hown_auth Hown_toks Hown_frac Hown_keys]") as "#Hinv".
      {
        iNext; iExists ∅, ∅, nil. iFrame.
        iSplit; first done. iSplit.
        {
          assert (node_lt bot_head tail); last (simpl; auto).
          rewrite /node_lt/node_key//=; apply HMIN_MAX.
        }
        iSplit; first rewrite /key_equiv //.
        iExists t, γ. by iFrame "# ∗".
      }

      wp_apply (newLoop_spec _ _ bot sub nil with "[Hown_frac_frag]").
      {
        iSplit; first done. iSplit; first done. 
        iSplit; first done. iSplit; last done.
        iExists ∅; iFrame "# ∗"; rewrite /key_equiv //.
      }

      iIntros (h top_head subs) "(Hh & %Hmin & Hlist)"; wp_let.
      iModIntro; iApply ("HΦ" $! _ bot subs).
      iExists h, top_head. by iFrame.
    Qed.

  End Proofs.
End NewSpec.