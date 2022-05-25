From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc.
From SkipList.skip_list Require Import node_rep code key_equiv.
From SkipList.skip_list.inv Require Import lazy_inv skip_inv.


Local Open Scope Z.
Module NewSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Invariant := SkipListInv Params.
  Import Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ}.

    Fixpoint is_empty (L: list (gset Z)) (lvl: Z) : iProp Σ :=
      match L with
      | nil => ⌜ lvl = 0 ⌝
      | h :: t => ⌜ h = ∅ ⌝
                  ∗
                  is_empty t (lvl - 1)
      end.

    Theorem newLoop_spec (head: node_rep) (lvl: Z) (Sbots: list (gset Z))
      (bot: lazy_gname) (bots: list lazy_gname) :
      {{{ 
        ⌜ node_key head = INT_MIN ⌝
        ∗
        ⌜ 1 ≤ lvl ⌝
        ∗
        is_empty (∅ :: Sbots) lvl
        ∗
        skip_list_equiv head lvl 1 (∅ :: Sbots) (bot :: bots)
      }}}
        newLoop (rep_to_node head) #lvl
      {{{ h top_head L_gset L_gname, RET #h;
        h ↦ rep_to_node top_head
        ∗
        ⌜ node_key top_head = INT_MIN ⌝
        ∗
        is_empty L_gset MAX_HEIGHT
        ∗
        skip_list_equiv top_head MAX_HEIGHT 1 L_gset L_gname
      }}}.
    Proof.
      iIntros (Φ) "(Hmin & Hlvl & Hempty & Hlist) HΦ".
      iRevert (head lvl Sbots bot bots) "Hmin Hlvl Hempty Hlist HΦ".
      iLöb as "IH".
      iIntros (head lvl Sbots bot bots) "%Hmin %Hlvl Hempty Hlist HΦ".

      wp_lam. wp_let. wp_alloc h as "Hh".
      wp_pures. case_bool_decide; wp_if.
      + iApply "HΦ". iModIntro.
        assert (lvl = MAX_HEIGHT) as <- by congruence.
        by iFrame.
      + iMod (own_alloc (● (∅ : gset node_rep) ⋅ ◯ (∅: gset node_rep)))
          as (γauth) "[Hown_auth Hown_auth_frag]"; 
          first by apply auth_both_valid.
        iMod (own_alloc (●F (∅ : gset node_rep) ⋅ ◯F (∅: gset node_rep)))
          as (γfrac) "[Hown_frac Hown_frac_frag]"; 
          first by apply auth_both_valid.
        iMod (own_alloc (GSet (Zlt_range INT_MIN INT_MAX)))
          as (γtok) "Hown_tok"; first done.

        assert (GSet (Zlt_range INT_MIN INT_MAX) =
          GSet (Zlt_range INT_MIN INT_MAX) ⋅ GSet (∅)) as ->.
        { rewrite gset_disj_union; f_equal; set_solver. }
        iDestruct "Hown_tok" as "(Hown_tok & Hown_emp)".
      
        wp_alloc t as "Ht". wp_let.
        iDestruct "Ht" as "(Ht1 & Ht2)".
        wp_apply (newlock_spec (node_inv t γtok (INT_MIN)) with "[Ht1 Hown_tok]").
        { iExists tail; iFrame. }
        
        iIntros (l) "#Hlock". iDestruct "Hlock" as (γ) "Hlock".
        wp_pures.
        set (top_head := (INT_MIN, Some t, Some h, l)).
        rewrite (fold_rep_to_node top_head).

        set (Γ := mk_lazy_gname γauth γfrac γtok).
        iMod (inv_alloc (levelN (lvl + 1)) ⊤ (lazy_list_inv top_head Γ (from_sub_list ∅)) 
          with "[Ht2 Hlock Hown_auth Hown_frac Hown_emp]") as "#Hinv".
        {
          iNext. iExists ∅, ∅, nil. iFrame.
          iSplit; first done. iSplit.
          {
            assert (node_lt top_head tail); last (simpl; auto).
            rewrite /node_lt/node_key//=; apply HMIN_MAX.
          }
          iSplit; first rewrite /key_equiv //.
          iExists t, γ. by iFrame "# ∗".
        }

        iApply ("IH" $! top_head (lvl+1) (∅ :: Sbots) Γ (bot :: bots) 
          with "[%] [%] [Hempty] [Hlist Hh Hown_frac_frag]").
        { done. }
        { lia. }
        { 
          rewrite /is_empty.
          assert (lvl + 1 - 1 = lvl) as -> by lia.
          by iFrame.
        }
        {
          iExists h, head, ∅.
          iSplit; first rewrite /key_equiv //.
          assert (lvl + 1 - 1 = lvl) as -> by lia.
          iFrame "# ∗". iPureIntro.
          by split; first lia.
        }
        
        iNext. iApply "HΦ".
    Qed.

    Theorem new_spec : 
      {{{ True }}}
        new #()
      {{{ v S L, RET v;
        is_skip_list v 1 S L
        ∗
        is_empty S MAX_HEIGHT
      }}}.
    Proof.
      iIntros (Φ) "_ HΦ".

      iMod (own_alloc (● (∅ : gset node_rep) ⋅ ◯ (∅: gset node_rep)))
        as (γauth) "[Hown_auth Hown_auth_frag]"; 
        first by apply auth_both_valid.
      iMod (own_alloc (●F (∅ : gset node_rep) ⋅ ◯F (∅: gset node_rep)))
        as (γfrac) "[Hown_frac Hown_frac_frag]"; 
        first by apply auth_both_valid.
      iMod (own_alloc (GSet (Zlt_range INT_MIN INT_MAX)))
        as (γtok) "Hown_tok"; first done.

      assert (GSet (Zlt_range INT_MIN INT_MAX) =
        GSet (Zlt_range INT_MIN INT_MAX) ⋅ GSet (∅)) as ->.
      { rewrite gset_disj_union; f_equal; set_solver. }
      iDestruct "Hown_tok" as "(Hown_tok & Hown_emp)".

      wp_lam. wp_alloc t as "Ht". wp_let.
      iDestruct "Ht" as "(Ht1 & Ht2)".
      wp_apply (newlock_spec (node_inv t γtok (INT_MIN)) with "[Ht1 Hown_tok]").
      { iExists tail; iFrame. }

      iIntros (l) "#Hlock". iDestruct "Hlock" as (γ) "Hlock".
      wp_pures.
      rewrite (fold_rep_to_node (INT_MIN, Some t, None, l)).
      set (bot_head := (INT_MIN, Some t, None, l)).

      set (Γ := mk_lazy_gname γauth γfrac γtok).
      iMod (inv_alloc (levelN 1) ⊤ (lazy_list_inv bot_head Γ from_bot_list) 
        with "[Ht2 Hlock Hown_auth Hown_frac Hown_emp]") as "#Hinv".
      {
        iNext. iExists ∅, ∅, nil. iFrame.
        iSplit; first done. iSplit.
        {
          assert (node_lt bot_head tail); last (simpl; auto).
          rewrite /node_lt/node_key//=; apply HMIN_MAX.
        }
        iSplit; first rewrite /key_equiv //.
        iExists t, γ. by iFrame "# ∗".
      }

      wp_apply (newLoop_spec _ _ nil Γ nil with "[Hown_frac_frag]").
      {
        iSplit; first done. iSplit; first done. iSplit; first done.
        iExists ∅. rewrite /key_equiv //.
        by iFrame "# ∗".
      }

      iIntros (h top_head S L) "(Hh & %Hmin & Hempty & Hlist)"; wp_let.
      iModIntro; iApply "HΦ".
      iFrame "# ∗". iExists h, top_head.
      by iFrame.
    Qed.

  End Proofs.
End NewSpec.