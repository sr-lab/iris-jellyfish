From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc.
From SkipList.lazy_list Require Import inv node_rep code key_equiv.


Local Open Scope Z.
Module NewSpec (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module Invariant := LazyListInv Params.
  Import Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, lockG Σ} (N : namespace).

    Theorem new_spec :
      {{{ True }}}
        new #()
      {{{ Γ v, RET v; 
        is_lazy_list N v ∅ 1 Γ
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
      set (head := (INT_MIN, Some t, l)).
      wp_pures; wp_alloc h as "Hh".
      rewrite (fold_rep_to_node head).

      iMod (inv_alloc N ⊤ (lazy_list_inv head γauth γfrac γtok) 
        with "[Ht2 Hlock Hown_auth Hown_frac Hown_emp]") as "#Hinv".
      + iNext. iExists ∅, ∅, nil. iFrame.
        iSplit; first done. iSplit. 
        { 
          assert (node_lt head tail); last (simpl; auto).
          rewrite /node_lt/node_key//=; apply HMIN_MAX. 
        }
        iSplit; first rewrite /key_equiv //.
        iExists t, γ. by iFrame "# ∗".
      + iModIntro; iApply ("HΦ" $! (mk_lazy_gname γauth γfrac γtok)).
        iExists h, head, ∅.
        iSplit; first rewrite /key_equiv //.
        by iFrame "# ∗".
    Qed.

  End Proofs.
End NewSpec.