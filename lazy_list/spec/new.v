From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lazy_list Require Import code.
From SkipList.lib Require Import misc node_rep node_lt key_equiv.
From SkipList.lazy_list.inv Require Import list_equiv inv.


Local Open Scope Z.

Module NewSpec (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module Invariant := LazyListInv Params.
  Export Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ}.

    Theorem new_spec :
      {{{ True }}}
        new #()
      {{{ v Γ, RET v; is_lazy_list v ∅ 1 Γ }}}.
    Proof.
      iIntros (Φ) "_ HΦ".

      iMod (own_alloc (● (∅ : gset node_rep) ⋅ ◯ (∅: gset node_rep)))
        as (γauth) "[Hown_auth Hown_auth_frag]"; 
        first by apply auth_both_valid.
      iMod (own_alloc (●F (∅ : gset Z) ⋅ ◯F (∅: gset Z)))
        as (γfrac) "[Hown_frac Hown_frac_frag]"; 
        first by apply auth_both_valid.
      iMod (own_alloc (GSet node_key_range))
        as (γkeys) "Hown_keys"; 
        first done.
      assert (node_key_range = node_key_range ∖ ∅) as -> by set_solver.

      wp_lam. wp_alloc t as "Ht". wp_let.
      iDestruct "Ht" as "(Ht1 & Ht2)".
      wp_apply (newlock_spec (in_lock t) with "[Ht1]").
      { iExists tail; iFrame. }

      iIntros (l γ) "#Hlock".
      wp_pures; wp_alloc h as "Hh".
      rewrite (fold_rep_to_node (INT_MIN, dummy_null, t, None, l)).
      set (head := (INT_MIN, dummy_null, t, None, l)).

      set (Γ := mk_lazy_gname γauth γfrac γkeys).
      iMod (inv_alloc lazyN ⊤ (lazy_list_inv head Γ) 
        with "[Ht2 Hlock Hown_auth Hown_frac Hown_keys]") as "#Hinv".
      {
        iNext; iExists ∅, ∅, nil. iFrame.
        iSplit; first done. iSplit. 
        { 
          assert (node_lt head tail); last (simpl; auto).
          rewrite /node_lt/node_key//=; apply HMIN_MAX. 
        }
        iSplit; first rewrite /key_equiv //.
        iExists γ. by iFrame "# ∗".
      }

      iModIntro; iApply "HΦ".
      iExists h, head. by iFrame "# ∗".
    Qed.

  End Proofs.
End NewSpec.