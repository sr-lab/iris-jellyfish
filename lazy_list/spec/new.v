From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lazy_list Require Import code.
From SkipList.lib Require Import misc node_rep node_lt.
From SkipList.lazy_list.inv Require Import list_equiv inv.


Local Open Scope Z.

Module NewSpec (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module Invariant := LazyListInv Params.
  Export Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !lazyGS Σ, !lockG Σ}.

    Theorem new_spec :
      {{{ True }}}
        new #()
      {{{ p Γ, RET #p; is_lazy_list p ∅ 1 Γ }}}.
    Proof.
      iIntros (Φ) "_ HΦ".

      wp_lam. wp_alloc t as "Ht". wp_let.
      iDestruct "Ht" as "(Ht1 & Ht2)".
      wp_apply (newlock_spec (in_lock t) with "[Ht1]").
      { iExists tail; iFrame. }
      iIntros (l γ) "#Hlock".

      wp_pures.
      set (head := (INT_MIN, dummy_null, t, @None loc, l, dummy_null)).
      rewrite (fold_rep_to_node head).

      iMod (own_alloc (● ∅ ⋅ ◯ ∅))
        as (γauth) "[Hown_auth Hown_auth_frag]"; 
        first by apply auth_both_valid.
      iMod (own_alloc (●F ∅ ⋅ ◯F ∅))
        as (γfrac) "[Hown_frac Hown_frac_frag]"; 
        first by apply auth_both_valid.

      wp_alloc h as "Hh".
      iMod (mapsto_persist with "Hh") as "#Hh".

      set (Γ := mk_lazy_gname γauth γfrac).
      iMod (inv_alloc lazyN ⊤ (lazy_list_inv head Γ) 
        with "[Ht2 Hlock Hown_auth Hown_frac]") as "#Hinv".
      {
        iNext; iExists ∅, nil.
        rewrite set_map_empty. iFrame. 
        iSplit; first done. iSplit.
        { 
          assert (node_lt head tail); last (simpl; auto).
          rewrite /node_lt/node_key//=; apply HMIN_MAX. 
        }
        iExists γ. by iFrame "# ∗".
      }

      iModIntro; iApply "HΦ".
      iExists head. by iFrame "# ∗".
    Qed.

  End Proofs.
End NewSpec.