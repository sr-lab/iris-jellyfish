From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc.
From SkipList.skip_list Require Import inv node_rep code key_equiv.


Local Open Scope Z.
Module NewSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Invariant := SkipListInv Params.
  Import Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, lockG Σ} (N : namespace).

    Theorem newLoop_spec (head: node_rep) (lvl: Z) (L: list (list node_rep)):
      {{{ 
        skip_list_equiv head lvl (nil :: L) ∅ ∅ 
      }}}
        newLoop (rep_to_node head) #lvl
      {{{ h top_head L', RET #h;
        h ↦ rep_to_node top_head
        ∗
        skip_list_equiv top_head MAX_HEIGHT L' ∅ ∅ 
      }}}.
    Proof.
      iIntros (Φ) "Hlist HΦ".
      iRevert (head lvl L) "Hlist HΦ".
      iLöb as "IH".
      iIntros (head lvl L) "Hlist HΦ".

      wp_lam. wp_let. wp_alloc h as "Hh".
      wp_pures. case_bool_decide; wp_if.
      + iApply "HΦ". iModIntro.
        assert (lvl = MAX_HEIGHT) as <- by congruence.
        iFrame.
      + wp_alloc t as "Ht". wp_let.
        iDestruct "Ht" as "(Ht1 & Ht2)".
        wp_apply (newlock_spec (node_inv t) with "[Ht1]").
        { iExists tail; iFrame. }
        iIntros (l) "#Hlock". iDestruct "Hlock" as (γ) "Hlock".
        wp_pures.
        set (top_head := (INT_MIN, Some t, Some h, l)).
        rewrite (fold_rep_to_node top_head).

        iMod (inv_alloc (levelN (lvl + 1)) ⊤ (lazy_list_inv top_head ∅) 
          with "[Ht2]") as "#Hinv".
        {
          iNext; iExists nil. 
          iSplit; first done. iSplit.
          {
            assert (node_lt top_head tail); last (simpl; auto).
            rewrite /node_lt/node_key//=; apply HMIN_MAX.
          }
          iSplit; first done.
          iExists t, γ. by iFrame "# ∗".
        }

        iApply ("IH" $! top_head (lvl+1) (nil :: L) with "[Hlist Hh]").
        - iExists ∅, h, head.
          assert (lvl + 1 - 1 = lvl) as -> by lia.
          by iFrame "# ∗".
        - iNext; iApply "HΦ".
    Qed.

    Theorem new_spec : 
      {{{ True }}}
        new #()
      {{{ v, RET v;
        is_skip_list N v ∅
      }}}.
    Proof.
      iIntros (Φ) "_ HΦ".
      wp_lam. wp_alloc t as "Ht". wp_let.
      iDestruct "Ht" as "(Ht1 & Ht2)".
      wp_apply (newlock_spec (node_inv t) with "[Ht1]").
      { iExists tail; iFrame. }
      iIntros (l) "#Hlock". iDestruct "Hlock" as (γ) "Hlock".
      wp_pures.
      rewrite (fold_rep_to_node (INT_MIN, Some t, None, l)).
      set (bot_head := (INT_MIN, Some t, None, l)).

      iMod (inv_alloc (levelN 0) ⊤ (lazy_list_inv bot_head ∅) 
        with "[Ht2]") as "#Hbot_inv".
      {
        iNext; iExists nil. 
        iSplit; first done. iSplit.
        {
          assert (node_lt bot_head tail); last (simpl; auto).
          rewrite /node_lt/node_key//=; apply HMIN_MAX.
        }
        iSplit; first done.
        iExists t, γ. by iFrame "# ∗".
      }

      wp_apply (newLoop_spec _ _ nil).
      { by iFrame "# ∗". }

      iIntros (h top_head L) "[Hh Hlist]"; wp_let.
      iMod (inv_alloc N ⊤ (skip_list_inv top_head ∅) 
        with "[Hlist Hlock]") as "#Hinv".
      { iNext; iExists ∅, L. by iFrame "# ∗". }
      iModIntro; iApply "HΦ". 
      iExists h, top_head, ∅.
      iSplit; first rewrite /key_equiv //.
      by iFrame "# ∗".
    Qed.

  End Proofs.
End NewSpec.