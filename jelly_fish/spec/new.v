From iris.algebra Require Import gmap gset excl_auth dfrac_agree.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import zrange gmap_extra.
From SkipList.jelly_fish Require Import code inv.


Module NewSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Invariant := SkipListInv Params.
  Export Invariant.

  Section proofs.
    Context `{!heapGS Σ, !skipG Σ} (N: namespace).
    Local Open Scope Z.

    Theorem initLocks_spec (lvl: Z) (head: node_rep) (t: loc)
      (Γm: map_gname) (Γ: gmap Z inv_gname) :
      1 ≤ lvl ≤ MAX_HEIGHT + 1 →
      node_key head = INT_MIN →
      t ↦□ rep_to_node tail -∗
      {{{
        (node_next head +ₗ lvl) ↦∗ replicate (Z.to_nat (MAX_HEIGHT + 1 - lvl)) #t
        ∗
        (node_lock head +ₗ lvl) ↦∗ replicate (Z.to_nat (MAX_HEIGHT + 1 - lvl)) #()
        ∗
        [∗ set] i ∈ zrange (-1) lvl, lazy_list_inv head Γm Γ i
      }}}
        initLocks #(node_lock head) #lvl
      {{{ Γ, RET #(); skip_list_inv head Γm Γ }}}.
    Proof.
      iIntros "%Hlvl %Hmin #Ht %Φ !> (Hnexts & Hlocks & Hskip) HΦ".
      iRevert (Γ lvl Hlvl) "Hnexts Hlocks Hskip HΦ".
      iLöb as "IH".
      iIntros (Γ lvl Hlvl) "Hnexts Hlocks Hskip HΦ".

      wp_lam. wp_let. wp_pures.
      case_bool_decide as Hcase; wp_if.
      + iModIntro; iApply ("HΦ" $! Γ).
        inversion Hcase; subst; iFrame.
      + assert (lvl ≠ MAX_HEIGHT + 1) as Hneq by congruence.
        replace (Z.to_nat (MAX_HEIGHT + 1 - lvl)) with (S (Z.to_nat (MAX_HEIGHT - lvl))) by lia.
        repeat rewrite replicate_S array_cons.
        iDestruct "Hlocks" as "(Hlock & Hlocks)".
        iDestruct "Hnexts" as "((Hnext & Hnext') & Hnexts)".

        wp_apply (newlock_spec (in_lock lvl (node_next head)) with "[Hnext']").
        { iExists t; iFrame; unfold locked_val; by case_decide; first lia. }
        iIntros (l γl) "#His_lock".
        wp_store. wp_pures.
        iMod (mapsto_persist with "Hlock") as "#Hlock".

        iMod (own_alloc (● (∅ : gset node_rep) ⋅ ◯ ∅))
          as (γauth) "[Hauth _]"; 
          first by apply auth_both_valid.
        iMod (own_alloc (GSet ∅ ⋅ ZRange (node_key head) (node_key tail)))
          as (γdisj) "[Hdisj Hkeys]";
          first by (pose HMIN_MAX; rewrite Hmin ZRange_disj).
        iMod (own_alloc (● GSet ∅ ⋅ ◯ GSet ∅))
          as (γtoks) "[Htoks _]"; 
          first by apply auth_both_valid.
        set (Γi := mk_inv_gname γauth γdisj γtoks).
        set (Γ' := <[lvl := Γi]>Γ).

        rewrite ?loc_add_assoc; replace (MAX_HEIGHT - lvl) with (MAX_HEIGHT + 1 - (lvl + 1)) by lia.
        iApply ("IH" $! Γ' with "[%] Hnexts Hlocks [-HΦ]"); first lia.
        {
          rewrite (zrange_split_r _ lvl); last lia.
          rewrite comm_L big_sepS_insert; last (rewrite zrange_spec; lia).
          iSplitR "Hskip".
          + iExists ∅; case_decide; first lia.
            rewrite right_id_L ?big_sepS_singleton big_sepS_empty set_map_empty lookup_total_insert; iFrame.
            iSplit; first (iExists γl, l; iFrame "#").
            iSplit; last done. iExists t, tail; iFrame "# ∗"; by iLeft.
          + iApply big_sepS_mono; last iFrame.
            iIntros (m Hm%zrange_spec) "Hlvl".
            rewrite /lazy_list_inv ?lookup_total_insert_ne //; lia.
        }
        iNext; done.
    Qed.

    Theorem new_spec : 
      {{{ True }}}
        new #()
      {{{ p Γm, RET #p; map_inv N p Γm ∗ map ∅ Γm }}}.
    Proof.
      iIntros (Φ) "_ HΦ"; wp_lam; pose proof HMAX_HEIGHT. 

      wp_alloc t as "Ht"; iMod (mapsto_persist with "Ht") as "#Ht".
      wp_alloc next as "Hnexts"; first lia. wp_let.
      wp_alloc locks as "Hlocks"; first lia. wp_let.

      replace (Z.to_nat (MAX_HEIGHT + 1)) with (S (Z.to_nat MAX_HEIGHT)) by lia.
      rewrite replicate_S ?array_cons.
      iDestruct "Hnexts" as "((Hnext & Hnext') & Hnexts)".
      iDestruct "Hlocks" as "(Hlock & Hlocks)".

      wp_lam. wp_let. wp_pures.
      case_bool_decide as Hcase; first (inversion Hcase; lia).
      wp_if.

      iMod (own_alloc (●E ∅ ⋅ ◯E ∅))
        as (γexcl) "[Hexcl● Hexcl◯]";
        first by apply auth_both_valid.
      iMod (own_alloc (● DMap ∅ ⋅ ◯ DMap∅))
        as (γvals) "[Hvals _]"; 
        first by apply auth_both_valid.
      set (Γm := mk_map_gname γexcl γvals).
      set (head := (INT_MIN, dummy_null, next, locks)).
      wp_apply (newlock_spec (in_lock 0 (node_next head)) with "[Hnext']").
      { iExists t; rewrite loc_add_0; iFrame. iExists tail; iFrame "#"; by iLeft. }
      iIntros (l γl) "#His_lock".

      wp_pures; rewrite loc_add_0.
      wp_store; iMod (mapsto_persist with "Hlock") as "#Hlock".
      wp_pures; replace (0 + 1) with 1 by lia.

      iMod (own_alloc (● ∅ ⋅ ◯ ∅))
        as (γauth) "[Hauth _]"; 
        first by apply auth_both_valid.
      iMod (own_alloc (GSet ∅ ⋅ ZRange (node_key head) (node_key tail)))
        as (γdisj) "[Hdisj Hkeys]";
        first by (pose HMIN_MAX; rewrite ZRange_disj).
      iMod (own_alloc (● GSet ∅ ⋅ ◯ GSet ∅))
        as (γtoks) "[Htoks _]"; 
        first by apply auth_both_valid.
      set (Γi := mk_inv_gname γauth γdisj γtoks).
      set (Γ' := ({[ 0 := Γi ]} : gmap Z inv_gname)).

      replace locks with (node_lock head) by auto.
      replace Γi with (Γ' !!! 0) by set_solver.
      wp_apply (initLocks_spec _ _ _ Γm Γ' with "Ht [-HΦ Hexcl◯ Hvals]"); first lia; first done.
      {
        replace (MAX_HEIGHT + 1 - 1) with MAX_HEIGHT by lia; iFrame. 
        replace 1 with (0 + 1) by lia; rewrite zrange_split_r; last lia.
        replace 0 with (-1 + 1) by lia; rewrite zrange_empty_r left_id_L big_sepS_singleton //.
        iExists ∅; case_decide; last lia.
        replace (Γ' !!! 0) with Γi by set_solver.
        rewrite right_id_L ?big_sepS_singleton /own_map big_sepS_empty set_map_empty; iFrame. 
        iSplit; first (iExists γl, l; rewrite ?loc_add_0; iFrame "#").
        iExists t, tail; rewrite loc_add_0; iFrame "# ∗"; by iLeft.
      }
      iIntros (Γ) "Hskip".
      iMod (inv_alloc (skipN N) ⊤ (skip_list_inv head Γm Γ) with "Hskip") as "#Hinv".

      wp_pures; rewrite (fold_rep_to_node head).
      wp_alloc p as "Hp"; iMod (mapsto_persist with "Hp") as "#Hp".
      iModIntro; iApply ("HΦ" $! _ Γm).
      iSplit; first by (iExists head, Γ; iFrame "#").
      rewrite -dom_empty; iFrame.
    Qed.
  End proofs.
End NewSpec.