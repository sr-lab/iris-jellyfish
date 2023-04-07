From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Import ghost_map.
From iris.heap_lang Require Import notation.

From SkipList.lib Require Import zrange.
From SkipList.atomic Require Import weakestpre proofmode lock.
From SkipList.jelly_fish Require Import code inv.


Module NewSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Invariant := SkipListInv Params.
  Export Invariant.

  Section proofs.
    Context `{!heapGS Σ, !skipG Σ}.
    Local Open Scope Z.

    Theorem alloc_levels (lvl: Z) (head: node_rep) (t: loc)
      (mΓ: gmap Z lazy_gname) :
      1 ≤ lvl ≤ MAX_HEIGHT + 1 →
      node_key head = INT_MIN →
      t ↦□ rep_to_node tail -∗
      (node_next head +ₗ lvl) ↦∗ 
        replicate (Z.to_nat (MAX_HEIGHT + 1 - lvl)) #t -∗
      (node_lock head +ₗ lvl) ↦∗ 
        replicate (Z.to_nat (MAX_HEIGHT + 1 - lvl)) #false -∗
      ([∗ set] i ∈ zrange 0 lvl, is_lazy_list head (mΓ !!! i) (mΓ !!! (i - 1)) i)
      ==∗
      ∃ (mΓ': gmap Z lazy_gname),
        ⌜ mΓ !!! 0 = mΓ' !!! 0 ⌝
        ∗
        [∗ set] i ∈ zrange 0 (MAX_HEIGHT + 1), 
          is_lazy_list head (mΓ' !!! i) (mΓ' !!! (i - 1)) i.
    Proof.
      iIntros "%Hlvl %Hmin #Ht".
      assert (lvl = Z.of_nat (Z.to_nat lvl)) as Heq by lia.
      remember (Z.to_nat (MAX_HEIGHT + 1 - lvl)) as diff eqn:Hdiff.
      iRevert (Hlvl); rewrite Heq; clear Heq; iRevert (lvl mΓ Hdiff).
      iInduction (diff) as [|diff] "Himp"; 
        iIntros (lvl mΓ) "%Hdiff %Hlvl' Hnexts Hlocks Hskip".
      + replace (MAX_HEIGHT + 1) with (Z.of_nat (Z.to_nat lvl)) by lia.
        by iModIntro; iExists mΓ; iFrame.
      + assert (lvl ≠ MAX_HEIGHT + 1) as Hneq by lia.

        rewrite ?replicate_S ?array_cons ?loc_add_assoc.
        replace (Z.to_nat lvl + 1) with (Z.of_nat (Z.to_nat (lvl + 1))) by lia.
        iDestruct "Hnexts" as "[[Hnext Hnext'] Hnexts]".
        iDestruct "Hlocks" as "[Hlock Hlocks]".

        iMod (own_alloc (● ∅ ⋅ ◯ ∅))
          as (γauth) "[Hauth _]";
          first by apply auth_both_valid.
        iMod (own_alloc (● GSet ∅ ⋅ ◯ GSet ∅))
          as (γtoks) "[Htoks _]"; 
          first by apply auth_both_valid.
        iMod (own_alloc (GSet ∅ ⋅ ZRange (node_key head) (node_key tail)))
          as (γsort) "[Hsort Hkeys]";
          first by (pose HMIN_MAX; rewrite Hmin ZRange_disj).
        set (Γ := mk_lazy_gname γauth γsort γtoks).

        iDestruct ("Himp" $! (lvl + 1) (<[lvl := Γ]>mΓ) with "[] [] Hnexts Hlocks [-]")
          as "Hskip'"; first (iPureIntro; lia); first (iPureIntro; lia);
          last (rewrite ?lookup_total_insert_ne //; lia).

        replace (Z.of_nat (Z.to_nat (lvl + 1))) with (Z.of_nat (Z.to_nat lvl) + 1) by lia.
        replace (Z.of_nat (Z.to_nat lvl)) with lvl by lia.
        rewrite (zrange_split_r _ lvl); last lia.
        rewrite (comm_L _ _ {[lvl]}) big_sepS_insert; last (rewrite zrange_spec; lia).
        iSplitR "Hskip".
        - iExists ∅. rewrite /lazy_list ?lookup_total_insert ?set_map_empty 
            right_id_L ?big_sepS_singleton big_sepS_empty; iFrame "# ∗".
          iSplitL "Hnext Hkeys"; first (iExists t, tail; iFrame "# ∗"; by iLeft).
          iSplit; last done. iExists Free, (node_lock head +ₗ lvl).
          iSplit; first done. iFrame. iExists t. iFrame.
          unfold locked_val; by case_match; first lia.
        - iApply big_sepS_mono; last iFrame.
          iIntros (i Hi%zrange_spec) "Hlazy".
          rewrite ?lookup_total_insert_ne //; lia.
    Qed.

    Theorem new_spec : 
      {{{ emp }}}
        newMap #()
      {{{ p mΓ, RET #p; vc_map p ∅ mΓ }}}.
    Proof.
      iIntros (Φ) "_ HΦ"; wp_lam; pose proof HMAX_HEIGHT. 

      wp_alloc t as "Ht"; iMod (mapsto_persist with "Ht") as "#Ht".
      wp_alloc next as "Hnexts"; first lia. wp_let.
      wp_alloc lock as "Hlocks"; first lia. wp_let.
      set (head := (INT_MIN, dummy_null, next, lock)).

      replace (Z.to_nat (MAX_HEIGHT + 1)) with (S (Z.to_nat MAX_HEIGHT)) by lia.
      rewrite ?replicate_S ?array_cons.
      iDestruct "Hnexts" as "[[Hnext Hnext'] Hnexts]".
      iDestruct "Hlocks" as "[Hlock Hlocks]".

      iMod ghost_map_alloc_empty as (γ) "Hvals".
      iMod (own_alloc (● ∅ ⋅ ◯ ∅))
        as (γauth) "[Hauth _]";
        first by apply auth_both_valid.
      iMod (own_alloc (● GSet ∅ ⋅ ◯ GSet ∅))
        as (γtoks) "[Htoks _]"; 
        first by apply auth_both_valid.
      iMod (own_alloc (GSet ∅ ⋅ ZRange (node_key head) (node_key tail)))
        as (γsort) "[Hsort Hkeys]";
        first by (pose HMIN_MAX; rewrite ZRange_disj).
      set (Γ := mk_lazy_gname γauth γsort γtoks).

      replace MAX_HEIGHT with (MAX_HEIGHT + 1 - 1) by lia.
      iMod (alloc_levels 1 head t {[ 0 := Γ ]} with "Ht Hnexts Hlocks []") 
        as (mΓ) "[%HmΓ Hskip]"; first lia; first done;
        last rewrite lookup_total_singleton in HmΓ.
      { replace 1 with (0 + 1) by lia; rewrite zrange_empty_r big_sepS_empty //. }

      wp_pures; rewrite (fold_rep_to_node head).
      wp_alloc p as "Hp"; iMod (mapsto_persist with "Hp") as "#Hp".
      iModIntro; iApply "HΦ".
      iExists head, ∅. iFrame "Hp Hskip". iSplit; first done.
      iSplitR "Hvals"; last first.
      { iExists γ. iFrame "Hvals". rewrite big_sepS_empty. iPureIntro; set_solver. }
      rewrite -HmΓ /lazy_list ?lookup_total_singleton ?set_map_empty
        right_id_L ?big_sepS_singleton; iFrame.
      iSplitR "Hlock Hnext'".
      { iExists t, tail; rewrite loc_add_0; iFrame "# ∗"; by iLeft. }
      iSplit; last done. iExists Free, lock.
      rewrite loc_add_0; iSplit; first done.
      iFrame. iExists t. rewrite loc_add_0; iFrame.
      unfold locked_val. iExists tail. iFrame "Ht". by iLeft.
    Qed.
  End proofs.
End NewSpec.