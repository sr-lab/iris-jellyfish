From iris.algebra Require Import gset excl_auth.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import zrange.
From SkipList.lazy_list Require Import code inv.
From SkipList.lazy_list.spec Require Import find.


Module LASpec (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module Invariant := FindSpec Params.
  Export Invariant.

  Section proofs.
    Context `{!heapGS Σ, !lazyG Σ} (N: namespace).
    Local Open Scope Z.

    Theorem new_spec :
      {{{ True }}}
        new #()
      {{{ p Γs, RET #p; set_inv N p Γs ∗ set ∅ Γs }}}.
    Proof.
      iIntros (Φ) "_ HΦ"; wp_lam. 

      wp_alloc t as "(Ht & Ht')"; wp_let.
      wp_apply (newlock_spec (in_lock t) with "[Ht']").
      { iExists tail; iFrame. }
      iIntros (l γl) "#His_lock".

      set (head := (INT_MIN, t, l)).
      wp_pures; rewrite (fold_rep_to_node head).
      wp_alloc h as "Hh"; iMod (mapsto_persist with "Hh") as "#Hh".

      iMod (own_alloc (● ∅ ⋅ ◯ ∅))
        as (γauth) "[Hauth _]"; 
        first by apply auth_both_valid.
      iMod (own_alloc (GSet ∅ ⋅ ZRange INT_MIN INT_MAX))
        as (γdisj) "[Hdisj Hkeys]";
        first by (pose HMIN_MAX; rewrite ZRange_disj).
      iMod (own_alloc (●E ∅ ⋅ ◯E ∅))
        as (γexcl) "[Hexcl Hexcl']";
        first by apply auth_both_valid.
      set (Γi := mk_inv_gname γauth γdisj).
      set (Γs := mk_set_gname γexcl).
      iMod (inv_alloc (lazyN N) ⊤ (lazy_list_inv head Γi Γs) 
        with "[Ht Hauth Hdisj Hkeys Hexcl]") as "#Hinv".
      {
        iNext; iExists ∅; rewrite set_map_empty; iFrame.
        rewrite right_id_L ?big_sepS_singleton.
        iSplit; first by iExists γl.
        iExists tail; iFrame; by iLeft.
      }

      iModIntro; iApply ("HΦ" $! h Γs).
      iFrame; iExists head, Γi; by iFrame "#".
    Qed.

    Theorem contains_spec (p: loc) (Γs: set_gname)
      (k: Z) (Hrange: INT_MIN < k < INT_MAX) :
      set_inv N p Γs -∗
      <<< ∀∀ (s: gset Z), set s Γs >>>
        contains #p #k @ ↑(lazyN N)
      <<< ∃∃ (b: bool), set s Γs ∗ ⌜ if b then k ∈ s else k ∉ s ⌝, RET #b >>>.
    Proof.
      iIntros "#H %Φ AU"; rewrite /set.
      iDestruct "H" as (head Γi) "(Hp & %Hmin & #Hinv)".
      wp_lam. wp_let. wp_load.

      awp_apply (find_spec with "[] Hinv"); first lia; first by iLeft.
      iApply (aacc_aupd with "AU"); first done.
      iIntros (s) "Hexcl◯"; iAaccIntro with "Hexcl◯".
      { do 2 (iIntros "?"; iModIntro; iFrame). }
      iIntros (pred succ) "(Hexcl' & %Hkin & _)".

      iModIntro; iRight; iFrame.
      iExists (bool_decide (k = node_key succ)).
      case_bool_decide; (rewrite -Hkin; iSplit; first done). 
      all: iIntros "HΦ"; iModIntro; wp_pures; wp_lam; wp_pures.
      all: case_bool_decide; try done; try congruence.
    Qed.

    Theorem add_spec (p: loc) (Γs: set_gname)
      (k: Z) (Hrange: INT_MIN < k < INT_MAX) :
      set_inv N p Γs -∗
      <<< ∀∀ (s: gset Z), set s Γs >>>
        add #p #k @ ↑(lazyN N)
      <<< set (s ∪ {[ k ]}) Γs, RET #() >>>.
    Proof.
      iIntros "#H %Φ AU"; rewrite /set.
      iDestruct "H" as (head Γi) "(Hp & %Hmin & #Hinv)".
      wp_lam. wp_let. wp_load.

      awp_apply (findLock_spec with "[] Hinv"); first lia; first by iLeft.
      iApply (aacc_aupd with "AU"); first done.
      iIntros (s) "Hexcl◯"; iAaccIntro with "Hexcl◯".
      { do 2 (iIntros "?"; iModIntro; iFrame). }
      iIntros (pred succ) "(Hexcl◯ & %Hkin & #Hpred & #Hsucc & %Hk & His_lock)".
      iDestruct "His_lock" as (γl) "(#His_lock & Hnext' & Hlocked)".

      destruct (decide (k = node_key succ)) as [->|Hneq].
      + replace (s ∪ {[node_key succ]}) with s by set_solver.
        iDestruct "Hsucc" as "[->|Hsucc]"; first (rewrite /node_key/tail/= in Hrange; lia).
        iModIntro; iRight; iFrame.
        iIntros "HΦ"; iModIntro.
        wp_pures; wp_lam; wp_pures; wp_lam; wp_pures.
        case_bool_decide; last congruence; wp_if.
        wp_apply (release_spec with "[Hnext' Hlocked]"); last by iIntros. 
        iFrame "# ∗"; iExists succ; iFrame.
      + iModIntro; iLeft; iFrame.
        iIntros "AU"; iModIntro.
        wp_pures; wp_lam; wp_pures; wp_lam; wp_pures.
        case_bool_decide; first congruence; wp_if.
        wp_lam; wp_pures; wp_load.

        wp_alloc n as "(Hn & Hn')"; wp_let.
        wp_apply (newlock_spec (in_lock n) with "[Hn']").
        { iExists succ; iFrame. }
        iIntros (lk γl') "#His_lock'".
        wp_pures; set (new := (k, n, lk)); rewrite (fold_rep_to_node new).

        wp_bind (Store _ _).
        iInv "Hinv" as (S) "(>Hauth & >Hdisj & Hlocks & Hnexts & >Hexcl●)".

        iDestruct (singleton_frag_in with "Hauth Hpred") as %Hpred.
        rewrite (big_sepS_delete (has_next _) _ pred) //.
        iDestruct "Hnexts" as "(Hnext & Hnexts)".
        iDestruct "Hnext" as (succ') ">(Hnext & _ & Hkeys)".
        iDestruct (mapsto_agree with "Hnext Hnext'") as %->%rep_to_node_inj.

        iCombine "Hnext Hnext'" as "Hnext"; wp_store.
        iDestruct "Hnext" as "(Hnext & Hnext')".

        iMod (own_update with "Hauth") as "[Hauth Hfrag]".
        { by apply auth_update_alloc, (op_local_update_discrete _ _ {[new]}). }
        rewrite right_id (comm _ {[new]} S).

        rewrite (ZRange_split k); last lia.
        iDestruct "Hkeys" as "((Hkeys & Hkey) & Hkeys')".
        iDestruct (own_valid_2 with "Hdisj Hkey") as %Hdisj%gset_disj_valid_op.
        iCombine "Hdisj Hkey" as "Hdisj"; rewrite gset_disj_union //.

        clear dependent s; iMod "AU" as (s) "[Hexcl◯ [_ Hclose]]".
        iDestruct (own_valid_2 with "Hexcl● Hexcl◯") as %<-%excl_auth_agree_L.
        iMod (own_update_2 with "Hexcl● Hexcl◯") as "[Hexcl● Hexcl◯]".
        { apply (excl_auth_update _ _ (set_map node_key S ∪ {[k]})). }
        iMod ("Hclose" with "Hexcl◯") as "AU"; iModIntro.

        iAssert (has_next _ pred) with "[Hnext Hfrag Hkeys]" as "Hnext".
        { iExists new; iFrame. }
        iCombine "Hnext Hnexts" as "Hnexts".
        rewrite -big_sepS_delete //.

        iAssert (has_lock new) as "Hlock".
        { iExists γl'; iFrame "#". }
        iAssert (has_next _ new) with "[Hn Hkeys']" as "Hnext".
        { iExists succ; iFrame "# ∗". }
        iCombine "Hlock Hlocks" as "Hlocks"; iCombine "Hnext Hnexts" as "Hnexts".
        assert (node_key new ≠ node_key head) by (rewrite Hmin /node_key/=; lia).
        assert (new ∉ {[head]} ∪ S) by set_solver.
        do 2 rewrite -big_sepS_insert // (comm_L _ _ ({[head]} ∪ S)) -assoc_L.

        iSplitL "Hauth Hdisj Hlocks Hnexts Hexcl●".
        { iNext; iExists (S ∪ {[new]}); rewrite set_map_union_L set_map_singleton_L; iFrame. }
        wp_pures.
        wp_apply (release_spec with "[Hnext' Hlocked]"); last by iIntros.
        iFrame "# ∗"; iExists new; iFrame.
    Qed.
  End proofs.
End LASpec.