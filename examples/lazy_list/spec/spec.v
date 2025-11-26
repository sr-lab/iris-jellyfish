From iris.algebra Require Import auth gset.
From AtomicInvariant.lib Require Import zrange.
From AtomicInvariant.atomic Require Import triple.
From iris.heap_lang Require Import proofmode notation.
From AtomicInvariant.examples.locks Require Import spin_lock.
From AtomicInvariant.examples.lazy_list Require Import code inv.
From AtomicInvariant.examples.lazy_list.spec Require Import find.


Module LASpec (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module Invariant := FindSpec Params.
  Export Invariant.

  Section proofs.
    Context `{!heapGS Σ, !lazyG Σ}.
    Local Open Scope Z.

    Theorem new_spec :
      {{{ emp }}}
        new #()
      {{{ p Γ, RET #p; set p ∅ Γ }}}.
    Proof.
      iIntros (Φ) "_ HΦ"; wp_lam. 

      wp_alloc t as "(Ht & Ht')"; wp_let.
      wp_alloc l as "Hl"; wp_let.

      set (head := (INT_MIN, t, l)).
      wp_pures; rewrite (fold_rep_to_node head).
      wp_alloc h as "Hh"; iMod (pointsto_persist with "Hh") as "#Hh".

      iMod (own_alloc (● ∅ ⋅ ◯ ∅))
        as (γauth) "[Hauth _]"; 
        first by apply auth_both_valid.
      iMod (own_alloc (GSet ∅ ⋅ ZRange INT_MIN INT_MAX))
        as (γdisj) "[Hdisj Hkeys]";
        first by (pose HMIN_MAX; rewrite ZRange_disj).
      set (Γ := mk_lazy_gname γauth γdisj).

      iModIntro; iApply ("HΦ" $! h Γ).
      iFrame; iExists head. 
      rewrite /lazy_list set_map_empty right_id_L ?big_sepS_singleton.
      iFrame "# ∗"; do 2 (iSplit; first done).
      iSplitL "Hkeys"; first (iFrame; by iLeft).
      iExists Free. iSplitR "Ht"; last by iExists tail. 
      iExists l. by iFrame.
    Qed.

    Theorem contains_spec (p: loc) (Γ: lazy_gname)
      (k: Z) (Hrange: INT_MIN < k < INT_MAX) :
      ⊢ <<{ ∀∀ (s: gset Z), set p s Γ }>> contains #p #k @ ∅
      <<{ ∃∃ (b: bool), set p s Γ ∗ ⌜ if b then k ∈ s else k ∉ s ⌝ | RET #b }>>.
    Proof.
      iIntros "%Φ AI".
      rewrite difference_empty_L.
      wp_lam. wp_let. 
      
      wp_bind (Load _). iMod "AI" as (s) "[Hset [Hclose _]]".
      iDestruct "Hset" as (head S) "(#Hhead & %Hmin & %Hkeys & Hlazy)".
      wp_load. iDestruct ("Hclose" with "[Hlazy]") as ">AI".
      { iExists head, S; by iFrame "# ∗". }
      iModIntro. clear dependent s S.

      wp_bind (find _ _).
      iApply find_spec; first lia; first by iLeft.
      iApply (ainv_ainv with "AI"); try done.
      iIntros "!> %s Hset !>".
      iDestruct "Hset" as (? S) "(#H & _ & %Hkeys & Hlazy)".
      iDestruct (pointsto_agree with "Hhead H") as %<-%rep_to_node_inj; iClear "H".
      iExists S. iFrame. iSplit.
      { iIntros "Hlazy". iExists head, S. by iFrame "# ∗". }
      iIntros (pred succ) "[Hlazy %Hkin] !>".
      iRight. iExists (bool_decide (k = node_key succ)).
      iSplitR "".
      {
        iSplit; first (iExists head, S; by iFrame "# ∗").
        case_bool_decide; subst; rewrite -Hkin //.
      }
      iIntros "HΦ !> _". wp_pures; wp_lam; wp_pures.
      iMod (ares_elim with "HΦ") as "HΦ".
      by do 2 case_bool_decide; try congruence.
    Qed.

    Theorem add_spec (p: loc) (Γ: lazy_gname)
      (k: Z) (Hrange: INT_MIN < k < INT_MAX) :
      ⊢ <<{ ∀∀ (s: gset Z), set p s Γ }>> add #p #k @ ∅
      <<{ set p (s ∪ {[ k ]}) Γ | RET #() }>>.
    Proof.
      iIntros "%Φ AI". wp_lam. wp_let. 
      
      wp_bind (Load _). iMod "AI" as (s) "[Hset [Hclose _]]".
      iDestruct "Hset" as (head S) "(#Hhead & %Hmin & %Hkeys & Hlazy)".
      wp_load. iDestruct ("Hclose" with "[Hlazy]") as ">AI".
      { by iExists head, S; iFrame "# ∗". }
      iModIntro; clear dependent s S.

      wp_bind (findLock _ _).
      iApply findLock_spec; first lia; first by iLeft.
      iApply (ainv_ainv with "AI"); try done.
      iIntros "!> %s Hset !>".
      iDestruct "Hset" as (? S) "(#H & _ & %Hkeys & Hlazy)".
      iDestruct (pointsto_agree with "Hhead H") as %<-%rep_to_node_inj; iClear "H".
      iExists S. iFrame. iSplit.
      { iIntros "Hlazy". iExists head, S. by iFrame "# ∗". }
      iIntros (pred succ) "[Hlazy %Hkin] !>".

      (* Whether we've reached the linearization point will depend on the key *)
      destruct (decide (k = node_key succ)) as [->|Hneq].
      + (* The key already exists, so the linearization point has been reached *)
        iRight. iSplitL "Hlazy".
        { iExists head, S; iFrame "# ∗". iSplit; first done. iPureIntro; set_solver. }
        iIntros "AR !> (#Hpred & _ & _ & Hnext' & Hacq)".
        wp_pures; wp_lam; wp_pures; wp_lam; wp_pures.
        case_bool_decide; last congruence; wp_if.

        (* We access the shared state after the linearization point to release the lock *)
        iApply (release_spec with "Hacq").
        iApply (ainv_ares_frame with "AR Hnext'"); try done.
        iIntros "!> %s' Hset !>".
        iDestruct "Hset" as (? S') "(#H & _ & %Hkeys' & Hlazy)".
        iDestruct (pointsto_agree with "Hhead H") as %<-%rep_to_node_inj; iClear "H".
        iDestruct (lazy_node_has_lock with "Hpred Hlazy") as "[Hlock Hlazy]".
        iDestruct "Hlock" as (st) "[Hlock Hin]". iExists st. iFrame.
        iSplit.
        {
          iIntros "Hlock". iExists head, S'.
          iFrame "#". do 2 (iSplit; first done).
          iApply "Hlazy". iExists st. iFrame.
        }
        iIntros "Hlock !> Hnext".
        iSplitR "". 
        {
          iExists head, S'.
          iFrame "#". do 2 (iSplit; first done).
          iApply "Hlazy". iExists Free. iFrame.
        }
        iIntros "AR". by iMod (ares_elim with "AR") as "HΦ".
      + (* The key does not exist, so the linearization point will come later *)
        iLeft. iSplitL "Hlazy". { by iExists head, S; iFrame "# ∗". }
        clear dependent s S.
        iIntros "AI !> (#Hpred & #Hsucc & %Hk & Hnext' & Hacq)".
        wp_pures; wp_lam; wp_pures; wp_lam; wp_pures.
        case_bool_decide; first congruence; wp_if.
        wp_lam; wp_pures; wp_load.

        (* Allocate the new node *)
        wp_alloc n as "Hn"; wp_let. wp_alloc l as "Hl"; wp_let.
        wp_pures; set (node := (k, n, l)); rewrite (fold_rep_to_node node).
        replace n with (node_next node) by done; replace l with (node_lock node) by done.

        (* Linearization point: we will execute the atomic update *)
        wp_bind (Store _ _). iMod "AI" as (s) "[Hset [_ Hclose]]".
        iDestruct (set_update with "Hhead Hset Hpred Hsucc Hnext' Hn Hl")
          as "[Hnext Hset]"; first done; first by unfold node_key in *; simpl; lia.
        wp_store. iMod ("Hset" with "Hnext") as "[Hset Hnext]".
        iMod ("Hclose" with "Hset") as "AR".
        iModIntro; wp_pures.

        (* We access the shared state after the linearization point to release the lock *)
        iApply (release_spec with "Hacq").
        iApply (ainv_ares_frame with "AR Hnext"); try done.
        iIntros "!> %s' Hset !>".
        iDestruct "Hset" as (? S') "(#H & _ & %Hkeys' & Hlazy)".
        iDestruct (pointsto_agree with "Hhead H") as %<-%rep_to_node_inj; iClear "H".
        iDestruct (lazy_node_has_lock with "Hpred Hlazy") as "[Hlock Hlazy]".
        iDestruct "Hlock" as (st) "[Hlock Hin]". iExists st. iFrame.
        iSplit.
        {
          iIntros "Hlock". iExists head, S'.
          iFrame "#". do 2 (iSplit; first done).
          iApply "Hlazy". iExists st. iFrame.
        }
        iIntros "Hlock !> Hnext".
        iSplitR "". 
        {
          iExists head, S'.
          iFrame "#". do 2 (iSplit; first done).
          iApply "Hlazy". iExists Free. iFrame.
        }
        iIntros "AR". by iMod (ares_elim with "AR") as "HΦ".
    Qed.
  End proofs.
End LASpec.