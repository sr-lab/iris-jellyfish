From Coq Require Import Sorting.Sorted.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.
From iris.bi Require Import updates.

From SkipList.lib Require Import lock misc.
From SkipList.skip_list Require Import node_lt node_rep code key_equiv.
From SkipList.skip_list.inv Require Import lazy_inv.


Local Open Scope Z.
Module SkipListInv (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Invariant := LazyListInv Params.
  Export Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ}.

    Definition levelN (lvl: Z) := nroot .@ "level" .@ lvl.

    Definition from_bot_list (obot: option lazy_gname) (key: Z) (odown: option loc) : iProp Σ := 
      match obot, odown with
      | None, None => True
      | Some bot, Some d => ∃ (down: node_rep),
                            d ↦ rep_to_node down
                            ∗
                            own (s_auth bot) (◯ {[ down ]})
                            ∗
                            own (s_toks bot) (GSet {[ node_key down ]})
                            ∗
                            ⌜ key = node_key down ⌝
      | _, _ => False
      end.

    Fixpoint skip_list_equiv (head: node_rep) (lvl: Z) (q: frac) 
      (L_gset: list (gset Z)) (L_gname: list lazy_gname) : iProp Σ :=
      match L_gset, L_gname with
      | Stop :: Sbots, top :: bots =>
        match Sbots, bots with
        | nil, nil => 
          ⌜ lvl = 1 ⌝
          ∗
          is_lazy_list (levelN lvl) head q Stop top (from_bot_list None)
          ∗
          ⌜ node_down head = None ⌝
                 
        | _ :: _, bot :: _ => 
          ∃ (d: loc) (down: node_rep),
          ⌜ lvl > 1 ⌝
          ∗
          is_lazy_list (levelN lvl) head q Stop top (from_bot_list (Some bot))
          ∗
          ⌜ node_down head = Some d ⌝
          ∗
          d ↦ rep_to_node down
          ∗
          ⌜ node_key head = node_key down ⌝
          ∗
          skip_list_equiv down (lvl - 1) q Sbots bots
        | _, _ => False
        end
      | _, _ => False
      end.

    Definition is_skip_list (v: val) (q: frac) 
      (L_gset: list (gset Z)) (L_gname: list lazy_gname) : iProp Σ := 
      ∃ (l:loc) (head: node_rep),
      ⌜ #l = v ⌝
      ∗
      l ↦ rep_to_node head
      ∗
      ⌜ node_key head = INT_MIN ⌝
      ∗
      skip_list_equiv head MAX_HEIGHT q L_gset L_gname.

  End Proofs.
End SkipListInv.