From Coq Require Import Sorting.Sorted.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.
From iris.bi Require Import updates.

From SkipList.lib Require Import lock misc.
From SkipList.skip_list Require Import node_lt node_rep code key_equiv.
From SkipList.skip_list.inv Require Import list_equiv lazy_inv.


Local Open Scope Z.
Module SkipListInv (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Invariant := LazyListInv Params.
  Export Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ}.

    Definition levelN (lvl: Z) := nroot .@ "level" .@ lvl.

    Fixpoint skip_list_equiv (head: node_rep) (lvl: Z) (q: frac) 
      (S: gset Z) (bot: bot_gname) (subs: list sub_gname) : iProp Σ :=
      match subs with
      | nil => False
      | top_sub :: bot_subs =>
        match bot_subs with
        | nil =>
          ⌜ lvl = 1 ⌝
          ∗
          is_bot_list (levelN lvl) head q S top_sub bot
          ∗
          ⌜ node_down head = None ⌝

        | bot_sub :: _ =>
          ∃ (d: loc) (down: node_rep),
          ⌜ lvl > 1 ⌝
          ∗
          is_top_list (levelN lvl) head top_sub bot_sub
          ∗
          ⌜ node_down head = Some d ⌝
          ∗
          d ↦ rep_to_node down
          ∗
          ⌜ node_key head = node_key down ⌝
          ∗
          skip_list_equiv down (lvl - 1) q S bot bot_subs
        end
      end.

    Definition is_skip_list (v: val) (q: frac) 
      (S: gset Z) (bot: bot_gname) (subs: list sub_gname) : iProp Σ := 
      ∃ (l:loc) (head: node_rep),
      ⌜ #l = v ⌝
      ∗
      l ↦ rep_to_node head
      ∗
      ⌜ node_key head = INT_MIN ⌝
      ∗
      skip_list_equiv head MAX_HEIGHT q S bot subs.

    
    Lemma skip_list_equiv_cons (top_head: node_rep) (lvl: Z) (q: frac)
      (S: gset Z) (bot: bot_gname)
      (top_sub: sub_gname) (bot_subs: list sub_gname) :
      skip_list_equiv top_head lvl q S bot (top_sub :: bot_subs) ⊢ 
        ∃ (P: Z → option loc → iProp Σ) (obot: option bot_gname),
        inv (levelN lvl) (lazy_list_inv top_head P top_sub obot)
        ∗
        skip_list_equiv top_head lvl q S bot (top_sub :: bot_subs).
    Proof.
      destruct bot_subs as [|bot_sub bot_subs].
      + iIntros "Htop". iExists from_bot_list, (Some bot).
        iDestruct "Htop" as "(? & Hlazy & ?)".
        iDestruct "Hlazy" as (Sfrac) "(? & ? & #Hinv)".
        iFrame "# ∗". iExists Sfrac. iFrame.
      + iIntros "Hlist". iExists (from_top_list bot_sub), None.
        iDestruct "Hlist" as (d down) "(? & #Hinv & ?)".
        iFrame "# ∗". iExists d, down. iFrame.
    Qed.

  End Proofs.
End SkipListInv.