From Coq Require Import Sorting.Sorted.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.
From iris.bi Require Import updates.

From SkipList.lib Require Import lock misc node_rep node_lt key_equiv.
From SkipList.skip_list Require Import code.
From SkipList.skip_list.inv Require Import list_equiv lazy_inv.


Local Open Scope Z.
Module SkipListInv (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Invariant := LazyListInv Params.
  Export Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ}.

    Definition levelN (lvl: Z) := nroot .@ "level" .@ lvl.

    Fixpoint skip_list_equiv (lvl: Z) (head: node_rep) (S: gset Z) (q: frac) 
      (bot: bot_gname) (subs: list sub_gname) : iProp Σ :=
      match subs with
      | nil => False
      | top_sub :: bot_subs =>
        match bot_subs with
        | nil =>
          ⌜ lvl = 1 ⌝
          ∗
          is_bot_list (levelN lvl) head S q top_sub bot
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
          d ↦{#q} rep_to_node down
          ∗
          ⌜ node_key head = node_key down ⌝
          ∗
          skip_list_equiv (lvl - 1) down S q bot bot_subs
        end
      end.

    Definition is_skip_list (v: val) (S: gset Z) (q: frac) 
      (bot: bot_gname) (subs: list sub_gname) : iProp Σ := 
      ∃ (l:loc) (head: node_rep),
      ⌜ #l = v ⌝
      ∗
      l ↦{#q} rep_to_node head
      ∗
      ⌜ node_key head = INT_MIN ⌝
      ∗
      skip_list_equiv MAX_HEIGHT head S q bot subs.

    
    Lemma skip_list_equiv_cons (top_head: node_rep) (lvl: Z) (S: gset Z) (q: frac) 
      (bot: bot_gname) (top_sub: sub_gname) (bot_subs: list sub_gname) :
      skip_list_equiv lvl top_head S q bot (top_sub :: bot_subs) ⊢ 
        ∃ (P: Z → option loc → iProp Σ) (obot: option bot_gname),
        inv (levelN lvl) (lazy_list_inv top_head top_sub obot P)
        ∗
        skip_list_equiv lvl top_head S q bot (top_sub :: bot_subs).
    Proof.
      destruct bot_subs as [|bot_sub bot_subs].
      + iIntros "Htop". iExists from_bot_list, (Some bot).
        iDestruct "Htop" as "(? & Hlazy & ?)".
        iDestruct "Hlazy" as "(? & #Hinv)".
        iFrame "# ∗".
      + iIntros "Hlist". iExists (from_top_list bot_sub), None.
        iDestruct "Hlist" as (d down) "(? & #Hinv & ?)".
        iFrame "# ∗". iExists d, down. iFrame.
    Qed.

  End Proofs.
End SkipListInv.