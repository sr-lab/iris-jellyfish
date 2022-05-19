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
    Context `{!heapGS Σ, !gset_list_unionGS Σ, lockG Σ} (N : namespace).

    Definition levelN (lvl: Z) := nroot .@ "level" .@ lvl.

    Definition from_sub_list (bot: gset node_rep) (curr: node_rep) : iProp Σ := 
      ∃ (l: loc) (down: node_rep),
      ⌜ node_down curr = Some l ⌝
      ∗
      l ↦ rep_to_node down
      ∗
      ⌜ down ∈ bot ⌝
      ∗
      ⌜ node_key curr = node_key down ⌝.

    Definition from_bot_list (curr: node_rep) : iProp Σ := 
      ⌜ node_down curr = None ⌝.

    Fixpoint skip_list_equiv (head: node_rep) (lvl: Z) (L: list (gset node_rep)) (S: gset node_rep) : iProp Σ :=
      match L with
      | nil => False
      | top :: bots =>
        match bots with
        | nil => ⌜ lvl = 0 ⌝
                 ∗
                 inv (levelN lvl) (lazy_list_inv head top from_bot_list)
                 ∗
                 ⌜ node_down head = None ⌝
                 ∗
                 ⌜ top = S ⌝
                 
        | bot :: _ => ∃ (l: loc) (down: node_rep),
                      ⌜ lvl > 0 ⌝
                      ∗
                      inv (levelN lvl) (lazy_list_inv head top (from_sub_list bot))
                      ∗
                      ⌜ node_down head = Some l ⌝
                      ∗
                      l ↦ rep_to_node down
                      ∗
                      ⌜ node_key head = node_key down ⌝
                      ∗
                      skip_list_equiv down (lvl - 1) bots S
        end
      end.

    Definition is_skip_list (v: val) (Skeys: gset Z) : iProp Σ := 
      ∃ (l:loc) (head: node_rep) (S: gset node_rep) (L: list (gset node_rep)),
      ⌜ key_equiv S Skeys ⌝
      ∗
      ⌜ #l = v ⌝
      ∗
      l ↦ rep_to_node head
      ∗
      ⌜ node_key head = INT_MIN ⌝
      ∗
      skip_list_equiv head MAX_HEIGHT L S.


    Lemma skip_list_equiv_cons_inv (top_head: node_rep) (lvl: Z) (S: gset node_rep)
      (L: list (gset node_rep)) (top: gset node_rep) :
      skip_list_equiv top_head lvl (top :: L) S ⊢ 
        ∃ (P: node_rep → iProp Σ),
        inv (levelN lvl) (lazy_list_inv top_head top P)
        ∗
        skip_list_equiv top_head lvl (top :: L) S
    .
    Proof.
      destruct L as [|bot].
      + iIntros "Htop". iExists from_bot_list.
        iDestruct "Htop" as "(%Hlvl & #Hinv & %Hnone & %Heq)".
        by iFrame "#".
      + iIntros "Hlist". iExists (from_sub_list bot).
        iDestruct "Hlist" as (l down) "(%Hlvl & #Hinv & %Hsome & Hpt & Hmatch)".
        iFrame "#". iExists l, down. by iFrame.
    Qed.

  End Proofs.
End SkipListInv.