From Coq Require Import Sorting.Sorted.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.
From iris.bi Require Import updates.

From SkipList.lib Require Import lock misc node_rep node_lt key_equiv.
From SkipList.skip_list.lists Require Import code.
From SkipList.skip_list.lists.inv Require Import list_equiv lazy_inv.


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
          ⌜ lvl = 0 ⌝
          ∗
          is_bot_list (levelN lvl) head S q top_sub bot
          ∗
          ⌜ node_down head = None ⌝

        | bot_sub :: _ =>
          ∃ (d: loc) (down: node_rep),
          ⌜ lvl > 0 ⌝
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

    
    Lemma skip_list_equiv_inv (top_head: node_rep) (lvl: Z) (S: gset Z) (q: frac) 
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

    Lemma skip_list_equiv_sep (lvl: Z) (head: node_rep) (S: gset Z) (q1 q2: frac) 
      (bot: bot_gname) (subs: list sub_gname) :
      skip_list_equiv lvl head S (q1 + q2) bot subs ⊢ 
        skip_list_equiv lvl head S q1 bot subs ∗ skip_list_equiv lvl head S q2 bot subs.
    Proof.
      iRevert (lvl head).
      iInduction subs as [|top_sub bot_subs] "IHsubs"; 
        iIntros (lvl head) "Hlist"; 
        first by iExFalso.

      destruct bot_subs as [|bot_sub bot_subs].
      + iDestruct "Hlist" as "(%Hlvl & (Hown_frag & #Hinv) & %Hnone)".
        iDestruct "Hown_frag" as "(Hown_frag1 & Hown_frag2)".
        by iFrame "# ∗".
      + iDestruct "Hlist" as (d down) "(%Hlvl & #Hinv & %Hsome & Hd & %Hkey & Hmatch)".
        iPoseProof ("IHsubs" with "Hmatch") as "(Hlist1 & Hlist2)".
        iDestruct "Hd" as "(Hd1 & Hd2)".
        iSplitL "Hd1 Hlist1".
        - iExists d, down. by iFrame "# ∗".
        - iExists d, down. by iFrame "# ∗".
    Qed.

    Lemma skip_list_equiv_join (lvl: Z) (head: node_rep) (S1 S2: gset Z) (q1 q2: frac) 
      (bot: bot_gname) (subs: list sub_gname) :
      skip_list_equiv lvl head S1 q1 bot subs ∗ skip_list_equiv lvl head S2 q2 bot subs ⊢ 
        skip_list_equiv lvl head (S1 ∪ S2) (q1 + q2) bot subs.
    Proof.
      iRevert (lvl head).
      iInduction subs as [|top_sub bot_subs] "IHsubs"; 
        iIntros (lvl head) "(Hlist1 & Hlist2)"; 
        first by iExFalso.

      destruct bot_subs as [|bot_sub bot_subs].
      + iDestruct "Hlist1" as "(%Hlvl & (Hown_frag1 & #Hinv) & %Hnone)".
        iDestruct "Hlist2" as "(_ & (Hown_frag2 & _) & _)".
        iCombine "Hown_frag1 Hown_frag2" as "Hown_frag".
        by iFrame "# ∗".
      + iDestruct "Hlist1" as (d down) "(%Hlvl & #Hinv & %Hsome & Hd1 & %Hkey & Hmatch1)".
        iDestruct "Hlist2" as (d' down') "(_ & _ & %Hsome' & Hd2 & _ & Hmatch2)".

        assert (d = d') as <- by congruence.
        iDestruct (mapsto_agree with "Hd1 Hd2") as %<-%rep_to_node_inj.
        iCombine "Hd1 Hd2" as "Hd".

        iCombine "Hmatch1 Hmatch2" as "Hmatch".
        iPoseProof ("IHsubs" with "Hmatch") as "Hlist".
        
        iExists d, down. by iFrame "# ∗".
    Qed.
      
    Lemma is_skip_list_sep (v: val) (S: gset Z) (q1 q2: frac) 
      (bot: bot_gname) (subs: list sub_gname) :
      is_skip_list v S (q1 + q2) bot subs ⊢ 
        is_skip_list v S q1 bot subs ∗ is_skip_list v S q2 bot subs.
    Proof.
      iIntros "Hlist".
      iDestruct "Hlist" as (h head) "(%Hv & Hpt & %Hmin & Hlist)".

      iDestruct "Hpt" as "(Hpt1 & Hpt2)".
      iDestruct (skip_list_equiv_sep with "Hlist") as "(Hlist1 & Hlist2)".

      iSplitL "Hpt1 Hlist1".
      + iExists h, head. by iFrame.
      + iExists h, head. by iFrame.
    Qed.      
    
    Lemma is_skip_list_join (v: val) (S1 S2: gset Z) (q1 q2: frac) 
      (bot: bot_gname) (subs: list sub_gname) :
      is_skip_list v S1 q1 bot subs ∗ is_skip_list v S2 q2 bot subs ⊢ 
        is_skip_list v (S1 ∪ S2) (q1 + q2) bot subs.
    Proof.
      iIntros "(Hlist1 & Hlist2)".
      iDestruct "Hlist1" as (h head) "(%Hv & Hpt1 & %Hmin & Hlist1)".
      iDestruct "Hlist2" as (h' head') "(%Hv' & Hpt2 & _ & Hlist2)".

      assert (h = h') as <- by congruence.
      iDestruct (mapsto_agree with "Hpt1 Hpt2") as %<-%rep_to_node_inj.
      iCombine "Hpt1 Hpt2" as "Hpt".

      iCombine "Hlist1 Hlist2" as "Hlist".
      rewrite skip_list_equiv_join.

      iExists h, head. by iFrame.
    Qed.

  End Proofs.
End SkipListInv.