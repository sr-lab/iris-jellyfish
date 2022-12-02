From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.
From iris.bi Require Import updates.

From SkipList.skip_list.lists Require Import code.
From SkipList.lib Require Import misc node_rep node_lt.
From SkipList.skip_list.lists.inv Require Import list_equiv lazy_inv.


Local Open Scope Z.

Module SkipListInv (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Invariant := LazyListInv Params.
  Export Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !skipGS Σ, !lockG Σ}.

    Definition levelN (lvl: Z) := nroot .@ "level" .@ lvl.

    Fixpoint skip_list_equiv (lvl: Z) (head: node_rep) (S: gset Z)
      (q: frac) (bot: bot_gname) (subs: list sub_gname) : iProp Σ :=
      match subs with
      | nil => False
      | Γ :: subs =>
        match subs with
        | nil =>
          ⌜ lvl = 0 ⌝
          ∗
          is_bot_list (levelN lvl) head S q bot Γ
          ∗
          ⌜ node_down head = None ⌝

        | γ :: _ =>
          ∃ (d: loc) (down: node_rep),
            ⌜ lvl > 0 ⌝
            ∗
            is_sub_list (levelN lvl) head Γ γ
            ∗
            ⌜ node_down head = Some d ⌝
            ∗
            d ↦□ rep_to_node down
            ∗
            ⌜ node_key head = node_key down ⌝
            ∗
            skip_list_equiv (lvl - 1) down S q bot subs
        end
      end.

    Definition is_skip_list (p: loc) (S: gset Z) (q: frac) 
      (bot: bot_gname) (subs: list sub_gname) : iProp Σ := 
      ∃ (head: node_rep),
        p ↦□ rep_to_node head
        ∗
        ⌜ node_key head = INT_MIN ⌝
        ∗
        skip_list_equiv MAX_HEIGHT head S q bot subs.

    
    Lemma skip_list_equiv_cons (lvl: Z) (head: node_rep) (S: gset Z) 
      (q: frac) (bot: bot_gname) (Γ: sub_gname) (subs: list sub_gname) :
      skip_list_equiv lvl head S q bot (Γ :: subs) ⊢ 
        ∃ (obot: option bot_gname) (osub: option sub_gname),
          inv (levelN lvl) (lazy_list_inv head obot Γ osub)
          ∗
          skip_list_equiv lvl head S q bot (Γ :: subs).
    Proof.
      destruct subs as [|γ subs].
      + iIntros "Htop". iExists (Some bot), None.
        iDestruct "Htop" as "(? & (? & #Hinv) & ?)".
        iFrame "# ∗".
      + iIntros "Hlist". iExists None, (Some γ).
        iDestruct "Hlist" as (d down) "(? & #Hinv & ?)".
        iFrame "# ∗". iExists d, down. iFrame.
    Qed.
    
    Lemma skip_list_equiv_cons_down (lvl: Z) (head: node_rep) (S: gset Z) 
      (q: frac) (bot: bot_gname) (Γ γ: sub_gname) (subs: list sub_gname) :
      skip_list_equiv lvl head S q bot (Γ :: γ :: subs) ⊢ 
        ∃ (d: loc) (down: node_rep) (obot: option bot_gname) (osub: option sub_gname),
          ⌜ node_down head = Some d ⌝
          ∗
          d ↦□ rep_to_node down
          ∗
          inv (levelN (lvl - 1)) (lazy_list_inv down obot γ osub)
          ∗
          skip_list_equiv lvl head S q bot (Γ :: γ :: subs).
    Proof.
      destruct subs as [|sub subs].
      + iIntros "Htop".
        iDestruct "Htop" as (d down) "(? & ? & #Hsome & #Hd & ? & ? & (? & #Hinv) & ?)".
        iExists d, down, (Some bot), None; iFrame "# ∗".
        iExists d, down; iFrame "# ∗".
      + iIntros "Htop".
        iDestruct "Htop" as (d down) "(? & ? & #Hsome & #Hd & ? & Hlist)".
        iDestruct "Hlist" as (d' down') "(? & #Hinv & ? & ? & ? & ?)"; unfold is_sub_list.
        iExists d, down, None, (Some sub); iFrame "# ∗".
        iExists d, down; iFrame "# ∗".
        iExists d', down'; iFrame "# ∗".
    Qed.

    Lemma skip_list_equiv_sep (lvl: Z) (head: node_rep) (S: gset Z) (q1 q2: frac) 
      (bot: bot_gname) (subs: list sub_gname) :
      skip_list_equiv lvl head S (q1 + q2) bot subs ⊢ 
        skip_list_equiv lvl head S q1 bot subs ∗ skip_list_equiv lvl head S q2 bot subs.
    Proof.
      iRevert (lvl head).
      iInduction subs as [|Γ subs] "IHsubs"; 
        iIntros (lvl head) "Hlist"; 
        first by iExFalso.

      destruct subs as [|γ subs].
      + iDestruct "Hlist" as "(%Hlvl & (Hown_frag & #Hinv) & %Hnone)".
        iDestruct "Hown_frag" as "(Hown_frag1 & Hown_frag2)".
        by iFrame "# ∗".
      + iDestruct "Hlist" as (d down) "(%Hlvl & #Hinv & %Hsome & #Hd & %Hkey & Hmatch)".
        iPoseProof ("IHsubs" with "Hmatch") as "(Hlist1 & Hlist2)".
        iSplitL "Hlist1"; iExists d, down; by iFrame "# ∗".
    Qed.

    Lemma skip_list_equiv_join (lvl: Z) (head: node_rep) (S1 S2: gset Z) (q1 q2: frac) 
      (bot: bot_gname) (subs: list sub_gname) :
      skip_list_equiv lvl head S1 q1 bot subs ∗ skip_list_equiv lvl head S2 q2 bot subs ⊢ 
        skip_list_equiv lvl head (S1 ∪ S2) (q1 + q2) bot subs.
    Proof.
      iRevert (lvl head).
      iInduction subs as [|Γ subs] "IHsubs"; 
        iIntros (lvl head) "(Hlist1 & Hlist2)"; 
        first by iExFalso.

      destruct subs as [|γ subs].
      + iDestruct "Hlist1" as "(%Hlvl & (Hown_frag1 & #Hinv) & %Hnone)".
        iDestruct "Hlist2" as "(_ & (Hown_frag2 & _) & _)".
        iCombine "Hown_frag1 Hown_frag2" as "Hown_frag".
        by iFrame "# ∗".
      + iDestruct "Hlist1" as (d down) "(%Hlvl & #Hinv & %Hsome & #Hd & %Hkey & Hmatch1)".
        iDestruct "Hlist2" as (d' down') "(_ & _ & %Hsome' & #Hd' & _ & Hmatch2)".

        assert (d = d') as <- by congruence.
        iDestruct (mapsto_agree with "Hd Hd'") as %<-%rep_to_node_inj; iClear "Hd'".

        iCombine "Hmatch1 Hmatch2" as "Hmatch".
        iPoseProof ("IHsubs" with "Hmatch") as "Hlist".
        iExists d, down. by iFrame "# ∗".
    Qed.
      
    Lemma is_skip_list_sep (p: loc) (S: gset Z) (q1 q2: frac) 
      (bot: bot_gname) (subs: list sub_gname) :
      is_skip_list p S (q1 + q2) bot subs ⊢ 
        is_skip_list p S q1 bot subs ∗ is_skip_list p S q2 bot subs.
    Proof.
      iIntros "Hlist".
      iDestruct "Hlist" as (head) "(#Hpt & %Hmin & Hlist)".
      iDestruct (skip_list_equiv_sep with "Hlist") as "(Hlist1 & Hlist2)".
      iSplitL "Hlist1"; iExists head; by iFrame "# ∗".
    Qed.      
    
    Lemma is_skip_list_join (p: loc) (S1 S2: gset Z) (q1 q2: frac) 
      (bot: bot_gname) (subs: list sub_gname) :
      is_skip_list p S1 q1 bot subs ∗ is_skip_list p S2 q2 bot subs ⊢ 
        is_skip_list p (S1 ∪ S2) (q1 + q2) bot subs.
    Proof.
      iIntros "(Hlist1 & Hlist2)".
      iDestruct "Hlist1" as (head) "(#Hpt & %Hmin & Hlist1)".
      iDestruct "Hlist2" as (head') "(Hpt' & _ & Hlist2)".
      iDestruct (mapsto_agree with "Hpt Hpt'") as %<-%rep_to_node_inj; iClear "Hpt'".

      iCombine "Hlist1 Hlist2" as "Hlist".
      rewrite skip_list_equiv_join.
      iExists head; by iFrame "# ∗".
    Qed.

  End Proofs.
End SkipListInv.