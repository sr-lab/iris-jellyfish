From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import gmap.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import arg_max.
From SkipList.jelly_fish Require Import code.
From SkipList.lib Require Import misc node_rep node_lt.
From SkipList.jelly_fish.inv Require Import list_equiv lazy_inv.


Local Open Scope Z.

Module SkipListInv (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Invariant := LazyListInv Params.
  Export Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !skipGS Σ, !lockG Σ}.

    Fixpoint skip_list_equiv (lvl: Z) (head: node_rep) (M: gmap Z (argmax Z)) 
      (q: frac) (bot: bot_gname) (subs: list sub_gname) : iProp Σ :=
      match subs with
      | nil => False
      | Γ :: subs =>
        match subs with
        | nil =>
          ⌜ lvl = 0 ⌝
          ∗
          is_bot_list 0 head M q bot Γ

        | γ :: _ =>
          ⌜ lvl > 0 ⌝
          ∗
          is_sub_list lvl head Γ γ
          ∗
          skip_list_equiv (lvl - 1) head M q bot subs
        end
      end.

    Definition is_skip_list (p: loc) (M: gmap Z (argmax Z)) (q: frac) 
      (bot: bot_gname) (subs: list sub_gname) : iProp Σ := 
      ∃ (head: node_rep),
        p ↦□ rep_to_node head
        ∗
        ⌜ node_key head = INT_MIN ⌝
        ∗
        skip_list_equiv MAX_HEIGHT head M q bot subs.

    
    Lemma skip_list_equiv_cons (head: node_rep) (lvl: Z) (M: gmap Z (argmax Z)) 
      (q: frac) (bot: bot_gname) (Γ: sub_gname) (subs: list sub_gname) :
      skip_list_equiv lvl head M q bot (Γ :: subs) ⊢ 
        ∃ (obot: option bot_gname) (osub: option sub_gname),
          inv (levelN lvl) (lazy_list_inv lvl head obot Γ osub)
          ∗
          skip_list_equiv lvl head M q bot (Γ :: subs).
    Proof.
      destruct subs as [|γ subs].
      + iIntros "Htop". iExists (Some bot), None.
        iDestruct "Htop" as "(%Hlvl & ? & #Hinv)".
        subst; by iFrame "# ∗".
      + iIntros "Hlist". iExists None, (Some γ).
        iDestruct "Hlist" as "(? & #Hinv & ?)".
        iFrame "# ∗".
    Qed.

    Lemma skip_list_equiv_inv (lvl: Z) (head: node_rep) (M: gmap Z (argmax Z)) 
      (q: frac) (bot: bot_gname) (subs: list sub_gname) :
      skip_list_equiv lvl head M q bot subs ⊢
        ∃ (sub: sub_gname),
          ⌜ last subs = Some sub ⌝
          ∗
          is_bot_list 0 head M q bot sub
          ∗
          (is_bot_list 0 head M q bot sub -∗ skip_list_equiv lvl head M q bot subs).
    Proof.
      iRevert (lvl).
      iInduction subs as [|Γ subs] "IHsubs";
        iIntros (lvl) "Hlist"; 
        first by iExFalso.
      
      destruct subs as [|γ subs].
      + iDestruct "Hlist" as "(%Hlvl & Hbot)".
        rewrite Hlvl.
        iExists Γ; iFrame.
        iSplit; first done.
        iIntros "Hbot"; by iFrame.
      + iDestruct "Hlist" as "(Hlvl & Hsub & Hmatch)".
        iPoseProof ("IHsubs" with "Hmatch") as "Hlist".
        iDestruct "Hlist" as (sub) "(Hlast & Hbot & Himp)".
        iExists sub; iFrame.
        iIntros "Hbot".
        iPoseProof ("Himp" with "Hbot") as "Hlist".
        iFrame.
    Qed.

    Lemma skip_list_equiv_sep (lvl: Z) (head: node_rep) (M: gmap Z (argmax Z)) 
      (q1 q2: frac) (bot: bot_gname) (subs: list sub_gname) :
      skip_list_equiv lvl head M (q1 + q2) bot subs ⊢ 
        skip_list_equiv lvl head M q1 bot subs ∗ skip_list_equiv lvl head M q2 bot subs.
    Proof.
      iRevert (lvl head).
      iInduction subs as [|Γ subs] "IHsubs"; 
        iIntros (lvl head) "Hlist"; 
        first by iExFalso.

      destruct subs as [|γ subs].
      + iDestruct "Hlist" as "(%Hlvl & Hown_frag & #Hinv)".
        iDestruct "Hown_frag" as "(Hown_frag1 & Hown_frag2)".
        by iFrame "# ∗".
      + iDestruct "Hlist" as "(%Hlvl & #Hinv & Hmatch)".
        iPoseProof ("IHsubs" with "Hmatch") as "(Hlist1 & Hlist2)".
        iSplitL "Hlist1"; by iFrame "# ∗".
    Qed.

    Lemma skip_list_equiv_join (lvl: Z) (head: node_rep) (M1 M2: gmap Z (argmax Z)) 
      (q1 q2: frac) (bot: bot_gname) (subs: list sub_gname) :
      skip_list_equiv lvl head M1 q1 bot subs ∗ skip_list_equiv lvl head M2 q2 bot subs ⊢ 
        skip_list_equiv lvl head (M1 ⋅ M2) (q1 + q2) bot subs.
    Proof.
      iRevert (lvl head).
      iInduction subs as [|Γ subs] "IHsubs"; 
        iIntros (lvl head) "(Hlist1 & Hlist2)"; 
        first by iExFalso.

      destruct subs as [|γ subs].
      + iDestruct "Hlist1" as "(%Hlvl & Hown_frag1 & #Hinv)".
        iDestruct "Hlist2" as "(_ & Hown_frag2 & _)".
        iCombine "Hown_frag1 Hown_frag2" as "Hown_frag".
        by iFrame "# ∗".
      + iDestruct "Hlist1" as "(%Hlvl & #Hinv & Hmatch1)".
        iDestruct "Hlist2" as "(_ & _ & Hmatch2)".
        iCombine "Hmatch1 Hmatch2" as "Hmatch".
        iPoseProof ("IHsubs" with "Hmatch") as "Hlist".
        by iFrame "# ∗".
    Qed.
      
    Lemma is_skip_list_sep (p: loc) (M: gmap Z (argmax Z)) 
      (q1 q2: frac) (bot: bot_gname) (subs: list sub_gname) :
      is_skip_list p M (q1 + q2) bot subs ⊢ 
        is_skip_list p M q1 bot subs ∗ is_skip_list p M q2 bot subs.
    Proof.
      iIntros "Hlist".
      iDestruct "Hlist" as (head) "(#Hpt & %Hmin & Hlist)".
      iDestruct (skip_list_equiv_sep with "Hlist") as "(Hlist1 & Hlist2)".
      iSplitL "Hlist1"; iExists head; by iFrame "# ∗".
    Qed.      
    
    Lemma is_skip_list_join (p: loc) (M1 M2: gmap Z (argmax Z))
      (q1 q2: frac) (bot: bot_gname) (subs: list sub_gname) :
      is_skip_list p M1 q1 bot subs ∗ is_skip_list p M2 q2 bot subs ⊢ 
        is_skip_list p (M1 ⋅ M2) (q1 + q2) bot subs.
    Proof.
      iIntros "(Hlist1 & Hlist2)".
      iDestruct "Hlist1" as (head) "(#Hpt1 & %Hmin & Hlist1)".
      iDestruct "Hlist2" as (head') "(#Hpt2 & _ & Hlist2)".
      iDestruct (mapsto_agree with "Hpt1 Hpt2") as %<-%rep_to_node_inj.
      iCombine "Hlist1 Hlist2" as "Hlist".
      rewrite skip_list_equiv_join.
      iExists head; by iFrame "# ∗".
    Qed.

  End Proofs.
End SkipListInv.