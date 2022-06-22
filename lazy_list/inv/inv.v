From Coq Require Import Sorting.Sorted.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc.
From SkipList.lazy_list Require Import node_lt node_rep code key_equiv.
From SkipList.lazy_list.inv Require Import list_equiv.


Class gset_list_unionGS Σ := GsetGS { 
  gset_nr_A_inGS :> inG Σ (authR (gsetUR node_rep));
  gset_nr_F_inGS :> inG Σ (frac_authR (gsetUR node_rep));
  gset_Z_disj_inGS :> inG Σ (gset_disjUR Z)
}.

Record lazy_gname := mk_lazy_gname {
  s_auth: gname;
  s_frac: gname;
  s_keys: gname
}.

Local Open Scope Z.
Module LazyListInv (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module ListEquiv := ListEquiv Params.
  Export ListEquiv.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ}.

    Definition lazyN := nroot .@ "lazy".

    Definition node_key_range : gset Z := Zlt_range INT_MIN INT_MAX.

    Definition lazy_list_inv (head: node_rep) (Γ: lazy_gname) : iProp Σ := 
      ∃ (S: gset node_rep) (Skeys: gset Z) (L: list node_rep),
      ⌜ Permutation L (elements S) ⌝
      ∗
      ⌜ Sorted node_lt ([head] ++ L ++ [tail]) ⌝
      ∗
      ⌜ key_equiv S Skeys ⌝
      ∗
      own (s_auth Γ) (● S)
      ∗
      own (s_frac Γ) (●F S)
      ∗
      own (s_keys Γ) (GSet (node_key_range ∖ Skeys))
      ∗
      list_equiv ([head] ++ L).

    Definition is_lazy_list (v: val) (Skeys: gset Z) (q: frac) (Γ: lazy_gname) : iProp Σ := 
      ∃ (l: loc) (head: node_rep) (Sfrac: gset node_rep),
      ⌜ #l = v ⌝
      ∗
      l ↦{#q} rep_to_node head
      ∗
      ⌜ node_key head = INT_MIN ⌝
      ∗
      ⌜ key_equiv Sfrac Skeys ⌝
      ∗
      own (s_frac Γ) (◯F{q} Sfrac)
      ∗
      inv lazyN (lazy_list_inv head Γ).


    Lemma is_lazy_list_sep (v: val) (S: gset Z) (q1 q2: frac) (Γ: lazy_gname) :
      is_lazy_list v S (q1 + q2) Γ ⊢ 
        is_lazy_list v S q1 Γ ∗ is_lazy_list v S q2 Γ.
    Proof.
      iIntros "Hlist".
      iDestruct "Hlist" as (h head Sfrac) "(%Hv & Hpt & %Hmin & %Hequiv & Hown_frag &#Hinv)".
      iDestruct "Hpt" as "(Hpt1 & Hpt2)".
      iDestruct "Hown_frag" as "(Hown_frag1 & Hown_frag2)".
      iSplitL "Hpt1 Hown_frag1".
      + iExists h, head, Sfrac. by iFrame "# ∗".
      + iExists h, head, Sfrac. by iFrame "# ∗".
    Qed.
    
    Lemma is_lazy_list_join (v: val) (S1 S2: gset Z) (q1 q2: frac) (Γ: lazy_gname) :
      is_lazy_list v S1 q1 Γ ∗ is_lazy_list v S2 q2 Γ ⊢ 
        is_lazy_list v (S1 ∪ S2) (q1 + q2) Γ.
    Proof.
      iIntros "(Hlist1 & Hlist2)".
      iDestruct "Hlist1" as (h head Sfrac1) "(%Hv & Hpt1 & %Hmin & %Hequiv1 & Hown_frag1 & #Hinv)".
      iDestruct "Hlist2" as (h' head' Sfrac2) "(%Hv' & Hpt2 & _ & %Hequiv2 & Hown_frag2 & _)".

      assert (h = h') as <- by congruence.
      iDestruct (mapsto_agree with "Hpt1 Hpt2") as %<-.
      iCombine "Hpt1 Hpt2" as "Hpt".
      iCombine "Hown_frag1 Hown_frag2" as "Hown_frag".
      rewrite gset_op.

      iAssert (|={⊤}=> is_lazy_list v (S1 ∪ S2) (q1 + q2) Γ)%I with "[Hpt Hown_frag]" as "Hlist"; last first.
      { admit. }

      iInv lazyN as (S Skeys L) "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_frac & >Hown_keys & Hlist)" "Hclose".
      iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
        as %Hsub%frac_auth_included_total%gset_included.

      assert (key_equiv (Sfrac1 ∪ Sfrac2) (S1 ∪ S2)).
      { 
        eapply (key_equiv_union L S); auto.
        by do 2 apply node_rep_sorted_app in Hsort as [? Hsort].
      }

      iMod ("Hclose" with "[Hown_auth Hown_frac Hown_keys Hlist]") as "_".
      { iNext; iExists S, Skeys, L; by iFrame. }

      iModIntro. 
      iExists h, head, (Sfrac1 ∪ Sfrac2). by iFrame "# ∗".
    Admitted.

  End Proofs.
End LazyListInv.