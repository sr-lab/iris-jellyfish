From Coq Require Import Sorting.Sorted.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lazy_list Require Import code.
From SkipList.lib Require Import misc node_rep node_lt key_equiv.
From SkipList.lazy_list.inv Require Import list_equiv.


Class gset_list_unionGS Σ := GsetGS { 
  gset_nr_A_inGS :> inG Σ (authR (gsetUR node_rep));
  gset_nr_F_inGS :> inG Σ (frac_authR (gsetUR Z));
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
      own (s_frac Γ) (●F Skeys)
      ∗
      own (s_keys Γ) (GSet (node_key_range ∖ Skeys))
      ∗
      list_equiv ([head] ++ L).

    Definition is_lazy_list (v: val) (Skeys: gset Z) (q: frac) (Γ: lazy_gname) : iProp Σ := 
      ∃ (l: loc) (head: node_rep),
      ⌜ #l = v ⌝
      ∗
      l ↦{#q} rep_to_node head
      ∗
      ⌜ node_key head = INT_MIN ⌝
      ∗
      own (s_frac Γ) (◯F{q} Skeys)
      ∗
      inv lazyN (lazy_list_inv head Γ).


    Lemma is_lazy_list_sep (v: val) (S: gset Z) (q1 q2: frac) (Γ: lazy_gname) :
      is_lazy_list v S (q1 + q2) Γ ⊢ 
        is_lazy_list v S q1 Γ ∗ is_lazy_list v S q2 Γ.
    Proof.
      iIntros "Hlist".
      iDestruct "Hlist" as (h head) "(%Hv & Hpt & %Hmin & Hown_frag &#Hinv)".
      iDestruct "Hpt" as "(Hpt1 & Hpt2)".
      iDestruct "Hown_frag" as "(Hown_frag1 & Hown_frag2)".
      iSplitL "Hpt1 Hown_frag1".
      + iExists h, head. by iFrame "# ∗".
      + iExists h, head. by iFrame "# ∗".
    Qed.
    
    Lemma is_lazy_list_join (v: val) (S1 S2: gset Z) (q1 q2: frac) (Γ: lazy_gname) :
      is_lazy_list v S1 q1 Γ ∗ is_lazy_list v S2 q2 Γ ⊢ 
        is_lazy_list v (S1 ∪ S2) (q1 + q2) Γ.
    Proof.
      iIntros "(Hlist1 & Hlist2)".
      iDestruct "Hlist1" as (h head) "(%Hv & Hpt1 & %Hmin & Hown_frag1 & #Hinv)".
      iDestruct "Hlist2" as (h' head') "(%Hv' & Hpt2 & _ & Hown_frag2 & _)".

      assert (h = h') as <- by congruence.
      iDestruct (mapsto_agree with "Hpt1 Hpt2") as %<-.
      iCombine "Hpt1 Hpt2" as "Hpt".
      iCombine "Hown_frag1 Hown_frag2" as "Hown_frag".
      iExists h, head. by iFrame "# ∗".
    Qed.

  End Proofs.
End LazyListInv.