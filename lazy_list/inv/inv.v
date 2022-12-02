From Coq Require Import Sorting.Sorted.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lazy_list Require Import code.
From SkipList.lib Require Import misc node_rep node_lt.
From SkipList.lazy_list.inv Require Import list_equiv.


Class lazyGS Σ := LazyGS { 
  frac_gsetR :> inG Σ (frac_authR (gsetUR Z));
  auth_gsetR :> inG Σ (authR (gsetUR node_rep))
}.

Record lazy_gname := mk_lazy_gname {
  s_auth: gname;
  s_frac: gname
}.

Local Open Scope Z.

Module LazyListInv (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module ListEquiv := ListEquiv Params.
  Export ListEquiv.

  Section Proofs.
    Context `{!heapGS Σ, !lazyGS Σ, !lockG Σ}.

    Definition lazyN := nroot .@ "lazy".

    Definition lazy_list_inv (head: node_rep) (Γ: lazy_gname) : iProp Σ := 
      ∃ (S: gset node_rep) (L: list node_rep),
        ⌜ Permutation L (elements S) ⌝
        ∗
        ⌜ Sorted node_lt ([head] ++ L ++ [tail]) ⌝
        ∗
        own (s_auth Γ) (● S)
        ∗
        own (s_frac Γ) (●F (set_map node_key S))
        ∗
        list_equiv ([head] ++ L).

    Definition is_lazy_list (p: loc) (Skeys: gset Z) (q: frac) (Γ: lazy_gname) : iProp Σ := 
      ∃ (head: node_rep),
        p ↦□ rep_to_node head
        ∗
        ⌜ node_key head = INT_MIN ⌝
        ∗
        own (s_frac Γ) (◯F{q} Skeys)
        ∗
        inv lazyN (lazy_list_inv head Γ).


    Lemma is_lazy_list_sep (p: loc) (S: gset Z) (q1 q2: frac) (Γ: lazy_gname) :
      is_lazy_list p S (q1 + q2) Γ ⊢ 
        is_lazy_list p S q1 Γ ∗ is_lazy_list p S q2 Γ.
    Proof.
      iIntros "Hlist".
      iDestruct "Hlist" as (head) "(#Hpt & %Hmin & Hown_frag &#Hinv)".
      iDestruct "Hown_frag" as "(Hown_frag1 & Hown_frag2)".
      iSplitL "Hown_frag1"; iExists head; by iFrame "# ∗".
    Qed.
    
    Lemma is_lazy_list_join (p: loc) (S1 S2: gset Z) (q1 q2: frac) (Γ: lazy_gname) :
      is_lazy_list p S1 q1 Γ ∗ is_lazy_list p S2 q2 Γ ⊢ 
        is_lazy_list p (S1 ∪ S2) (q1 + q2) Γ.
    Proof.
      iIntros "(Hlist1 & Hlist2)".
      iDestruct "Hlist1" as (head) "(#Hpt & %Hmin & Hown_frag1 & #Hinv)".
      iDestruct "Hlist2" as (head') "(Hpt' & _ & Hown_frag2 & _)".
      iDestruct (mapsto_agree with "Hpt Hpt'") as %<-%rep_to_node_inj; iClear "Hpt'".

      iCombine "Hown_frag1 Hown_frag2" as "Hown_frag".
      iExists head; by iFrame "# ∗".
    Qed.

  End Proofs.
End LazyListInv.