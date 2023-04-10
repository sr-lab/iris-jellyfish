From iris.algebra Require Import auth gset.
From iris.heap_lang Require Import notation.

From SkipList.lib Require Import zrange.
From SkipList.atomic Require Import proofmode lock.
From SkipList.lazy_list Require Import code.


Class lazyG Σ := LazyG { 
  lazy_authG :: inG Σ (authR (gsetR node_rep));
  lazy_disjG :: inG Σ (gset_disjR Z)
}.

Record lazy_gname := mk_lazy_gname {
  auth_gname: gname;
  disj_gname: gname
}.

Module LazyListInv (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module LazyList := LazyList Params.
  Export LazyList.

  Section invariant.
    Context `{!heapGS Σ, !lazyG Σ}.

    (* Successor chain *)
    Definition has_next (Γ: lazy_gname) (pred: node_rep) : iProp Σ :=
      ∃ (succ: node_rep), 
        node_next pred ↦{#1 / 2} rep_to_node succ
        ∗
        (⌜ succ = tail ⌝ ∨ own Γ.(auth_gname) (◯ {[succ]}))
        ∗
        own Γ.(disj_gname) (ZRange (node_key pred) (node_key succ)).

    (* Lock resources *)
    Definition in_lock (pred: node_rep) : iProp Σ := 
      ∃ (succ: node_rep), node_next pred ↦{#1 / 2} rep_to_node succ.
    Definition has_lock (pred: node_rep) : iProp Σ := 
      ∃ (st: state), lock #(node_lock pred) st ∗
        match st with Free => in_lock pred | Locked => emp end.

    (* Lazy list resources *)
    Definition lazy_list (head: node_rep) (S: gset node_rep) (Γ: lazy_gname) : iProp Σ :=
      own Γ.(auth_gname) (● S)
      ∗
      own Γ.(disj_gname) (GSet (set_map node_key S))
      ∗
      ([∗ set] n ∈ {[head]} ∪ S, has_next Γ n)
      ∗
      ([∗ set] n ∈ {[head]} ∪ S, has_lock n).

    (* Abstract representation predicate *)
    Definition set (p: loc) (s: gset Z) (Γ: lazy_gname) : iProp Σ :=
      ∃ (head: node_rep) (S: gset node_rep),
        p ↦□ rep_to_node head
        ∗
        ⌜ node_key head = INT_MIN ⌝
        ∗
        ⌜ s = set_map node_key S ⌝
        ∗
        lazy_list head S Γ.

    Global Instance has_lock_timeless n : Timeless (has_lock n).
    Proof. apply bi.exist_timeless; intros; case_match; apply _. Qed.
  End invariant.

  Section proofs.
    Context `{!heapGS Σ, !lazyG Σ}.

    Lemma singleton_frag_in (h n s: node_rep) (S: gset node_rep) (Γ: lazy_gname) :
      ⌜ n = s ⌝ ∨ own Γ.(auth_gname) (◯ {[n]}) -∗ lazy_list h S Γ -∗ ⌜ n ∈ {[s]} ∪ S ⌝.
    Proof.
      iIntros "Hnode Hlazy".
      iDestruct "Hlazy" as "(Hauth & Hdisj & Hnexts & Hlocks)".
      iDestruct "Hnode" as "[->|Hnode]"; first (iPureIntro; set_solver).
      iDestruct (own_valid_2 with "Hauth Hnode") 
        as %[?%gset_included]%auth_both_valid_discrete.
      iPureIntro; set_solver.
    Qed.

    Lemma node_has_next (head pred: node_rep) (S: gset node_rep) (Γ: lazy_gname) :
      ⌜ pred = head ⌝ ∨ own Γ.(auth_gname) (◯ {[pred]}) -∗
      lazy_list head S Γ -∗
        ∃ (succ: node_rep), 
          node_next pred ↦{#1 / 2} rep_to_node succ
          ∗
          (⌜ succ = tail ⌝ ∨ own Γ.(auth_gname) (◯ {[succ]}))
          ∗
          ⌜ set_map node_key S ## zrange (node_key pred) (node_key succ) ⌝
          ∗
          (node_next pred ↦{#1 / 2} rep_to_node succ -∗ lazy_list head S Γ).
    Proof.
      iIntros "#Hpred Hlazy".
      iDestruct (singleton_frag_in with "Hpred Hlazy") as %Hpred.
      iDestruct "Hlazy" as "(Hauth & Hdisj & Hnexts & Hlocks)".
      rewrite (big_sepS_delete (has_next Γ) _ pred) //.
      iDestruct "Hnexts" as "(Hnext & Hnexts)".
      iDestruct "Hnext" as (succ) "(Hnext & #Hsucc & Hkeys)".
      iDestruct (own_valid_2 with "Hdisj Hkeys") as %[Hdisj _]%ZRange_disj.

      iExists succ; iFrame "# ∗"; iSplit; first done. iIntros "Hnext". 
      iAssert (has_next Γ pred) with "[Hnext Hkeys]" as "Hnext".
      { iExists succ; by iFrame. }
      iCombine "Hnext Hnexts" as "Hnexts"; rewrite -big_sepS_delete //.
    Qed.

    Lemma lazy_node_has_lock (head node: node_rep) (S: gset node_rep) (Γ: lazy_gname) :
      ⌜ node = head ⌝ ∨ own Γ.(auth_gname) (◯ {[node]}) -∗
      lazy_list head S Γ -∗
        has_lock node ∗ (has_lock node -∗ lazy_list head S Γ).
    Proof.
      iIntros "#Hnode Hlazy".
      iDestruct (singleton_frag_in with "Hnode Hlazy") as %Hnode.
      iDestruct "Hlazy" as "(Hauth & Hdisj & Hnexts & Hlocks)".
      rewrite (big_sepS_delete has_lock _ node) //.
      iDestruct "Hlocks" as "(Hlock & Hlocks)".
      iFrame; iIntros "Hlock".
      iCombine "Hlock Hlocks" as "Hlocks"; rewrite -big_sepS_delete //.
    Qed.

    Lemma set_node_has_lock (p: loc) (head node: node_rep) (s: gset Z) (Γ: lazy_gname) :
      p ↦□ rep_to_node head -∗
      ⌜ node = head ⌝ ∨ own Γ.(auth_gname) (◯ {[node]}) -∗
      set p s Γ -∗
        has_lock node ∗ (has_lock node -∗ set p s Γ).
    Proof.
      iIntros "Hhead #Hnode Hset".
      iDestruct "Hset" as (h' S) "(H & Hmin & Hkeys & Hlazy)".
      iDestruct (mapsto_agree with "Hhead H") as %<-%rep_to_node_inj; iClear "H".
      iDestruct (lazy_node_has_lock with "Hnode Hlazy") as "[Hlock Hlazy]".
      iFrame "Hlock". iIntros. iExists head, S. iFrame. by iApply "Hlazy".
    Qed.

    Lemma set_has_lazy (p: loc) (head: node_rep) (s: gset Z) (Γ: lazy_gname) :
      p ↦□ rep_to_node head -∗
      set p s Γ -∗
        ∃ (S : gset node_rep), 
          lazy_list head S Γ ∗ (lazy_list head S Γ -∗ set p s Γ).
    Proof.
      iIntros "Hhead Hset". iDestruct "Hset" as (Γl S) "(H & ? & ? & Hlazy)".
      iDestruct (mapsto_agree with "Hhead H") as %<-%rep_to_node_inj; iClear "H".
      iExists S. iFrame "Hlazy". iIntros "Hlazy". iExists head, S. iFrame.
    Qed. 
  End proofs.
End LazyListInv.