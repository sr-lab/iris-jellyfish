From iris.algebra Require Import auth gset.
From AtomicInvariant.lib Require Import zrange.
From iris.heap_lang Require Import proofmode notation.
From AtomicInvariant.atomic Require Import lock.
From AtomicInvariant.lazy_list Require Import code.


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
    Local Open Scope Z.

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
      iDestruct (pointsto_agree with "Hhead H") as %<-%rep_to_node_inj; iClear "H".
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
      iDestruct (pointsto_agree with "Hhead H") as %<-%rep_to_node_inj; iClear "H".
      iExists S. iFrame "Hlazy". iIntros "Hlazy". iExists head, S. iFrame.
    Qed. 

    Lemma set_update (p: loc) (head pred node succ: node_rep) (s: gset Z) (Γ: lazy_gname) :
      (* The ranges for the new key *)
      INT_MIN < node_key node < INT_MAX →
      node_key pred < node_key node < node_key succ →
      (* Ownership of the full set *)
      p ↦□ rep_to_node head -∗ set p s Γ -∗
      (* Ownership of the link between pred and succ after acquiring pred's lock *)
      ⌜ pred = head ⌝ ∨ own Γ.(auth_gname) (◯ {[pred]}) -∗
      ⌜ succ = tail ⌝ ∨ own Γ.(auth_gname) (◯ {[succ]}) -∗
      node_next pred ↦{#1 / 2} rep_to_node succ -∗
      (* Ownership of the allocated resources for the new node *)
      node_next node ↦ rep_to_node succ -∗ node_lock node ↦ #false -∗
      (* We obtain the right to update pred and to update the set accordingly *)
      node_next pred ↦ rep_to_node succ ∗ (node_next pred ↦ rep_to_node node ==∗
      set p (s ∪ {[node_key node]}) Γ ∗ node_next pred ↦{#1 / 2} rep_to_node node).
    Proof.
      iIntros (Hrange Hkey) "Hhead Hset #Hpred #Hsucc Hnext [Hn Hn'] Hl".
      
      (* Destruct set resources *)
      iDestruct "Hset" as (h' S) "(H & %Hmin & %Hkeys & Hlazy)".
      iDestruct (pointsto_agree with "Hhead H") as %<-%rep_to_node_inj; iClear "H".
      iDestruct (singleton_frag_in with "Hpred Hlazy") as %Hpred.
      iDestruct "Hlazy" as "(Hauth & Hdisj & Hnexts & Hlocks)".
      (* Assert ownership of pred's successor pointer and assume update *)
      rewrite (big_sepS_delete (has_next _) _ pred) //.
      iDestruct "Hnexts" as "[Hnext' Hnexts]".
      iDestruct "Hnext'" as (succ') "(Hnext' & _ & Hkeys)".
      iDestruct (pointsto_agree with "Hnext Hnext'") as %<-%rep_to_node_inj.
      iFrame. iIntros "[Hnext Hnext']".

      (* Update authoritative ghost state *)
      iMod (own_update with "Hauth") as "[Hauth Hfrag]".
      { by apply auth_update_alloc, (op_local_update_discrete _ _ {[node]}). }
      rewrite right_id (comm op {[node]} S).
      (* Update sublist tokens *)
      rewrite (ZRange_split (node_key node)); last done.
      iDestruct "Hkeys" as "((Hkeys & Hkey) & Hkeys')".
      iDestruct (own_valid_2 with "Hdisj Hkey") as %Hdisj%gset_disj_valid_op.
      iCombine "Hdisj Hkey" as "Hdisj"; rewrite gset_disj_union //.
      (* Ghost updates done *)
      iModIntro.

      (* Add pred resources back to set *)
      iAssert (has_next _ pred) with "[Hnext Hfrag Hkeys]"
        as "Hnext". { iExists node; iFrame. }
      iCombine "Hnext Hnexts" as "Hnexts". rewrite -big_sepS_delete //.
      (* Add new node resources to set *)
      iAssert (has_next _ node) with "[Hn Hkeys']" as "Hnext".
      { iExists succ; iFrame "# ∗". }
      iCombine "Hnext Hnexts" as "Hnexts".
      (* Add lock resources of the new node to set *)
      iAssert (has_lock node) with "[Hn' Hl]" as "Hlock".
      { iExists Free. iSplitR "Hn'"; last by iExists succ. iExists _. by iFrame. }
      iCombine "Hlock Hlocks" as "Hlocks".
      (* Simplify [∗ set] *)
      assert (node_key node ≠ node_key head) by lia.
      assert (node ∉ {[head]} ∪ S) by set_solver.
      do 2 rewrite -big_sepS_insert // (comm_L _ _ ({[head]} ∪ S)) -assoc_L.

      (* Assert update to set *)
      iFrame. rewrite Hkeys set_map_union_L set_map_singleton_L. by iFrame.
    Qed.
  End proofs.
End LazyListInv.