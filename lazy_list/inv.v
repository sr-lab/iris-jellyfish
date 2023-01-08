From iris.algebra Require Import gset excl_auth.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import zrange.
From SkipList.lazy_list Require Import code.


Class lazyG Σ := LazyG { 
  lazy_authG :> inG Σ (authR (gsetR node_rep));
  lazy_disjG :> inG Σ (gset_disjR Z);
  lazy_exclG :> inG Σ (excl_authR (gset Z));
  lazy_lockG :> lockG Σ
}.

Record inv_gname := mk_inv_gname {
  auth_gname: gname;
  disj_gname: gname
}.

Record set_gname := mk_set_gname {
  excl_gname: gname
}.

Module LazyListInv (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module LazyList := LazyList Params.
  Export LazyList.

  Section invariant.
    Context `{!heapGS Σ, !lazyG Σ} (N: namespace).

    Definition lazyN := N .@ "lazy".

    Definition in_lock (l: loc) : iProp Σ := 
      ∃ (succ: node_rep), l ↦{#1 / 2} rep_to_node succ.

    Definition has_lock (node: node_rep) : iProp Σ := 
      ∃ (γl: gname), is_lock γl (node_lock node) (in_lock (node_next node)).

    Definition has_next (Γi: inv_gname) (pred: node_rep) : iProp Σ :=
      ∃ (succ: node_rep), 
        node_next pred ↦{#1 / 2} rep_to_node succ
        ∗
        (⌜ succ = tail ⌝ ∨ own Γi.(auth_gname) (◯ {[succ]}))
        ∗
        own Γi.(disj_gname) (ZRange (node_key pred) (node_key succ)).

    Definition lazy_list_inv (head: node_rep) (Γi: inv_gname) (Γs: set_gname) : iProp Σ :=
      ∃ (S: gset node_rep),
        own Γi.(auth_gname) (● S)
        ∗
        own Γi.(disj_gname) (GSet (set_map node_key S))
        ∗
        ([∗ set] n ∈ {[head]} ∪ S, has_lock n)
        ∗
        ([∗ set] n ∈ {[head]} ∪ S, has_next Γi n)
        ∗
        own Γs.(excl_gname) (●E (set_map node_key S)).

    Definition set_inv (p: loc) (Γs: set_gname) : iProp Σ :=
      ∃ (head: node_rep) (Γi: inv_gname),
        p ↦□ rep_to_node head
        ∗
        ⌜ node_key head = INT_MIN ⌝
        ∗
        inv lazyN (lazy_list_inv head Γi Γs).

    Definition set (s: gset Z) (Γs: set_gname) : iProp Σ := 
      own Γs.(excl_gname) (◯E s).

  End invariant.

  Section proofs.
    Context `{!lazyG Σ}.

    Lemma singleton_frag_in (S: gset node_rep) (n s: node_rep) (γ: gname) :
      own γ (● S) -∗ ⌜ n = s ⌝ ∨ own γ (◯ {[n]}) -∗ ⌜ n ∈ {[s]} ∪ S ⌝.
    Proof.
      iIntros "Hauth Hnode".
      iDestruct "Hnode" as "[->|Hnode]"; first (iPureIntro; set_solver).
      iDestruct (own_valid_2 with "Hauth Hnode") 
        as %[?%gset_included]%auth_both_valid_discrete.
      iPureIntro; set_solver.
    Qed.
  End proofs.
End LazyListInv.