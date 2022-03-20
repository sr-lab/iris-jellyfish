From iris.heap_lang Require Import notation proofmode.
From iris.base_logic.lib Require Export invariants.

From SkipList.lazy_list Require Import code.

Local Open Scope Z.
Module LazyListSpec (Params: LAZYLIST_PARAMS).
  Import Params.
  Module Code := Lazylist Params.
  Export Code.

  Section Proofs.
    Context `{!heapGS Σ} (N : namespace).

    (* 
    * The sequence of keys must be the same and
    * the lock invariant must hold in all nodes.
    *)
    Fixpoint list_equiv (L: list Z) (node: val) : iProp Σ :=
      match L with
      | nil => ⌜ node = NONEV ⌝
      | h :: t => ∃ (k: Z) (n: loc) (m: bool) (l: val) (v': val),
                  ⌜ node = SOMEV (#k, #n, #m, l) ⌝
                  ∗
                  ⌜ k = h ⌝
                  ∗
                  n ↦ v'
                  ∗
                  (* is_lock γ l ???
                  ∗ *)
                  ▷list_equiv t v'
      end.

    (* 
    * The invariant for the lazy list asserts that
    * the underlying set S is sorted and must contain
    * the same elements as S.
    *)
    Definition lazy_list_inv (S: gset Z) (v: val) : iProp Σ := 
      ∃ (l: loc) (L: list Z) (head: val),
      ⌜v = #l⌝
      ∗
      ⌜ Permutation L (elements S) ⌝
      ∗
      (* ⌜ Sorted Zlt L ⌝
      ∗ *)
      l ↦ head
      ∗
      list_equiv ([INT_MIN] ++ L ++ [INT_MAX]) head
    .

    (* 
    * Asserts that l points to a heap cell that 
    * represents the set S as a lazy list.
    *)
    Definition is_lazy_list (S: gset Z) (v: val) : iProp Σ := 
      inv N (lazy_list_inv S v).

    Theorem new_spec :
      {{{ True }}}
        new #()
      {{{ v, RET v; 
        is_lazy_list ∅ v 
      }}}.
    Proof.
      iIntros (Φ) "_ HPost".
      wp_lam. 
      wp_alloc n as "Hn"; wp_alloc t as "Ht"; wp_alloc h as "Hh".
      iMod (inv_alloc N ⊤ (lazy_list_inv ∅ #h) with "[Hh Ht Hn]") as "Hinv".
      + iNext.
        iExists h, nil, (SOMEV (#INT_MIN, #t, #false, dummy_lock)). 
        iFrame. iSplit. done. iSplit. done. simpl.
        iExists INT_MIN, t, false, dummy_lock.
        iExists (SOMEV (#INT_MAX, #n, #false, dummy_lock)).
        iFrame. iSplit. done. iSplit. done.
        iNext.
        iExists INT_MAX, n, false, dummy_lock.
        iExists NONEV.
        iFrame. iSplit. done. iSplit; done.
      + by iApply "HPost".
    Qed.

    Theorem contains_spec (S: gset Z) (v: val) (key: Z) :
      {{{ is_lazy_list S v }}}
        contains !v #key
      {{{ b, RET b; 
        is_lazy_list S v
        ∗
        ⌜ (b = #false ∧ ¬ key ∈ S)
        ∨
        (b = #true ∧ key ∈ S) ⌝
      }}}.
    Proof.
    Admitted.
  End Proofs.
End LazyListSpec.