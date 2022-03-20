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
    * The current key is separated from the list
    * in order to make the recursion possible.
    *)
    Fixpoint list_equiv (node: val) (cur: Z) (L: list Z) : iProp Σ :=
      match L with
      | nil => ∃ (n: loc) (k: Z) (m: bool) (l: val),
                  ⌜ node = SOMEV #n ⌝
                  ∗
                  n ↦ (#k, NONEV, #m, l)
                  ∗
                  ⌜ k = cur ⌝
                  (* ∗
                  is_lock γ l ??? *)

      | h :: t => ∃ (n: loc) (k: Z) (next: val) (m: bool) (l: val),
                  ⌜ node = SOMEV #n ⌝
                  ∗
                  n ↦ (#k, next, #m, l)
                  ∗
                  ⌜ k = cur ⌝
                  ∗
                  (* is_lock γ l ???
                  ∗ *)
                  ▷list_equiv next h t
      end.

    (* 
    * The invariant for the lazy list asserts that
    * the underlying set S is sorted and must contain
    * the same elements as S.
    *)
    Definition lazy_list_inv (S: gset Z) (v: val) : iProp Σ := 
      ∃ (L: list Z),
      ⌜ Permutation L (elements S) ⌝
      ∗
      (* ⌜ Sorted Zlt L ⌝
      ∗ *)
      list_equiv (SOMEV v) INT_MIN (L ++ [INT_MAX]) 
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
      wp_alloc t as "Ht"; wp_alloc h as "Hh".
      iMod (inv_alloc N ⊤ (lazy_list_inv ∅ #h) with "[Hh Ht]") as "Hinv".
      + iNext.
        iExists nil. 
        iSplit. done.
        simpl.
        iExists h, INT_MIN, (SOMEV #t), false, dummy_lock.
        iFrame. iSplit. done. iSplit. done.
        iNext.
        iExists t, INT_MAX, false, dummy_lock.
        iFrame. iSplit; done.
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